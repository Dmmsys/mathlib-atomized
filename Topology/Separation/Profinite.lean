/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Separation properties: profinite spaces
-/

public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Profinite

/-- A T0 space with a clopen basis is totally separated. -/
/-
**totallySeparatedSpace_of_t0_of_basis_clopen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：totallySeparatedSpace_of_t0_of_basis_clopen [T0Space X] (h : IsTopological
Basis { s : Set X | IsClopen s }) : TotallySeparatedSpace X
参数：h : IsTopologicalBasis { s : Set X | IsClopen s }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsClopen.compl`：IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用定理 `Eq.superset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] {a b : α}, a = b → b ⊆ a
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen_iff`：∀ {α : Type u} [t : Topo
logicalSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalB
asis b → (IsOpen s ↔ ∀ a ∈ s, ∃ t ∈ …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `disjoint_compl_left`：disjoint_compl_left : Disjoint aᶜ a
· 使用定理 `exists_isOpen_xor_mem`：exists_isOpen_xor_mem [T0Space X] {x y : X} (h : 
x != y) : exists U : Set X, IsOpen U ∧ Xor (x in U) (y in U)

--- 原说明 ---
A T0 space with a clopen basis is totally separated.
-/
theorem totallySeparatedSpace_of_t0_of_basis_clopen [T0Space X]
    (h : IsTopologicalBasis { s : Set X | IsClopen s }) : TotallySeparatedSpace X := by
  constructor
  rintro x - y - hxy
  choose U hU using exists_isOpen_xor_mem hxy
  obtain ⟨hU₀, hU₁⟩ := hU
  rcases hU₁ with hx | hy
  · choose V hV using h.isOpen_iff.mp hU₀ x hx.1
    exact ⟨V, Vᶜ, hV.1.isOpen, hV.1.compl.isOpen, hV.2.1, notMem_subset hV.2.2 hx.2,
      (union_compl_self V).superset, disjoint_compl_right⟩
  · choose V hV using h.isOpen_iff.mp hU₀ y hy.1
    exact ⟨Vᶜ, V, hV.1.compl.isOpen, hV.1.isOpen, notMem_subset hV.2.2 hy.2, hV.2.1,
      (union_comm _ _ ▸ union_compl_self V).superset, disjoint_compl_left⟩

variable [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
/-
**nhds_basis_clopen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_basis_clopen (x : X) : (𝓝 x).HasBasis (fun s : Set X => x in s ∧ IsCl
open s) id
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `totallyDisconnectedSpace_iff_connectedComponent_singleton`：totallyDiscon
nectedSpace_iff_connectedComponent_singleton : TotallyDisconnectedSpace α ↔ fora
ll x : α, connectedComponent x = {x}
· 使用定理 `isClopen_univ`：isClopen_univ : IsClopen (univ : Set X)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsClopen.inter`：IsClopen.inter (hs : IsClopen s) (ht : IsClopen t) : IsC
lopen (s inter t)
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `connectedComponent_eq_iInter_isClopen`：connectedComponent_eq_iInter_isCl
open [T2Space X] [CompactSpace X] (x : X) : connectedComponent x = ⋂ s : { s : S
et X // IsClopen s ∧ x in s…
· 使用定理 `exists_subset_nhds_of_compactSpace`：exists_subset_nhds_of_compactSpace [
CompactSpace X] [Nonempty ι] {V : ι -> Set X} (hV : Directed (· ⊇ ·) V) (hV_clos
ed : forall i, IsClosed …
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
-/
theorem nhds_basis_clopen (x : X) : (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsClopen s) id :=
  ⟨fun U => by
    constructor
    · have hx : connectedComponent x = {x} :=
        totallyDisconnectedSpace_iff_connectedComponent_singleton.mp ‹_› x
      rw [connectedComponent_eq_iInter_isClopen] at hx
      intro hU
      let N := { s // IsClopen s ∧ x ∈ s }
      rsuffices ⟨⟨s, hs, hs'⟩, hs''⟩ : ∃ s : N, s.val ⊆ U
      · exact ⟨s, ⟨hs', hs⟩, hs''⟩
      have : Nonempty N := ⟨⟨univ, isClopen_univ, mem_univ x⟩⟩
      have hNcl : ∀ s : N, IsClosed s.val := fun s => s.property.1.1
      have hdir : Directed GE.ge fun s : N => s.val := by
        rintro ⟨s, hs, hxs⟩ ⟨t, ht, hxt⟩
        exact ⟨⟨s ∩ t, hs.inter ht, ⟨hxs, hxt⟩⟩, inter_subset_left, inter_subset_right⟩
      have h_nhds : ∀ y ∈ ⋂ s : N, s.val, U ∈ 𝓝 y := fun y y_in => by
        rw [hx, mem_singleton_iff] at y_in
        rwa [y_in]
      exact exists_subset_nhds_of_compactSpace hdir hNcl h_nhds
    · rintro ⟨V, ⟨hxV, -, V_op⟩, hUV : V ⊆ U⟩
      rw [mem_nhds_iff]
      exact ⟨V, hUV, V_op, hxV⟩⟩
/-
**isTopologicalBasis_isClopen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTopologicalBasis_isClopen : IsTopologicalBasis { s : Set X | IsClopen s 
}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`：isTopologicalBasi
s_of_isOpen_of_nhds {s : Set (Set α)} (h_open : forall u in s, IsOpen u) (h_nhds
 : forall (a : α) (u : Set α), a in u -> Is…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `nhds_basis_clopen`：nhds_basis_clopen (x : X) : (𝓝 x).HasBasis (fun s : S
et X => x in s ∧ IsClopen s) id
-/
theorem isTopologicalBasis_isClopen : IsTopologicalBasis { s : Set X | IsClopen s } := by
  apply isTopologicalBasis_of_isOpen_of_nhds fun U (hU : IsClopen U) => hU.2
  intro x U hxU U_op
  have : U ∈ 𝓝 x := IsOpen.mem_nhds U_op hxU
  rcases (nhds_basis_clopen x).mem_iff.mp this with ⟨V, ⟨hxV, hV⟩, hVU : V ⊆ U⟩
  use V
  tauto

/-- Every member of an open set in a compact Hausdorff totally disconnected space
  is contained in a clopen set contained in the open set. -/
/-
**compact_exists_isClopen_in_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compact_exists_isClopen_in_isOpen {x : X} {U : Set X} (is_open : IsOpen U)
 (memU : x in U) : exists V : Set X, IsClopen V ∧ x in V ∧ V subseteq U
参数：is_open : IsOpen U；memU : x in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.mem_nhds_iff`：∀ {α : Type u} [t : To
pologicalSpace α] {a : α} {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTo
pologicalBasis b → (s ∈ nhds a ↔ ∃ t ∈…
· 使用定理 `isTopologicalBasis_isClopen`：isTopologicalBasis_isClopen : IsTopological
Basis { s : Set X | IsClopen s }
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
Every member of an open set in a compact Hausdorff totally disconnected space
  is contained in a clopen set contained in the open set.
-/
theorem compact_exists_isClopen_in_isOpen {x : X} {U : Set X} (is_open : IsOpen U) (memU : x ∈ U) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U :=
  isTopologicalBasis_isClopen.mem_nhds_iff.1 (is_open.mem_nhds memU)

end Profinite

section LocallyCompact

variable {H : Type*} [TopologicalSpace H] [LocallyCompactSpace H] [T2Space H]

/-- A locally compact Hausdorff totally disconnected space has a basis with clopen elements. -/
/-
**loc_compact_Haus_tot_disc_of_zero_dim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：loc_compact_Haus_tot_disc_of_zero_dim [TotallyDisconnectedSpace H] : IsTop
ologicalBasis { s : Set H | IsClopen s }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`：isTopologicalBasi
s_of_isOpen_of_nhds {s : Set (Set α)} (h_open : forall u in s, IsOpen u) (h_nhds
 : forall (a : α) (u : Set α), a in u -> Is…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `exists_compact_subset`：exists_compact_subset [LocallyCompactSpace X] {x 
: X} {U : Set X} (hU : IsOpen U) (hx : x in U) : exists K : Set X, IsCompact K ∧
 x in inter…
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `compact_exists_isClopen_in_isOpen`：compact_exists_isClopen_in_isOpen {x 
: X} {U : Set X} (is_open : IsOpen U) (memU : x in U) : exists V : Set X, IsClop
en V ∧ x in V ∧ V subse…
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `Topology.IsClosedEmbedding.isClosed_iff_image_isClosed`：∀ {X : Type u_1}
 {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpa
ce Y],   Topology.IsClosedEmbedding f → ∀ {s…
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
A locally compact Hausdorff totally disconnected space has a basis with clopen e
lements.
-/
theorem loc_compact_Haus_tot_disc_of_zero_dim [TotallyDisconnectedSpace H] :
    IsTopologicalBasis { s : Set H | IsClopen s } := by
  refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => hu.2) fun x U memU hU => ?_
  obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset hU memU
  let u : Set s := ((↑) : s → H) ⁻¹' interior s
  have u_open_in_s : IsOpen u := isOpen_interior.preimage continuous_subtype_val
  lift x to s using interior_subset xs
  have : CompactSpace s := isCompact_iff_compactSpace.1 comp
  obtain ⟨V : Set s, VisClopen, Vx, V_sub⟩ := compact_exists_isClopen_in_isOpen u_open_in_s xs
  have VisClopen' : IsClopen (((↑) : s → H) '' V) := by
    refine ⟨comp.isClosed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.1 VisClopen.1,
      ?_⟩
    let v : Set u := ((↑) : u → s) ⁻¹' V
    have : ((↑) : u → H) = ((↑) : s → H) ∘ ((↑) : u → s) := rfl
    have f0 : IsEmbedding ((↑) : u → H) := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
    have f1 : IsOpenEmbedding ((↑) : u → H) := by
      refine ⟨f0, ?_⟩
      · have : Set.range ((↑) : u → H) = interior s := by
          rw [this, Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe]
          apply Set.inter_eq_self_of_subset_right interior_subset
        rw [this]
        apply isOpen_interior
    have f2 : IsOpen v := VisClopen.2.preimage continuous_subtype_val
    have f3 : ((↑) : s → H) '' V = ((↑) : u → H) '' v := by
      rw [this, image_comp, Subtype.image_preimage_coe, inter_eq_self_of_subset_right V_sub]
    rw [f3]
    apply f1.isOpenMap v f2
  use (↑) '' V, VisClopen', by simp [Vx], Subset.trans (by simp) sU

/-- A locally compact Hausdorff space is totally disconnected
  if and only if it is totally separated. -/
/-
**loc_compact_t2_tot_disc_iff_tot_sep** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：loc_compact_t2_tot_disc_iff_tot_sep : TotallyDisconnectedSpace H ↔ Totally
SeparatedSpace H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `totallySeparatedSpace_of_t0_of_basis_clopen`：totallySeparatedSpace_of_t0
_of_basis_clopen [T0Space X] (h : IsTopologicalBasis { s : Set X | IsClopen s })
 : TotallySeparatedSpace X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `loc_compact_Haus_tot_disc_of_zero_dim`：loc_compact_Haus_tot_disc_of_zero
_dim [TotallyDisconnectedSpace H] : IsTopologicalBasis { s : Set H | IsClopen s 
}
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α

--- 原说明 ---
A locally compact Hausdorff space is totally disconnected
  if and only if it is totally separated.
-/
theorem loc_compact_t2_tot_disc_iff_tot_sep :
    TotallyDisconnectedSpace H ↔ TotallySeparatedSpace H := by
  constructor
  · intro h
    exact totallySeparatedSpace_of_t0_of_basis_clopen loc_compact_Haus_tot_disc_of_zero_dim
  apply TotallySeparatedSpace.totallyDisconnectedSpace

/-- A totally disconnected compact Hausdorff space is totally separated. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A totally disconnected compact Hausdorff space is totally separated.
-/
instance (priority := 100) [TotallyDisconnectedSpace H] : TotallySeparatedSpace H :=
  loc_compact_t2_tot_disc_iff_tot_sep.mp inferInstance

/-- In a totally disconnected compact Hausdorff space `X`, if `Z ⊆ U` are subsets with `Z` closed
and `U` open, there exists a clopen `C` with `Z ⊆ C ⊆ U`. -/
/-
**exists_clopen_of_closed_subset_open** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_clopen_of_closed_subset_open {X : Type*} [TopologicalSpace X] [Comp
actSpace X] [T2Space X] [TotallyDisconnectedSpace X] {Z U : Set X} (hZ : IsClose
d Z) (hU : IsOpen U) (hZU : Z subseteq U) : exists C : Set X, IsClopen C ∧ Z sub
seteq C ∧ C subseteq U
参数：hZ : IsClosed Z；hU : IsOpen U；hZU : Z subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Finite.isClopen_biUnion`：Set.Finite.isClopen_biUnion {Y} {s : Set Y}
 {f : Y -> Set X} (hs : s.Finite) (h : forall i in s, IsClopen <| f i) : IsClope
n (⋃ i in s, f i)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `compact_exists_isClopen_in_isOpen`：compact_exists_isClopen_in_isOpen {x 
: X} {U : Set X} (is_open : IsOpen U) (memU : x in U) : exists V : Set X, IsClop
en V ∧ x in V ∧ V subse…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
In a totally disconnected compact Hausdorff space `X`, if `Z ⊆ U` are subsets wi
th `Z` closed
and `U` open, there exists a clopen `C` with `Z ⊆ C ⊆ U`.
-/
lemma exists_clopen_of_closed_subset_open {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {Z U : Set X} (hZ : IsClosed Z) (hU : IsOpen U) (hZU : Z ⊆ U) :
    ∃ C : Set X, IsClopen C ∧ Z ⊆ C ∧ C ⊆ U := by
  -- every `z ∈ Z` has clopen neighborhood `V z ⊆ U`
  choose V hV using fun (z : Z) ↦ compact_exists_isClopen_in_isOpen hU (hZU z.property)
  -- the `V z` cover `Z`
  have V_cover : Z ⊆ ⋃ z, V z := fun z hz ↦ mem_iUnion.mpr ⟨⟨z, hz⟩, (hV ⟨z, hz⟩).2.1⟩
  -- choose a finite subcover
  choose I hI using hZ.isCompact.elim_finite_subcover V (fun z ↦ (hV z).1.isOpen) V_cover
  -- the union of this finite subcover does the job
  exact ⟨⋃ (i ∈ I), V i, I.finite_toSet.isClopen_biUnion (fun i _ ↦ (hV i).1), hI, by simp_all⟩

/-- Let `X` be a totally disconnected compact Hausdorff space, `D i ⊆ X` a finite family of clopens,
and `Z i ⊆ D i` closed. Assume that the `Z i` are pairwise disjoint. Then there exist clopens
`Z i ⊆ C i ⊆ D i` with the `C i` disjoint, and such that `∪ D i ⊆ ∪ C i`. -/
/-
**exists_clopen_partition_of_clopen_cover** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_clopen_partition_of_clopen_cover {X I : Type*} [TopologicalSpace X]
 [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [Finite I] {Z D : I -
> Set X} (Z_closed : forall i, IsClosed (Z i)) (D_clopen : forall i, IsClopen (D
 i)) (Z_subset_D : forall i, Z i subseteq D i) (Z_disj : univ.PairwiseDisjoint Z
) : exists C : I -> Set X, (forall i, IsClopen (C i)) ∧ (forall i, Z i subseteq 
C i) ∧ (forall i, C i subseteq D i) ∧ (⋃ i, D i) subseteq (⋃ i, C i) ∧ (univ.Pai
rwiseDisjoint C)
参数：Z_closed : forall i, IsClosed (Z i)；D_clopen : forall i, IsClopen (D i)；Z_sub
set_D : forall i, Z i subseteq D i；Z_disj : univ.PairwiseDisjoint Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.induction_empty_option`：Finite.induction_empty_option {P : Type u
 -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β) (h_empty : P PEmpty) (h
_option : forall {α…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.InjOn.pairwiseDisjoint_image`：∀ {α : Type u_1} {ι : Type u_4} {ι' : 
Type u_5} [inst : PartialOrder α] [inst_1 : OrderBot α] {f : ι → α} {g : ι' → ι}
   {s : Set ι'}, Set.I…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Function.Surjective.iUnion_comp`：iUnion_comp {f : ι -> ι₂} (hf : Surject
ive f) (g : ι₂ -> Set α) : ⋃ x, g (f x) = ⋃ y, g y
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `Set.PairwiseDisjoint.subset`：∀ {α : Type u_1} {ι : Type u_4} [inst : Par
tialOrder α] [inst_1 : OrderBot α] {s t : Set ι} {f : ι → α},   t.PairwiseDisjoi
nt f → s ⊆ t → s.…
· 使用定理 `IsOpen.sdiff`：IsOpen.sdiff (h₁ : IsOpen s) (h₂ : IsClosed t) : IsOpen (s
 \ t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isClosed_iUnion_of_finite`：isClosed_iUnion_of_finite [Finite ι] {s : ι -
> Set X} (h : forall i, IsClosed (s i)) : IsClosed (⋃ i, s i)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `exists_clopen_of_closed_subset_open`：exists_clopen_of_closed_subset_open
 {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnec
tedSpace X] {Z U : Set X}…
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
Let `X` be a totally disconnected compact Hausdorff space, `D i ⊆ X` a finite fa
mily of clopens,
and `Z i ⊆ D i` closed. Assume that the `Z i` are pairwise disjoint. Then there 
exist clopens
`Z i ⊆ C i ⊆ D i` with the `C i` disjoint, and such that `∪ D i ⊆ ∪ C i`.
-/
lemma exists_clopen_partition_of_clopen_cover
    {X I : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [Finite I] {Z D : I → Set X}
    (Z_closed : ∀ i, IsClosed (Z i)) (D_clopen : ∀ i, IsClopen (D i))
    (Z_subset_D : ∀ i, Z i ⊆ D i) (Z_disj : univ.PairwiseDisjoint Z) :
    ∃ C : I → Set X, (∀ i, IsClopen (C i)) ∧ (∀ i, Z i ⊆ C i) ∧ (∀ i, C i ⊆ D i) ∧
    (⋃ i, D i) ⊆ (⋃ i, C i) ∧ (univ.PairwiseDisjoint C) := by
  induction I using Finite.induction_empty_option with
  | of_equiv e IH =>
    obtain ⟨C, h1, h2, h3, h4, h5⟩ := IH (Z := Z ∘ e) (D := D ∘ e)
      (fun i ↦ Z_closed (e i)) (fun i ↦ D_clopen (e i))
      (fun i ↦ Z_subset_D (e i)) (by simpa [← e.injective.injOn.pairwiseDisjoint_image])
    refine ⟨C ∘ e.symm, fun i ↦ h1 (e.symm i), fun i ↦ by simpa using h2 (e.symm i),
      fun i ↦ by simpa using h3 (e.symm i), ?_,
      by simpa [← e.symm.injective.injOn.pairwiseDisjoint_image]⟩
    simp only [Function.comp_apply, iUnion_subset_iff] at h4
    simpa [e.symm.surjective.iUnion_comp C] using fun i ↦ h4 (e.symm i)
  | h_empty => exact ⟨fun _ ↦ univ, by simp, by simp, by simp, by simp, fun i ↦ PEmpty.elim i⟩
  | @h_option I _ IH =>
    -- let `Z'` be the restriction of `Z` along `some : I → Option I`
    let Z' : I → Set X := fun i ↦ Z (some i)
    have Z'_closed (i : I) : IsClosed (Z (some i)) := Z_closed (some i)
    have Z'_disj : univ.PairwiseDisjoint (Z ∘ some) := by
      rw [← (Option.some_injective _).injOn.pairwiseDisjoint_image]
      exact PairwiseDisjoint.subset Z_disj (by simp)
    -- find `Z none ⊆ V ⊆ D none \ ⋃ Z'` using `exists_clopen_of_closed_subset_open`
    let U : Set X := D none \ ⋃ i, Z (some i)
    have U_open : IsOpen U := IsOpen.sdiff (D_clopen none).2
      (isClosed_iUnion_of_finite (fun i ↦ Z_closed (some i)))
    have Z0_subset_U : Z none ⊆ U := by
      rw [subset_sdiff]
      simpa using ⟨Z_subset_D none, fun i ↦ (by apply Z_disj; all_goals simp)⟩
    obtain ⟨V, V_clopen, Z0_subset_V, V_subset_U⟩ :=
      exists_clopen_of_closed_subset_open (Z_closed none) U_open Z0_subset_U
    have V_subset_D0 : V ⊆ D none := subset_trans V_subset_U sdiff_subset
    -- choose `Z' i ⊆ C' i ⊆ D' i = D i.succ \ V` using the inductive hypothesis
    let D' : I → Set X := fun i ↦ D (some i) \ V
    have D'_clopen (i : I) : IsClopen (D' i) := (D_clopen (some i)).diff V_clopen
    have Z'_subset_D' (i : I) : Z' i ⊆ D' i := by
      rw [subset_sdiff]
      refine ⟨by grind, Disjoint.mono_right V_subset_U ?_⟩
      exact Disjoint.mono_left (subset_iUnion_of_subset i fun _ h ↦ h) (by grind)
    obtain ⟨C', C'_clopen, Z'_subset_C', C'_subset_D', C'_cover_D', C'_disj⟩ :=
      IH Z'_closed D'_clopen Z'_subset_D' Z'_disj
    -- now choose `C0 = D none \ ⋃ C' i`
    let C0 : Set X := D none \ ⋃ i, C' i
    have : IsClopen C0 := (D_clopen none).diff (isClopen_iUnion_of_finite C'_clopen)
    have : Z none ⊆ C0 := by
      simp only [C0, subset_sdiff]
      exact ⟨by grind, Disjoint.mono_left Z0_subset_V (by simp; grind)⟩
    -- patch together to define `C none := C0`, `C (some i) := C' i`
    -- and verify the needed properties
    let C : Option I → Set X := fun i ↦ Option.casesOn i C0 C'
    refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try rintro (_ | i); all_goals grind
    · intro x hx
      rw [mem_iUnion] at hx ⊢
      by_cases hx0 : x ∈ C0; { exact ⟨none, hx0⟩ }
      by_cases hxD : x ∈ D none
      · have hxC' : x ∈ ⋃ i, C' i := by grind
        obtain ⟨i, hi⟩ := mem_iUnion.mp hxC'
        exact ⟨some i, hi⟩
      · obtain ⟨none | j, hi⟩ := hx; {grind}
        have hxD' : x ∈ ⋃ i, D' i := mem_iUnion.mpr ⟨j, by grind⟩
        obtain ⟨k, hk⟩ := mem_iUnion.mp <| C'_cover_D' hxD'
        exact ⟨some k, hk⟩
    · rw [Set.pairwiseDisjoint_iff]
      rintro (_ | i) _ (_ | j) _
      · simp
      · simpa [C, C0, Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] using
          Disjoint.mono_right (subset_iUnion C' j) disjoint_sdiff_left
      · simpa [C, C0, Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] using
          Disjoint.mono_left (subset_iUnion C' i) disjoint_sdiff_right
      · simpa using (Set.pairwiseDisjoint_iff.mp C'_disj) (by trivial) (by trivial)

end LocallyCompact

