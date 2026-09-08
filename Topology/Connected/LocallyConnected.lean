/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.Clopen

/-!
# Locally connected topological spaces

A topological space is **locally connected** if each neighborhood filter admits a basis
of connected *open* sets. Local connectivity is equivalent to each point having a basis
of connected (not necessarily open) sets --- but in a non-trivial way, so we choose this definition
and prove the equivalence later in `locallyConnectedSpace_iff_connected_basis`.
-/

public section

open Set Topology

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι → Type*} [TopologicalSpace α]
  {s t u v : Set α}

section LocallyConnectedSpace

/-- A topological space is **locally connected** if each neighborhood filter admits a basis
of connected *open* sets. Note that it is equivalent to each point having a basis of connected
(not necessarily open) sets but in a non-trivial way, so we choose this definition and prove the
equivalence later in `locallyConnectedSpace_iff_connected_basis`. -/
/-
**LocallyConnectedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is **locally connected** if each neighborhood filter admits 
a basis
of connected *open* sets. Note that it is equivalent to each point having a basi
s of connected
(not necessarily open) sets but in a non-trivial way, so we choose this definiti
on and prove the
equivalence later in `locallyConnectedSpace_iff_connected_basis`.
-/
class LocallyConnectedSpace (α : Type*) [TopologicalSpace α] : Prop where
  /-- Open connected neighborhoods form a basis of the neighborhoods filter. -/
  open_connected_basis : ∀ x, (𝓝 x).HasBasis (fun s : Set α => IsOpen s ∧ x ∈ s ∧ IsConnected s) id
/-
**locallyConnectedSpace_iff_hasBasis_isOpen_isConnected** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：locallyConnectedSpace_iff_hasBasis_isOpen_isConnected : LocallyConnectedSp
ace α ↔ forall x, (𝓝 x).HasBasis (fun s : Set α => IsOpen s ∧ x in s ∧ IsConnect
ed s) id
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyConnectedSpace.open_connected_basis`：∀ {α : Type u_3} {inst : Top
ologicalSpace α} [self : LocallyConnectedSpace α] (x : α),   (nhds x).HasBasis (
fun s => IsOpen s ∧ x ∈ s ∧ IsCo…
-/
theorem locallyConnectedSpace_iff_hasBasis_isOpen_isConnected :
    LocallyConnectedSpace α ↔
      ∀ x, (𝓝 x).HasBasis (fun s : Set α => IsOpen s ∧ x ∈ s ∧ IsConnected s) id :=
  ⟨@LocallyConnectedSpace.open_connected_basis _ _, LocallyConnectedSpace.mk⟩
/-
**locallyConnectedSpace_iff_subsets_isOpen_isConnected** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：locallyConnectedSpace_iff_subsets_isOpen_isConnected : LocallyConnectedSpa
ce α ↔ forall x, forall U in 𝓝 x, exists V : Set α, V subseteq U ∧ IsOpen V ∧ x 
in V ∧ IsConnected V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
-/
theorem locallyConnectedSpace_iff_subsets_isOpen_isConnected :
    LocallyConnectedSpace α ↔
      ∀ x, ∀ U ∈ 𝓝 x, ∃ V : Set α, V ⊆ U ∧ IsOpen V ∧ x ∈ V ∧ IsConnected V := by
  simp_rw [locallyConnectedSpace_iff_hasBasis_isOpen_isConnected]
  refine forall_congr' fun _ => ?_
  constructor
  · intro h U hU
    rcases h.mem_iff.mp hU with ⟨V, hV, hVU⟩
    exact ⟨V, hVU, hV⟩
  · exact fun h => ⟨fun U => ⟨fun hU =>
      let ⟨V, hVU, hV⟩ := h U hU
      ⟨V, hV, hVU⟩, fun ⟨V, ⟨hV, hxV, _⟩, hVU⟩ => mem_nhds_iff.mpr ⟨V, hVU, hV, hxV⟩⟩⟩

/-- A space with discrete topology is a locally connected space. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A space with discrete topology is a locally connected space.
-/
instance (priority := 100) DiscreteTopology.toLocallyConnectedSpace (α) [TopologicalSpace α]
    [DiscreteTopology α] : LocallyConnectedSpace α :=
  locallyConnectedSpace_iff_subsets_isOpen_isConnected.2 fun x _U hU =>
    ⟨{x}, singleton_subset_iff.2 <| mem_of_mem_nhds hU, isOpen_discrete _, rfl,
      isConnected_singleton⟩
/-
**connectedComponentIn_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponentIn_mem_nhds [LocallyConnectedSpace α] {F : Set α} {x : α
} (h : F in 𝓝 x) : connectedComponentIn F x in 𝓝 x
参数：h : F in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `LocallyConnectedSpace.open_connected_basis`：∀ {α : Type u_3} {inst : Top
ologicalSpace α} [self : LocallyConnectedSpace α] (x : α),   (nhds x).HasBasis (
fun s => IsOpen s ∧ x ∈ s ∧ IsCo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `IsPreconnected.subset_connectedComponentIn`：IsPreconnected.subset_connec
tedComponentIn {x : α} {F : Set α} (hs : IsPreconnected s) (hxs : x in s) (hsF :
 s subseteq F) : s subseteq conn…
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
-/
theorem connectedComponentIn_mem_nhds [LocallyConnectedSpace α] {F : Set α} {x : α} (h : F ∈ 𝓝 x) :
    connectedComponentIn F x ∈ 𝓝 x := by
  rw [(LocallyConnectedSpace.open_connected_basis x).mem_iff] at h
  rcases h with ⟨s, ⟨h1s, hxs, h2s⟩, hsF⟩
  exact mem_nhds_iff.mpr ⟨s, h2s.isPreconnected.subset_connectedComponentIn hxs hsF, h1s, hxs⟩
/-
**IsOpen.connectedComponentIn** 是 Mathlib 中的一个定理，位于命名空间 `IsOpen`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] [LocallyConnectedSpace α] {F : 
Set α} {x : α},   IsOpen F → IsOpen (connectedComponentIn F x)
参数：connectedComponentIn F x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `connectedComponentIn_eq`：connectedComponentIn_eq {x y : α} {F : Set α} (
h : y in connectedComponentIn F x) : connectedComponentIn F x = connectedCompone
ntIn F y
· 使用定理 `connectedComponentIn_mem_nhds`：connectedComponentIn_mem_nhds [LocallyCon
nectedSpace α] {F : Set α} {x : α} (h : F in 𝓝 x) : connectedComponentIn F x in 
𝓝 x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `connectedComponentIn_subset`：connectedComponentIn_subset (F : Set α) (x 
: α) : connectedComponentIn F x subseteq F
-/
protected theorem IsOpen.connectedComponentIn [LocallyConnectedSpace α] {F : Set α} {x : α}
    (hF : IsOpen F) : IsOpen (connectedComponentIn F x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [connectedComponentIn_eq hy]
  exact connectedComponentIn_mem_nhds (hF.mem_nhds <| connectedComponentIn_subset F x hy)
/-
**isOpen_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_connectedComponent [LocallyConnectedSpace α] {x : α} : IsOpen (conn
ectedComponent x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `connectedComponentIn_univ`：connectedComponentIn_univ (x : α) : connected
ComponentIn univ x = connectedComponent x
· 使用定理 `IsOpen.connectedComponentIn`：∀ {α : Type u} [inst : TopologicalSpace α] 
[LocallyConnectedSpace α] {F : Set α} {x : α},   IsOpen F → IsOpen (connectedCom
ponentIn F x)
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
theorem isOpen_connectedComponent [LocallyConnectedSpace α] {x : α} :
    IsOpen (connectedComponent x) := by
  rw [← connectedComponentIn_univ]
  exact isOpen_univ.connectedComponentIn
/-
**isClopen_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_connectedComponent [LocallyConnectedSpace α] {x : α} : IsClopen (
connectedComponent x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_connectedComponent`：isClosed_connectedComponent {x : α} : IsClo
sed (connectedComponent x)
· 使用定理 `isOpen_connectedComponent`：isOpen_connectedComponent [LocallyConnectedSp
ace α] {x : α} : IsOpen (connectedComponent x)
-/
theorem isClopen_connectedComponent [LocallyConnectedSpace α] {x : α} :
    IsClopen (connectedComponent x) :=
  ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩
/-
**locallyConnectedSpace_iff_connectedComponentIn_open** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：locallyConnectedSpace_iff_connectedComponentIn_open : LocallyConnectedSpac
e α ↔ forall F : Set α, IsOpen F -> forall x in F, IsOpen (connectedComponentIn 
F x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.connectedComponentIn`：∀ {α : Type u} [inst : TopologicalSpace α] 
[LocallyConnectedSpace α] {F : Set α} {x : α},   IsOpen F → IsOpen (connectedCom
ponentIn F x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `locallyConnectedSpace_iff_subsets_isOpen_isConnected`：locallyConnectedSp
ace_iff_subsets_isOpen_isConnected : LocallyConnectedSpace α ↔ forall x, forall 
U in 𝓝 x, exists V : Set α, V subseteq U ∧…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `connectedComponentIn_subset`：connectedComponentIn_subset (F : Set α) (x 
: α) : connectedComponentIn F x subseteq F
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `mem_connectedComponentIn`：mem_connectedComponentIn {x : α} {F : Set α} (
hx : x in F) : x in connectedComponentIn F x
· 使用定理 `isConnected_connectedComponentIn_iff`：isConnected_connectedComponentIn_i
ff {x : α} {F : Set α} : IsConnected (connectedComponentIn F x) ↔ x in F
-/
theorem locallyConnectedSpace_iff_connectedComponentIn_open :
    LocallyConnectedSpace α ↔
      ∀ F : Set α, IsOpen F → ∀ x ∈ F, IsOpen (connectedComponentIn F x) := by
  constructor
  · intro h
    exact fun F hF x _ => hF.connectedComponentIn
  · intro h
    rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    refine fun x U hU =>
        ⟨connectedComponentIn (interior U) x,
          (connectedComponentIn_subset _ _).trans interior_subset, h _ isOpen_interior x ?_,
          mem_connectedComponentIn ?_, isConnected_connectedComponentIn_iff.mpr ?_⟩ <;>
      exact mem_interior_iff_mem_nhds.mpr hU
/-
**locallyConnectedSpace_iff_connected_subsets** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：locallyConnectedSpace_iff_connected_subsets : LocallyConnectedSpace α ↔ fo
rall (x : α), forall U in 𝓝 x, exists V in 𝓝 x, IsPreconnected V ∧ V subseteq U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `locallyConnectedSpace_iff_subsets_isOpen_isConnected`：locallyConnectedSp
ace_iff_subsets_isOpen_isConnected : LocallyConnectedSpace α ↔ forall x, forall 
U in 𝓝 x, exists V : Set α, V subseteq U ∧…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `locallyConnectedSpace_iff_connectedComponentIn_open`：locallyConnectedSpa
ce_iff_connectedComponentIn_open : LocallyConnectedSpace α ↔ forall F : Set α, I
sOpen F -> forall x in F, IsOpen (connect…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `connectedComponentIn_eq`：connectedComponentIn_eq {x y : α} {F : Set α} (
h : y in connectedComponentIn F x) : connectedComponentIn F x = connectedCompone
ntIn F y
· 使用定理 `connectedComponentIn_subset`：connectedComponentIn_subset (F : Set α) (x 
: α) : connectedComponentIn F x subseteq F
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `IsPreconnected.subset_connectedComponentIn`：IsPreconnected.subset_connec
tedComponentIn {x : α} {F : Set α} (hs : IsPreconnected s) (hxs : x in s) (hsF :
 s subseteq F) : s subseteq conn…
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem locallyConnectedSpace_iff_connected_subsets :
    LocallyConnectedSpace α ↔ ∀ (x : α), ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, IsPreconnected V ∧ V ⊆ U := by
  constructor
  · rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    intro h x U hxU
    rcases h x U hxU with ⟨V, hVU, hV₁, hxV, hV₂⟩
    exact ⟨V, hV₁.mem_nhds hxV, hV₂.isPreconnected, hVU⟩
  · rw [locallyConnectedSpace_iff_connectedComponentIn_open]
    refine fun h U hU x _ => isOpen_iff_mem_nhds.mpr fun y hy => ?_
    rw [connectedComponentIn_eq hy]
    rcases h y U (hU.mem_nhds <| (connectedComponentIn_subset _ _) hy) with ⟨V, hVy, hV, hVU⟩
    exact Filter.mem_of_superset hVy (hV.subset_connectedComponentIn (mem_of_mem_nhds hVy) hVU)
/-
**locallyConnectedSpace_iff_connected_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：locallyConnectedSpace_iff_connected_basis : LocallyConnectedSpace α ↔ fora
ll x, (𝓝 x).HasBasis (fun s : Set α => s in 𝓝 x ∧ IsPreconnected s) id
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `locallyConnectedSpace_iff_connected_subsets`：locallyConnectedSpace_iff_c
onnected_subsets : LocallyConnectedSpace α ↔ forall (x : α), forall U in 𝓝 x, ex
ists V in 𝓝 x, IsPreconnected V ∧…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
-/
theorem locallyConnectedSpace_iff_connected_basis :
    LocallyConnectedSpace α ↔
      ∀ x, (𝓝 x).HasBasis (fun s : Set α => s ∈ 𝓝 x ∧ IsPreconnected s) id := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  exact forall_congr' fun x => Filter.hasBasis_self.symm
/-
**locallyConnectedSpace_of_connected_bases** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：locallyConnectedSpace_of_connected_bases {ι : Type*} (b : α -> ι -> Set α)
 (p : α -> ι -> Prop) (hbasis : forall x, (𝓝 x).HasBasis (p x) (b x)) (hconnecte
d : forall x i, p x i -> IsPreconnected (b x i)) : LocallyConnectedSpace α
参数：b : α -> ι -> Set α；p : α -> ι -> Prop；hbasis : forall x, (𝓝 x).HasBasis (p x
) (b x)；hconnected : forall x i, p x i -> IsPreconnected (b x i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `locallyConnectedSpace_iff_connected_basis`：locallyConnectedSpace_iff_con
nected_basis : LocallyConnectedSpace α ↔ forall x, (𝓝 x).HasBasis (fun s : Set α
 => s in 𝓝 x ∧ IsPreconnected s…
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.HasBasis.property_index`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α} {t : Set α} (h : l.HasBasis p s)   (ht : t
 ∈ l), p ↑(h.index t…
· 使用定理 `Filter.HasBasis.set_index_subset`：∀ {α : Type u_1} {ι : Sort u_4} {l : F
ilter α} {p : ι → Prop} {s : ι → Set α} {t : Set α} (h : l.HasBasis p s)   (ht :
 t ∈ l), s ↑(h.index t…
-/
theorem locallyConnectedSpace_of_connected_bases {ι : Type*} (b : α → ι → Set α) (p : α → ι → Prop)
    (hbasis : ∀ x, (𝓝 x).HasBasis (p x) (b x))
    (hconnected : ∀ x i, p x i → IsPreconnected (b x i)) : LocallyConnectedSpace α := by
  rw [locallyConnectedSpace_iff_connected_basis]
  exact fun x =>
    (hbasis x).to_hasBasis
      (fun i hi => ⟨b x i, ⟨(hbasis x).mem_of_mem hi, hconnected x i hi⟩, subset_rfl⟩) fun s hs =>
      ⟨(hbasis x).index s hs.1, ⟨(hbasis x).property_index hs.1, (hbasis x).set_index_subset hs.1⟩⟩
/-
**TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected [LocallyConnecte
dSpace α] : TopologicalSpace.IsTopologicalBasis {s : Set α | IsOpen s ∧ IsPrecon
nected s}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.of_hasBasis_nhds`：∀ {α : Type u} [t 
: TopologicalSpace α] {s : Set (Set α)},   (∀ (a : α), (nhds a).HasBasis (fun t 
=> t ∈ s ∧ a ∈ t) id) → TopologicalSpace.I…
· 使用定理 `Filter.HasBasis.congr`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p
 : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {p' : ι → Prop} {s' : ι →
 Set α}, (∀…
· 使用定理 `LocallyConnectedSpace.open_connected_basis`：∀ {α : Type u_3} {inst : Top
ologicalSpace α} [self : LocallyConnectedSpace α] (x : α),   (nhds x).HasBasis (
fun s => IsOpen s ∧ x ∈ s ∧ IsCo…
-/
theorem TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected [LocallyConnectedSpace α] :
    TopologicalSpace.IsTopologicalBasis {s : Set α | IsOpen s ∧ IsPreconnected s} :=
  .of_hasBasis_nhds fun x =>
    (LocallyConnectedSpace.open_connected_basis x).congr
      (by grind [IsConnected, Set.Nonempty])
      (fun _ _ => rfl)
/-
**locallyConnectedSpace_iff_isTopologicalBasis_isOpen_isPreconnected** 是 Mathlib
 中的一个定理，位于命名空间 ``。
形式化陈述：locallyConnectedSpace_iff_isTopologicalBasis_isOpen_isPreconnected : Local
lyConnectedSpace α ↔ TopologicalSpace.IsTopologicalBasis {s : Set α | IsOpen s ∧
 IsPreconnected s} where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected`：TopologicalSp
ace.IsTopologicalBasis.isOpen_isPreconnected [LocallyConnectedSpace α] : Topolog
icalSpace.IsTopologicalBasis {s : Set α | IsOpe…
· 使用定理 `Filter.HasBasis.congr`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p
 : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {p' : ι → Prop} {s' : ι →
 Set α}, (∀…
· 使用定理 `TopologicalSpace.IsTopologicalBasis.nhds_hasBasis`：∀ {α : Type u} [t : T
opologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologicalBasis b → 
∀ {a : α}, (nhds a).HasBasis (fun t => …
-/
theorem locallyConnectedSpace_iff_isTopologicalBasis_isOpen_isPreconnected :
    LocallyConnectedSpace α ↔
      TopologicalSpace.IsTopologicalBasis {s : Set α | IsOpen s ∧ IsPreconnected s} where
  mp _ := .isOpen_isPreconnected
  mpr h := ⟨fun _ => h.nhds_hasBasis.congr (by grind [IsConnected, Set.Nonempty]) (fun _ _ => rfl)⟩
/-
**Topology.IsOpenEmbedding.locallyConnectedSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.locallyConnectedSpace [LocallyConnectedSpace α] [
TopologicalSpace β] {f : β -> α} (h : IsOpenEmbedding f) : LocallyConnectedSpace
 β
参数：h : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `locallyConnectedSpace_of_connected_bases`：locallyConnectedSpace_of_conne
cted_bases {ι : Type*} (b : α -> ι -> Set α) (p : α -> ι -> Prop) (hbasis : fora
ll x, (𝓝 x).HasBasis (p x) (b …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.HasBasis.restrict_subset`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fi
lter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {V : Set α}, V ∈ l 
→ l.HasBasis (fun i =…
· 使用定理 `LocallyConnectedSpace.open_connected_basis`：∀ {α : Type u_3} {inst : Top
ologicalSpace α} [self : LocallyConnectedSpace α] (x : α),   (nhds x).HasBasis (
fun s => IsOpen s ∧ x ∈ s ∧ IsCo…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `IsPreconnected.preimage_of_isOpenMap`：IsPreconnected.preimage_of_isOpenM
ap [TopologicalSpace β] {f : α -> β} {s : Set β} (hs : IsPreconnected s) (hinj :
 Function.Injective f) (hf…
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
-/
lemma Topology.IsOpenEmbedding.locallyConnectedSpace [LocallyConnectedSpace α] [TopologicalSpace β]
    {f : β → α} (h : IsOpenEmbedding f) : LocallyConnectedSpace β := by
  refine locallyConnectedSpace_of_connected_bases (fun _ s ↦ f ⁻¹' s)
    (fun x s ↦ (IsOpen s ∧ f x ∈ s ∧ IsConnected s) ∧ s ⊆ range f) (fun x ↦ ?_)
    (fun x s hxs ↦ hxs.1.2.2.isPreconnected.preimage_of_isOpenMap h.injective h.isOpenMap hxs.2)
  rw [h.nhds_eq_comap]
  exact LocallyConnectedSpace.open_connected_basis (f x) |>.restrict_subset
    (h.isOpen_range.mem_nhds <| mem_range_self _) |>.comap _
/-
**IsOpen.locallyConnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.locallyConnectedSpace [LocallyConnectedSpace α] {U : Set α} (hU : I
sOpen U) : LocallyConnectedSpace U
参数：hU : IsOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsOpenEmbedding.locallyConnectedSpace`：Topology.IsOpenEmbedding
.locallyConnectedSpace [LocallyConnectedSpace α] [TopologicalSpace β] {f : β -> 
α} (h : IsOpenEmbedding f) : Locally…
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
-/
theorem IsOpen.locallyConnectedSpace [LocallyConnectedSpace α] {U : Set α} (hU : IsOpen U) :
    LocallyConnectedSpace U :=
  hU.isOpenEmbedding_subtypeVal.locallyConnectedSpace

/-- Any topology coinduced by a locally connected topology is locally connected. -/
/-
**Topology.IsCoinducing.locallyConnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsCoinducing.locallyConnectedSpace [LocallyConnectedSpace α] [Top
ologicalSpace β] {f : α -> β} (hf : IsCoinducing f) : LocallyConnectedSpace β
参数：hf : IsCoinducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `locallyConnectedSpace_iff_connectedComponentIn_open`：locallyConnectedSpa
ce_iff_connectedComponentIn_open : LocallyConnectedSpace α ↔ forall F : Set α, I
sOpen F -> forall x in F, IsOpen (connect…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.isOpen_preimage`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsCoinducing f → ∀ {s : Se…
· 使用定理 `ContinuousOn.preimage_connectedComponentIn`：ContinuousOn.preimage_connec
tedComponentIn [TopologicalSpace β] {f : α -> β} {F : Set β} (hf : ContinuousOn 
f (f ⁻¹' F)) (y : β) : f ⁻¹' con…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Topology.IsCoinducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsCo
inducing f → Continuou…
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `IsOpen.connectedComponentIn`：∀ {α : Type u} [inst : TopologicalSpace α] 
[LocallyConnectedSpace α] {F : Set α} {x : α},   IsOpen F → IsOpen (connectedCom
ponentIn F x)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)

--- 原说明 ---
Any topology coinduced by a locally connected topology is locally connected.
-/
theorem Topology.IsCoinducing.locallyConnectedSpace [LocallyConnectedSpace α]
    [TopologicalSpace β] {f : α → β} (hf : IsCoinducing f) : LocallyConnectedSpace β := by
  refine locallyConnectedSpace_iff_connectedComponentIn_open.2 fun F hF y _ ↦ ?_
  rw [← hf.isOpen_preimage, hf.continuous.continuousOn.preimage_connectedComponentIn]
  exact isOpen_biUnion fun x _ ↦ (hF.preimage hf.continuous).connectedComponentIn

/-- If a space is locally connected, the topology of its connected components is discrete. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a space is locally connected, the topology of its connected components is dis
crete.
-/
instance [LocallyConnectedSpace α] : DiscreteTopology <| ConnectedComponents α := by
  refine discreteTopology_iff_isOpen_singleton.mpr fun c ↦ ?_
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  simp [← ConnectedComponents.isQuotientMap_coe.isOpen_preimage,
    connectedComponents_preimage_singleton, isOpen_connectedComponent]

/-- A locally connected compact space has finitely many connected components. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A locally connected compact space has finitely many connected components.
-/
instance [LocallyConnectedSpace α] [CompactSpace α] : Finite <| ConnectedComponents α :=
  finite_of_compact_of_discrete

/-- The product of two locally connected spaces is locally connected. -/
/-
**Prod.locallyConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.locallyConnectedSpace [TopologicalSpace β] [LocallyConnectedSpace α] 
[LocallyConnectedSpace β] : LocallyConnectedSpace (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `locallyConnectedSpace_iff_connected_subsets`：locallyConnectedSpace_iff_c
onnected_subsets : LocallyConnectedSpace α ↔ forall (x : α), forall U in 𝓝 x, ex
ists V in 𝓝 x, IsPreconnected V ∧…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_prod_iff`：mem_nhds_prod_iff {x : X} {y : Y} {s : Set (X × Y)} :
 s in 𝓝 (x, y) ↔ exists u in 𝓝 x, exists v in 𝓝 y, u ×ˢ v subseteq s
· 使用定理 `prod_mem_nhds`：prod_mem_nhds {s : Set X} {t : Set Y} {x : X} {y : Y} (hx
 : s in 𝓝 x) (hy : t in 𝓝 y) : s ×ˢ t in 𝓝 (x, y)
· 使用定理 `connectedComponentIn_mem_nhds`：connectedComponentIn_mem_nhds [LocallyCon
nectedSpace α] {F : Set α} {x : α} (h : F in 𝓝 x) : connectedComponentIn F x in 
𝓝 x
· 使用定理 `isPreconnected_connectedComponentIn`：isPreconnected_connectedComponentIn
 {x : α} {F : Set α} : IsPreconnected (connectedComponentIn F x)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `connectedComponentIn_subset`：connectedComponentIn_subset (F : Set α) (x 
: α) : connectedComponentIn F x subseteq F

--- 原说明 ---
The product of two locally connected spaces is locally connected.
-/
instance Prod.locallyConnectedSpace [TopologicalSpace β] [LocallyConnectedSpace α]
    [LocallyConnectedSpace β] : LocallyConnectedSpace (α × β) := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  rintro ⟨x, y⟩ U hU
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hU
  exact ⟨connectedComponentIn u x ×ˢ connectedComponentIn v y,
    prod_mem_nhds (connectedComponentIn_mem_nhds hu) (connectedComponentIn_mem_nhds hv),
    isPreconnected_connectedComponentIn.prod isPreconnected_connectedComponentIn,
    (prod_mono (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)).trans huv⟩

/-- If each `X i` is locally connected and all but finitely many are preconnected, then
`∀ i, X i` is locally connected. -/
/-
**Pi.locallyConnectedSpace_of_finite_not_preconnectedSpace** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：Pi.locallyConnectedSpace_of_finite_not_preconnectedSpace [forall i, Topolo
gicalSpace (X i)] [forall i, LocallyConnectedSpace (X i)] (hfinite : {i | ¬Preco
nnectedSpace (X i)}.Finite) : LocallyConnectedSpace (forall i, X i)
参数：X i；X i；hfinite : {i | ¬PreconnectedSpace (X i)}.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `locallyConnectedSpace_iff_connected_subsets`：locallyConnectedSpace_iff_c
onnected_subsets : LocallyConnectedSpace α ↔ forall (x : α), forall U in 𝓝 x, ex
ists V in 𝓝 x, IsPreconnected V ∧…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_pi`：mem_pi {s : Set (forall i, α i)} : s in pi f ↔ exists I :
 Set ι, I.Finite ∧ exists t : forall i, Set (α i), (forall i, t i in f i) ∧ I.pi
 t …
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `set_pi_mem_nhds`：set_pi_mem_nhds {i : Set ι} {s : forall a, Set (A a)} {
x : forall a, A a} (hi : i.Finite) (hs : forall a in i, s a in 𝓝 (x a)) : pi i s
 in 𝓝…
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `connectedComponentIn_mem_nhds`：connectedComponentIn_mem_nhds [LocallyCon
nectedSpace α] {F : Set α} {x : α} (h : F in 𝓝 x) : connectedComponentIn F x in 
𝓝 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_pi_piecewise_univ`：univ_pi_piecewise_univ {ι : Type*} {α : ι ->
 Type*} (s : Set ι) (t : forall i, Set (α i)) [forall x, Decidable (x in s)] : p
i univ (s.piecew…
· 使用定理 `isPreconnected_univ_pi`：isPreconnected_univ_pi [forall i, TopologicalSpa
ce (X i)] {s : forall i, Set (X i)} (hs : forall i, IsPreconnected (s i)) : IsPr
econnected (…
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `isPreconnected_connectedComponentIn`：isPreconnected_connectedComponentIn
 {x : α} {F : Set α} : IsPreconnected (connectedComponentIn F x)
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `connectedComponentIn_subset`：connectedComponentIn_subset (F : Set α) (x 
: α) : connectedComponentIn F x subseteq F
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b

--- 原说明 ---
If each `X i` is locally connected and all but finitely many are preconnected, t
hen
`∀ i, X i` is locally connected.
-/
theorem Pi.locallyConnectedSpace_of_finite_not_preconnectedSpace [∀ i, TopologicalSpace (X i)]
    [∀ i, LocallyConnectedSpace (X i)] (hfinite : {i | ¬PreconnectedSpace (X i)}.Finite) :
    LocallyConnectedSpace (∀ i, X i) := by
  refine locallyConnectedSpace_iff_connected_subsets.2 fun x U hU ↦ ?_
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨J, hJ, t, ht, htU⟩ := hU
  let K := J ∪ {i | ¬PreconnectedSpace (X i)}
  refine ⟨K.pi fun i ↦ connectedComponentIn (t i) (x i),
    set_pi_mem_nhds (hJ.union hfinite) fun i _ ↦ connectedComponentIn_mem_nhds (ht i), ?_,
    fun f hf ↦ htU fun i hiJ ↦ connectedComponentIn_subset _ _ (hf i (mem_union_left _ hiJ))⟩
  classical
  rw [← univ_pi_piecewise_univ]
  refine isPreconnected_univ_pi fun i ↦ ?_
  by_cases hi : i ∈ K
  · rw [piecewise_eq_of_mem _ _ _ hi]
    exact isPreconnected_connectedComponentIn
  · rw [piecewise_eq_of_notMem _ _ _ hi]
    have : PreconnectedSpace (X i) := not_not.mp (not_or.1 hi).2
    exact isPreconnected_univ

/-- A finite product of locally connected spaces is locally connected. -/
/-
**Pi.locallyConnectedSpace_of_finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.locallyConnectedSpace_of_finite [Finite ι] [forall i, TopologicalSpace 
(X i)] [forall i, LocallyConnectedSpace (X i)] : LocallyConnectedSpace (forall i
, X i)
参数：X i；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.locallyConnectedSpace_of_finite_not_preconnectedSpace`：Pi.locallyConn
ectedSpace_of_finite_not_preconnectedSpace [forall i, TopologicalSpace (X i)] [f
orall i, LocallyConnectedSpace (X i)] (hfinite…
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite

--- 原说明 ---
A finite product of locally connected spaces is locally connected.
-/
instance Pi.locallyConnectedSpace_of_finite [Finite ι] [∀ i, TopologicalSpace (X i)]
    [∀ i, LocallyConnectedSpace (X i)] : LocallyConnectedSpace (∀ i, X i) :=
  locallyConnectedSpace_of_finite_not_preconnectedSpace (toFinite _)

/-- A product of preconnected, locally connected spaces is locally connected. Note that an
arbitrary product of locally connected spaces need not be locally connected, so the
preconnectedness assumption cannot be dropped entirely (though it can be dropped for finitely
many factors, see `Pi.locallyConnectedSpace_of_finite_not_preconnectedSpace`). -/
/-
**Pi.locallyConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.locallyConnectedSpace [forall i, TopologicalSpace (X i)] [forall i, Loc
allyConnectedSpace (X i)] [forall i, PreconnectedSpace (X i)] : LocallyConnected
Space (forall i, X i)
参数：X i；X i；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.locallyConnectedSpace_of_finite_not_preconnectedSpace`：Pi.locallyConn
ectedSpace_of_finite_not_preconnectedSpace [forall i, TopologicalSpace (X i)] [f
orall i, LocallyConnectedSpace (X i)] (hfinite…
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite

--- 原说明 ---
A product of preconnected, locally connected spaces is locally connected. Note t
hat an
arbitrary product of locally connected spaces need not be locally connected, so 
the
preconnectedness assumption cannot be dropped entirely (though it can be dropped
 for finitely
many factors, see `Pi.locallyConnectedSpace_of_finite_not_preconnectedSpace`).
-/
instance Pi.locallyConnectedSpace [∀ i, TopologicalSpace (X i)]
    [∀ i, LocallyConnectedSpace (X i)] [∀ i, PreconnectedSpace (X i)] :
    LocallyConnectedSpace (∀ i, X i) :=
  locallyConnectedSpace_of_finite_not_preconnectedSpace
    (finite_empty.subset fun _ hi ↦ hi inferInstance)

/-- A product of spaces is locally connected iff it is empty, or every factor is locally
connected and all but finitely many factors are preconnected. -/
/-
**Pi.locallyConnectedSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.locallyConnectedSpace_iff [forall i, TopologicalSpace (X i)] : LocallyC
onnectedSpace (forall i, X i) ↔ IsEmpty (forall i, X i) ∨ (forall i, LocallyConn
ectedSpace (X i)) ∧ {i | ¬PreconnectedSpace (X i)}.Finite
参数：X i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.nonempty_pi`：Classical.nonempty_pi {ι} {α : ι -> Sort*} : None
mpty (forall i, α i) ↔ forall i, Nonempty (α i)
· 使用定理 `Topology.IsCoinducing.locallyConnectedSpace`：Topology.IsCoinducing.local
lyConnectedSpace [LocallyConnectedSpace α] [TopologicalSpace β] {f : α -> β} (hf
 : IsCoinducing f) : LocallyConne…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `IsOpenMap.isQuotientMap`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → Continuo
us f → Functi…
· 使用引理 `isOpenMap_eval`：isOpenMap_eval (i : ι) : IsOpenMap (Function.eval i : (f
orall i, X i) -> X i)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Function.surjective_eval`：surjective_eval {α : Sort u} {β : α -> Sort v}
 [h : forall a, Nonempty (β a)] (a : α) : Surjective (eval a : (forall a, β a) -
> β a)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_connectedComponent`：isOpen_connectedComponent [LocallyConnectedSp
ace α] {x : α} : IsOpen (connectedComponent x)
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_pi`：mem_pi {s : Set (forall i, α i)} : s in pi f ↔ exists I :
 Set ι, I.Finite ∧ exists t : forall i, Set (α i), (forall i, t i in f i) ∧ I.pi
 t …
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `isPreconnected_connectedComponent`：isPreconnected_connectedComponent {x 
: α} : IsPreconnected (connectedComponent x)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
A product of spaces is locally connected iff it is empty, or every factor is loc
ally
connected and all but finitely many factors are preconnected.
-/
theorem Pi.locallyConnectedSpace_iff [∀ i, TopologicalSpace (X i)] :
    LocallyConnectedSpace (∀ i, X i) ↔
      IsEmpty (∀ i, X i) ∨
        (∀ i, LocallyConnectedSpace (X i)) ∧ {i | ¬PreconnectedSpace (X i)}.Finite := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases isEmpty_or_nonempty (∀ i, X i) with he | hne
    · exact .inl he
    obtain ⟨x⟩ := hne
    classical
    have : ∀ i, Nonempty (X i) := Classical.nonempty_pi.mp ⟨x⟩
    refine .inr ⟨fun i ↦ ((isOpenMap_eval i).isQuotientMap (continuous_apply i)
      (Function.surjective_eval i)).locallyConnectedSpace, ?_⟩
    have hVn : connectedComponent x ∈ 𝓝 x :=
      isOpen_connectedComponent.mem_nhds mem_connectedComponent
    rw [nhds_pi, Filter.mem_pi] at hVn
    obtain ⟨J, hJ, t, ht, htV⟩ := hVn
    refine hJ.subset fun i hi ↦ by_contra fun hiJ ↦ hi ?_
    suffices himg : Function.eval i '' connectedComponent x = univ from
      ⟨himg ▸ isPreconnected_connectedComponent.image _ (continuous_apply i).continuousOn⟩
    refine (subset_univ _).antisymm fun z _ ↦ ⟨Function.update x i z, htV fun j hj ↦ ?_, by simp⟩
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hiJ)]
    exact mem_of_mem_nhds (ht j)
  · rintro (he | ⟨hloc, hfin⟩)
    · exact ⟨he.elim⟩
    · exact locallyConnectedSpace_of_finite_not_preconnectedSpace hfin

end LocallyConnectedSpace

