/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Ben Eltschig
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.AlexandrovDiscrete

/-!
# Locally path-connected spaces

This file defines `LocallyPathConnectedSpace X`, a predicate class asserting that `X` is locally
path-connected, in that each point has a basis of path-connected neighborhoods.

## Main results

* `IsOpen.pathComponent` / `IsClosed.pathComponent`: in locally path-connected spaces,
  path-components are both open and closed.
* `pathComponent_eq_connectedComponent`: in locally path-connected spaces, path-components and
  connected components agree.
* `pathConnectedSpace_iff_connectedSpace`: locally path-connected spaces are path-connected iff they
  are connected.
* `instLocallyConnectedSpace`: locally path-connected spaces are also locally connected.
* `IsOpen.locallyPathConnectedSpace`: open subsets of locally path-connected spaces are
  locally path-connected.
* `LocallyPathConnectedSpace.coinduced` / `Quotient.locallyPathConnectedSpace`: quotients of locally
  path-connected spaces are locally path-connected.
* `Sum.locallyPathConnectedSpace` / `Sigma.locallyPathConnectedSpace`: disjoint unions of locally
  path-connected spaces are locally path-connected.
* `Prod.locallyPathConnectedSpace` / `Pi.locallyPathConnectedSpace`: binary products of locally
  path-connected spaces are locally path-connected; likewise for pi types when the index type is
  finite or all factors are path-connected.
* `Pi.locallyPathConnectedSpace_iff`: a product of spaces is locally path-connected iff it is
  empty, or every factor is locally path-connected and all but finitely many factors are
  path-connected.

Abstractly, this also shows that locally path-connected spaces form a coreflective subcategory of
the category of topological spaces, although we do not prove that in this form here.

## Implementation notes

In the definition of `LocallyPathConnectedSpace X` we require neighbourhoods in the basis to be
path-connected, but not necessarily open; that they can also be required to be open is shown as
a theorem in `isOpen_isPathConnected_basis`.
-/

@[expose] public section

noncomputable section

open Topology Filter unitInterval Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*} {F : Set X}

section LocallyPathConnectedSpace

/-- A topological space is locally path connected if, at every point, path connected
neighborhoods form a neighborhood basis. -/
/-
**LocallyPathConnectedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_4) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is locally path connected if, at every point, path connected
neighborhoods form a neighborhood basis.
-/
class LocallyPathConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Each neighborhood filter has a basis of path-connected neighborhoods. -/
  path_connected_basis : ∀ x : X, (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s) id

@[deprecated (since := "2026-06-21")] alias LocPathConnectedSpace := LocallyPathConnectedSpace
@[deprecated (since := "2026-06-21")]
alias LocPathConnectedSpace.path_connected_basis :=
  LocallyPathConnectedSpace.path_connected_basis

export LocallyPathConnectedSpace (path_connected_basis)
/-
**LocallyPathConnectedSpace.of_bases** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LocallyPathConnectedSpace.of_bases {p : X -> ι -> Prop} {s : X -> ι -> Set
 X} (h : forall x, (𝓝 x).HasBasis (p x) (s x)) (h' : forall x i, p x i -> IsPath
Connected (s x i)) : LocallyPathConnectedSpace X where path_connected_basis x
参数：h : forall x, (𝓝 x).HasBasis (p x) (s x)；h' : forall x i, p x i -> IsPathConn
ected (s x i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
-/
theorem LocallyPathConnectedSpace.of_bases {p : X → ι → Prop} {s : X → ι → Set X}
    (h : ∀ x, (𝓝 x).HasBasis (p x) (s x)) (h' : ∀ x i, p x i → IsPathConnected (s x i)) :
    LocallyPathConnectedSpace X where
  path_connected_basis x := by
    rw [hasBasis_self]
    intro t ht
    rcases (h x).mem_iff.mp ht with ⟨i, hpi, hi⟩
    exact ⟨s x i, (h x).mem_of_mem hpi, h' x i hpi, hi⟩

@[deprecated (since := "2026-06-21")]
alias LocPathConnectedSpace.of_bases := LocallyPathConnectedSpace.of_bases

variable [LocallyPathConnectedSpace X]
/-
**IsOpen.pathComponentIn** 是 Mathlib 中的一个定理，位于命名空间 `IsOpen`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {F : Set X} [LocallyPathConne
ctedSpace X],   IsOpen F → ∀ (x : X), IsOpen (pathComponentIn F x)
参数：x : X；pathComponentIn F x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `LocallyPathConnectedSpace.path_connected_basis`：∀ {X : Type u_4} {inst :
 TopologicalSpace X} [self : LocallyPathConnectedSpace X] (x : X),   (nhds x).Ha
sBasis (fun s => s ∈ nhds x ∧ IsPath…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `pathComponentIn_subset`：pathComponentIn_subset : pathComponentIn F x sub
seteq F
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsPathConnected.subset_pathComponentIn`：IsPathConnected.subset_pathCompo
nentIn {s : Set X} (hs : IsPathConnected s) (hxs : x in s) (hsF : s subseteq F) 
: s subseteq pathComponentIn…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `pathComponentIn_congr`：pathComponentIn_congr (h : x in pathComponentIn F
 y) : pathComponentIn F x = pathComponentIn F y
-/
protected theorem IsOpen.pathComponentIn (hF : IsOpen F) (x : X) :
    IsOpen (pathComponentIn F x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  let ⟨s, hs⟩ := (path_connected_basis y).mem_iff.mp (hF.mem_nhds (pathComponentIn_subset hy))
  exact mem_of_superset hs.1.1 <| pathComponentIn_congr hy ▸
    hs.1.2.subset_pathComponentIn (mem_of_mem_nhds hs.1.1) hs.2

/-- In a locally path connected space, each path component is an open set. -/
/-
**IsOpen.pathComponent** 是 Mathlib 中的一个定理，位于命名空间 `IsOpen`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [LocallyPathConnectedSpace X]
 (x : X), IsOpen (pathComponent x)
参数：x : X；pathComponent x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pathComponentIn_univ`：pathComponentIn_univ (x : X) : pathComponentIn uni
v x = pathComponent x
· 使用定理 `IsOpen.pathComponentIn`：∀ {X : Type u_1} [inst : TopologicalSpace X] {F 
: Set X} [LocallyPathConnectedSpace X],   IsOpen F → ∀ (x : X), IsOpen (pathComp
onentIn F x)
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ

--- 原说明 ---
In a locally path connected space, each path component is an open set.
-/
protected theorem IsOpen.pathComponent (x : X) : IsOpen (pathComponent x) := by
  rw [← pathComponentIn_univ]
  exact isOpen_univ.pathComponentIn _

/-- In a locally path connected space, each path component is a closed set. -/
/-
**IsClosed.pathComponent** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [LocallyPathConnectedSpace X]
 (x : X), IsClosed (pathComponent x)
参数：x : X；pathComponent x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Filter.HasBasis.ex_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {
p : ι → Prop} {s : ι → Set α}, l.HasBasis p s → ∃ i, p i
· 使用定理 `LocallyPathConnectedSpace.path_connected_basis`：∀ {X : Type u_4} {inst :
 TopologicalSpace X} [self : LocallyPathConnectedSpace X] (x : X),   (nhds x).Ha
sBasis (fun s => s ∈ nhds x ∧ IsPath…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Joined.trans`：Joined.trans {x y z : X} (hxy : Joined x y) (hyz : Joined 
y z) : Joined x z
· 使用定理 `JoinedIn.joined`：JoinedIn.joined (h : JoinedIn F x y) : Joined x y
· 使用定理 `IsPathConnected.joinedIn`：IsPathConnected.joinedIn (h : IsPathConnected 
F) : forallᵉ (x in F) (y in F), JoinedIn F x y
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
In a locally path connected space, each path component is a closed set.
-/
protected theorem IsClosed.pathComponent (x : X) : IsClosed (pathComponent x) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hxy
  rcases (path_connected_basis y).ex_mem with ⟨V, hVy, hVc⟩
  filter_upwards [hVy] with z hz hxz
  exact hxy <| hxz.trans (hVc.joinedIn _ hz _ (mem_of_mem_nhds hVy)).joined

/-- In a locally path connected space, each path component is a clopen set. -/
/-
**IsClopen.pathComponent** 是 Mathlib 中的一个定理，位于命名空间 `IsClopen`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [LocallyPathConnectedSpace X]
 (x : X), IsClopen (pathComponent x)
参数：x : X；pathComponent x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.pathComponent`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Lo
callyPathConnectedSpace X] (x : X), IsClosed (pathComponent x)
· 使用定理 `IsOpen.pathComponent`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Loca
llyPathConnectedSpace X] (x : X), IsOpen (pathComponent x)

--- 原说明 ---
In a locally path connected space, each path component is a clopen set.
-/
protected theorem IsClopen.pathComponent (x : X) : IsClopen (pathComponent x) :=
  ⟨.pathComponent x, .pathComponent x⟩
/-
**pathComponentIn_mem_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pathComponentIn_mem_nhds (hF : F in 𝓝 x) : pathComponentIn F x in 𝓝 x
参数：hF : F in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pathComponentIn_mono`：pathComponentIn_mono {G : Set X} (h : F subseteq G
) : pathComponentIn F x subseteq pathComponentIn G x
· 使用定理 `IsOpen.pathComponentIn`：∀ {X : Type u_1} [inst : TopologicalSpace X] {F 
: Set X} [LocallyPathConnectedSpace X],   IsOpen F → ∀ (x : X), IsOpen (pathComp
onentIn F x)
· 使用定理 `mem_pathComponentIn_self`：mem_pathComponentIn_self (h : x in F) : x in p
athComponentIn F x
-/
lemma pathComponentIn_mem_nhds (hF : F ∈ 𝓝 x) : pathComponentIn F x ∈ 𝓝 x := by
  let ⟨u, huF, hu, hxu⟩ := mem_nhds_iff.mp hF
  exact mem_nhds_iff.mpr ⟨pathComponentIn u x, pathComponentIn_mono huF,
    hu.pathComponentIn x, mem_pathComponentIn_self hxu⟩
/-
**PathConnectedSpace.of_locallyPathConnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PathConnectedSpace.of_locallyPathConnectedSpace [ConnectedSpace X] : PathC
onnectedSpace X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConnectedSpace.toNonempty`：∀ {α : Type u} {inst : TopologicalSpace α} [s
elf : ConnectedSpace α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClopen.eq_univ`：IsClopen.eq_univ [PreconnectedSpace α] {s : Set α} (h'
 : IsClopen s) (h : s.Nonempty) : s = univ
· 使用定理 `IsClopen.pathComponent`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Lo
callyPathConnectedSpace X] (x : X), IsClopen (pathComponent x)
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem PathConnectedSpace.of_locallyPathConnectedSpace [ConnectedSpace X] : PathConnectedSpace X :=
  ⟨inferInstance, by simp [← mem_pathComponent_iff, IsClopen.pathComponent _ |>.eq_univ]⟩

@[deprecated (since := "2026-06-21")]
alias PathConnectedSpace.of_locPathConnectedSpace := PathConnectedSpace.of_locallyPathConnectedSpace
/-
**pathConnectedSpace_iff_connectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathConnectedSpace_iff_connectedSpace : PathConnectedSpace X ↔ ConnectedSp
ace X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `PathConnectedSpace.of_locallyPathConnectedSpace`：PathConnectedSpace.of_l
ocallyPathConnectedSpace [ConnectedSpace X] : PathConnectedSpace X
-/
theorem pathConnectedSpace_iff_connectedSpace : PathConnectedSpace X ↔ ConnectedSpace X :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ .of_locallyPathConnectedSpace⟩
/-
**pathComponent_eq_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathComponent_eq_connectedComponent (x : X) : pathComponent x = connectedC
omponent x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `pathComponent_subset_component`：pathComponent_subset_component (x : X) :
 pathComponent x subseteq connectedComponent x
· 使用定理 `IsClopen.connectedComponent_subset`：IsClopen.connectedComponent_subset {
x} (hs : IsClopen s) (hx : x in s) : connectedComponent x subseteq s
· 使用定理 `IsClopen.pathComponent`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Lo
callyPathConnectedSpace X] (x : X), IsClopen (pathComponent x)
· 使用定理 `mem_pathComponent_self`：mem_pathComponent_self (x : X) : x in pathCompon
ent x
-/
theorem pathComponent_eq_connectedComponent (x : X) : pathComponent x = connectedComponent x :=
  (pathComponent_subset_component x).antisymm <|
    (IsClopen.pathComponent x).connectedComponent_subset (mem_pathComponent_self _)
/-
**connectedComponent_eq_iff_joined** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponent_eq_iff_joined (x y : X) : connectedComponent x = connec
tedComponent y ↔ Joined x y
参数：x y : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_pathComponent_iff`：mem_pathComponent_iff : x in pathComponent y ↔ Jo
ined y x
· 使用定理 `pathComponent_eq_connectedComponent`：pathComponent_eq_connectedComponent
 (x : X) : pathComponent x = connectedComponent x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `connectedComponent_eq_iff_mem`：connectedComponent_eq_iff_mem {x y : α} :
 connectedComponent x = connectedComponent y ↔ x in connectedComponent y
-/
theorem connectedComponent_eq_iff_joined (x y : X) :
    connectedComponent x = connectedComponent y ↔ Joined x y := by
  rw [← mem_pathComponent_iff, pathComponent_eq_connectedComponent, eq_comm]
  exact connectedComponent_eq_iff_mem
/-
**connectedComponentSetoid_eq_pathSetoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponentSetoid_eq_pathSetoid : connectedComponentSetoid X = path
Setoid X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `connectedComponent_eq_iff_joined`：connectedComponent_eq_iff_joined (x y 
: X) : connectedComponent x = connectedComponent y ↔ Joined x y
-/
theorem connectedComponentSetoid_eq_pathSetoid : connectedComponentSetoid X = pathSetoid X :=
  Setoid.ext connectedComponent_eq_iff_joined

/-- In a locally path-connected space, connected components and path-connected components align -/
/-
**connectedComponentsEquivZerothHomotopy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：connectedComponentsEquivZerothHomotopy : ConnectedComponents X ≃ ZerothHom
otopy X where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a locally path-connected space, connected components and path-connected compo
nents align
-/
def connectedComponentsEquivZerothHomotopy : ConnectedComponents X ≃ ZerothHomotopy X where
  toFun := Quotient.map id (connectedComponent_eq_iff_joined · · |>.mp ·)
  invFun := ZerothHomotopy.toConnectedComponents
  left_inv := Quot.ind <| congrFun rfl
  right_inv := Quot.ind <| congrFun rfl

@[simp]
/-
**connectedComponentsEquivZerothHomotopy_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：connectedComponentsEquivZerothHomotopy_apply (x : X) : connectedComponents
EquivZerothHomotopy ⟦x⟧ = (.mk x)
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma connectedComponentsEquivZerothHomotopy_apply (x : X) :
    connectedComponentsEquivZerothHomotopy ⟦x⟧ = (.mk x) :=
  rfl

@[simp]
/-
**coe_connectedComponentsEquivZerothHomotopy_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_connectedComponentsEquivZerothHomotopy_symm : ⇑connectedComponentsEqui
vZerothHomotopy.symm = ZerothHomotopy.toConnectedComponents (X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma coe_connectedComponentsEquivZerothHomotopy_symm :
    ⇑connectedComponentsEquivZerothHomotopy.symm = ZerothHomotopy.toConnectedComponents (X := X) :=
  rfl
/-
**connectedComponentsEquivZerothHomotopy_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：connectedComponentsEquivZerothHomotopy_symm_apply (x : X) : connectedCompo
nentsEquivZerothHomotopy.symm (.mk x) = ⟦x⟧
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma connectedComponentsEquivZerothHomotopy_symm_apply (x : X) :
    connectedComponentsEquivZerothHomotopy.symm (.mk x) = ⟦x⟧ :=
  rfl
/-
**pathConnected_subset_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathConnected_subset_basis {U : Set X} (h : IsOpen U) (hx : x in U) : (𝓝 x
).HasBasis (fun s : Set X => s in 𝓝 x ∧ IsPathConnected s ∧ s subseteq U) id
参数：h : IsOpen U；hx : x in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.hasBasis_self_subset`：∀ {α : Type u_1} {l : Filter α} {p
 : Set α → Prop},   l.HasBasis (fun s => s ∈ l ∧ p s) id → ∀ {V : Set α}, V ∈ l 
→ l.HasBasis (fun s => s ∈…
· 使用定理 `LocallyPathConnectedSpace.path_connected_basis`：∀ {X : Type u_4} {inst :
 TopologicalSpace X} [self : LocallyPathConnectedSpace X] (x : X),   (nhds x).Ha
sBasis (fun s => s ∈ nhds x ∧ IsPath…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem pathConnected_subset_basis {U : Set X} (h : IsOpen U) (hx : x ∈ U) :
    (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s ∧ s ⊆ U) id :=
  (path_connected_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)
/-
**isOpen_isPathConnected_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_isPathConnected_basis (x : X) : (𝓝 x).HasBasis (fun s : Set X => Is
Open s ∧ x in s ∧ IsPathConnected s) id
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `IsOpen.pathComponentIn`：∀ {X : Type u_1} [inst : TopologicalSpace X] {F 
: Set X} [LocallyPathConnectedSpace X],   IsOpen F → ∀ (x : X), IsOpen (pathComp
onentIn F x)
· 使用定理 `mem_pathComponentIn_self`：mem_pathComponentIn_self (h : x in F) : x in p
athComponentIn F x
· 使用定理 `isPathConnected_pathComponentIn`：isPathConnected_pathComponentIn (h : x 
in F) : IsPathConnected (pathComponentIn F x)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `pathComponentIn_subset`：pathComponentIn_subset : pathComponentIn F x sub
seteq F
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isOpen_isPathConnected_basis (x : X) :
    (𝓝 x).HasBasis (fun s : Set X ↦ IsOpen s ∧ x ∈ s ∧ IsPathConnected s) id := by
  refine ⟨fun s ↦ ⟨fun hs ↦ ?_, fun ⟨u, hu⟩ ↦ mem_nhds_iff.mpr ⟨u, hu.2, hu.1.1, hu.1.2.1⟩⟩⟩
  have ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp hs
  exact ⟨pathComponentIn u x, ⟨hu.pathComponentIn _, ⟨mem_pathComponentIn_self hxu,
    isPathConnected_pathComponentIn hxu⟩⟩, pathComponentIn_subset.trans hus⟩
/-
**Topology.IsOpenEmbedding.locallyPathConnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：Topology.IsOpenEmbedding.locallyPathConnectedSpace {e : Y -> X} (he : IsOp
enEmbedding e) : LocallyPathConnectedSpace Y
参数：he : IsOpenEmbedding e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.basis_nhds`：basis_nhds {p : ι -> Prop} {s : ι -> Set
 Y} (hf : IsInducing f) {x : X} (h_basis : (𝓝 (f x)).HasBasis p s) : (𝓝 x).HasBa
sis p (preimage f ∘ …
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `pathConnected_subset_basis`：pathConnected_subset_basis {U : Set X} (h : 
IsOpen U) (hx : x in U) : (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ IsPathConn
ected s ∧ s subs…
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `LocallyPathConnectedSpace.of_bases`：LocallyPathConnectedSpace.of_bases {
p : X -> ι -> Prop} {s : X -> ι -> Set X} (h : forall x, (𝓝 x).HasBasis (p x) (s
 x)) (h' : forall x i, p…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.isPathConnected_iff`：∀ {X : Type u_1} {Y : Type u_2}
 [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {F : Set X} {f : X → 
Y},   Topology.IsInducing f →…
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
-/
theorem Topology.IsOpenEmbedding.locallyPathConnectedSpace {e : Y → X} (he : IsOpenEmbedding e) :
    LocallyPathConnectedSpace Y :=
  have (y : Y) :
      (𝓝 y).HasBasis (fun s ↦ s ∈ 𝓝 (e y) ∧ IsPathConnected s ∧ s ⊆ range e) (e ⁻¹' ·) :=
    he.basis_nhds <| pathConnected_subset_basis he.isOpen_range (mem_range_self _)
  .of_bases this fun x s ⟨_, hs, hse⟩ ↦ by
    rwa [he.isPathConnected_iff, image_preimage_eq_of_subset hse]

@[deprecated (since := "2026-06-21")]
alias Topology.IsOpenEmbedding.locPathConnectedSpace :=
  Topology.IsOpenEmbedding.locallyPathConnectedSpace
/-
**IsOpen.locallyPathConnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.locallyPathConnectedSpace {U : Set X} (h : IsOpen U) : LocallyPathC
onnectedSpace U
参数：h : IsOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.locallyPathConnectedSpace`：Topology.IsOpenEmbed
ding.locallyPathConnectedSpace {e : Y -> X} (he : IsOpenEmbedding e) : LocallyPa
thConnectedSpace Y
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
-/
theorem IsOpen.locallyPathConnectedSpace {U : Set X} (h : IsOpen U) : LocallyPathConnectedSpace U :=
  h.isOpenEmbedding_subtypeVal.locallyPathConnectedSpace

@[deprecated (since := "2026-06-21")]
alias IsOpen.locPathConnectedSpace := IsOpen.locallyPathConnectedSpace
/-
**IsOpen.isConnected_iff_isPathConnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.isConnected_iff_isPathConnected {U : Set X} (U_op : IsOpen U) : IsC
onnected U ↔ IsPathConnected U
参数：U_op : IsOpen U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isConnected_iff_connectedSpace`：isConnected_iff_connectedSpace {s : Set 
α} : IsConnected s ↔ ConnectedSpace s
· 使用定理 `isPathConnected_iff_pathConnectedSpace`：isPathConnected_iff_pathConnecte
dSpace : IsPathConnected F ↔ PathConnectedSpace F
· 使用定理 `IsOpen.locallyPathConnectedSpace`：IsOpen.locallyPathConnectedSpace {U : 
Set X} (h : IsOpen U) : LocallyPathConnectedSpace U
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `pathConnectedSpace_iff_connectedSpace`：pathConnectedSpace_iff_connectedS
pace : PathConnectedSpace X ↔ ConnectedSpace X
-/
theorem IsOpen.isConnected_iff_isPathConnected {U : Set X} (U_op : IsOpen U) :
    IsConnected U ↔ IsPathConnected U := by
  rw [isConnected_iff_connectedSpace, isPathConnected_iff_pathConnectedSpace]
  have := U_op.locallyPathConnectedSpace
  exact pathConnectedSpace_iff_connectedSpace.symm

/-- Locally path-connected spaces are locally connected. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Locally path-connected spaces are locally connected.
-/
instance : LocallyConnectedSpace X := by
  refine ⟨forall_imp (fun x h ↦ ⟨fun s ↦ ?_⟩) isOpen_isPathConnected_basis⟩
  refine ⟨fun hs ↦ ?_, fun ⟨u, ⟨hu, hxu, _⟩, hus⟩ ↦ mem_nhds_iff.mpr ⟨u, hus, hu, hxu⟩⟩
  let ⟨u, ⟨hu, hxu, hu'⟩, hus⟩ := (h.mem_iff' s).mp hs
  exact ⟨u, ⟨hu, hxu, hu'.isConnected⟩, hus⟩

/-- A space is locally path-connected iff all path components of open subsets are open. -/
/-
**locallyPathConnectedSpace_iff_isOpen_pathComponentIn** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：locallyPathConnectedSpace_iff_isOpen_pathComponentIn {X : Type*} [Topologi
calSpace X] : LocallyPathConnectedSpace X ↔ forall (x : X) (u : Set X), IsOpen u
 -> IsOpen (pathComponentIn u x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.pathComponentIn`：∀ {X : Type u_1} [inst : TopologicalSpace X] {F 
: Set X} [LocallyPathConnectedSpace X],   IsOpen F → ∀ (x : X), IsOpen (pathComp
onentIn F x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mem_pathComponentIn_self`：mem_pathComponentIn_self (h : x in F) : x in p
athComponentIn F x
· 使用定理 `isPathConnected_pathComponentIn`：isPathConnected_pathComponentIn (h : x 
in F) : IsPathConnected (pathComponentIn F x)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `pathComponentIn_subset`：pathComponentIn_subset : pathComponentIn F x sub
seteq F
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f

--- 原说明 ---
A space is locally path-connected iff all path components of open subsets are op
en.
-/
lemma locallyPathConnectedSpace_iff_isOpen_pathComponentIn {X : Type*} [TopologicalSpace X] :
    LocallyPathConnectedSpace X ↔ ∀ (x : X) (u : Set X), IsOpen u → IsOpen (pathComponentIn u x) :=
  ⟨fun _ _ _ hu ↦ hu.pathComponentIn _, fun h ↦ ⟨fun x ↦ ⟨fun s ↦ by
    refine ⟨fun hs ↦ ?_, fun ⟨_, ht⟩ ↦ Filter.mem_of_superset ht.1.1 ht.2⟩
    let ⟨u, hu⟩ := mem_nhds_iff.mp hs
    exact ⟨pathComponentIn u x, ⟨(h x u hu.2.1).mem_nhds (mem_pathComponentIn_self hu.2.2),
      isPathConnected_pathComponentIn hu.2.2⟩, pathComponentIn_subset.trans hu.1⟩⟩⟩⟩

@[deprecated (since := "2026-06-21")]
alias locPathConnectedSpace_iff_isOpen_pathComponentIn :=
  locallyPathConnectedSpace_iff_isOpen_pathComponentIn

/-- A space is locally path-connected iff all path components of open subsets are neighbourhoods. -/
/-
**locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds {X : Type*} [Topolo
gicalSpace X] : LocallyPathConnectedSpace X ↔ forall x : X, forall u : Set X, Is
Open u -> x in u -> pathComponentIn u x in nhds x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `locallyPathConnectedSpace_iff_isOpen_pathComponentIn`：locallyPathConnect
edSpace_iff_isOpen_pathComponentIn {X : Type*} [TopologicalSpace X] : LocallyPat
hConnectedSpace X ↔ forall (x : X) (u : Se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a → b ↔ a → c)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `mem_pathComponentIn_self`：mem_pathComponentIn_self (h : x in F) : x in p
athComponentIn F x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `pathComponentIn_congr`：pathComponentIn_congr (h : x in pathComponentIn F
 y) : pathComponentIn F x = pathComponentIn F y
· 使用定理 `pathComponentIn_subset`：pathComponentIn_subset : pathComponentIn F x sub
seteq F

--- 原说明 ---
A space is locally path-connected iff all path components of open subsets are ne
ighbourhoods.
-/
lemma locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds {X : Type*} [TopologicalSpace X] :
    LocallyPathConnectedSpace X ↔
    ∀ x : X, ∀ u : Set X, IsOpen u → x ∈ u → pathComponentIn u x ∈ nhds x := by
  rw [locallyPathConnectedSpace_iff_isOpen_pathComponentIn]
  simp_rw [forall_comm (β := Set X), ← imp_forall_iff]
  refine forall_congr' fun u ↦ imp_congr_right fun _ ↦ ?_
  exact ⟨fun h x hxu ↦ (h x).mem_nhds (mem_pathComponentIn_self hxu),
    fun h x ↦ isOpen_iff_mem_nhds.mpr fun y hy ↦
      pathComponentIn_congr hy ▸ h y <| pathComponentIn_subset hy⟩

@[deprecated (since := "2026-06-21")]
alias locPathConnectedSpace_iff_pathComponentIn_mem_nhds :=
  locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds

/-- Any topology coinduced by a locally path-connected topology is locally path-connected. -/
/-
**LocallyPathConnectedSpace.coinduced** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyPathConnectedSpace.coinduced {Y : Type*} (f : X -> Y) : @LocallyPat
hConnectedSpace Y (.coinduced f ‹_›)
参数：f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `locallyPathConnectedSpace_iff_isOpen_pathComponentIn`：locallyPathConnect
edSpace_iff_isOpen_pathComponentIn {X : Type*} [TopologicalSpace X] : LocallyPat
hConnectedSpace X ↔ forall (x : X) (u : Se…
· 使用定理 `isOpen_coinduced`：isOpen_coinduced {t : TopologicalSpace α} {s : Set β} 
{f : α -> β} : IsOpen[t.coinduced f] s ↔ IsOpen (f ⁻¹' s)
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `pathComponentIn_subset`：pathComponentIn_subset : pathComponentIn F x sub
seteq F
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `pathComponentIn_congr`：pathComponentIn_congr (h : x in pathComponentIn F
 y) : pathComponentIn F x = pathComponentIn F y
· 使用定理 `IsPathConnected.subset_pathComponentIn`：IsPathConnected.subset_pathCompo
nentIn {s : Set X} (hs : IsPathConnected s) (hxs : x in s) (hsF : s subseteq F) 
: s subseteq pathComponentIn…
· 使用定理 `IsPathConnected.image`：IsPathConnected.image (hF : IsPathConnected F) {f
 : X -> Y} (hf : Continuous f) : IsPathConnected (f '' F)
· 使用定理 `isPathConnected_pathComponentIn`：isPathConnected_pathComponentIn (h : x 
in F) : IsPathConnected (pathComponentIn F x)
· 使用定理 `mem_pathComponentIn_self`：mem_pathComponentIn_self (h : x in F) : x in p
athComponentIn F x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `IsOpen.pathComponentIn`：∀ {X : Type u_1} [inst : TopologicalSpace X] {F 
: Set X} [LocallyPathConnectedSpace X],   IsOpen F → ∀ (x : X), IsOpen (pathComp
onentIn F x)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)

--- 原说明 ---
Any topology coinduced by a locally path-connected topology is locally path-conn
ected.
-/
lemma LocallyPathConnectedSpace.coinduced {Y : Type*} (f : X → Y) :
    @LocallyPathConnectedSpace Y (.coinduced f ‹_›) := by
  let _ := TopologicalSpace.coinduced f ‹_›; have hf : Continuous f := continuous_coinduced_rng
  refine locallyPathConnectedSpace_iff_isOpen_pathComponentIn.mpr fun y u hu ↦
    isOpen_coinduced.mpr <| isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
  have hx' := preimage_mono pathComponentIn_subset hx
  refine mem_nhds_iff.mpr ⟨pathComponentIn (f ⁻¹' u) x, ?_,
    (hu.preimage hf).pathComponentIn _, mem_pathComponentIn_self hx'⟩
  rw [← image_subset_iff, ← pathComponentIn_congr hx]
  exact ((isPathConnected_pathComponentIn hx').image hf).subset_pathComponentIn
    ⟨x, mem_pathComponentIn_self hx', rfl⟩ <|
    (image_mono pathComponentIn_subset).trans <| u.image_preimage_subset f

@[deprecated (since := "2026-06-21")]
alias LocPathConnectedSpace.coinduced := LocallyPathConnectedSpace.coinduced

/-- Quotients of locally path-connected spaces are locally path-connected. -/
/-
**Topology.IsQuotientMap.locallyPathConnectedSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsQuotientMap.locallyPathConnectedSpace {f : X -> Y} (h : IsQuoti
entMap f) : LocallyPathConnectedSpace Y
参数：h : IsQuotientMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LocallyPathConnectedSpace.coinduced`：LocallyPathConnectedSpace.coinduced
 {Y : Type*} (f : X -> Y) : @LocallyPathConnectedSpace Y (.coinduced f ‹_›)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.eq_coinduced`：∀ {X : Type u_1} {Y : Type u_2} [tX 
: TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsCoindu
cing f → tY = Topologica…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…

--- 原说明 ---
Quotients of locally path-connected spaces are locally path-connected.
-/
lemma Topology.IsQuotientMap.locallyPathConnectedSpace {f : X → Y} (h : IsQuotientMap f) :
    LocallyPathConnectedSpace Y :=
  h.isCoinducing.eq_coinduced ▸ LocallyPathConnectedSpace.coinduced f

@[deprecated (since := "2026-06-21")]
alias Topology.IsQuotientMap.locPathConnectedSpace :=
  Topology.IsQuotientMap.locallyPathConnectedSpace

/-- Quotients of locally path-connected spaces are locally path-connected. -/
/-
**Quot.locallyPathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quot.locallyPathConnectedSpace {r : X -> X -> Prop} : LocallyPathConnected
Space (Quot r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsQuotientMap.locallyPathConnectedSpace`：Topology.IsQuotientMap
.locallyPathConnectedSpace {f : X -> Y} (h : IsQuotientMap f) : LocallyPathConne
ctedSpace Y
· 使用定理 `isQuotientMap_quot_mk`：isQuotientMap_quot_mk : IsQuotientMap (@Quot.mk X
 r)

--- 原说明 ---
Quotients of locally path-connected spaces are locally path-connected.
-/
instance Quot.locallyPathConnectedSpace {r : X → X → Prop} : LocallyPathConnectedSpace (Quot r) :=
  isQuotientMap_quot_mk.locallyPathConnectedSpace

@[deprecated (since := "2026-06-21")]
alias Quot.locPathConnectedSpace := Quot.locallyPathConnectedSpace

/-- Quotients of locally path-connected spaces are locally path-connected. -/
/-
**Quotient.locallyPathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quotient.locallyPathConnectedSpace {s : Setoid X} : LocallyPathConnectedSp
ace (Quotient s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsQuotientMap.locallyPathConnectedSpace`：Topology.IsQuotientMap
.locallyPathConnectedSpace {f : X -> Y} (h : IsQuotientMap f) : LocallyPathConne
ctedSpace Y
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `isQuotientMap_quotient_mk'`：isQuotientMap_quotient_mk' : IsQuotientMap (
@Quotient.mk' X s)

--- 原说明 ---
Quotients of locally path-connected spaces are locally path-connected.
-/
instance Quotient.locallyPathConnectedSpace {s : Setoid X} :
    LocallyPathConnectedSpace (Quotient s) :=
  isQuotientMap_quotient_mk'.locallyPathConnectedSpace

@[deprecated (since := "2026-06-21")]
alias Quotient.locPathConnectedSpace := Quotient.locallyPathConnectedSpace

/-- Disjoint unions of locally path-connected spaces are locally path-connected. -/
/-
**Sum.locallyPathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sum.locallyPathConnectedSpace [LocallyPathConnectedSpace Y] : LocallyPathC
onnectedSpace (X oplus Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds`：locallyPathConne
ctedSpace_iff_pathComponentIn_mem_nhds {X : Type*} [TopologicalSpace X] : Locall
yPathConnectedSpace X ↔ forall x : X, forall…
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `IsPathConnected.subset_pathComponentIn`：IsPathConnected.subset_pathCompo
nentIn {s : Set X} (hs : IsPathConnected s) (hxs : x in s) (hsF : s subseteq F) 
: s subseteq pathComponentIn…
· 使用定理 `IsPathConnected.image`：IsPathConnected.image (hF : IsPathConnected F) {f
 : X -> Y} (hf : Continuous f) : IsPathConnected (f '' F)
· 使用定理 `isPathConnected_pathComponentIn`：isPathConnected_pathComponentIn (h : x 
in F) : IsPathConnected (pathComponentIn F x)
· 使用定理 `continuous_inl`：continuous_inl : Continuous (@inl X Y)
· 使用定理 `mem_pathComponentIn_self`：mem_pathComponentIn_self (h : x in F) : x in p
athComponentIn F x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `pathComponentIn_subset`：pathComponentIn_subset : pathComponentIn F x sub
seteq F
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `isOpenMap_inl`：isOpenMap_inl : IsOpenMap (@inl X Y)
· 使用定理 `IsOpen.pathComponentIn`：∀ {X : Type u_1} [inst : TopologicalSpace X] {F 
: Set X} [LocallyPathConnectedSpace X],   IsOpen F → ∀ (x : X), IsOpen (pathComp
onentIn F x)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_inr`：continuous_inr : Continuous (@inr X Y)
· 使用定理 `isOpenMap_inr`：isOpenMap_inr : IsOpenMap (@inr X Y)

--- 原说明 ---
Disjoint unions of locally path-connected spaces are locally path-connected.
-/
instance Sum.locallyPathConnectedSpace [LocallyPathConnectedSpace Y] :
    LocallyPathConnectedSpace (X ⊕ Y) := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]; intro x u hu hxu; rw [mem_nhds_iff]
  obtain x | y := x
  · refine ⟨Sum.inl '' pathComponentIn (Sum.inl ⁻¹' u) x, ?_, ?_, ?_⟩
    · apply IsPathConnected.subset_pathComponentIn
      · exact (isPathConnected_pathComponentIn (by exact hxu)).image continuous_inl
      · exact ⟨x, mem_pathComponentIn_self hxu, rfl⟩
      · exact (image_mono pathComponentIn_subset).trans (u.image_preimage_subset _)
    · exact isOpenMap_inl _ <| (hu.preimage continuous_inl).pathComponentIn _
    · exact ⟨x, mem_pathComponentIn_self hxu, rfl⟩
  · refine ⟨Sum.inr '' pathComponentIn (Sum.inr ⁻¹' u) y, ?_, ?_, ?_⟩
    · apply IsPathConnected.subset_pathComponentIn
      · exact (isPathConnected_pathComponentIn (by exact hxu)).image continuous_inr
      · exact ⟨y, mem_pathComponentIn_self hxu, rfl⟩
      · exact (image_mono pathComponentIn_subset).trans (u.image_preimage_subset _)
    · exact isOpenMap_inr _ <| (hu.preimage continuous_inr).pathComponentIn _
    · exact ⟨y, mem_pathComponentIn_self hxu, rfl⟩

@[deprecated (since := "2026-06-21")]
alias Sum.locPathConnectedSpace := Sum.locallyPathConnectedSpace

/-- Disjoint unions of locally path-connected spaces are locally path-connected. -/
/-
**Sigma.locallyPathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sigma.locallyPathConnectedSpace {X : ι -> Type*} [(i : ι) -> TopologicalSp
ace (X i)] [(i : ι) -> LocallyPathConnectedSpace (X i)] : LocallyPathConnectedSp
ace ((i : ι) × X i)
参数：i : ι；X i；i : ι；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds`：locallyPathConne
ctedSpace_iff_pathComponentIn_mem_nhds {X : Type*} [TopologicalSpace X] : Locall
yPathConnectedSpace X ↔ forall x : X, forall…
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `IsPathConnected.subset_pathComponentIn`：IsPathConnected.subset_pathCompo
nentIn {s : Set X} (hs : IsPathConnected s) (hxs : x in s) (hsF : s subseteq F) 
: s subseteq pathComponentIn…
· 使用定理 `IsPathConnected.image`：IsPathConnected.image (hF : IsPathConnected F) {f
 : X -> Y} (hf : Continuous f) : IsPathConnected (f '' F)
· 使用定理 `isPathConnected_pathComponentIn`：isPathConnected_pathComponentIn (h : x 
in F) : IsPathConnected (pathComponentIn F x)
· 使用定理 `continuous_sigmaMk`：continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι
 σ i)
· 使用定理 `mem_pathComponentIn_self`：mem_pathComponentIn_self (h : x in F) : x in p
athComponentIn F x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `pathComponentIn_subset`：pathComponentIn_subset : pathComponentIn F x sub
seteq F
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `isOpenMap_sigmaMk`：isOpenMap_sigmaMk {i : ι} : IsOpenMap (@Sigma.mk ι σ 
i)
· 使用定理 `IsOpen.pathComponentIn`：∀ {X : Type u_1} [inst : TopologicalSpace X] {F 
: Set X} [LocallyPathConnectedSpace X],   IsOpen F → ∀ (x : X), IsOpen (pathComp
onentIn F x)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)

--- 原说明 ---
Disjoint unions of locally path-connected spaces are locally path-connected.
-/
instance Sigma.locallyPathConnectedSpace {X : ι → Type*}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι) → LocallyPathConnectedSpace (X i)] :
    LocallyPathConnectedSpace ((i : ι) × X i) := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]; intro x u hu hxu; rw [mem_nhds_iff]
  refine ⟨(Sigma.mk x.1) '' pathComponentIn ((Sigma.mk x.1) ⁻¹' u) x.2, ?_, ?_, ?_⟩
  · apply IsPathConnected.subset_pathComponentIn
    · exact (isPathConnected_pathComponentIn (by exact hxu)).image continuous_sigmaMk
    · exact ⟨x.2, mem_pathComponentIn_self hxu, rfl⟩
    · exact (image_mono pathComponentIn_subset).trans (u.image_preimage_subset _)
  · exact isOpenMap_sigmaMk _ <| (hu.preimage continuous_sigmaMk).pathComponentIn _
  · exact ⟨x.2, mem_pathComponentIn_self hxu, rfl⟩

@[deprecated (since := "2026-06-21")]
alias Sigma.locPathConnectedSpace := Sigma.locallyPathConnectedSpace

/-- The product of two locally path-connected spaces is locally path-connected. -/
/-
**Prod.locallyPathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.locallyPathConnectedSpace [LocallyPathConnectedSpace Y] : LocallyPath
ConnectedSpace (X × Y) where path_connected_basis
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_prod_iff`：mem_nhds_prod_iff {x : X} {y : Y} {s : Set (X × Y)} :
 s in 𝓝 (x, y) ↔ exists u in 𝓝 x, exists v in 𝓝 y, u ×ˢ v subseteq s
· 使用定理 `prod_mem_nhds`：prod_mem_nhds {s : Set X} {t : Set Y} {x : X} {y : Y} (hx
 : s in 𝓝 x) (hy : t in 𝓝 y) : s ×ˢ t in 𝓝 (x, y)
· 使用引理 `pathComponentIn_mem_nhds`：pathComponentIn_mem_nhds (hF : F in 𝓝 x) : pat
hComponentIn F x in 𝓝 x
· 使用定理 `IsPathConnected.prod`：IsPathConnected.prod (hs : IsPathConnected s) (ht 
: IsPathConnected t) : IsPathConnected (s ×ˢ t)
· 使用定理 `isPathConnected_pathComponentIn`：isPathConnected_pathComponentIn (h : x 
in F) : IsPathConnected (pathComponentIn F x)
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `pathComponentIn_subset`：pathComponentIn_subset : pathComponentIn F x sub
seteq F

--- 原说明 ---
The product of two locally path-connected spaces is locally path-connected.
-/
instance Prod.locallyPathConnectedSpace [LocallyPathConnectedSpace Y] :
    LocallyPathConnectedSpace (X × Y) where
  path_connected_basis := fun (x, y) ↦ hasBasis_self.mpr fun U hU ↦ by
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hU
    exact ⟨pathComponentIn u x ×ˢ pathComponentIn v y,
      prod_mem_nhds (pathComponentIn_mem_nhds hu) (pathComponentIn_mem_nhds hv),
      (isPathConnected_pathComponentIn (mem_of_mem_nhds hu)).prod
        (isPathConnected_pathComponentIn (mem_of_mem_nhds hv)),
      (Set.prod_mono pathComponentIn_subset pathComponentIn_subset).trans huv⟩

/-- If each `Z i` is locally path-connected and all but finitely many are path-connected, then
`∀ i, Z i` is locally path-connected. -/
/-
**Pi.locallyPathConnectedSpace_of_finite_not_pathConnectedSpace** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：Pi.locallyPathConnectedSpace_of_finite_not_pathConnectedSpace {Z : ι -> Ty
pe*} [forall i, TopologicalSpace (Z i)] [forall i, LocallyPathConnectedSpace (Z 
i)] (hfinite : {i | ¬PathConnectedSpace (Z i)}.Finite) : LocallyPathConnectedSpa
ce (forall i, Z i) where path_connected_basis x
参数：Z i；Z i；hfinite : {i | ¬PathConnectedSpace (Z i)}.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
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
· 使用引理 `pathComponentIn_mem_nhds`：pathComponentIn_mem_nhds (hF : F in 𝓝 x) : pat
hComponentIn F x in 𝓝 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_pi_piecewise_univ`：univ_pi_piecewise_univ {ι : Type*} {α : ι ->
 Type*} (s : Set ι) (t : forall i, Set (α i)) [forall x, Decidable (x in s)] : p
i univ (s.piecew…
· 使用定理 `IsPathConnected.pi`：IsPathConnected.pi {s : forall i, Set (Z i)} (h : fo
rall i, IsPathConnected (s i)) : IsPathConnected (Set.univ.pi s)
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `isPathConnected_pathComponentIn`：isPathConnected_pathComponentIn (h : x 
in F) : IsPathConnected (pathComponentIn F x)
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `isPathConnected_univ`：isPathConnected_univ [PathConnectedSpace X] : IsPa
thConnected (univ : Set X)
· 使用定理 `pathComponentIn_subset`：pathComponentIn_subset : pathComponentIn F x sub
seteq F
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b

--- 原说明 ---
If each `Z i` is locally path-connected and all but finitely many are path-conne
cted, then
`∀ i, Z i` is locally path-connected.
-/
theorem Pi.locallyPathConnectedSpace_of_finite_not_pathConnectedSpace {Z : ι → Type*}
    [∀ i, TopologicalSpace (Z i)] [∀ i, LocallyPathConnectedSpace (Z i)]
    (hfinite : {i | ¬PathConnectedSpace (Z i)}.Finite) :
    LocallyPathConnectedSpace (∀ i, Z i) where
  path_connected_basis x := hasBasis_self.mpr fun U hU ↦ by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨J, hJ, t, ht, htU⟩ := hU
    let K := J ∪ {i | ¬PathConnectedSpace (Z i)}
    refine ⟨K.pi fun i ↦ pathComponentIn (t i) (x i),
      set_pi_mem_nhds (hJ.union hfinite) fun i _ ↦ pathComponentIn_mem_nhds (ht i), ?_,
      fun f hf ↦ htU fun i hiJ ↦ pathComponentIn_subset (hf i (mem_union_left _ hiJ))⟩
    classical
    rw [← univ_pi_piecewise_univ]
    refine .pi fun i ↦ ?_
    by_cases hi : i ∈ K
    · rw [piecewise_eq_of_mem _ _ _ hi]
      exact isPathConnected_pathComponentIn (mem_of_mem_nhds (ht i))
    · rw [piecewise_eq_of_notMem _ _ _ hi]
      have : PathConnectedSpace (Z i) := not_not.mp (not_or.1 hi).2
      exact isPathConnected_univ

/-- A finite product of locally path-connected spaces is locally path-connected. -/
/-
**Pi.locallyPathConnectedSpace_of_finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.locallyPathConnectedSpace_of_finite [Finite ι] {Z : ι -> Type*} [forall
 i, TopologicalSpace (Z i)] [forall i, LocallyPathConnectedSpace (Z i)] : Locall
yPathConnectedSpace (forall i, Z i)
参数：Z i；Z i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.locallyPathConnectedSpace_of_finite_not_pathConnectedSpace`：Pi.locall
yPathConnectedSpace_of_finite_not_pathConnectedSpace {Z : ι -> Type*} [forall i,
 TopologicalSpace (Z i)] [forall i, LocallyPathConn…
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite

--- 原说明 ---
A finite product of locally path-connected spaces is locally path-connected.
-/
instance Pi.locallyPathConnectedSpace_of_finite [Finite ι] {Z : ι → Type*}
    [∀ i, TopologicalSpace (Z i)] [∀ i, LocallyPathConnectedSpace (Z i)] :
    LocallyPathConnectedSpace (∀ i, Z i) :=
  locallyPathConnectedSpace_of_finite_not_pathConnectedSpace (toFinite _)

/-- A product of path-connected, locally path-connected spaces is locally path-connected. Note
that an arbitrary product of locally path-connected spaces need not be locally path-connected, so
the path-connectedness assumption cannot be dropped entirely (though it can be dropped for
finitely many factors, see `Pi.locallyPathConnectedSpace_of_finite_not_pathConnectedSpace`). -/
/-
**Pi.locallyPathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.locallyPathConnectedSpace {Z : ι -> Type*} [forall i, TopologicalSpace 
(Z i)] [forall i, LocallyPathConnectedSpace (Z i)] [forall i, PathConnectedSpace
 (Z i)] : LocallyPathConnectedSpace (forall i, Z i)
参数：Z i；Z i；Z i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.locallyPathConnectedSpace_of_finite_not_pathConnectedSpace`：Pi.locall
yPathConnectedSpace_of_finite_not_pathConnectedSpace {Z : ι -> Type*} [forall i,
 TopologicalSpace (Z i)] [forall i, LocallyPathConn…
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite

--- 原说明 ---
A product of path-connected, locally path-connected spaces is locally path-conne
cted. Note
that an arbitrary product of locally path-connected spaces need not be locally p
ath-connected, so
the path-connectedness assumption cannot be dropped entirely (though it can be d
ropped for
finitely many factors, see `Pi.locallyPathConnectedSpace_of_finite_not_pathConne
ctedSpace`).
-/
instance Pi.locallyPathConnectedSpace {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)]
    [∀ i, LocallyPathConnectedSpace (Z i)] [∀ i, PathConnectedSpace (Z i)] :
    LocallyPathConnectedSpace (∀ i, Z i) :=
  locallyPathConnectedSpace_of_finite_not_pathConnectedSpace
    (finite_empty.subset fun _ hi ↦ hi inferInstance)

/-- A product of spaces is locally path-connected iff it is empty, or every factor is locally
path-connected and all but finitely many factors are path-connected. -/
/-
**Pi.locallyPathConnectedSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.locallyPathConnectedSpace_iff {Z : ι -> Type*} [forall i, TopologicalSp
ace (Z i)] : LocallyPathConnectedSpace (forall i, Z i) ↔ IsEmpty (forall i, Z i)
 ∨ (forall i, LocallyPathConnectedSpace (Z i)) ∧ {i | ¬PathConnectedSpace (Z i)}
.Finite
参数：Z i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.nonempty_pi`：Classical.nonempty_pi {ι} {α : ι -> Sort*} : None
mpty (forall i, α i) ↔ forall i, Nonempty (α i)
· 使用引理 `Topology.IsQuotientMap.locallyPathConnectedSpace`：Topology.IsQuotientMap
.locallyPathConnectedSpace {f : X -> Y} (h : IsQuotientMap f) : LocallyPathConne
ctedSpace Y
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
· 使用定理 `IsOpen.pathComponent`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Loca
llyPathConnectedSpace X] (x : X), IsOpen (pathComponent x)
· 使用定理 `mem_pathComponent_self`：mem_pathComponent_self (x : X) : x in pathCompon
ent x
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pathConnectedSpace_iff_univ`：pathConnectedSpace_iff_univ : PathConnected
Space X ↔ IsPathConnected (univ : Set X)
· 使用定理 `IsPathConnected.image`：IsPathConnected.image (hF : IsPathConnected F) {f
 : X -> Y} (hf : Continuous f) : IsPathConnected (f '' F)
· 使用定理 `isPathConnected_pathComponent`：isPathConnected_pathComponent : IsPathCon
nected (pathComponent x)
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
A product of spaces is locally path-connected iff it is empty, or every factor i
s locally
path-connected and all but finitely many factors are path-connected.
-/
theorem Pi.locallyPathConnectedSpace_iff {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)] :
    LocallyPathConnectedSpace (∀ i, Z i) ↔
      IsEmpty (∀ i, Z i) ∨
        (∀ i, LocallyPathConnectedSpace (Z i)) ∧ {i | ¬PathConnectedSpace (Z i)}.Finite := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases isEmpty_or_nonempty (∀ i, Z i) with he | hne
    · exact .inl he
    obtain ⟨x⟩ := hne
    classical
    have : ∀ i, Nonempty (Z i) := Classical.nonempty_pi.mp ⟨x⟩
    refine .inr ⟨fun i ↦ ((isOpenMap_eval i).isQuotientMap (continuous_apply i)
      (surjective_eval i)).locallyPathConnectedSpace, ?_⟩
    have hVn : pathComponent x ∈ 𝓝 x :=
      (IsOpen.pathComponent x).mem_nhds (mem_pathComponent_self x)
    rw [nhds_pi, Filter.mem_pi] at hVn
    obtain ⟨J, hJ, t, ht, htV⟩ := hVn
    refine hJ.subset fun i hi ↦ by_contra fun hiJ ↦ hi ?_
    suffices himg : eval i '' pathComponent x = univ from pathConnectedSpace_iff_univ.mpr
      (himg ▸ isPathConnected_pathComponent.image (continuous_apply i))
    refine (subset_univ _).antisymm fun z _ ↦ ⟨update x i z, htV fun j hj ↦ ?_, by simp⟩
    rw [update_of_ne (ne_of_mem_of_not_mem hj hiJ)]
    exact mem_of_mem_nhds (ht j)
  · rintro (he | ⟨hloc, hfin⟩)
    · exact ⟨he.elim⟩
    · exact locallyPathConnectedSpace_of_finite_not_pathConnectedSpace hfin
/-
**AlexandrovDiscrete.locallyPathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AlexandrovDiscrete.locallyPathConnectedSpace [AlexandrovDiscrete X] : Loca
llyPathConnectedSpace X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyPathConnectedSpace.of_bases`：LocallyPathConnectedSpace.of_bases {
p : X -> ι -> Prop} {s : X -> ι -> Set X} (h : forall x, (𝓝 x).HasBasis (p x) (s
 x)) (h' : forall x i, p…
· 使用定理 `nhds_basis_nhdsKer_singleton`：∀ {α : Type u_3} [inst : TopologicalSpace 
α] [AlexandrovDiscrete α] (a : α),   (nhds a).HasBasis (fun x => True) fun x => 
nhdsKer {a}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `specializes_rfl`：specializes_rfl : x ⤳ x
· 使用定理 `JoinedIn.symm`：JoinedIn.symm (h : JoinedIn F x y) : JoinedIn F y x
· 使用定理 `Specializes.joinedIn`：Specializes.joinedIn (h : x ⤳ y) (hx : x in F) (hy
 : y in F) : JoinedIn F x y
· 使用定理 `mem_nhdsKer_singleton`：mem_nhdsKer_singleton : x in nhdsKer {y} ↔ x ⤳ y
· 使用定理 `specializes_refl`：specializes_refl (x : X) : x ⤳ x
-/
instance AlexandrovDiscrete.locallyPathConnectedSpace [AlexandrovDiscrete X] :
    LocallyPathConnectedSpace X := by
  apply LocallyPathConnectedSpace.of_bases nhds_basis_nhdsKer_singleton
  simp only [forall_const, IsPathConnected, mem_nhdsKer_singleton]
  intro x
  exists x, specializes_rfl
  intro y hy
  symm
  apply hy.joinedIn <;> rewrite [mem_nhdsKer_singleton] <;> [assumption; rfl]

@[deprecated (since := "2026-06-21")]
alias AlexandrovDiscrete.locPathConnectedSpace := AlexandrovDiscrete.locallyPathConnectedSpace

/-- If a space is locally path-connected, the topology of its path components is discrete. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a space is locally path-connected, the topology of its path components is dis
crete.
-/
instance : DiscreteTopology <| ZerothHomotopy X := by
  refine discreteTopology_iff_isOpen_singleton.mpr fun c ↦ ?_
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
  rw [← ZerothHomotopy.isQuotientMap_mk.isOpen_preimage]
  grind [ZerothHomotopy.preimage_singleton_eq_pathComponent, IsOpen.pathComponent]

/-- A locally path-connected compact space has finitely many path components. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A locally path-connected compact space has finitely many path components.
-/
instance [CompactSpace X] : Finite <| ZerothHomotopy X :=
  finite_of_compact_of_discrete

end LocallyPathConnectedSpace

