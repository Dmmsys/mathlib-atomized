/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Topology.Sets.Opens

/-!
# Open covers

We define `IsOpenCover` as a predicate on indexed families of open sets in a topological space `X`,
asserting that their union is `X`. This is an example of a declaration whose name is actually
longer than its content; but giving it a name serves as a way of standardizing API.
-/

@[expose] public section

open Set Topology

namespace TopologicalSpace

/-- An indexed family of open sets whose union is `X`. -/
/-
**TopologicalSpace.IsOpenCover** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace`。
形式化陈述：IsOpenCover {ι X : Type*} [TopologicalSpace X] (u : ι -> Opens X) : Prop
参数：u : ι -> Opens X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An indexed family of open sets whose union is `X`.
-/
def IsOpenCover {ι X : Type*} [TopologicalSpace X] (u : ι → Opens X) : Prop :=
  iSup u = ⊤

variable {ι κ X Y : Type*} [TopologicalSpace X] {u : ι → Opens X}
  [TopologicalSpace Y] {v : κ → Opens Y}

namespace IsOpenCover

/-
**TopologicalSpace.IsOpenCover.mk** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.Is
OpenCover`。
形式化陈述：mk (h : iSup u = ⊤) : IsOpenCover u
参数：h : iSup u = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk (h : iSup u = ⊤) : IsOpenCover u := h
/-
**TopologicalSpace.IsOpenCover.of_sets** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpa
ce.IsOpenCover`。
形式化陈述：of_sets {v : ι -> Set X} (h_open : forall i, IsOpen (v i)) (h_iUnion : ⋃ i
, v i = univ) : IsOpenCover (fun i => ⟨v i, h_open i⟩)
参数：h_open : forall i, IsOpen (v i)；h_iUnion : ⋃ i, v i = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma of_sets {v : ι → Set X} (h_open : ∀ i, IsOpen (v i)) (h_iUnion : ⋃ i, v i = univ) :
    IsOpenCover (fun i ↦ ⟨v i, h_open i⟩) := by
  simp [IsOpenCover, h_iUnion]
/-
**TopologicalSpace.IsOpenCover.iSup_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Topologica
lSpace.IsOpenCover`。
形式化陈述：iSup_eq_top (hu : IsOpenCover u) : ⨆ i, u i = ⊤
参数：hu : IsOpenCover u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iSup_eq_top (hu : IsOpenCover u) : ⨆ i, u i = ⊤ := hu
/-
**TopologicalSpace.IsOpenCover.iSup_set_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Topol
ogicalSpace.IsOpenCover`。
形式化陈述：iSup_set_eq_univ (hu : IsOpenCover u) : ⋃ i, (u i : Set X) = univ
参数：hu : IsOpenCover u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用引理 `TopologicalSpace.IsOpenCover.iSup_eq_top`：iSup_eq_top (hu : IsOpenCover 
u) : ⨆ i, u i = ⊤
-/
lemma iSup_set_eq_univ (hu : IsOpenCover u) : ⋃ i, (u i : Set X) = univ := by
  simpa [← SetLike.coe_set_eq] using hu.iSup_eq_top

/-- Pullback of a covering of `Y` by a continuous map `X → Y`, giving a covering of `X` with the
same index type. -/
/-
**TopologicalSpace.IsOpenCover.comap** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace
.IsOpenCover`。
形式化陈述：comap (hv : IsOpenCover v) (f : C(X, Y)) : IsOpenCover fun k => (v k).coma
p f
参数：hv : IsOpenCover v；f : C(X, Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用引理 `TopologicalSpace.IsOpenCover.iSup_set_eq_univ`：iSup_set_eq_univ (hu : Is
OpenCover u) : ⋃ i, (u i : Set X) = univ
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Pullback of a covering of `Y` by a continuous map `X → Y`, giving a covering of 
`X` with the
same index type.
-/
lemma comap (hv : IsOpenCover v) (f : C(X, Y)) : IsOpenCover fun k ↦ (v k).comap f := by
  simp [IsOpenCover, ← preimage_iUnion, hv.iSup_set_eq_univ]
/-
**TopologicalSpace.IsOpenCover.exists_mem** 是 Mathlib 中的一个引理，位于命名空间 `Topological
Space.IsOpenCover`。
形式化陈述：exists_mem (hu : IsOpenCover u) (a : X) : exists i, a in u i
参数：hu : IsOpenCover u；a : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `TopologicalSpace.IsOpenCover.iSup_set_eq_univ`：iSup_set_eq_univ (hu : Is
OpenCover u) : ⋃ i, (u i : Set X) = univ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
lemma exists_mem (hu : IsOpenCover u) (a : X) : ∃ i, a ∈ u i := by
  simpa [← hu.iSup_set_eq_univ] using mem_univ a
/-
**TopologicalSpace.IsOpenCover.exists_mem_nhds** 是 Mathlib 中的一个引理，位于命名空间 `Topolo
gicalSpace.IsOpenCover`。
形式化陈述：exists_mem_nhds (hu : IsOpenCover u) (a : X) : exists i, (u i : Set X) in 
𝓝 a
参数：hu : IsOpenCover u；a : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopologicalSpace.IsOpenCover.exists_mem`：exists_mem (hu : IsOpenCover u)
 (a : X) : exists i, a in u i
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
-/
lemma exists_mem_nhds (hu : IsOpenCover u) (a : X) : ∃ i, (u i : Set X) ∈ 𝓝 a :=
  match hu.exists_mem a with | ⟨i, hi⟩ => ⟨i, (u i).isOpen.mem_nhds hi⟩
/-
**TopologicalSpace.IsOpenCover.iUnion_inter** 是 Mathlib 中的一个引理，位于命名空间 `Topologic
alSpace.IsOpenCover`。
形式化陈述：iUnion_inter (hu : IsOpenCover u) (s : Set X) : ⋃ i, s inter u i = s
参数：hu : IsOpenCover u；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TopologicalSpace.IsOpenCover.iSup_set_eq_univ`：iSup_set_eq_univ (hu : Is
OpenCover u) : ⋃ i, (u i : Set X) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iUnion_inter (hu : IsOpenCover u) (s : Set X) :
    ⋃ i, s ∩ u i = s := by
  simp [← inter_iUnion, hu.iSup_set_eq_univ]
/-
**TopologicalSpace.IsOpenCover.isTopologicalBasis** 是 Mathlib 中的一个引理，位于命名空间 `Top
ologicalSpace.IsOpenCover`。
形式化陈述：isTopologicalBasis (hu : IsOpenCover u) {B : forall i, Set (Set (u i))} (h
B : forall i, IsTopologicalBasis (B i)) : IsTopologicalBasis (⋃ i, (Subtype.val 
'' ·) '' B i)
参数：hu : IsOpenCover u；Set (u i)；hB : forall i, IsTopologicalBasis (B i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.isTopologicalBasis_of_cover`：isTopologicalBasis_of_cove
r {ι} {U : ι -> Set α} (Uo : forall i, IsOpen (U i)) (Uc : ⋃ i, U i = univ) {b :
 forall i, Set (Set (U i))} (hb : …
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用引理 `TopologicalSpace.IsOpenCover.iSup_set_eq_univ`：iSup_set_eq_univ (hu : Is
OpenCover u) : ⋃ i, (u i : Set X) = univ
-/
lemma isTopologicalBasis (hu : IsOpenCover u)
    {B : ∀ i, Set (Set (u i))} (hB : ∀ i, IsTopologicalBasis (B i)) :
    IsTopologicalBasis (⋃ i, (Subtype.val '' ·) '' B i) :=
  isTopologicalBasis_of_cover (fun i ↦ (u i).2) hu.iSup_set_eq_univ hB
/-
**TopologicalSpace.IsOpenCover.exists_finite_of_compactSpace** 是 Mathlib 中的一个引理，
位于命名空间 `TopologicalSpace.IsOpenCover`。
形式化陈述：exists_finite_of_compactSpace (hu : IsOpenCover u) [CompactSpace X] : exis
ts (s : Finset ι), IsOpenCover (fun i : s => u i.1)
参数：hu : IsOpenCover u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `TopologicalSpace.IsOpenCover.eq_1`：∀ {ι : Type u_1} {X : Type u_2} [inst
 : TopologicalSpace X] (u : ι → TopologicalSpace.Opens X),   TopologicalSpace.Is
OpenCover u = (iSup u =…
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `Set.iUnion_subtype`：iUnion_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
-/
lemma exists_finite_of_compactSpace (hu : IsOpenCover u) [CompactSpace X] :
    ∃ (s : Finset ι), IsOpenCover (fun i : s ↦ u i.1) := by
  rw [IsOpenCover, eq_top_iff, ← SetLike.coe_subset_coe] at hu
  obtain ⟨s, hs⟩ := IsCompact.elim_finite_subcover isCompact_univ _ (fun i ↦ (u i).2)
    (by simpa using hu)
  use s
  simpa [IsOpenCover, eq_top_iff, ← SetLike.coe_subset_coe, Set.iUnion_subtype] using hs

end IsOpenCover

/-
**TopologicalSpace.Opens.IsBasis.isOpenCover** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace.Opens.IsBasis`。
形式化陈述：∀ {X : Type u_3} [inst : TopologicalSpace X] {S : Set (TopologicalSpace.Op
ens X)},   TopologicalSpace.Opens.IsBasis S → TopologicalSpace.IsOpenCover fun U
 => ↑U
参数：TopologicalSpace.Opens X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.IsTopologicalBasis.sUnion_eq`：∀ {α : Type u} [t : Topol
ogicalSpace α] {s : Set (Set α)}, TopologicalSpace.IsTopologicalBasis s → ⋃₀ s =
 Set.univ
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Opens.IsBasis.isOpenCover {S : Set (Opens X)} (hS : Opens.IsBasis S) :
    IsOpenCover (fun U : S ↦ (U : Opens X)) := by
  ext1
  simp [← hS.2]

/-- Given an open cover and a basis,
the set of basis elements contained in any of the covers is still a cover. -/
/-
**TopologicalSpace.Opens.IsBasis.isOpenCover_mem_and_le** 是 Mathlib 中的一个定理，位于命名空
间 `TopologicalSpace.Opens.IsBasis`。
形式化陈述：∀ {ι : Type u_1} {X : Type u_3} [inst : TopologicalSpace X] {S : Set (Topo
logicalSpace.Opens X)},   TopologicalSpace.Opens.IsBasis S →     ∀ {U : ι → Topo
logicalSpace.Opens X}, TopologicalSpace.IsOpenCover U → TopologicalSpace.IsOpenC
over fun V => (↑V).1
参数：TopologicalSpace.Opens X；↑V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `TopologicalSpace.IsOpenCover.exists_mem`：exists_mem (hu : IsOpenCover u)
 (a : X) : exists i, a in u i
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Given an open cover and a basis,
the set of basis elements contained in any of the covers is still a cover.
-/
lemma Opens.IsBasis.isOpenCover_mem_and_le {S : Set (Opens X)} (hS : Opens.IsBasis S)
    {U : ι → Opens X} (hU : IsOpenCover U) :
    IsOpenCover (fun V : { x : Opens X × ι // x.1 ∈ S ∧ x.1 ≤ U x.2 } ↦ V.1.1) := by
  refine top_le_iff.mp fun x _ ↦ ?_
  obtain ⟨i, hxi⟩ := hU.exists_mem x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := hS.exists_subset_of_mem_open hxi (U i).2
  simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.mem_mk, Set.mem_iUnion, SetLike.mem_coe]
  exact ⟨⟨(V, i), hV, hVU⟩, hxV⟩

end TopologicalSpace

section Irreducible

open TopologicalSpace Function

/-- (Pre)Irreducibility of an open set can be checked on a cover by opens
with pairwise non-empty intersections. -/
/-
**IsPreirreducible.of_subset_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreirreducible.of_subset_iUnion {X ι : Type*} [TopologicalSpace X] {U : 
ι -> Opens X} (hn : Pairwise ((¬ Disjoint · ·) on U)) (h : forall i, IsPreirredu
cible ((U i) : Set X)) {s : Set X} (hs : IsOpen s) (hsU : s subseteq ⋃ i, U i) :
 IsPreirreducible s
参数：hn : Pairwise ((¬ Disjoint · ·) on U)；h : forall i, IsPreirreducible ((U i) :
 Set X)；hs : IsOpen s；hsU : s subseteq ⋃ i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPreirreducible_empty`：isPreirreducible_empty : IsPreirreducible (∅ : S
et X)
· 使用引理 `exists_mem_irreducibleComponents_subset_of_isIrreducible`：exists_mem_irr
educibleComponents_subset_of_isIrreducible (s : Set X) (hs : IsIrreducible s) : 
exists u in irreducibleComponents X, s subsete…
· 使用定理 `IsPreirreducible.open_subset`：IsPreirreducible.open_subset {U : Set X} (
ht : IsPreirreducible t) (hU : IsOpen U) (hU' : U subseteq t) : IsPreirreducible
 U
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_of_mem_irreducibleComponents`：isClosed_of_mem_irreducibleCompon
ents (s) (H : s in irreducibleComponents X) : IsClosed s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `Set.inter_nonempty_iff_exists_left`：inter_nonempty_iff_exists_left : (s 
inter t).Nonempty ↔ exists x in s, x in t
· 使用定理 `Set.Nonempty.right`：∀ {α : Type u} {s t : Set α}, (s ∩ t).Nonempty → t.N
onempty
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
(Pre)Irreducibility of an open set can be checked on a cover by opens
with pairwise non-empty intersections.
-/
theorem IsPreirreducible.of_subset_iUnion {X ι : Type*} [TopologicalSpace X]
    {U : ι → Opens X} (hn : Pairwise ((¬ Disjoint · ·) on U))
    (h : ∀ i, IsPreirreducible ((U i) : Set X))
    {s : Set X} (hs : IsOpen s) (hsU : s ⊆ ⋃ i, U i) :
    IsPreirreducible s := by
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he]; exact isPreirreducible_empty
  · choose x hx using hne
    choose i hi using mem_iUnion.mp <| hsU hx
    rcases exists_mem_irreducibleComponents_subset_of_isIrreducible (U i).carrier ⟨⟨x, hi⟩, h i⟩
      with ⟨u, hu, hUu⟩
    by_cases huniv : s ⊆ u
    · exact hu.1.2.open_subset hs huniv
    · have huo : IsOpen uᶜ :=
        IsClosed.isOpen_compl (self := isClosed_of_mem_irreducibleComponents u hu)
      rcases not_subset.mp huniv with ⟨a, ⟨ha₁, ha₂⟩⟩
      choose j haj using mem_iUnion.mp <| hsU ha₁
      have hji : j ≠ i := fun hji' ↦ ha₂ <| hUu <| hji' ▸ haj
      rcases inter_nonempty_iff_exists_left.mp
        ((h j) (U i) uᶜ (U i).isOpen huo
        (not_disjoint_iff_nonempty_inter.mp (by simpa using hn hji)) ⟨a, ⟨haj, ha₂⟩⟩).right
        with ⟨x, hx₁, hx₂⟩
      exfalso; exact hx₂ <| hUu hx₁

/-- (Pre)Irreducibility can be checked on an open cover with pairwise non-empty intersections. -/
/-
**PreirreducibleSpace.of_isOpenCover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PreirreducibleSpace.of_isOpenCover {X ι : Type*} [TopologicalSpace X] {U :
 ι -> Opens X} (hn : Pairwise ((¬ Disjoint · ·) on U)) (hU : IsOpenCover U) (h :
 forall i, PreirreducibleSpace (U i)) : PreirreducibleSpace X
参数：hn : Pairwise ((¬ Disjoint · ·) on U)；hU : IsOpenCover U；h : forall i, Preirr
educibleSpace (U i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsPreirreducible.of_subtype`：IsPreirreducible.of_subtype [Preirreducible
Space s] : IsPreirreducible s
· 使用定理 `IsPreirreducible.of_subset_iUnion`：IsPreirreducible.of_subset_iUnion {X 
ι : Type*} [TopologicalSpace X] {U : ι -> Opens X} (hn : Pairwise ((¬ Disjoint ·
 ·) on U)) (h : forall …
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用引理 `TopologicalSpace.IsOpenCover.iSup_set_eq_univ`：iSup_set_eq_univ (hu : Is
OpenCover u) : ⋃ i, (u i : Set X) = univ

--- 原说明 ---
(Pre)Irreducibility can be checked on an open cover with pairwise non-empty inte
rsections.
-/
theorem PreirreducibleSpace.of_isOpenCover {X ι : Type*} [TopologicalSpace X]
    {U : ι → Opens X} (hn : Pairwise ((¬ Disjoint · ·) on U)) (hU : IsOpenCover U)
    (h : ∀ i, PreirreducibleSpace (U i)) :
    PreirreducibleSpace X :=
  have h' (i : _) : IsPreirreducible (U i).carrier := IsPreirreducible.of_subtype
  ⟨IsPreirreducible.of_subset_iUnion hn h' isOpen_univ (by simpa using hU.iSup_set_eq_univ)⟩

end Irreducible

