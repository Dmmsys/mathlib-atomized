/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Clopen

/-!
# Closed sets

We define a few types of closed sets in a topological space.

## Main Definitions

For a topological space `α`,
* `TopologicalSpace.Closeds α`: The type of closed sets.
* `TopologicalSpace.Clopens α`: The type of clopen sets.
-/

@[expose] public section


open Order OrderDual Set Topology


variable {ι α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-! ### Closed sets -/


/-- The type of closed subsets of a topological space. -/
/-
**TopologicalSpace.Closeds** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopologicalSpace`。
形式化陈述：(α : Type u_4) → [TopologicalSpace α] → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of closed subsets of a topological space.
-/
structure Closeds (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isClosed' : IsClosed carrier

namespace Closeds

/-
**TopologicalSpace.Closeds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Closeds`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Closeds α) α where
  coe := Closeds.carrier
  coe_injective s t h := by cases s; cases t; congr
/-
**TopologicalSpace.Closeds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Closeds`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Closeds α) := fast_instance% .ofSetLike (Closeds α) α
/-
**TopologicalSpace.Closeds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Closeds`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift (Set α) (Closeds α) (↑) IsClosed where
  prf s hs := ⟨⟨s, hs⟩, rfl⟩
/-
**TopologicalSpace.Closeds.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Closeds`。
形式化陈述：isClosed (s : Closeds α) : IsClosed (s : Set α)
参数：s : Closeds α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Closeds.isClosed'`：∀ {α : Type u_4} [inst : Topological
Space α] (self : TopologicalSpace.Closeds α), IsClosed self.carrier
-/
theorem isClosed (s : Closeds α) : IsClosed (s : Set α) :=
  s.isClosed'

/-- See Note [custom simps projection]. -/
/-
**TopologicalSpace.Closeds.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace
.Closeds.Simps`。
形式化陈述：{α : Type u_2} → [inst : TopologicalSpace α] → TopologicalSpace.Closeds α 
→ Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.coe (s : Closeds α) : Set α := s

initialize_simps_projections Closeds (carrier → coe, as_prefix coe)

@[simp]
/-
**TopologicalSpace.Closeds.carrier_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `Topological
Space.Closeds`。
形式化陈述：carrier_eq_coe (s : Closeds α) : s.carrier = (s : Set α)
参数：s : Closeds α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma carrier_eq_coe (s : Closeds α) : s.carrier = (s : Set α) := rfl

@[ext]
/-
**TopologicalSpace.Closeds.ext** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Close
ds`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {s t : TopologicalSpace.Close
ds α}, ↑s = ↑t → s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
-/
protected theorem ext {s t : Closeds α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/-
**TopologicalSpace.Closeds.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Cl
oseds`。
形式化陈述：coe_mk (s : Set α) (h) : (mk s h : Set α) = s
参数：s : Set α；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl

@[simp]
/-
**TopologicalSpace.Closeds.mem_mk** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.Cl
oseds`。
形式化陈述：mem_mk {s : Set α} {hs : IsClosed s} {x : α} : x in (⟨s, hs⟩ : Closeds α) 
↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_mk {s : Set α} {hs : IsClosed s} {x : α} : x ∈ (⟨s, hs⟩ : Closeds α) ↔ x ∈ s :=
  .rfl

/-- The closure of a set, as an element of `TopologicalSpace.Closeds`. -/
@[simps]
/-
**TopologicalSpace.Closeds.closure** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.C
loseds`。
形式化陈述：{α : Type u_2} → [inst : TopologicalSpace α] → Set α → TopologicalSpace.Cl
oseds α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)

--- 原说明 ---
The closure of a set, as an element of `TopologicalSpace.Closeds`.
-/
protected def closure (s : Set α) : Closeds α :=
  ⟨closure s, isClosed_closure⟩

@[simp]
/-
**TopologicalSpace.Closeds.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpa
ce.Closeds`。
形式化陈述：mem_closure {s : Set α} {x : α} : x in Closeds.closure s ↔ x in closure s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closure {s : Set α} {x : α} : x ∈ Closeds.closure s ↔ x ∈ closure s := .rfl
/-
**TopologicalSpace.Closeds.gc** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Closed
s`。
形式化陈述：gc : GaloisConnection Closeds.closure ((↑) : Closeds α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `TopologicalSpace.Closeds.isClosed`：isClosed (s : Closeds α) : IsClosed (
s : Set α)
-/
theorem gc : GaloisConnection Closeds.closure ((↑) : Closeds α → Set α) := fun _ U =>
  ⟨subset_closure.trans, fun h => closure_minimal h U.isClosed⟩

@[simp]
/-
**TopologicalSpace.Closeds.closure_le** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpac
e.Closeds`。
形式化陈述：closure_le {s : Set α} {t : Closeds α} : .closure s <= t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `TopologicalSpace.Closeds.isClosed`：isClosed (s : Closeds α) : IsClosed (
s : Set α)
-/
lemma closure_le {s : Set α} {t : Closeds α} : .closure s ≤ t ↔ s ⊆ t :=
  t.isClosed.closure_subset_iff

/-- The Galois insertion between sets and closeds. -/
/-
**TopologicalSpace.Closeds.gi** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Closed
s`。
形式化陈述：gi : GaloisInsertion (@Closeds.closure α _) (↑) where choice s hs
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Closeds.gc`：gc : GaloisConnection Closeds.closure ((↑) 
: Closeds α -> Set α)

--- 原说明 ---
The Galois insertion between sets and closeds.
-/
def gi : GaloisInsertion (@Closeds.closure α _) (↑) where
  choice s hs := ⟨s, closure_eq_iff_isClosed.1 <| hs.antisymm subset_closure⟩
  gc := gc
  le_l_u _ := subset_closure
  choice_eq _s hs := SetLike.coe_injective <| subset_closure.antisymm hs
/-
**TopologicalSpace.Closeds.instCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 `Topolo
gicalSpace.Closeds`。
形式化陈述：instCompleteLattice : CompleteLattice (Closeds α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
-/
instance instCompleteLattice : CompleteLattice (Closeds α) :=
  fast_instance% CompleteLattice.copy
    (GaloisInsertion.liftCompleteLattice gi)
    -- le
    _ rfl
    -- top
    ⟨univ, isClosed_univ⟩ rfl
    -- bot
    ⟨∅, isClosed_empty⟩ (SetLike.coe_injective closure_empty.symm)
    -- sup
    (fun s t => ⟨s ∪ t, s.2.union t.2⟩)
    (funext fun s => funext fun t => SetLike.coe_injective (s.2.union t.2).closure_eq.symm)
    -- inf
    (fun s t => ⟨s ∩ t, s.2.inter t.2⟩) rfl
    -- sSup
    _ rfl
    -- sInf
    (fun S => ⟨⋂ s ∈ S, ↑s, isClosed_biInter fun s _ => s.2⟩)
    (funext fun _ => SetLike.coe_injective sInf_image.symm)

/-- The type of closed sets is inhabited, with default element the empty set. -/
/-
**TopologicalSpace.Closeds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Closeds`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of closed sets is inhabited, with default element the empty set.
-/
instance : Inhabited (Closeds α) :=
  ⟨⊥⟩

@[simp, norm_cast]
/-
**TopologicalSpace.Closeds.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.C
loseds`。
形式化陈述：coe_sup (s t : Closeds α) : (↑(s ⊔ t) : Set α) = ↑s union ↑t
参数：s t : Closeds α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (s t : Closeds α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t := by
  rfl

@[simp, norm_cast]
/-
**TopologicalSpace.Closeds.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.C
loseds`。
形式化陈述：coe_inf (s t : Closeds α) : (↑(s ⊓ t) : Set α) = ↑s inter ↑t
参数：s t : Closeds α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (s t : Closeds α) : (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t :=
  rfl

@[simp, norm_cast]
/-
**TopologicalSpace.Closeds.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.C
loseds`。
形式化陈述：coe_top : (↑(⊤ : Closeds α) : Set α) = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : (↑(⊤ : Closeds α) : Set α) = univ :=
  rfl

@[simp, norm_cast]
/-
**TopologicalSpace.Closeds.coe_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpa
ce.Closeds`。
形式化陈述：coe_eq_univ {s : Closeds α} : (s : Set α) = univ ↔ s = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem coe_eq_univ {s : Closeds α} : (s : Set α) = univ ↔ s = ⊤ :=
  SetLike.coe_injective.eq_iff' rfl

@[simp, norm_cast]
/-
**TopologicalSpace.Closeds.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.C
loseds`。
形式化陈述：coe_bot : (↑(⊥ : Closeds α) : Set α) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : (↑(⊥ : Closeds α) : Set α) = ∅ :=
  rfl

@[simp, norm_cast]
/-
**TopologicalSpace.Closeds.coe_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.Closeds`。
形式化陈述：coe_eq_empty {s : Closeds α} : (s : Set α) = ∅ ↔ s = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem coe_eq_empty {s : Closeds α} : (s : Set α) = ∅ ↔ s = ⊥ :=
  SetLike.coe_injective.eq_iff' rfl
/-
**TopologicalSpace.Closeds.coe_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.Closeds`。
形式化陈述：coe_nonempty {s : Closeds α} : (s : Set α).Nonempty ↔ s != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `TopologicalSpace.Closeds.coe_eq_empty`：coe_eq_empty {s : Closeds α} : (s
 : Set α) = ∅ ↔ s = ⊥
-/
theorem coe_nonempty {s : Closeds α} : (s : Set α).Nonempty ↔ s ≠ ⊥ :=
  nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp, norm_cast]
/-
**TopologicalSpace.Closeds.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Closeds`。
形式化陈述：coe_sInf {S : Set (Closeds α)} : (↑(sInf S) : Set α) = ⋂ i in S, ↑i
参数：Closeds α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sInf {S : Set (Closeds α)} : (↑(sInf S) : Set α) = ⋂ i ∈ S, ↑i :=
  rfl

@[simp]
/-
**TopologicalSpace.Closeds.coe_sSup** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.
Closeds`。
形式化陈述：coe_sSup {S : Set (Closeds α)} : ((sSup S : Closeds α) : Set α) = closure 
(⋃₀ ((↑) '' S))
参数：Closeds α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_sSup {S : Set (Closeds α)} : ((sSup S : Closeds α) : Set α) =
    closure (⋃₀ ((↑) '' S)) := by rfl

@[simp, norm_cast]
/-
**TopologicalSpace.Closeds.coe_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.Closeds`。
形式化陈述：coe_finset_sup (f : ι -> Closeds α) (s : Finset ι) : (↑(s.sup f) : Set α) 
= s.sup ((↑) ∘ f)
参数：f : ι -> Closeds α；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_sup`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type
 u_5} [inst : SemilatticeSup α] [inst_1 : OrderBot α]   [inst_2 : SemilatticeSup
 β] …
· 使用定理 `SupBotHom.instSupBotHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Ma
x α] [inst_1 : Bot α] [inst_2 : Max β] [inst_3 : Bot β],   SupBotHomClass (SupBo
tHom α β) α β
· 使用定理 `TopologicalSpace.Closeds.coe_sup`：coe_sup (s t : Closeds α) : (↑(s ⊔ t) 
: Set α) = ↑s union ↑t
· 使用定理 `TopologicalSpace.Closeds.coe_bot`：coe_bot : (↑(⊥ : Closeds α) : Set α) =
 ∅
-/
theorem coe_finset_sup (f : ι → Closeds α) (s : Finset ι) :
    (↑(s.sup f) : Set α) = s.sup ((↑) ∘ f) :=
  map_finset_sup (⟨⟨(↑), coe_sup⟩, coe_bot⟩ : SupBotHom (Closeds α) (Set α)) _ _

@[simp, norm_cast]
/-
**TopologicalSpace.Closeds.coe_finset_inf** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.Closeds`。
形式化陈述：coe_finset_inf (f : ι -> Closeds α) (s : Finset ι) : (↑(s.inf f) : Set α) 
= s.inf ((↑) ∘ f)
参数：f : ι -> Closeds α；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_inf`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type
 u_5} [inst : SemilatticeInf α] [inst_1 : OrderTop α]   [inst_2 : SemilatticeInf
 β] …
· 使用定理 `InfTopHom.instInfTopHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Mi
n α] [inst_1 : Top α] [inst_2 : Min β] [inst_3 : Top β],   InfTopHomClass (InfTo
pHom α β) α β
· 使用定理 `TopologicalSpace.Closeds.coe_inf`：coe_inf (s t : Closeds α) : (↑(s ⊓ t) 
: Set α) = ↑s inter ↑t
· 使用定理 `TopologicalSpace.Closeds.coe_top`：coe_top : (↑(⊤ : Closeds α) : Set α) =
 univ
-/
theorem coe_finset_inf (f : ι → Closeds α) (s : Finset ι) :
    (↑(s.inf f) : Set α) = s.inf ((↑) ∘ f) :=
  map_finset_inf (⟨⟨(↑), coe_inf⟩, coe_top⟩ : InfTopHom (Closeds α) (Set α)) _ _

@[simp]
/-
**TopologicalSpace.Closeds.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Closeds`。
形式化陈述：mem_sInf {S : Set (Closeds α)} {x : α} : x in sInf S ↔ forall s in S, x in
 s
参数：Closeds α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_sInf {S : Set (Closeds α)} {x : α} : x ∈ sInf S ↔ ∀ s ∈ S, x ∈ s := mem_iInter₂

@[simp]
/-
**TopologicalSpace.Closeds.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Closeds`。
形式化陈述：mem_iInf {ι} {x : α} {s : ι -> Closeds α} : x in iInf s ↔ forall i, x in s
 i
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
theorem mem_iInf {ι} {x : α} {s : ι → Closeds α} : x ∈ iInf s ↔ ∀ i, x ∈ s i := by simp [iInf]

@[simp, norm_cast]
/-
**TopologicalSpace.Closeds.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Closeds`。
形式化陈述：coe_iInf {ι} (s : ι -> Closeds α) : ((⨅ i, s i : Closeds α) : Set α) = ⋂ i
, s i
参数：s : ι -> Closeds α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem coe_iInf {ι} (s : ι → Closeds α) : ((⨅ i, s i : Closeds α) : Set α) = ⋂ i, s i := by
  ext; simp
/-
**TopologicalSpace.Closeds.iInf_def** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Closeds`。
形式化陈述：iInf_def {ι} (s : ι -> Closeds α) : ⨅ i, s i = ⟨⋂ i, s i, isClosed_iInter 
fun i => (s i).2⟩
参数：s : ι -> Closeds α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Closeds.ext`：∀ {α : Type u_2} [inst : TopologicalSpace 
α] {s t : TopologicalSpace.Closeds α}, ↑s = ↑t → s = t
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `TopologicalSpace.Closeds.isClosed'`：∀ {α : Type u_4} [inst : Topological
Space α] (self : TopologicalSpace.Closeds α), IsClosed self.carrier
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Closeds.coe_iInf`：coe_iInf {ι} (s : ι -> Closeds α) : (
(⨅ i, s i : Closeds α) : Set α) = ⋂ i, s i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInf_def {ι} (s : ι → Closeds α) :
    ⨅ i, s i = ⟨⋂ i, s i, isClosed_iInter fun i => (s i).2⟩ := by ext1; simp

@[simp]
/-
**TopologicalSpace.Closeds.iInf_mk** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.C
loseds`。
形式化陈述：iInf_mk {ι} (s : ι -> Set α) (h : forall i, IsClosed (s i)) : (⨅ i, ⟨s i, 
h i⟩ : Closeds α) = ⟨⋂ i, s i, isClosed_iInter h⟩
参数：s : ι -> Set α；h : forall i, IsClosed (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Closeds.iInf_def`：iInf_def {ι} (s : ι -> Closeds α) : ⨅
 i, s i = ⟨⋂ i, s i, isClosed_iInter fun i => (s i).2⟩
-/
theorem iInf_mk {ι} (s : ι → Set α) (h : ∀ i, IsClosed (s i)) :
    (⨅ i, ⟨s i, h i⟩ : Closeds α) = ⟨⋂ i, s i, isClosed_iInter h⟩ :=
  iInf_def _
/-
**TopologicalSpace.Closeds.instCoframe** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpa
ce.Closeds`。
形式化陈述：instCoframe : Coframe (Closeds α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoframe : Coframe (Closeds α) := fast_instance% .ofMinimalAxioms {
  iInf_sup_le_sup_sInf a s :=
    (SetLike.coe_injective <| by simp only [coe_sup, coe_iInf, coe_sInf, Set.union_iInter₂]).le }

@[simps]
/-
**TopologicalSpace.Closeds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Closeds`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T1Space α] : Singleton α (Closeds α) where
  singleton x := ⟨{x}, isClosed_singleton⟩

@[simp]
/-
**TopologicalSpace.Closeds.mk_singleton** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.Closeds`。
形式化陈述：mk_singleton [T1Space α] {x : α} : (⟨{x}, isClosed_singleton⟩ : Closeds α)
 = {x}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
-/
theorem mk_singleton [T1Space α] {x : α} :
    (⟨{x}, isClosed_singleton⟩ : Closeds α) = {x} :=
  rfl
/-
**TopologicalSpace.Closeds.mem_singleton** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.Closeds`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] [inst_1 : T1Space α] {a b : α
}, a ∈ {b} ↔ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_singleton [T1Space α] {a b : α} : a ∈ ({b} : Closeds α) ↔ a = b := Iff.rfl
/-
**TopologicalSpace.Closeds.singleton_injective** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gicalSpace.Closeds`。
形式化陈述：singleton_injective [T1Space α] : Function.Injective ({·} : α -> Closeds α
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Set.singleton_injective`：singleton_injective : Injective (singleton : α 
-> Set α)
-/
theorem singleton_injective [T1Space α] : Function.Injective ({·} : α → Closeds α) :=
  .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]
/-
**TopologicalSpace.Closeds.singleton_inj** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.Closeds`。
形式化陈述：singleton_inj [T1Space α] {x y : α} : ({x} : Closeds α) = {y} ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `TopologicalSpace.Closeds.singleton_injective`：singleton_injective [T1Spa
ce α] : Function.Injective ({·} : α -> Closeds α)
-/
theorem singleton_inj [T1Space α] {x y : α} : ({x} : Closeds α) = {y} ↔ x = y :=
  singleton_injective.eq_iff

/-- The preimage of a closed set under a continuous map. -/
@[simps]
/-
**TopologicalSpace.Closeds.preimage** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.
Closeds`。
形式化陈述：preimage (s : Closeds β) {f : α -> β} (hf : Continuous f) : Closeds α
参数：s : Closeds β；hf : Continuous f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a closed set under a continuous map.
-/
def preimage (s : Closeds β) {f : α → β} (hf : Continuous f) : Closeds α :=
  ⟨f ⁻¹' s, s.isClosed.preimage hf⟩
/-
**TopologicalSpace.Closeds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Closeds`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SProd (Closeds α) (Closeds β) (Closeds (α × β)) where
  sprod s t := ⟨s ×ˢ t, s.isClosed.prod t.isClosed⟩

@[simp]
/-
**TopologicalSpace.Closeds.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Closeds`。
形式化陈述：coe_prod (s : Closeds α) (t : Closeds β) : (s ×ˢ t : Closeds (α × β)) = (s
 : Set α) ×ˢ (t : Set β)
参数：s : Closeds α；t : Closeds β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (s : Closeds α) (t : Closeds β) :
    (s ×ˢ t : Closeds (α × β)) = (s : Set α) ×ˢ (t : Set β) :=
  rfl

@[simp]
/-
**TopologicalSpace.Closeds.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Closeds`。
形式化陈述：mem_prod {s : Closeds α} {t : Closeds β} {x : α × β} : x in s ×ˢ t ↔ x.1 i
n s ∧ x.2 in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prod {s : Closeds α} {t : Closeds β} {x : α × β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.rfl

@[simp]
/-
**TopologicalSpace.Closeds.singleton_prod_singleton** 是 Mathlib 中的一个定理，位于命名空间 `T
opologicalSpace.Closeds`。
形式化陈述：singleton_prod_singleton [T1Space α] [T1Space β] (x : α) (y : β) : ({x} ×ˢ
 {y} : Closeds (α × β)) = {(x, y)}
参数：x : α；y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Closeds.ext`：∀ {α : Type u_2} [inst : TopologicalSpace 
α] {s t : TopologicalSpace.Closeds α}, ↑s = ↑t → s = t
· 使用定理 `instT1SpaceProd`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace Y] [T1Space X] [T1Space Y],   T1Space (X × Y)
· 使用定理 `Set.singleton_prod_singleton`：singleton_prod_singleton : ({a} : Set α) ×
ˢ ({b} : Set β) = {(a, b)}
-/
theorem singleton_prod_singleton [T1Space α] [T1Space β] (x : α) (y : β) :
    ({x} ×ˢ {y} : Closeds (α × β)) = {(x, y)} :=
  Closeds.ext Set.singleton_prod_singleton

end Closeds

/-- The complement of a closed set as an open set. -/
@[simps]
/-
**TopologicalSpace.Closeds.compl** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Clo
seds`。
形式化陈述：{α : Type u_2} → [inst : TopologicalSpace α] → TopologicalSpace.Closeds α 
→ TopologicalSpace.Opens α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complement of a closed set as an open set.
-/
def Closeds.compl (s : Closeds α) : Opens α :=
  ⟨sᶜ, s.2.isOpen_compl⟩

/-- The complement of an open set as a closed set. -/
@[simps]
/-
**TopologicalSpace.Opens.compl** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Opens
`。
形式化陈述：{α : Type u_2} → [inst : TopologicalSpace α] → TopologicalSpace.Opens α → 
TopologicalSpace.Closeds α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complement of an open set as a closed set.
-/
def Opens.compl (s : Opens α) : Closeds α :=
  ⟨sᶜ, s.2.isClosed_compl⟩

nonrec theorem Closeds.compl_compl (s : Closeds α) : s.compl.compl = s :=
  Closeds.ext (compl_compl (s : Set α))

nonrec theorem Opens.compl_compl (s : Opens α) : s.compl.compl = s :=
  Opens.ext (compl_compl (s : Set α))
/-
**TopologicalSpace.Closeds.compl_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.Closeds`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α], Function.Bijective Topologic
alSpace.Closeds.compl
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `TopologicalSpace.Closeds.compl_compl`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (s : TopologicalSpace.Closeds α), s.compl.compl = s
· 使用定理 `TopologicalSpace.Opens.compl_compl`：∀ {α : Type u_2} [inst : Topological
Space α] (s : TopologicalSpace.Opens α), s.compl.compl = s
-/
theorem Closeds.compl_bijective : Function.Bijective (@Closeds.compl α _) :=
  Function.bijective_iff_has_inverse.mpr ⟨Opens.compl, Closeds.compl_compl, Opens.compl_compl⟩
/-
**TopologicalSpace.Opens.compl_bijective** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.Opens`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α], Function.Bijective Topologic
alSpace.Opens.compl
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `TopologicalSpace.Opens.compl_compl`：∀ {α : Type u_2} [inst : Topological
Space α] (s : TopologicalSpace.Opens α), s.compl.compl = s
· 使用定理 `TopologicalSpace.Closeds.compl_compl`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (s : TopologicalSpace.Closeds α), s.compl.compl = s
-/
theorem Opens.compl_bijective : Function.Bijective (@Opens.compl α _) :=
  Function.bijective_iff_has_inverse.mpr ⟨Closeds.compl, Opens.compl_compl, Closeds.compl_compl⟩

variable (α)

/-- `TopologicalSpace.Closeds.compl` as an `OrderIso` to the order dual of
`TopologicalSpace.Opens α`. -/
@[simps]
/-
**TopologicalSpace.Closeds.complOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalS
pace.Closeds`。
形式化陈述：(α : Type u_2) → [inst : TopologicalSpace α] → TopologicalSpace.Closeds α 
≃o (TopologicalSpace.Opens α)ᵒᵈ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TopologicalSpace.Closeds.compl` as an `OrderIso` to the order dual of
`TopologicalSpace.Opens α`.
-/
def Closeds.complOrderIso : Closeds α ≃o (Opens α)ᵒᵈ where
  toFun := OrderDual.toDual ∘ Closeds.compl
  invFun := Opens.compl ∘ OrderDual.ofDual
  left_inv s := by simp [Closeds.compl_compl]
  right_inv s := by simp [Opens.compl_compl]
  map_rel_iff' := (@OrderDual.toDual_le_toDual (Opens α)).trans compl_subset_compl

/-- `TopologicalSpace.Opens.compl` as an `OrderIso` to the order dual of
`TopologicalSpace.Closeds α`. -/
@[simps]
/-
**TopologicalSpace.Opens.complOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpa
ce.Opens`。
形式化陈述：(α : Type u_2) → [inst : TopologicalSpace α] → TopologicalSpace.Opens α ≃o
 (TopologicalSpace.Closeds α)ᵒᵈ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TopologicalSpace.Opens.compl` as an `OrderIso` to the order dual of
`TopologicalSpace.Closeds α`.
-/
def Opens.complOrderIso : Opens α ≃o (Closeds α)ᵒᵈ where
  toFun := OrderDual.toDual ∘ Opens.compl
  invFun := Closeds.compl ∘ OrderDual.ofDual
  left_inv s := by simp [Opens.compl_compl]
  right_inv s := by simp [Closeds.compl_compl]
  map_rel_iff' := (@OrderDual.toDual_le_toDual (Closeds α)).trans compl_subset_compl

variable {α}
/-
**TopologicalSpace.Closeds.coe_eq_singleton_of_isAtom** 是 Mathlib 中的一个定理，位于命名空间 
`TopologicalSpace.Closeds`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] [T0Space α] {s : TopologicalS
pace.Closeds α}, IsAtom s → ∃ a, ↑s = {a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minimal_nonempty_closed_eq_singleton`：minimal_nonempty_closed_eq_singlet
on [T0Space X] {s : Set X} (hs : IsClosed s) (hne : s.Nonempty) (hmin : forall t
, t subseteq s -> t.Nonemp…
· 使用定理 `TopologicalSpace.Closeds.isClosed'`：∀ {α : Type u_4} [inst : Topological
Space α] (self : TopologicalSpace.Closeds α), IsClosed self.carrier
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.Closeds.coe_nonempty`：coe_nonempty {s : Closeds α} : (s
 : Set α).Nonempty ↔ s != ⊥
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `TopologicalSpace.Closeds.instCanLiftSetCoeIsClosed`：∀ {α : Type u_2} [in
st : TopologicalSpace α], CanLift (Set α) (TopologicalSpace.Closeds α) SetLike.c
oe IsClosed
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsAtom.le_iff_eq`：IsAtom.le_iff_eq (ha : IsAtom a) (hb : b != ⊥) : b <= 
a ↔ b = a
-/
lemma Closeds.coe_eq_singleton_of_isAtom [T0Space α] {s : Closeds α} (hs : IsAtom s) :
    ∃ a, (s : Set α) = {a} := by
  refine minimal_nonempty_closed_eq_singleton s.2 (coe_nonempty.2 hs.1) fun t hts ht ht' ↦ ?_
  lift t to Closeds α using ht'
  exact SetLike.coe_injective.eq_iff.2 <| (hs.le_iff_eq <| coe_nonempty.1 ht).1 hts
/-
**TopologicalSpace.Closeds.isAtom_coe** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpac
e.Closeds`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] [T1Space α] {s : TopologicalS
pace.Closeds α}, IsAtom ↑s ↔ IsAtom s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.isAtom_iff'`：isAtom_iff' [OrderBot α] [IsAtomic α] [Orde
rBot β] {l : α -> β} {u : β -> α} (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h
_atom : forall a,…
· 使用定理 `IsAtomistic.instIsAtomic`：∀ {α : Type u_2} [inst : PartialOrder α] [inst
_1 : OrderBot α] [IsAtomistic α], IsAtomic α
· 使用定理 `Set.instIsAtomistic`：∀ {α : Type u_2}, IsAtomistic (Set α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.isAtom_iff`：isAtom_iff {s : Set α} : IsAtom s ↔ exists x, s = {x}
· 使用定理 `closure_singleton`：closure_singleton [T1Space X] {x : X} : closure ({x} 
: Set X) = {x}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp, norm_cast] lemma Closeds.isAtom_coe [T1Space α] {s : Closeds α} :
    IsAtom (s : Set α) ↔ IsAtom s :=
  Closeds.gi.isAtom_iff' rfl
    (fun t ht ↦ by obtain ⟨x, rfl⟩ := Set.isAtom_iff.1 ht; exact closure_singleton) s

/-- in a `T1Space`, atoms of `TopologicalSpace.Closeds α` are precisely the singletons. -/
/-
**TopologicalSpace.Closeds.isAtom_iff** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpac
e.Closeds`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] [inst_1 : T1Space α] {s : Top
ologicalSpace.Closeds α},   IsAtom s ↔ ∃ x, s = {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
in a `T1Space`, atoms of `TopologicalSpace.Closeds α` are precisely the singleto
ns.
-/
theorem Closeds.isAtom_iff [T1Space α] {s : Closeds α} :
    IsAtom s ↔ ∃ x, s = {x} := by
  simp [← Closeds.isAtom_coe, Set.isAtom_iff, SetLike.ext_iff, Set.ext_iff]

/-- in a `T1Space`, coatoms of `TopologicalSpace.Opens α` are precisely complements of singletons:
`({x} : Closeds α).compl`. -/
/-
**TopologicalSpace.Opens.isCoatom_iff** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpac
e.Opens`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] [inst_1 : T1Space α] {s : Top
ologicalSpace.Opens α},   IsCoatom s ↔ ∃ x, s = {x}.compl
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.compl_compl`：∀ {α : Type u_2} [inst : Topological
Space α] (s : TopologicalSpace.Opens α), s.compl.compl = s
· 使用定理 `isAtom_dual_iff_isCoatom`：isAtom_dual_iff_isCoatom [OrderTop α] {a : α} 
: IsAtom (OrderDual.toDual a) ↔ IsCoatom a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OrderIso.isAtom_iff`：isAtom_iff [OrderBot α] [OrderBot β] (f : α ≃o β) (
a : α) : IsAtom (f a) ↔ IsAtom a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `TopologicalSpace.Closeds.compl_bijective`：∀ {α : Type u_2} [inst : Topol
ogicalSpace α], Function.Bijective TopologicalSpace.Closeds.compl
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
in a `T1Space`, coatoms of `TopologicalSpace.Opens α` are precisely complements 
of singletons:
`({x} : Closeds α).compl`.
-/
theorem Opens.isCoatom_iff [T1Space α] {s : Opens α} :
    IsCoatom s ↔ ∃ x, s = ({x} : Closeds α).compl := by
  rw [← s.compl_compl, ← isAtom_dual_iff_isCoatom]
  change IsAtom (Closeds.complOrderIso α s.compl) ↔ _
  simp only [(Closeds.complOrderIso α).isAtom_iff, Closeds.isAtom_iff,
    Closeds.compl_bijective.injective.eq_iff]

/-! ### Clopen sets -/


/-- The type of clopen sets of a topological space. -/
/-
**TopologicalSpace.Clopens** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopologicalSpace`。
形式化陈述：(α : Type u_4) → [TopologicalSpace α] → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of clopen sets of a topological space.
-/
structure Clopens (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isClopen' : IsClopen carrier

namespace Clopens

/-
**TopologicalSpace.Clopens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Clopens`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Clopens α) α where
  coe s := s.carrier
  coe_injective s t h := by cases s; cases t; congr
/-
**TopologicalSpace.Clopens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Clopens`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Clopens α) := fast_instance% .ofSetLike (Clopens α) α
/-
**TopologicalSpace.Clopens.isClopen** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Clopens`。
形式化陈述：isClopen (s : Clopens α) : IsClopen (s : Set α)
参数：s : Clopens α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Clopens.isClopen'`：∀ {α : Type u_4} [inst : Topological
Space α] (self : TopologicalSpace.Clopens α), IsClopen self.carrier
-/
theorem isClopen (s : Clopens α) : IsClopen (s : Set α) :=
  s.isClopen'
/-
**TopologicalSpace.Clopens.isOpen** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.Cl
opens`。
形式化陈述：isOpen (s : Clopens α) : IsOpen (s : Set α)
参数：s : Clopens α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `TopologicalSpace.Clopens.isClopen`：isClopen (s : Clopens α) : IsClopen (
s : Set α)
-/
lemma isOpen (s : Clopens α) : IsOpen (s : Set α) := s.isClopen.isOpen
/-
**TopologicalSpace.Clopens.isClosed** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.
Clopens`。
形式化陈述：isClosed (s : Clopens α) : IsClosed (s : Set α)
参数：s : Clopens α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClopen.isClosed`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X
}, IsClopen s → IsClosed s
· 使用定理 `TopologicalSpace.Clopens.isClopen`：isClopen (s : Clopens α) : IsClopen (
s : Set α)
-/
lemma isClosed (s : Clopens α) : IsClosed (s : Set α) := s.isClopen.isClosed

/-- See Note [custom simps projection]. -/
/-
**TopologicalSpace.Clopens.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace
.Clopens.Simps`。
形式化陈述：{α : Type u_2} → [inst : TopologicalSpace α] → TopologicalSpace.Clopens α 
→ Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.coe (s : Clopens α) : Set α := s

initialize_simps_projections Clopens (carrier → coe, as_prefix coe)

/-- Reinterpret a clopen as an open. -/
/-
**TopologicalSpace.Clopens.toOpens** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.C
lopens`。
形式化陈述：{α : Type u_2} → [inst : TopologicalSpace α] → TopologicalSpace.Clopens α 
→ TopologicalSpace.Opens α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `TopologicalSpace.Clopens.isOpen`：isOpen (s : Clopens α) : IsOpen (s : Se
t α)

--- 原说明 ---
Reinterpret a clopen as an open.
-/
@[simps] def toOpens (s : Clopens α) : Opens α := ⟨s, s.isOpen⟩

/-- Reinterpret a clopen as a closed. -/
/-
**TopologicalSpace.Clopens.toCloseds** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace
.Clopens`。
形式化陈述：{α : Type u_2} → [inst : TopologicalSpace α] → TopologicalSpace.Clopens α 
→ TopologicalSpace.Closeds α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `TopologicalSpace.Clopens.isClosed`：isClosed (s : Clopens α) : IsClosed (
s : Set α)

--- 原说明 ---
Reinterpret a clopen as a closed.
-/
@[simps] def toCloseds (s : Clopens α) : Closeds α := ⟨s, s.isClosed⟩

@[ext]
/-
**TopologicalSpace.Clopens.ext** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Clope
ns`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {s t : TopologicalSpace.Clope
ns α}, ↑s = ↑t → s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q

--- 原说明 ---
Reinterpret a clopen as a closed.
-/
protected theorem ext {s t : Clopens α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/-
**TopologicalSpace.Clopens.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Cl
opens`。
形式化陈述：coe_mk (s : Set α) (h) : (mk s h : Set α) = s
参数：s : Set α；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl
/-
**TopologicalSpace.Clopens.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Cl
opens`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {s : Set α} {x : α} {h : IsCl
open s},   x ∈ { carrier := s, isClopen' := h } ↔ x ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_mk {s : Set α} {x h} : x ∈ mk s h ↔ x ∈ s := .rfl
/-
**TopologicalSpace.Clopens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Clopens`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (Clopens α) := ⟨fun s t => ⟨s ∪ t, s.isClopen.union t.isClopen⟩⟩
/-
**TopologicalSpace.Clopens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Clopens`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (Clopens α) := ⟨fun s t => ⟨s ∩ t, s.isClopen.inter t.isClopen⟩⟩
/-
**TopologicalSpace.Clopens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Clopens`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (Clopens α) := ⟨⟨⊤, isClopen_univ⟩⟩
/-
**TopologicalSpace.Clopens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Clopens`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (Clopens α) := ⟨⟨⊥, isClopen_empty⟩⟩
/-
**TopologicalSpace.Clopens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Clopens`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SDiff (Clopens α) := ⟨fun s t => ⟨s \ t, s.isClopen.diff t.isClopen⟩⟩
/-
**TopologicalSpace.Clopens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Clopens`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HImp (Clopens α) where himp s t := ⟨s ⇨ t, s.isClopen.himp t.isClopen⟩
/-
**TopologicalSpace.Clopens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Clopens`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Compl (Clopens α) := ⟨fun s => ⟨sᶜ, s.isClopen.compl⟩⟩
/-
**TopologicalSpace.Clopens.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.C
lopens`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] (s t : TopologicalSpace.Clope
ns α), ↑(s ⊔ t) = ↑s ∪ ↑t
参数：s t : TopologicalSpace.Clopens α；s ⊔ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_sup (s t : Clopens α) : ↑(s ⊔ t) = (s ∪ t : Set α) := rfl
/-
**TopologicalSpace.Clopens.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.C
lopens`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] (s t : TopologicalSpace.Clope
ns α), ↑(s ⊓ t) = ↑s ∩ ↑t
参数：s t : TopologicalSpace.Clopens α；s ⊓ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inf (s t : Clopens α) : ↑(s ⊓ t) = (s ∩ t : Set α) := rfl
/-
**TopologicalSpace.Clopens.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.C
lopens`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α], ↑⊤ = Set.univ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_top : (↑(⊤ : Clopens α) : Set α) = univ := rfl
/-
**TopologicalSpace.Clopens.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.C
lopens`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α], ↑⊥ = ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_bot : (↑(⊥ : Clopens α) : Set α) = ∅ := rfl
/-
**TopologicalSpace.Clopens.coe_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace
.Clopens`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] (s t : TopologicalSpace.Clope
ns α), ↑(s \ t) = ↑s \ ↑t
参数：s t : TopologicalSpace.Clopens α；s \ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_sdiff (s t : Clopens α) : ↑(s \ t) = (s \ t : Set α) := rfl
/-
**TopologicalSpace.Clopens.coe_himp** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Clopens`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] (s t : TopologicalSpace.Clope
ns α), ↑(s ⇨ t) = ↑s ⇨ ↑t
参数：s t : TopologicalSpace.Clopens α；s ⇨ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_himp (s t : Clopens α) : ↑(s ⇨ t) = (s ⇨ t : Set α) := rfl
/-
**TopologicalSpace.Clopens.coe_compl** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace
.Clopens`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] (s : TopologicalSpace.Clopens
 α), ↑sᶜ = (↑s)ᶜ
参数：s : TopologicalSpace.Clopens α；↑s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_compl (s : Clopens α) : (↑sᶜ : Set α) = (↑s)ᶜ := rfl
/-
**TopologicalSpace.Clopens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Clopens`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BooleanAlgebra (Clopens α) := fast_instance%
  SetLike.coe_injective.booleanAlgebra _ .rfl .rfl coe_sup coe_inf coe_top coe_bot coe_compl
    coe_sdiff coe_himp
/-
**TopologicalSpace.Clopens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Clopens`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Clopens α) := ⟨⊥⟩
/-
**TopologicalSpace.Clopens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Clopens`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SProd (Clopens α) (Clopens β) (Clopens (α × β)) where
  sprod s t := ⟨s ×ˢ t, s.2.prod t.2⟩

@[simp]
/-
**TopologicalSpace.Clopens.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Clopens`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β]   {s : TopologicalSpace.Clopens α} {t : TopologicalSpace.Clopens
 β} {x : α × β}, x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma mem_prod {s : Clopens α} {t : Clopens β} {x : α × β} :
    x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t := .rfl

@[simp]
/-
**TopologicalSpace.Clopens.coe_finset_sup** 是 Mathlib 中的一个引理，位于命名空间 `Topological
Space.Clopens`。
形式化陈述：coe_finset_sup (s : Finset ι) (U : ι -> Clopens α) : (↑(s.sup U) : Set α) 
= ⋃ i in s, U i
参数：s : Finset ι；U : ι -> Clopens α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
-/
lemma coe_finset_sup (s : Finset ι) (U : ι → Clopens α) :
    (↑(s.sup U) : Set α) = ⋃ i ∈ s, U i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ _ IH => simp [IH]

@[simp, norm_cast]
/-
**TopologicalSpace.Clopens.coe_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSp
ace.Clopens`。
形式化陈述：coe_disjoint {s t : Clopens α} : Disjoint (s : Set α) t ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_disjoint {s t : Clopens α} : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, ← SetLike.coe_set_eq]

end Clopens

/-! ### Irreducible closed sets -/

/-- The type of irreducible closed subsets of a topological space. -/
/-
**TopologicalSpace.IrreducibleCloseds** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopologicalSp
ace`。
形式化陈述：(α : Type u_4) → [TopologicalSpace α] → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of irreducible closed subsets of a topological space.
-/
structure IrreducibleCloseds (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isIrreducible' : IsIrreducible carrier
  isClosed' : IsClosed carrier

namespace IrreducibleCloseds

/-
**TopologicalSpace.IrreducibleCloseds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpa
ce.IrreducibleCloseds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (IrreducibleCloseds α) α where
  coe := IrreducibleCloseds.carrier
  coe_injective s t h := by cases s; cases t; congr
/-
**TopologicalSpace.IrreducibleCloseds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpa
ce.IrreducibleCloseds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (IrreducibleCloseds α) := fast_instance% .ofSetLike (IrreducibleCloseds α) α
/-
**TopologicalSpace.IrreducibleCloseds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpa
ce.IrreducibleCloseds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift (Set α) (IrreducibleCloseds α) (↑) (fun s ↦ IsIrreducible s ∧ IsClosed s) where
  prf s hs := ⟨⟨s, hs.1, hs.2⟩, rfl⟩
/-
**TopologicalSpace.IrreducibleCloseds.isIrreducible** 是 Mathlib 中的一个定理，位于命名空间 `T
opologicalSpace.IrreducibleCloseds`。
形式化陈述：isIrreducible (s : IrreducibleCloseds α) : IsIrreducible (s : Set α)
参数：s : IrreducibleCloseds α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IrreducibleCloseds.isIrreducible'`：∀ {α : Type u_4} [in
st : TopologicalSpace α] (self : TopologicalSpace.IrreducibleCloseds α), IsIrred
ucible self.carrier
-/
theorem isIrreducible (s : IrreducibleCloseds α) : IsIrreducible (s : Set α) := s.isIrreducible'
/-
**TopologicalSpace.IrreducibleCloseds.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gicalSpace.IrreducibleCloseds`。
形式化陈述：isClosed (s : IrreducibleCloseds α) : IsClosed (s : Set α)
参数：s : IrreducibleCloseds α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IrreducibleCloseds.isClosed'`：∀ {α : Type u_4} [inst : 
TopologicalSpace α] (self : TopologicalSpace.IrreducibleCloseds α), IsClosed sel
f.carrier
-/
theorem isClosed (s : IrreducibleCloseds α) : IsClosed (s : Set α) := s.isClosed'

/-- See Note [custom simps projection]. -/
/-
**TopologicalSpace.IrreducibleCloseds.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `Topol
ogicalSpace.IrreducibleCloseds.Simps`。
形式化陈述：{α : Type u_2} → [inst : TopologicalSpace α] → TopologicalSpace.Irreducibl
eCloseds α → Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.coe (s : IrreducibleCloseds α) : Set α := s

initialize_simps_projections IrreducibleCloseds (carrier → coe, as_prefix coe)

@[ext]
/-
**TopologicalSpace.IrreducibleCloseds.ext** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.IrreducibleCloseds`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {s t : TopologicalSpace.Irred
ucibleCloseds α}, ↑s = ↑t → s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
-/
protected theorem ext {s t : IrreducibleCloseds α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/-
**TopologicalSpace.IrreducibleCloseds.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace.IrreducibleCloseds`。
形式化陈述：coe_mk (s : Set α) (h : IsIrreducible s) (h' : IsClosed s) : (mk s h h' : 
Set α) = s
参数：s : Set α；h : IsIrreducible s；h' : IsClosed s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (s : Set α) (h : IsIrreducible s) (h' : IsClosed s) : (mk s h h' : Set α) = s :=
  rfl

@[simps]
/-
**TopologicalSpace.IrreducibleCloseds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpa
ce.IrreducibleCloseds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T1Space α] : Singleton α (IrreducibleCloseds α) where
  singleton x := ⟨{x}, isIrreducible_singleton, isClosed_singleton⟩

@[simp]
/-
**TopologicalSpace.IrreducibleCloseds.mk_singleton** 是 Mathlib 中的一个定理，位于命名空间 `To
pologicalSpace.IrreducibleCloseds`。
形式化陈述：mk_singleton [T1Space α] {x : α} : (⟨{x}, isIrreducible_singleton, isClose
d_singleton⟩ : IrreducibleCloseds α) = {x}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isIrreducible_singleton`：isIrreducible_singleton {x} : IsIrreducible ({x
} : Set X)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
-/
theorem mk_singleton [T1Space α] {x : α} :
    (⟨{x}, isIrreducible_singleton, isClosed_singleton⟩ : IrreducibleCloseds α) = {x} :=
  rfl
/-
**TopologicalSpace.IrreducibleCloseds.mem_singleton** 是 Mathlib 中的一个定理，位于命名空间 `T
opologicalSpace.IrreducibleCloseds`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] [inst_1 : T1Space α] {a b : α
}, a ∈ {b} ↔ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_singleton [T1Space α] {a b : α} : a ∈ ({b} : IrreducibleCloseds α) ↔ a = b :=
  Iff.rfl
/-
**TopologicalSpace.IrreducibleCloseds.singleton_injective** 是 Mathlib 中的一个定理，位于命
名空间 `TopologicalSpace.IrreducibleCloseds`。
形式化陈述：singleton_injective [T1Space α] : Function.Injective ({·} : α -> Irreducib
leCloseds α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Set.singleton_injective`：singleton_injective : Injective (singleton : α 
-> Set α)
-/
theorem singleton_injective [T1Space α] : Function.Injective ({·} : α → IrreducibleCloseds α) :=
  .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]
/-
**TopologicalSpace.IrreducibleCloseds.singleton_inj** 是 Mathlib 中的一个定理，位于命名空间 `T
opologicalSpace.IrreducibleCloseds`。
形式化陈述：singleton_inj [T1Space α] {x y : α} : ({x} : IrreducibleCloseds α) = {y} ↔
 x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `TopologicalSpace.IrreducibleCloseds.singleton_injective`：singleton_injec
tive [T1Space α] : Function.Injective ({·} : α -> IrreducibleCloseds α)
-/
theorem singleton_inj [T1Space α] {x y : α} : ({x} : IrreducibleCloseds α) = {y} ↔ x = y :=
  singleton_injective.eq_iff

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
The equivalence between `IrreducibleCloseds α` and `{x : Set α // IsIrreducible x ∧ IsClosed x }`.
-/
@[simps apply symm_apply]
/-
**TopologicalSpace.IrreducibleCloseds.equivSubtype** 是 Mathlib 中的一个定义，位于命名空间 `To
pologicalSpace.IrreducibleCloseds`。
形式化陈述：equivSubtype : IrreducibleCloseds α ≃ { x : Set α // IsIrreducible x ∧ IsC
losed x } where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `IrreducibleCloseds α` and `{x : Set α // IsIrreducible 
x ∧ IsClosed x }`.
-/
def equivSubtype : IrreducibleCloseds α ≃ { x : Set α // IsIrreducible x ∧ IsClosed x } where
  toFun a  := ⟨a.1, a.2, a.3⟩
  invFun a := ⟨a.1, a.2.1, a.2.2⟩

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
The equivalence between `IrreducibleCloseds α` and `{x : Set α // IsClosed x ∧ IsIrreducible x }`.
-/
@[simps apply symm_apply]
/-
**TopologicalSpace.IrreducibleCloseds.equivSubtype'** 是 Mathlib 中的一个定义，位于命名空间 `T
opologicalSpace.IrreducibleCloseds`。
形式化陈述：equivSubtype' : IrreducibleCloseds α ≃ { x : Set α // IsClosed x ∧ IsIrred
ucible x } where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `IrreducibleCloseds α` and `{x : Set α // IsClosed x ∧ I
sIrreducible x }`.
-/
def equivSubtype' : IrreducibleCloseds α ≃ { x : Set α // IsClosed x ∧ IsIrreducible x } where
  toFun a  := ⟨a.1, a.3, a.2⟩
  invFun a := ⟨a.1, a.2.2, a.2.1⟩

variable (α) in
/-- The equivalence `IrreducibleCloseds α ≃ { x : Set α // IsIrreducible x ∧ IsClosed x }` is an
order isomorphism. -/
/-
**TopologicalSpace.IrreducibleCloseds.orderIsoSubtype** 是 Mathlib 中的一个定义，位于命名空间 
`TopologicalSpace.IrreducibleCloseds`。
形式化陈述：orderIsoSubtype : IrreducibleCloseds α ≃o { x : Set α // IsIrreducible x ∧
 IsClosed x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `IrreducibleCloseds α ≃ { x : Set α // IsIrreducible x ∧ IsClose
d x }` is an
order isomorphism.
-/
def orderIsoSubtype : IrreducibleCloseds α ≃o { x : Set α // IsIrreducible x ∧ IsClosed x } :=
  equivSubtype.toOrderIso (fun _ _ h ↦ h) (fun _ _ h ↦ h)

variable (α) in
/-- The equivalence `IrreducibleCloseds α ≃ { x : Set α // IsClosed x ∧ IsIrreducible x }` is an
order isomorphism. -/
/-
**TopologicalSpace.IrreducibleCloseds.orderIsoSubtype'** 是 Mathlib 中的一个定义，位于命名空间
 `TopologicalSpace.IrreducibleCloseds`。
形式化陈述：orderIsoSubtype' : IrreducibleCloseds α ≃o { x : Set α // IsClosed x ∧ IsI
rreducible x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `IrreducibleCloseds α ≃ { x : Set α // IsClosed x ∧ IsIrreducibl
e x }` is an
order isomorphism.
-/
def orderIsoSubtype' : IrreducibleCloseds α ≃o { x : Set α // IsClosed x ∧ IsIrreducible x } :=
  equivSubtype'.toOrderIso (fun _ _ h ↦ h) (fun _ _ h ↦ h)

/-! ### Partial order structure on irreducible closed sets and maps thereof.-/

/-- The map on irreducible closed sets induced by a continuous map `f`. -/
/-
**TopologicalSpace.IrreducibleCloseds.map** 是 Mathlib 中的一个定义，位于命名空间 `Topological
Space.IrreducibleCloseds`。
形式化陈述：map (f : β -> α) (hf : Continuous f) (c : IrreducibleCloseds β) : Irreduci
bleCloseds α where carrier
参数：f : β -> α；hf : Continuous f；c : IrreducibleCloseds β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map on irreducible closed sets induced by a continuous map `f`.
-/
def map (f : β → α) (hf : Continuous f)
    (c : IrreducibleCloseds β) : IrreducibleCloseds α where
  carrier := closure (f '' c)
  isIrreducible' := c.isIrreducible.image f hf.continuousOn |>.closure
  isClosed' := isClosed_closure

@[simp]
/-
**TopologicalSpace.IrreducibleCloseds.coe_map** 是 Mathlib 中的一个引理，位于命名空间 `Topolog
icalSpace.IrreducibleCloseds`。
形式化陈述：coe_map (f : β -> α) (hf : Continuous f) (s : IrreducibleCloseds β) : (map
 f hf s : Set α) = closure (f '' s)
参数：f : β -> α；hf : Continuous f；s : IrreducibleCloseds β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_map (f : β → α) (hf : Continuous f) (s : IrreducibleCloseds β) :
    (map f hf s : Set α) = closure (f '' s) :=
  rfl
/-
**TopologicalSpace.IrreducibleCloseds.map_mono** 是 Mathlib 中的一个引理，位于命名空间 `Topolo
gicalSpace.IrreducibleCloseds`。
形式化陈述：map_mono {f : β -> α} (hf : Continuous f) : Monotone (map f hf)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
lemma map_mono {f : β → α} (hf : Continuous f) : Monotone (map f hf) :=
  fun _ _ h_le => closure_mono <| Set.image_mono h_le

/-- The map `IrreducibleCloseds.map` is injective when `f` is inducing.
This relies on the property of embeddings that a closed set in the domain is the preimage
of the closure of its image. -/
/-
**TopologicalSpace.IrreducibleCloseds.map_injective_of_isInducing** 是 Mathlib 中的
一个引理，位于命名空间 `TopologicalSpace.IrreducibleCloseds`。
形式化陈述：map_injective_of_isInducing {f : β -> α} (hf : IsInducing f) : Function.In
jective (map f hf.continuous)
参数：hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `TopologicalSpace.IrreducibleCloseds.isClosed`：isClosed (s : IrreducibleC
loseds α) : IsClosed (s : Set α)
· 使用引理 `Topology.IsInducing.closure_eq_preimage_closure_image`：closure_eq_preima
ge_closure_image (hf : IsInducing f) (s : Set X) : closure s = f ⁻¹' closure (f 
'' s)

--- 原说明 ---
The map `IrreducibleCloseds.map` is injective when `f` is inducing.
This relies on the property of embeddings that a closed set in the domain is the
 preimage
of the closure of its image.
-/
lemma map_injective_of_isInducing {f : β → α} (hf : IsInducing f) :
    Function.Injective (map f hf.continuous) := by
  intro A B h_images_eq
  apply SetLike.coe_injective
  replace h_images_eq : closure (f '' A) = closure (f '' B) := congr($h_images_eq)
  rw [← A.isClosed.closure_eq, hf.closure_eq_preimage_closure_image, h_images_eq,
    ← hf.closure_eq_preimage_closure_image, B.isClosed.closure_eq]

/-- The map `IrreducibleCloseds.map` is strictly monotone when `f` is inducing. -/
/-
**TopologicalSpace.IrreducibleCloseds.map_strictMono_of_isInducing** 是 Mathlib 中
的一个引理，位于命名空间 `TopologicalSpace.IrreducibleCloseds`。
形式化陈述：map_strictMono_of_isInducing {f : β -> α} (hf : IsInducing f) : StrictMono
 (map f hf.continuous)
参数：hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用引理 `TopologicalSpace.IrreducibleCloseds.map_mono`：map_mono {f : β -> α} (hf 
: Continuous f) : Monotone (map f hf)
· 使用引理 `TopologicalSpace.IrreducibleCloseds.map_injective_of_isInducing`：map_inj
ective_of_isInducing {f : β -> α} (hf : IsInducing f) : Function.Injective (map 
f hf.continuous)

--- 原说明 ---
The map `IrreducibleCloseds.map` is strictly monotone when `f` is inducing.
-/
lemma map_strictMono_of_isInducing {f : β → α} (hf : IsInducing f) :
    StrictMono (map f hf.continuous) :=
  Monotone.strictMono_of_injective (map_mono hf.continuous) (map_injective_of_isInducing hf)

set_option backward.isDefEq.respectTransparency false in
/--
Given `f : U → X` a continuous open embedding, the irreducible closeds of `U` are order isomorphic
to the irreducible closeds of `X` nontrivially intersecting the range of `f`.
-/
noncomputable
/-
**TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding** 是 Mathlib 中的一个
定义，位于命名空间 `TopologicalSpace.IrreducibleCloseds`。
形式化陈述：orderIsoOfIsOpenEmbedding (f : β -> α) (h : IsOpenEmbedding f) : Irreducib
leCloseds β ≃o {V : IrreducibleCloseds α | (f ⁻¹' V).Nonempty} where toFun T
参数：f : β -> α；h : IsOpenEmbedding f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
-/
def orderIsoOfIsOpenEmbedding (f : β → α) (h : IsOpenEmbedding f) :
    IrreducibleCloseds β ≃o {V : IrreducibleCloseds α | (f ⁻¹' V).Nonempty} where
  toFun T := ⟨map f h.continuous T, nonempty_preimage_closure_image h.continuous T T.2.nonempty⟩
  invFun V :=
    { carrier := f ⁻¹' V
      isIrreducible' := ⟨V.2, V.1.2.isPreirreducible.preimage h⟩
      isClosed' := V.1.3.preimage h.continuous }
  left_inv V := by
    ext
    simp [h.isOpenMap.preimage_closure_image h.injective h.continuous _ V.isClosed]
  right_inv V := by
    ext
    simp [closure_image_preimage_of_isPreirreducible f h.isOpenMap V V.2 V.1.2.2 V.1.3]
  map_rel_iff' {a b} := by
    refine ⟨fun hle ↦ ?_, fun hle ↦ map_mono h.continuous hle⟩
    simpa [← h.isEmbedding.closure_eq_preimage_closure_image, a.isClosed.closure_eq,
      b.isClosed.closure_eq] using Set.preimage_mono (f := f) hle

end IrreducibleCloseds

end TopologicalSpace

