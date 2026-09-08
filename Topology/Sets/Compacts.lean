/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.QuasiSeparated

/-!
# Compact sets

We define a few types of compact sets in a topological space.

## Main Definitions

For a topological space `α`,
* `TopologicalSpace.Compacts α`: The type of compact sets.
* `TopologicalSpace.NonemptyCompacts α`: The type of non-empty compact sets.
* `TopologicalSpace.PositiveCompacts α`: The type of compact sets with non-empty interior.
* `TopologicalSpace.CompactOpens α`: The type of compact open sets. This is a central object in the
  study of spectral spaces.
-/

@[expose] public section


open Set

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace TopologicalSpace

/-! ### Compact sets -/

/-- The type of compact sets of a topological space. -/
/-
**TopologicalSpace.Compacts** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopologicalSpace`。
形式化陈述：(α : Type u_4) → [TopologicalSpace α] → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of compact sets of a topological space.
-/
structure Compacts (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isCompact' : IsCompact carrier

namespace Compacts

/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Compacts α) α where
  coe := Compacts.carrier
  coe_injective s t h := by cases s; cases t; congr
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Compacts α) := .ofSetLike (Compacts α) α

/-- See Note [custom simps projection]. -/
/-
**TopologicalSpace.Compacts.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpac
e.Compacts.Simps`。
形式化陈述：{α : Type u_1} → [inst : TopologicalSpace α] → TopologicalSpace.Compacts α
 → Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.coe (s : Compacts α) : Set α := s

initialize_simps_projections Compacts (carrier → coe, as_prefix coe)
/-
**TopologicalSpace.Compacts.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpac
e.Compacts`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] (s : TopologicalSpace.Compact
s α), IsCompact ↑s
参数：s : TopologicalSpace.Compacts α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
-/
protected theorem isCompact (s : Compacts α) : IsCompact (s : Set α) :=
  s.isCompact'
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : Compacts α) : CompactSpace K :=
  isCompact_iff_compactSpace.1 K.isCompact

/-- Reinterpret a compact as a closed set. -/
@[simps]
/-
**TopologicalSpace.Compacts.toCloseds** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpac
e.Compacts`。
形式化陈述：toCloseds [T2Space α] (s : Compacts α) : Closeds α
参数：s : Compacts α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a compact as a closed set.
-/
def toCloseds [T2Space α] (s : Compacts α) : Closeds α :=
  ⟨s, s.isCompact.isClosed⟩

@[simp]
/-
**TopologicalSpace.Compacts.mem_toCloseds** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.Compacts`。
形式化陈述：mem_toCloseds [T2Space α] {x : α} {s : Compacts α} : x in s.toCloseds ↔ x 
in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toCloseds [T2Space α] {x : α} {s : Compacts α} :
    x ∈ s.toCloseds ↔ x ∈ s :=
  Iff.rfl
/-
**TopologicalSpace.Compacts.toCloseds_injective** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogicalSpace.Compacts`。
形式化陈述：toCloseds_injective [T2Space α] : Function.Injective (toCloseds (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem toCloseds_injective [T2Space α] : Function.Injective (toCloseds (α := α)) :=
  .of_comp (f := SetLike.coe) SetLike.coe_injective
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift (Set α) (Compacts α) (↑) IsCompact where prf K hK := ⟨⟨K, hK⟩, rfl⟩

@[ext]
/-
**TopologicalSpace.Compacts.ext** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Comp
acts`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {s t : TopologicalSpace.Compa
cts α}, ↑s = ↑t → s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
-/
protected theorem ext {s t : Compacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/-
**TopologicalSpace.Compacts.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.C
ompacts`。
形式化陈述：coe_mk (s : Set α) (h) : (mk s h : Set α) = s
参数：s : Set α；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl

@[simp]
/-
**TopologicalSpace.Compacts.carrier_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.Compacts`。
形式化陈述：carrier_eq_coe (s : Compacts α) : s.carrier = s
参数：s : Compacts α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem carrier_eq_coe (s : Compacts α) : s.carrier = s :=
  rfl
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (Compacts α) :=
  ⟨fun s t => ⟨s ∪ t, s.isCompact.union t.isCompact⟩⟩
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space α] : Min (Compacts α) :=
  ⟨fun s t => ⟨s ∩ t, s.isCompact.inter t.isCompact⟩⟩
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace α] : Top (Compacts α) :=
  ⟨⟨univ, isCompact_univ⟩⟩
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (Compacts α) :=
  ⟨⟨∅, isCompact_empty⟩⟩
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (Compacts α) :=
  fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ ↦ rfl
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space α] : DistribLattice (Compacts α) :=
  fast_instance% SetLike.coe_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (Compacts α) :=
  fast_instance% OrderBot.lift ((↑) : _ → Set α) (fun _ _ => id) rfl
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace α] : BoundedOrder (Compacts α) :=
  fast_instance% BoundedOrder.lift ((↑) : _ → Set α) (fun _ _ => id) rfl rfl

/-- The type of compact sets is inhabited, with default element the empty set. -/
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of compact sets is inhabited, with default element the empty set.
-/
instance : Inhabited (Compacts α) := ⟨⊥⟩
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : Unique (Compacts α) where
  uniq _ := Compacts.ext (Subsingleton.elim _ _)

@[simp]
/-
**TopologicalSpace.Compacts.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Compacts`。
形式化陈述：coe_sup (s t : Compacts α) : (↑(s ⊔ t) : Set α) = ↑s union ↑t
参数：s t : Compacts α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (s t : Compacts α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t :=
  rfl

@[simp]
/-
**TopologicalSpace.Compacts.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Compacts`。
形式化陈述：coe_inf [T2Space α] (s t : Compacts α) : (↑(s ⊓ t) : Set α) = ↑s inter ↑t
参数：s t : Compacts α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf [T2Space α] (s t : Compacts α) : (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t :=
  rfl

@[simp]
/-
**TopologicalSpace.Compacts.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Compacts`。
形式化陈述：coe_top [CompactSpace α] : (↑(⊤ : Compacts α) : Set α) = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top [CompactSpace α] : (↑(⊤ : Compacts α) : Set α) = univ :=
  rfl

@[simp]
/-
**TopologicalSpace.Compacts.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Compacts`。
形式化陈述：coe_bot : (↑(⊥ : Compacts α) : Set α) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : (↑(⊥ : Compacts α) : Set α) = ∅ :=
  rfl

@[simp, norm_cast]
/-
**TopologicalSpace.Compacts.coe_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.Compacts`。
形式化陈述：coe_eq_empty {s : Compacts α} : (s : Set α) = ∅ ↔ s = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem coe_eq_empty {s : Compacts α} : (s : Set α) = ∅ ↔ s = ⊥ :=
  SetLike.coe_injective.eq_iff' rfl

@[simp]
/-
**TopologicalSpace.Compacts.coe_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.Compacts`。
形式化陈述：coe_nonempty {s : Compacts α} : (s : Set α).Nonempty ↔ s != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `TopologicalSpace.Compacts.coe_eq_empty`：coe_eq_empty {s : Compacts α} : 
(s : Set α) = ∅ ↔ s = ⊥
-/
theorem coe_nonempty {s : Compacts α} : (s : Set α).Nonempty ↔ s ≠ ⊥ :=
  nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp]
/-
**TopologicalSpace.Compacts.coe_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.Compacts`。
形式化陈述：coe_finset_sup {ι : Type*} {s : Finset ι} {f : ι -> Compacts α} : (↑(s.sup
 f) : Set α) = s.sup fun i => ↑(f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
-/
theorem coe_finset_sup {ι : Type*} {s : Finset ι} {f : ι → Compacts α} :
    (↑(s.sup f) : Set α) = s.sup fun i => ↑(f i) := by
  refine Finset.cons_induction_on s rfl fun a s _ h => ?_
  simp_rw [Finset.sup_cons, coe_sup, sup_eq_union]
  congr

@[simps]
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Singleton α (Compacts α) where
  singleton x := ⟨{x}, isCompact_singleton⟩

@[simp]
/-
**TopologicalSpace.Compacts.mem_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.Compacts`。
形式化陈述：mem_singleton (x y : α) : x in ({y} : Compacts α) ↔ x = y
参数：x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_singleton (x y : α) : x ∈ ({y} : Compacts α) ↔ x = y :=
  Iff.rfl

@[simp]
/-
**TopologicalSpace.Compacts.toCloseds_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogicalSpace.Compacts`。
形式化陈述：toCloseds_singleton [T2Space α] (x : α) : toCloseds {x} = {x}
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCloseds_singleton [T2Space α] (x : α) : toCloseds {x} = {x} :=
  rfl
/-
**TopologicalSpace.Compacts.singleton_injective** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogicalSpace.Compacts`。
形式化陈述：singleton_injective : Function.Injective ({·} : α -> Compacts α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Set.singleton_injective`：singleton_injective : Injective (singleton : α 
-> Set α)
-/
theorem singleton_injective : Function.Injective ({·} : α → Compacts α) :=
  .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]
/-
**TopologicalSpace.Compacts.singleton_inj** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.Compacts`。
形式化陈述：singleton_inj {x y : α} : ({x} : Compacts α) = {y} ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `TopologicalSpace.Compacts.singleton_injective`：singleton_injective : Fun
ction.Injective ({·} : α -> Compacts α)
-/
theorem singleton_inj {x y : α} : ({x} : Compacts α) = {y} ↔ x = y :=
  singleton_injective.eq_iff
/-
**TopologicalSpace.Compacts.disjoint_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace.Compacts`。
形式化陈述：disjoint_coe_iff (K L : Compacts α) : Disjoint (K : Set α) L ↔ Disjoint K 
L where mp h
参数：K L : Compacts α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Disjoint.of_orderEmbedding`：Disjoint.of_orderEmbedding [OrderBot α] [Ord
erBot β] {a₁ a₂ : α} : Disjoint (f a₁) (f a₂) -> Disjoint a₁ a₂
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem disjoint_coe_iff (K L : Compacts α) : Disjoint (K : Set α) L ↔ Disjoint K L where
  mp h := .of_orderEmbedding (.ofMapLEIff SetLike.coe (fun _ _ => SetLike.coe_subset_coe)) h
  mpr h := by
    rw [Set.disjoint_iff]
    intro x ⟨hxK, hxL⟩
    specialize @h {x}
    simp_rw [← SetLike.coe_subset_coe, coe_singleton, singleton_subset_iff] at h
    exact h hxK hxL
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nontrivial (Compacts α) := by
  constructor
  obtain ⟨x⟩ := ‹Nonempty α›
  exact ⟨⊥, {x}, ne_of_apply_ne SetLike.coe (Set.empty_ne_singleton x)⟩

@[simp]
/-
**TopologicalSpace.Compacts.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace.Compacts`。
形式化陈述：subsingleton_iff : Subsingleton (Compacts α) ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `TopologicalSpace.Compacts.instNontrivialOfNonempty`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [Nonempty α], Nontrivial (TopologicalSpace.Compacts α)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem subsingleton_iff : Subsingleton (Compacts α) ↔ IsEmpty α := by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  contrapose! h
  infer_instance

@[simp]
/-
**TopologicalSpace.Compacts.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.Compacts`。
形式化陈述：nontrivial_iff : Nontrivial (Compacts α) ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用定理 `TopologicalSpace.Compacts.subsingleton_iff`：subsingleton_iff : Subsingle
ton (Compacts α) ↔ IsEmpty α
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nontrivial_iff : Nontrivial (Compacts α) ↔ Nonempty α := by
  rw [← not_subsingleton_iff_nontrivial, subsingleton_iff, not_isEmpty_iff]

/-- The image of a compact set under a continuous function. -/
/-
**TopologicalSpace.Compacts.map** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Comp
acts`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : TopologicalSpace α] →     
  [inst_1 : TopologicalSpace β] →         (f : α → β) → Continuous f → Topologic
alSpace.Compacts α → TopologicalSpace.Compacts β
参数：f : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a compact set under a continuous function.
-/
protected def map (f : α → β) (hf : Continuous f) (K : Compacts α) : Compacts β :=
  ⟨f '' K.1, K.2.image hf⟩

@[simp, norm_cast]
/-
**TopologicalSpace.Compacts.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Compacts`。
形式化陈述：coe_map {f : α -> β} (hf : Continuous f) (s : Compacts α) : (s.map f hf : 
Set β) = f '' s
参数：hf : Continuous f；s : Compacts α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map {f : α → β} (hf : Continuous f) (s : Compacts α) : (s.map f hf : Set β) = f '' s :=
  rfl

@[simp]
/-
**TopologicalSpace.Compacts.map_id** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.C
ompacts`。
形式化陈述：map_id (K : Compacts α) : K.map id continuous_id = K
参数：K : Compacts α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Compacts.ext`：∀ {α : Type u_1} [inst : TopologicalSpace
 α] {s t : TopologicalSpace.Compacts α}, ↑s = ↑t → s = t
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem map_id (K : Compacts α) : K.map id continuous_id = K :=
  Compacts.ext <| Set.image_id _
/-
**TopologicalSpace.Compacts.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace
.Compacts`。
形式化陈述：map_comp (f : β -> γ) (g : α -> β) (hf : Continuous f) (hg : Continuous g)
 (K : Compacts α) : K.map (f ∘ g) (hf.comp hg) = (K.map g hg).map f hf
参数：f : β -> γ；g : α -> β；hf : Continuous f；hg : Continuous g；K : Compacts α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Compacts.ext`：∀ {α : Type u_1} [inst : TopologicalSpace
 α] {s t : TopologicalSpace.Compacts α}, ↑s = ↑t → s = t
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
theorem map_comp (f : β → γ) (g : α → β) (hf : Continuous f) (hg : Continuous g) (K : Compacts α) :
    K.map (f ∘ g) (hf.comp hg) = (K.map g hg).map f hf :=
  Compacts.ext <| Set.image_comp _ _ _
/-
**TopologicalSpace.Compacts.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.Compacts`。
形式化陈述：map_injective {f : α -> β} (hf : Continuous f) (hf' : Function.Injective f
) : Function.Injective (Compacts.map f hf)
参数：hf : Continuous f；hf' : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem map_injective {f : α → β} (hf : Continuous f) (hf' : Function.Injective f) :
    Function.Injective (Compacts.map f hf) :=
  .of_comp (f := SetLike.coe) <| hf'.image_injective.comp SetLike.coe_injective

@[simp]
/-
**TopologicalSpace.Compacts.map_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.Compacts`。
形式化陈述：map_singleton {f : α -> β} (hf : Continuous f) (x : α) : Compacts.map f hf
 {x} = {f x}
参数：hf : Continuous f；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Compacts.ext`：∀ {α : Type u_1} [inst : TopologicalSpace
 α] {s t : TopologicalSpace.Compacts α}, ↑s = ↑t → s = t
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
-/
theorem map_singleton {f : α → β} (hf : Continuous f) (x : α) : Compacts.map f hf {x} = {f x} :=
  Compacts.ext Set.image_singleton

@[simp]
/-
**TopologicalSpace.Compacts.map_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
icalSpace.Compacts`。
形式化陈述：map_injective_iff {f : α -> β} (hf : Continuous f) : Function.Injective (C
ompacts.map f hf) ↔ Function.Injective f
参数：hf : Continuous f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Compacts.map_singleton`：map_singleton {f : α -> β} (hf 
: Continuous f) (x : α) : Compacts.map f hf {x} = {f x}
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `TopologicalSpace.Compacts.singleton_injective`：singleton_injective : Fun
ction.Injective ({·} : α -> Compacts α)
· 使用定理 `TopologicalSpace.Compacts.map_injective`：map_injective {f : α -> β} (hf 
: Continuous f) (hf' : Function.Injective f) : Function.Injective (Compacts.map 
f hf)
-/
theorem map_injective_iff {f : α → β} (hf : Continuous f) :
    Function.Injective (Compacts.map f hf) ↔ Function.Injective f := by
  refine ⟨fun h => .of_comp (f := ({·} : β → Compacts β)) ?_, map_injective hf⟩
  simp_rw [Function.comp_def, ← map_singleton hf]
  exact h.comp singleton_injective
/-
**TopologicalSpace.Compacts.range_map** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpac
e.Compacts`。
形式化陈述：range_map {f : α -> β} (hf : Topology.IsInducing f) : range (Compacts.map 
f hf.continuous) = {K : Compacts β | ↑K subseteq range f}
参数：hf : Topology.IsInducing f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用引理 `Topology.IsInducing.isCompact_preimage'`：Topology.IsInducing.isCompact_p
reimage' (hf : IsInducing f) {K : Set Y} (hK : IsCompact K) (Kf : K subseteq ran
ge f) : IsCompact (f ⁻¹' K)
· 使用定理 `TopologicalSpace.Compacts.isCompact`：∀ {α : Type u_1} [inst : Topologica
lSpace α] (s : TopologicalSpace.Compacts α), IsCompact ↑s
· 使用定理 `TopologicalSpace.Compacts.ext`：∀ {α : Type u_1} [inst : TopologicalSpace
 α] {s t : TopologicalSpace.Compacts α}, ↑s = ↑t → s = t
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
-/
theorem range_map {f : α → β} (hf : Topology.IsInducing f) :
    range (Compacts.map f hf.continuous) = {K : Compacts β | ↑K ⊆ range f} :=
  subset_antisymm
    (range_subset_iff.mpr fun _ => image_subset_range _ _)
    (fun L hL => ⟨
      { carrier := f ⁻¹' L
        isCompact' := hf.isCompact_preimage' L.isCompact hL },
      Compacts.ext (image_preimage_eq_of_subset hL)⟩)

/-- A homeomorphism induces an equivalence on compact sets, by taking the image. -/
@[simps]
/-
**TopologicalSpace.Compacts.equiv** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Co
mpacts`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : TopologicalSpace α] →     
  [inst_1 : TopologicalSpace β] → α ≃ₜ β → TopologicalSpace.Compacts α ≃ Topolog
icalSpace.Compacts β
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h

--- 原说明 ---
A homeomorphism induces an equivalence on compact sets, by taking the image.
-/
protected def equiv (f : α ≃ₜ β) : Compacts α ≃ Compacts β where
  toFun := Compacts.map f f.continuous
  invFun := Compacts.map _ f.symm.continuous
  left_inv s := by
    ext1
    simp only [coe_map, ← image_comp, f.symm_comp_self, image_id]
  right_inv s := by
    ext1
    simp only [coe_map, ← image_comp, f.self_comp_symm, image_id]

@[simp]
/-
**TopologicalSpace.Compacts.equiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpa
ce.Compacts`。
形式化陈述：equiv_refl : Compacts.equiv (Homeomorph.refl α) = Equiv.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `TopologicalSpace.Compacts.map_id`：map_id (K : Compacts α) : K.map id con
tinuous_id = K
-/
theorem equiv_refl : Compacts.equiv (Homeomorph.refl α) = Equiv.refl _ :=
  Equiv.ext map_id

@[simp]
/-
**TopologicalSpace.Compacts.equiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.Compacts`。
形式化陈述：equiv_trans (f : α ≃ₜ β) (g : β ≃ₜ γ) : Compacts.equiv (f.trans g) = (Comp
acts.equiv f).trans (Compacts.equiv g)
参数：f : α ≃ₜ β；g : β ≃ₜ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `TopologicalSpace.Compacts.map_comp`：map_comp (f : β -> γ) (g : α -> β) (
hf : Continuous f) (hg : Continuous g) (K : Compacts α) : K.map (f ∘ g) (hf.comp
 hg) = (K.map g hg).map …
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
-/
theorem equiv_trans (f : α ≃ₜ β) (g : β ≃ₜ γ) :
    Compacts.equiv (f.trans g) = (Compacts.equiv f).trans (Compacts.equiv g) :=
  Equiv.ext <| map_comp g f g.continuous f.continuous

@[simp]
/-
**TopologicalSpace.Compacts.equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpa
ce.Compacts`。
形式化陈述：equiv_symm (f : α ≃ₜ β) : Compacts.equiv f.symm = (Compacts.equiv f).symm
参数：f : α ≃ₜ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_symm (f : α ≃ₜ β) : Compacts.equiv f.symm = (Compacts.equiv f).symm :=
  rfl

/-- The image of a compact set under a homeomorphism can also be expressed as a preimage. -/
/-
**TopologicalSpace.Compacts.coe_equiv_apply_eq_preimage** 是 Mathlib 中的一个定理，位于命名空
间 `TopologicalSpace.Compacts`。
形式化陈述：coe_equiv_apply_eq_preimage (f : α ≃ₜ β) (K : Compacts α) : (Compacts.equi
v f K : Set β) = f.symm ⁻¹' (K : Set α)
参数：f : α ≃ₜ β；K : Compacts α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s

--- 原说明 ---
The image of a compact set under a homeomorphism can also be expressed as a prei
mage.
-/
theorem coe_equiv_apply_eq_preimage (f : α ≃ₜ β) (K : Compacts α) :
    (Compacts.equiv f K : Set β) = f.symm ⁻¹' (K : Set α) :=
  f.toEquiv.image_eq_preimage_symm K

/-- The product of two `TopologicalSpace.Compacts`, as a `TopologicalSpace.Compacts` in the product
space. -/
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two `TopologicalSpace.Compacts`, as a `TopologicalSpace.Compacts`
 in the product
space.
-/
instance : SProd (Compacts α) (Compacts β) (Compacts (α × β)) where
  sprod K L := { carrier := K ×ˢ L, isCompact' := IsCompact.prod K.2 L.2 }

@[simp]
/-
**TopologicalSpace.Compacts.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace
.Compacts`。
形式化陈述：coe_prod (K : Compacts α) (L : Compacts β) : (K ×ˢ L : Compacts (α × β)) =
 (K : Set α) ×ˢ (L : Set β)
参数：K : Compacts α；L : Compacts β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (K : Compacts α) (L : Compacts β) :
    (K ×ˢ L : Compacts (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

@[simp]
/-
**TopologicalSpace.Compacts.toCloseds_prod** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.Compacts`。
形式化陈述：toCloseds_prod [T2Space α] [T2Space β] (K : Compacts α) (L : Compacts β) :
 (K ×ˢ L).toCloseds = K.toCloseds ×ˢ L.toCloseds
参数：K : Compacts α；L : Compacts β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCloseds_prod [T2Space α] [T2Space β] (K : Compacts α) (L : Compacts β) :
    (K ×ˢ L).toCloseds = K.toCloseds ×ˢ L.toCloseds := by
  rfl

@[simp]
/-
**TopologicalSpace.Compacts.singleton_prod_singleton** 是 Mathlib 中的一个定理，位于命名空间 `
TopologicalSpace.Compacts`。
形式化陈述：singleton_prod_singleton (x : α) (y : β) : ({x} ×ˢ {y} : Compacts (α × β))
 = {(x, y)}
参数：x : α；y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Compacts.ext`：∀ {α : Type u_1} [inst : TopologicalSpace
 α] {s t : TopologicalSpace.Compacts α}, ↑s = ↑t → s = t
· 使用定理 `Set.singleton_prod_singleton`：singleton_prod_singleton : ({a} : Set α) ×
ˢ ({b} : Set β) = {(a, b)}
-/
theorem singleton_prod_singleton (x : α) (y : β) :
    ({x} ×ˢ {y} : Compacts (α × β)) = {(x, y)} :=
  Compacts.ext Set.singleton_prod_singleton

-- todo: add `pi`

open Topology

/-- The compacts neighbourhoods of a compact -/
/-
**TopologicalSpace.Compacts.compactNhds** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSp
ace.Compacts`。
形式化陈述：compactNhds (K : Compacts α) : Set (Compacts α)
参数：K : Compacts α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The compacts neighbourhoods of a compact
-/
def compactNhds (K : Compacts α) : Set (Compacts α) :=
  {K' | ∀ (x : K), (K': Set α) ∈ 𝓝 x.val}
/-
**TopologicalSpace.Compacts.subset_of_mem_compactNhds** 是 Mathlib 中的一个引理，位于命名空间 
`TopologicalSpace.Compacts`。
形式化陈述：subset_of_mem_compactNhds {K K' : Compacts α} (h : K' in K.compactNhds) : 
(K : Set α) subseteq K'
参数：h : K' in K.compactNhds。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
lemma subset_of_mem_compactNhds {K K' : Compacts α} (h : K' ∈ K.compactNhds) :
    (K : Set α) ⊆ K' :=
  fun x hx ↦ mem_of_mem_nhds (h ⟨x, hx⟩)
/-
**TopologicalSpace.Compacts.exists_open_set_nhds_of_compactsNhds** 是 Mathlib 中的一
个引理，位于命名空间 `TopologicalSpace.Compacts`。
形式化陈述：exists_open_set_nhds_of_compactsNhds {K : Compacts α} (L : K.compactNhds) 
: exists U : Opens α, (K : Set α) subseteq U ∧ (U : Set α) subseteq L
参数：L : K.compactNhds。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_open_set_nhds`：exists_open_set_nhds {U : Set X} (h : forall x in 
s, U in 𝓝 x) : exists V : Set X, s subseteq V ∧ IsOpen V ∧ V subseteq U
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma exists_open_set_nhds_of_compactsNhds {K : Compacts α} (L : K.compactNhds) :
    ∃ U : Opens α, (K : Set α) ⊆ U ∧ (U : Set α) ⊆ L := by
  obtain ⟨U, KsubU, openU, UsubL⟩ := exists_open_set_nhds (fun x hx ↦ L.2 ⟨x, hx⟩)
  exact ⟨⟨U, openU⟩, KsubU, UsubL⟩
/-
**TopologicalSpace.Compacts.exists_open_set_nhds_of_mem_compactsNhds** 是 Mathlib
 中的一个引理，位于命名空间 `TopologicalSpace.Compacts`。
形式化陈述：exists_open_set_nhds_of_mem_compactsNhds {K K' : Compacts α} (h : K' in K.
compactNhds) : exists U : Opens α, (K : Set α) subseteq U ∧ (U : Set α) subseteq
 K'
参数：h : K' in K.compactNhds。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopologicalSpace.Compacts.exists_open_set_nhds_of_compactsNhds`：exists_o
pen_set_nhds_of_compactsNhds {K : Compacts α} (L : K.compactNhds) : exists U : O
pens α, (K : Set α) subseteq U ∧ (U : Set α) subsete…
-/
lemma exists_open_set_nhds_of_mem_compactsNhds {K K' : Compacts α} (h : K' ∈ K.compactNhds) :
    ∃ U : Opens α, (K : Set α) ⊆ U ∧ (U : Set α) ⊆ K' :=
  exists_open_set_nhds_of_compactsNhds ⟨K', h⟩

/-- The compact neighbourhood induced by the existence of an open subset between two compacts -/
/-
**TopologicalSpace.Compacts.compactNhdsMkOfOpens** 是 Mathlib 中的一个定义，位于命名空间 `Topo
logicalSpace.Compacts`。
形式化陈述：compactNhdsMkOfOpens {K : Compacts α} (L : Compacts α) (U : Opens α) (h1 :
 (K : Set α) subseteq U) (h2 : (U : Set α) subseteq L) : K.compactNhds
参数：L : Compacts α；U : Opens α；h1 : (K : Set α) subseteq U；h2 : (U : Set α) subse
teq L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The compact neighbourhood induced by the existence of an open subset between two
 compacts
-/
def compactNhdsMkOfOpens {K : Compacts α} (L : Compacts α) (U : Opens α)
    (h1 : (K : Set α) ⊆ U) (h2 : (U : Set α) ⊆ L) :
    K.compactNhds :=
  ⟨L, fun _ ↦ Filter.mem_of_superset (IsOpen.mem_nhds U.is_open' (h1 (Subtype.coe_prop _))) h2⟩
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space α] (K : Compacts α) : SemilatticeInf (K.compactNhds) where
  inf L M := ⟨L.1 ⊓ M.1, fun x ↦ Filter.inter_mem_iff.2 ⟨L.2 x, M.2 x⟩⟩
  inf_le_right _ _ := Subtype.coe_le_coe.mp inf_le_right
  inf_le_left _ _:= Subtype.coe_le_coe.mp inf_le_left
  le_inf _ _ _ h k :=
    Subtype.coe_le_coe.mp (le_inf (Subtype.coe_le_coe.mpr h) (Subtype.coe_le_coe.mpr k))

/-- The set of opens neighbourhood of a compact subset -/
/-
**TopologicalSpace.Compacts.openNhds** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace
.Compacts`。
形式化陈述：openNhds (K : Compacts α) : Set (Opens α)
参数：K : Compacts α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of opens neighbourhood of a compact subset
-/
def openNhds (K : Compacts α) : Set (Opens α) := {U | (K : Set α) ⊆ U}
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : Compacts α) : IsCodirectedOrder K.openNhds where
  directed U1 U2 := ⟨⟨U1.val ⊓ U2.val, Set.subset_inter U1.property U2.property⟩,
  ⟨Subtype.mk_le_mk.2 inf_le_left, Subtype.mk_le_mk.2 inf_le_right⟩⟩
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : Compacts α) : Top K.openNhds := ⟨⊤, Set.subset_univ _⟩
-- in particular `K.openNhds` is not empty and thus the induced category is cofiltered
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (⊥ : Compacts α).openNhds := ⟨⊥, fun _ h ↦ h⟩

/-- The opens neighbourhood of a compact subset that are relatively compact -/
/-
**TopologicalSpace.Compacts.openRcNhds** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpa
ce.Compacts`。
形式化陈述：openRcNhds (K : Compacts α) : Set (Opens α)
参数：K : Compacts α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opens neighbourhood of a compact subset that are relatively compact
-/
def openRcNhds (K : Compacts α) : Set (Opens α) :=
  {U | IsCompact (closure (U : Set α )) ∧ (K : Set α) ⊆ U}
/-
**TopologicalSpace.Compacts.subset_of_mem_openRcNhds** 是 Mathlib 中的一个引理，位于命名空间 `
TopologicalSpace.Compacts`。
形式化陈述：subset_of_mem_openRcNhds {K : Compacts α} {U : Opens α} (h : U in K.openRc
Nhds) : (K : Set α) subseteq U
参数：h : U in K.openRcNhds。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma subset_of_mem_openRcNhds {K : Compacts α} {U : Opens α} (h : U ∈ K.openRcNhds) :
    (K : Set α) ⊆ U :=
  fun _ hx ↦ h.right hx
/-
**TopologicalSpace.Compacts.isCompact_closure_of_mem_openRcNhds** 是 Mathlib 中的一个
引理，位于命名空间 `TopologicalSpace.Compacts`。
形式化陈述：isCompact_closure_of_mem_openRcNhds {K : Compacts α} {U : Opens α} (h : U 
in K.openRcNhds) : IsCompact (closure (U : Set α))
参数：h : U in K.openRcNhds。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma isCompact_closure_of_mem_openRcNhds {K : Compacts α} {U : Opens α} (h : U ∈ K.openRcNhds) :
  IsCompact (closure (U : Set α)) := h.left
/-
**TopologicalSpace.Compacts.closure_mem_compactNhds_of_mem_openRcNhds** 是 Mathli
b 中的一个引理，位于命名空间 `TopologicalSpace.Compacts`。
形式化陈述：closure_mem_compactNhds_of_mem_openRcNhds {K : Compacts α} {U : Opens α} (
h : U in K.openRcNhds) : ⟨closure (U : Set α), isCompact_closure_of_mem_openRcNh
ds h⟩ in K.compactNhds
参数：h : U in K.openRcNhds。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用引理 `TopologicalSpace.Compacts.subset_of_mem_openRcNhds`：subset_of_mem_openRc
Nhds {K : Compacts α} {U : Opens α} (h : U in K.openRcNhds) : (K : Set α) subset
eq U
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用引理 `TopologicalSpace.Compacts.isCompact_closure_of_mem_openRcNhds`：isCompact
_closure_of_mem_openRcNhds {K : Compacts α} {U : Opens α} (h : U in K.openRcNhds
) : IsCompact (closure (U : Set α))
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
lemma closure_mem_compactNhds_of_mem_openRcNhds {K : Compacts α} {U : Opens α}
    (h : U ∈ K.openRcNhds) :
    ⟨closure (U : Set α), isCompact_closure_of_mem_openRcNhds h⟩ ∈ K.compactNhds := by
  intro x
  have H : (U : Set α) ∈ 𝓝 (x : α) :=
    U.isOpen.mem_nhds <| Compacts.subset_of_mem_openRcNhds h (by simp)
  exact Filter.mem_of_superset H subset_closure

/-- The converting map from relatively compact opens
neighbourhood of a compact subset to its opens neighbourhoods -/
/-
**TopologicalSpace.Compacts.openRcNhdsToOpenNhds** 是 Mathlib 中的一个定义，位于命名空间 `Topo
logicalSpace.Compacts`。
形式化陈述：openRcNhdsToOpenNhds (K : Compacts α) : K.openRcNhds -> K.openNhds
参数：K : Compacts α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The converting map from relatively compact opens
neighbourhood of a compact subset to its opens neighbourhoods
-/
def openRcNhdsToOpenNhds (K : Compacts α) : K.openRcNhds → K.openNhds :=
  fun U ↦ ⟨_, U.property.2⟩
/-
**TopologicalSpace.Compacts.openRcNhdsToOpenNhds_mono** 是 Mathlib 中的一个引理，位于命名空间 
`TopologicalSpace.Compacts`。
形式化陈述：openRcNhdsToOpenNhds_mono (K : Compacts α) : Monotone K.openRcNhdsToOpenNh
ds
参数：K : Compacts α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma openRcNhdsToOpenNhds_mono (K : Compacts α) :
    Monotone K.openRcNhdsToOpenNhds := fun _ _ h ↦ h

/-- An open relatively compact neighbourhood of `K` induces a compact neighbourhood by taking
the closure
-/
/-
**TopologicalSpace.Compacts.openRcNhdsToCompactNhds** 是 Mathlib 中的一个定义，位于命名空间 `T
opologicalSpace.Compacts`。
形式化陈述：openRcNhdsToCompactNhds (K : Compacts α) : K.openRcNhds -> K.compactNhds
参数：K : Compacts α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open relatively compact neighbourhood of `K` induces a compact neighbourhood 
by taking
the closure
-/
def openRcNhdsToCompactNhds (K : Compacts α) : K.openRcNhds → K.compactNhds :=
  fun U ↦ ⟨_, closure_mem_compactNhds_of_mem_openRcNhds (Subtype.coe_prop U)⟩
/-
**TopologicalSpace.Compacts.openRcNhdsToCompactNhds_mono** 是 Mathlib 中的一个引理，位于命名
空间 `TopologicalSpace.Compacts`。
形式化陈述：openRcNhdsToCompactNhds_mono (K : Compacts α) : Monotone K.openRcNhdsToCom
pactNhds
参数：K : Compacts α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
lemma openRcNhdsToCompactNhds_mono (K : Compacts α) : Monotone K.openRcNhdsToCompactNhds :=
  fun _ _ h ↦ closure_mono h
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space α] (K : Compacts α) : IsCodirectedOrder K.openRcNhds where
  directed U1 U2 := ⟨⟨U1 ⊓ U2, (isCompact_closure_of_mem_openRcNhds (Subtype.coe_prop U1) |>.inter
    <| isCompact_closure_of_mem_openRcNhds U2.coe_prop).of_isClosed_subset
      isClosed_closure <| closure_inter_subset_inter_closure ..,
      le_inf (subset_of_mem_openRcNhds (Subtype.coe_prop U1))
      <| subset_of_mem_openRcNhds (Subtype.coe_prop U2)⟩,
         Subtype.coe_le_coe.mp inf_le_left,
         Subtype.coe_le_coe.mp inf_le_right⟩

end Compacts

namespace Opens

/-- The set of compacts inside an open subset -/
/-
**TopologicalSpace.Opens.compactsInside** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSp
ace.Opens`。
形式化陈述：compactsInside (U : Opens α) : Set (Compacts α)
参数：U : Opens α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of compacts inside an open subset
-/
def compactsInside (U : Opens α) : Set (Compacts α) := {K | (K : Set α) ⊆ U}

/-- For `K` a compact subset inside an open subset `U`, `U` has a structure of open neighbourhood
of `K` -/
/-
**TopologicalSpace.Opens.openNhdsOfCompactsInside** 是 Mathlib 中的一个定义，位于命名空间 `Top
ologicalSpace.Opens`。
形式化陈述：openNhdsOfCompactsInside {U : Opens α} (K : U.compactsInside) : (K.val).op
enNhds
参数：K : U.compactsInside。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `K` a compact subset inside an open subset `U`, `U` has a structure of open 
neighbourhood
of `K`
-/
def openNhdsOfCompactsInside {U : Opens α} (K : U.compactsInside) : (K.val).openNhds :=
  ⟨U, K.property⟩

end Opens

/-- For `U` an open neighbourhood of `K`, `K` has a structure of compact inside `U` -/
/-
**TopologicalSpace.Compacts.compactsInsideOfOpenNhds** 是 Mathlib 中的一个定义，位于命名空间 `
TopologicalSpace.Compacts`。
形式化陈述：{α : Type u_1} →   [inst : TopologicalSpace α] → {K : TopologicalSpace.Com
pacts α} → (U : ↑K.openNhds) → ↑(↑U).compactsInside
参数：U : ↑K.openNhds；↑U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `U` an open neighbourhood of `K`, `K` has a structure of compact inside `U`
-/
def Compacts.compactsInsideOfOpenNhds {K : Compacts α} (U : K.openNhds) : (U.val).compactsInside :=
  ⟨K, U.property⟩

/-! ### Nonempty compact sets -/

/-- The type of nonempty compact sets of a topological space. -/
/-
**TopologicalSpace.NonemptyCompacts** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopologicalSpac
e`。
形式化陈述：(α : Type u_4) → [TopologicalSpace α] → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of nonempty compact sets of a topological space.
-/
structure NonemptyCompacts (α : Type*) [TopologicalSpace α] extends Compacts α where
  nonempty' : carrier.Nonempty

namespace NonemptyCompacts

/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (NonemptyCompacts α) α where
  coe s := s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (NonemptyCompacts α) := .ofSetLike (NonemptyCompacts α) α

/-- See Note [custom simps projection]. -/
/-
**TopologicalSpace.NonemptyCompacts.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `Topolog
icalSpace.NonemptyCompacts.Simps`。
形式化陈述：{α : Type u_1} → [inst : TopologicalSpace α] → TopologicalSpace.NonemptyCo
mpacts α → Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.coe (s : NonemptyCompacts α) : Set α := s

initialize_simps_projections NonemptyCompacts (carrier → coe, as_prefix coe, as_prefix toCompacts)
/-
**TopologicalSpace.NonemptyCompacts.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
icalSpace.NonemptyCompacts`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] (s : TopologicalSpace.Nonempt
yCompacts α), IsCompact ↑s
参数：s : TopologicalSpace.NonemptyCompacts α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
-/
protected theorem isCompact (s : NonemptyCompacts α) : IsCompact (s : Set α) :=
  s.isCompact'
/-
**TopologicalSpace.NonemptyCompacts.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace.NonemptyCompacts`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] (s : TopologicalSpace.Nonempt
yCompacts α), (↑s).Nonempty
参数：s : TopologicalSpace.NonemptyCompacts α；↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.NonemptyCompacts.nonempty'`：∀ {α : Type u_4} [inst : To
pologicalSpace α] (self : TopologicalSpace.NonemptyCompacts α), self.carrier.Non
empty
-/
protected theorem nonempty (s : NonemptyCompacts α) : (s : Set α).Nonempty :=
  s.nonempty'

/-- Reinterpret a nonempty compact as a closed set. -/
@[simps]
/-
**TopologicalSpace.NonemptyCompacts.toCloseds** 是 Mathlib 中的一个定义，位于命名空间 `Topolog
icalSpace.NonemptyCompacts`。
形式化陈述：toCloseds [T2Space α] (s : NonemptyCompacts α) : Closeds α
参数：s : NonemptyCompacts α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a nonempty compact as a closed set.
-/
def toCloseds [T2Space α] (s : NonemptyCompacts α) : Closeds α :=
  ⟨s, s.isCompact.isClosed⟩

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.toCloseds_toCompacts** 是 Mathlib 中的一个定理，位于命名
空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：toCloseds_toCompacts [T2Space α] (s : NonemptyCompacts α) : s.toCompacts.t
oCloseds = s.toCloseds
参数：s : NonemptyCompacts α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCloseds_toCompacts [T2Space α] (s : NonemptyCompacts α) :
    s.toCompacts.toCloseds = s.toCloseds :=
  rfl

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.mem_toCloseds** 是 Mathlib 中的一个定理，位于命名空间 `Top
ologicalSpace.NonemptyCompacts`。
形式化陈述：mem_toCloseds [T2Space α] {x : α} {s : NonemptyCompacts α} : x in s.toClos
eds ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toCloseds [T2Space α] {x : α} {s : NonemptyCompacts α} :
    x ∈ s.toCloseds ↔ x ∈ s :=
  Iff.rfl
/-
**TopologicalSpace.NonemptyCompacts.toCloseds_injective** 是 Mathlib 中的一个定理，位于命名空
间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：toCloseds_injective [T2Space α] : Function.Injective (toCloseds (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem toCloseds_injective [T2Space α] : Function.Injective (toCloseds (α := α)) :=
  .of_comp (f := SetLike.coe) SetLike.coe_injective

@[ext]
/-
**TopologicalSpace.NonemptyCompacts.ext** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.NonemptyCompacts`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {s t : TopologicalSpace.Nonem
ptyCompacts α}, ↑s = ↑t → s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
-/
protected theorem ext {s t : NonemptyCompacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.NonemptyCompacts`。
形式化陈述：coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s
参数：s : Compacts α；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl
/-
**TopologicalSpace.NonemptyCompacts.carrier_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `To
pologicalSpace.NonemptyCompacts`。
形式化陈述：carrier_eq_coe (s : NonemptyCompacts α) : s.carrier = s
参数：s : NonemptyCompacts α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem carrier_eq_coe (s : NonemptyCompacts α) : s.carrier = s :=
  rfl

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.coe_toCompacts** 是 Mathlib 中的一个定理，位于命名空间 `To
pologicalSpace.NonemptyCompacts`。
形式化陈述：coe_toCompacts (s : NonemptyCompacts α) : (s.toCompacts : Set α) = s
参数：s : NonemptyCompacts α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toCompacts (s : NonemptyCompacts α) : (s.toCompacts : Set α) = s := rfl

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.mem_toCompacts** 是 Mathlib 中的一个定理，位于命名空间 `To
pologicalSpace.NonemptyCompacts`。
形式化陈述：mem_toCompacts {x : α} {s : NonemptyCompacts α} : x in s.toCompacts ↔ x in
 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toCompacts {x : α} {s : NonemptyCompacts α} :
    x ∈ s.toCompacts ↔ x ∈ s :=
  Iff.rfl
/-
**TopologicalSpace.NonemptyCompacts.toCompacts_injective** 是 Mathlib 中的一个定理，位于命名
空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：toCompacts_injective : Function.Injective (toCompacts (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem toCompacts_injective : Function.Injective (toCompacts (α := α)) :=
  .of_comp (f := SetLike.coe) SetLike.coe_injective

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.range_toCompacts** 是 Mathlib 中的一个定理，位于命名空间 `
TopologicalSpace.NonemptyCompacts`。
形式化陈述：range_toCompacts : range (toCompacts (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mem_compl_singleton_iff`：mem_compl_singleton_iff : a in ({b} : Set α
)ᶜ ↔ a != b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Compacts.coe_nonempty`：coe_nonempty {s : Compacts α} : 
(s : Set α).Nonempty ↔ s != ⊥
· 使用定理 `TopologicalSpace.NonemptyCompacts.nonempty`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] (s : TopologicalSpace.NonemptyCompacts α), (↑s).Nonempty
-/
theorem range_toCompacts : range (toCompacts (α := α)) = {⊥}ᶜ := by
  ext K
  rw [mem_compl_singleton_iff, ← Compacts.coe_nonempty]
  refine ⟨?_, fun h => ⟨⟨K, h⟩, rfl⟩⟩
  rintro ⟨K, rfl⟩
  exact K.nonempty
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (NonemptyCompacts α) :=
  ⟨fun s t => ⟨s.toCompacts ⊔ t.toCompacts, s.nonempty.mono subset_union_left⟩⟩
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace α] [Nonempty α] : Top (NonemptyCompacts α) :=
  ⟨⟨⊤, univ_nonempty⟩⟩
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (NonemptyCompacts α) :=
  fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ ↦ rfl
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace α] [Nonempty α] : OrderTop (NonemptyCompacts α) :=
  fast_instance% OrderTop.lift ((↑) : _ → Set α) (fun _ _ => id) rfl

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `Topologic
alSpace.NonemptyCompacts`。
形式化陈述：coe_sup (s t : NonemptyCompacts α) : (↑(s ⊔ t) : Set α) = ↑s union ↑t
参数：s t : NonemptyCompacts α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (s t : NonemptyCompacts α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t :=
  rfl

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.toCompacts_sup** 是 Mathlib 中的一个定理，位于命名空间 `To
pologicalSpace.NonemptyCompacts`。
形式化陈述：toCompacts_sup (s t : NonemptyCompacts α) : (s ⊔ t).toCompacts = s.toCompa
cts ⊔ t.toCompacts
参数：s t : NonemptyCompacts α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCompacts_sup (s t : NonemptyCompacts α) :
    (s ⊔ t).toCompacts = s.toCompacts ⊔ t.toCompacts :=
  rfl

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Topologic
alSpace.NonemptyCompacts`。
形式化陈述：coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : NonemptyCompacts α) : Set α
) = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : NonemptyCompacts α) : Set α) = univ :=
  rfl

@[simps! singleton_coe singleton_toCompacts]
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Singleton α (NonemptyCompacts α) where
  singleton x := ⟨{x}, singleton_nonempty x⟩

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.mem_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Top
ologicalSpace.NonemptyCompacts`。
形式化陈述：mem_singleton (x y : α) : x in ({y} : NonemptyCompacts α) ↔ x = y
参数：x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_singleton (x y : α) : x ∈ ({y} : NonemptyCompacts α) ↔ x = y :=
  Iff.rfl

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.toCloseds_singleton** 是 Mathlib 中的一个定理，位于命名空
间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：toCloseds_singleton [T2Space α] (x : α) : toCloseds {x} = {x}
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCloseds_singleton [T2Space α] (x : α) : toCloseds {x} = {x} :=
  rfl
/-
**TopologicalSpace.NonemptyCompacts.singleton_injective** 是 Mathlib 中的一个定理，位于命名空
间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：singleton_injective : Function.Injective ({·} : α -> NonemptyCompacts α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Set.singleton_injective`：singleton_injective : Injective (singleton : α 
-> Set α)
-/
theorem singleton_injective : Function.Injective ({·} : α → NonemptyCompacts α) :=
  .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.singleton_inj** 是 Mathlib 中的一个定理，位于命名空间 `Top
ologicalSpace.NonemptyCompacts`。
形式化陈述：singleton_inj {x y : α} : ({x} : NonemptyCompacts α) = {y} ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `TopologicalSpace.NonemptyCompacts.singleton_injective`：singleton_injecti
ve : Function.Injective ({·} : α -> NonemptyCompacts α)
-/
theorem singleton_inj {x y : α} : ({x} : NonemptyCompacts α) = {y} ↔ x = y :=
  singleton_injective.eq_iff

/-- In an inhabited space, the type of nonempty compact subsets is also inhabited, with
default element the singleton set containing the default element. -/
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In an inhabited space, the type of nonempty compact subsets is also inhabited, w
ith
default element the singleton set containing the default element.
-/
instance [Inhabited α] : Inhabited (NonemptyCompacts α) :=
  ⟨{default}⟩
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : IsEmpty (NonemptyCompacts α) :=
  ⟨fun K => not_isEmpty_iff.mpr K.nonempty.to_type ‹_›⟩

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.isEmpty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogicalSpace.NonemptyCompacts`。
形式化陈述：isEmpty_iff : IsEmpty (NonemptyCompacts α) ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
· 使用定理 `TopologicalSpace.NonemptyCompacts.instIsEmpty`：∀ {α : Type u_1} [inst : 
TopologicalSpace α] [IsEmpty α], IsEmpty (TopologicalSpace.NonemptyCompacts α)
-/
theorem isEmpty_iff : IsEmpty (NonemptyCompacts α) ↔ IsEmpty α :=
  ⟨fun _ => Function.isEmpty ({·} : α → NonemptyCompacts α), fun _ => inferInstance⟩
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nonempty (NonemptyCompacts α) :=
  .map ({·}) ‹_›

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalSpace.NonemptyCompacts`。
形式化陈述：nonempty_iff : Nonempty (NonemptyCompacts α) ↔ Nonempty α
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
theorem nonempty_iff : Nonempty (NonemptyCompacts α) ↔ Nonempty α := by
  simp_rw [← not_isEmpty_iff, isEmpty_iff]
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] : Subsingleton (NonemptyCompacts α) := by
  refine ⟨fun K L => NonemptyCompacts.ext ?_⟩
  rw [Subsingleton.eq_univ_of_nonempty K.nonempty, Subsingleton.eq_univ_of_nonempty L.nonempty]

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `
TopologicalSpace.NonemptyCompacts`。
形式化陈述：subsingleton_iff : Subsingleton (NonemptyCompacts α) ↔ Subsingleton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `TopologicalSpace.NonemptyCompacts.singleton_injective`：singleton_injecti
ve : Function.Injective ({·} : α -> NonemptyCompacts α)
· 使用定理 `TopologicalSpace.NonemptyCompacts.instSubsingleton`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [Subsingleton α], Subsingleton (TopologicalSpace.Nonemp
tyCompacts α)
-/
theorem subsingleton_iff : Subsingleton (NonemptyCompacts α) ↔ Subsingleton α :=
  ⟨fun _ => singleton_injective.subsingleton, fun _ => inferInstance⟩
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique α] : Unique (NonemptyCompacts α) :=
  .mk' _
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial α] : Nontrivial (NonemptyCompacts α) :=
  singleton_injective.nontrivial

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `To
pologicalSpace.NonemptyCompacts`。
形式化陈述：nontrivial_iff : Nontrivial (NonemptyCompacts α) ↔ Nontrivial α
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
theorem nontrivial_iff : Nontrivial (NonemptyCompacts α) ↔ Nontrivial α := by
  simp_rw [← not_subsingleton_iff_nontrivial, subsingleton_iff]

/-- The image of a nonempty compact set under a continuous function. -/
@[simps! toCompacts]
/-
**TopologicalSpace.NonemptyCompacts.map** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSp
ace.NonemptyCompacts`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : TopologicalSpace α] →     
  [inst_1 : TopologicalSpace β] →         (f : α → β) → Continuous f → Topologic
alSpace.NonemptyCompacts α → TopologicalSpace.NonemptyCompacts β
参数：f : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a nonempty compact set under a continuous function.
-/
protected def map (f : α → β) (hf : Continuous f) (K : NonemptyCompacts α) : NonemptyCompacts β :=
  ⟨K.toCompacts.map f hf, K.nonempty.image f⟩

@[simp, norm_cast]
/-
**TopologicalSpace.NonemptyCompacts.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Topologic
alSpace.NonemptyCompacts`。
形式化陈述：coe_map {f : α -> β} (hf : Continuous f) (s : NonemptyCompacts α) : (s.map
 f hf : Set β) = f '' s
参数：hf : Continuous f；s : NonemptyCompacts α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map {f : α → β} (hf : Continuous f) (s : NonemptyCompacts α) :
    (s.map f hf : Set β) = f '' s :=
  rfl

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.NonemptyCompacts`。
形式化陈述：map_id (K : NonemptyCompacts α) : K.map id continuous_id = K
参数：K : NonemptyCompacts α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.NonemptyCompacts.ext`：∀ {α : Type u_1} [inst : Topologi
calSpace α] {s t : TopologicalSpace.NonemptyCompacts α}, ↑s = ↑t → s = t
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_id (K : NonemptyCompacts α) : K.map id continuous_id = K := by
  ext
  simp
/-
**TopologicalSpace.NonemptyCompacts.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace.NonemptyCompacts`。
形式化陈述：map_comp (f : β -> γ) (g : α -> β) (hf : Continuous f) (hg : Continuous g)
 (K : NonemptyCompacts α) : K.map (f ∘ g) (hf.comp hg) = (K.map g hg).map f hf
参数：f : β -> γ；g : α -> β；hf : Continuous f；hg : Continuous g；K : NonemptyCompact
s α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.NonemptyCompacts.ext`：∀ {α : Type u_1} [inst : Topologi
calSpace α] {s t : TopologicalSpace.NonemptyCompacts α}, ↑s = ↑t → s = t
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_comp (f : β → γ) (g : α → β) (hf : Continuous f) (hg : Continuous g)
    (K : NonemptyCompacts α) : K.map (f ∘ g) (hf.comp hg) = (K.map g hg).map f hf := by
  ext
  simp

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.map_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Top
ologicalSpace.NonemptyCompacts`。
形式化陈述：map_singleton {f : α -> β} (hf : Continuous f) (x : α) : NonemptyCompacts.
map f hf {x} = {f x}
参数：hf : Continuous f；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.NonemptyCompacts.ext`：∀ {α : Type u_1} [inst : Topologi
calSpace α] {s t : TopologicalSpace.NonemptyCompacts α}, ↑s = ↑t → s = t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_singleton {f : α → β} (hf : Continuous f) (x : α) :
    NonemptyCompacts.map f hf {x} = {f x} := by
  ext
  simp
/-
**TopologicalSpace.NonemptyCompacts.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Top
ologicalSpace.NonemptyCompacts`。
形式化陈述：map_injective {f : α -> β} (hf : Continuous f) (hf' : Function.Injective f
) : Function.Injective (NonemptyCompacts.map f hf)
参数：hf : Continuous f；hf' : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem map_injective {f : α → β} (hf : Continuous f) (hf' : Function.Injective f) :
    Function.Injective (NonemptyCompacts.map f hf) :=
  .of_comp (f := SetLike.coe) <| hf'.image_injective.comp SetLike.coe_injective

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.map_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 
`TopologicalSpace.NonemptyCompacts`。
形式化陈述：map_injective_iff {f : α -> β} (hf : Continuous f) : Function.Injective (N
onemptyCompacts.map f hf) ↔ Function.Injective f
参数：hf : Continuous f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `TopologicalSpace.NonemptyCompacts.singleton_injective`：singleton_injecti
ve : Function.Injective ({·} : α -> NonemptyCompacts α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.NonemptyCompacts.map_singleton`：map_singleton {f : α ->
 β} (hf : Continuous f) (x : α) : NonemptyCompacts.map f hf {x} = {f x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TopologicalSpace.NonemptyCompacts.map_injective`：map_injective {f : α ->
 β} (hf : Continuous f) (hf' : Function.Injective f) : Function.Injective (Nonem
ptyCompacts.map f hf)
-/
theorem map_injective_iff {f : α → β} (hf : Continuous f) :
    Function.Injective (NonemptyCompacts.map f hf) ↔ Function.Injective f :=
  ⟨fun h => .of_comp (f := ({·} : β → NonemptyCompacts β)) fun _ _ _ ↦
    singleton_injective (h (by simp_all)), map_injective hf⟩
/-
**TopologicalSpace.NonemptyCompacts.range_map** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
icalSpace.NonemptyCompacts`。
形式化陈述：range_map {f : α -> β} (hf : Topology.IsInducing f) : range (NonemptyCompa
cts.map f hf.continuous) = {K : NonemptyCompacts β | ↑K subseteq range f}
参数：hf : Topology.IsInducing f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用引理 `Topology.IsInducing.isCompact_preimage'`：Topology.IsInducing.isCompact_p
reimage' (hf : IsInducing f) {K : Set Y} (hK : IsCompact K) (Kf : K subseteq ran
ge f) : IsCompact (f ⁻¹' K)
· 使用定理 `TopologicalSpace.NonemptyCompacts.isCompact`：∀ {α : Type u_1} [inst : To
pologicalSpace α] (s : TopologicalSpace.NonemptyCompacts α), IsCompact ↑s
· 使用定理 `Set.Nonempty.preimage'`：∀ {α : Type u_1} {β : Type u_2} {s : Set β}, s.N
onempty → ∀ {f : α → β}, s ⊆ Set.range f → (f ⁻¹' s).Nonempty
· 使用定理 `TopologicalSpace.NonemptyCompacts.nonempty`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] (s : TopologicalSpace.NonemptyCompacts α), (↑s).Nonempty
· 使用定理 `TopologicalSpace.NonemptyCompacts.ext`：∀ {α : Type u_1} [inst : Topologi
calSpace α] {s t : TopologicalSpace.NonemptyCompacts α}, ↑s = ↑t → s = t
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
-/
theorem range_map {f : α → β} (hf : Topology.IsInducing f) :
    range (NonemptyCompacts.map f hf.continuous) = {K : NonemptyCompacts β | ↑K ⊆ range f} :=
  subset_antisymm
    (range_subset_iff.mpr fun _ => image_subset_range _ _)
    (fun L hL => ⟨
      { carrier := f ⁻¹' L
        isCompact' := hf.isCompact_preimage' L.isCompact hL
        nonempty' := L.nonempty.preimage' hL },
      NonemptyCompacts.ext (image_preimage_eq_of_subset hL)⟩)
/-
**TopologicalSpace.NonemptyCompacts.toCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 `To
pologicalSpace.NonemptyCompacts`。
形式化陈述：toCompactSpace {s : NonemptyCompacts α} : CompactSpace s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `TopologicalSpace.NonemptyCompacts.isCompact`：∀ {α : Type u_1} [inst : To
pologicalSpace α] (s : TopologicalSpace.NonemptyCompacts α), IsCompact ↑s
-/
instance toCompactSpace {s : NonemptyCompacts α} : CompactSpace s :=
  isCompact_iff_compactSpace.1 s.isCompact
/-
**TopologicalSpace.NonemptyCompacts.toNonempty** 是 Mathlib 中的一个实例，位于命名空间 `Topolo
gicalSpace.NonemptyCompacts`。
形式化陈述：toNonempty {s : NonemptyCompacts α} : Nonempty s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `TopologicalSpace.NonemptyCompacts.nonempty`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] (s : TopologicalSpace.NonemptyCompacts α), (↑s).Nonempty
-/
instance toNonempty {s : NonemptyCompacts α} : Nonempty s :=
  s.nonempty.to_subtype

/-- The product of two `TopologicalSpace.NonemptyCompacts`, as a `TopologicalSpace.NonemptyCompacts`
in the product space. -/
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two `TopologicalSpace.NonemptyCompacts`, as a `TopologicalSpace.N
onemptyCompacts`
in the product space.
-/
instance : SProd (NonemptyCompacts α) (NonemptyCompacts β) (NonemptyCompacts (α × β)) where
  sprod K L := { K.toCompacts ×ˢ L.toCompacts with nonempty' := K.nonempty.prod L.nonempty }

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace.NonemptyCompacts`。
形式化陈述：coe_prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) : (K ×ˢ L : Non
emptyCompacts (α × β)) = (K : Set α) ×ˢ (L : Set β)
参数：K : NonemptyCompacts α；L : NonemptyCompacts β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) :
    (K ×ˢ L : NonemptyCompacts (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.toCompacts_prod** 是 Mathlib 中的一个定理，位于命名空间 `T
opologicalSpace.NonemptyCompacts`。
形式化陈述：toCompacts_prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) : (K ×ˢ 
L).toCompacts = K.toCompacts ×ˢ L.toCompacts
参数：K : NonemptyCompacts α；L : NonemptyCompacts β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCompacts_prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) :
    (K ×ˢ L).toCompacts = K.toCompacts ×ˢ L.toCompacts :=
  rfl

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.toCloseds_prod** 是 Mathlib 中的一个定理，位于命名空间 `To
pologicalSpace.NonemptyCompacts`。
形式化陈述：toCloseds_prod [T2Space α] [T2Space β] (K : NonemptyCompacts α) (L : Nonem
ptyCompacts β) : (K ×ˢ L).toCloseds = K.toCloseds ×ˢ L.toCloseds
参数：K : NonemptyCompacts α；L : NonemptyCompacts β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCloseds_prod [T2Space α] [T2Space β] (K : NonemptyCompacts α) (L : NonemptyCompacts β) :
    (K ×ˢ L).toCloseds = K.toCloseds ×ˢ L.toCloseds := by
  rfl

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.singleton_prod_singleton** 是 Mathlib 中的一个定理，
位于命名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：singleton_prod_singleton (x : α) (y : β) : ({x} ×ˢ {y} : NonemptyCompacts 
(α × β)) = {(x, y)}
参数：x : α；y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.NonemptyCompacts.ext`：∀ {α : Type u_1} [inst : Topologi
calSpace α] {s t : TopologicalSpace.NonemptyCompacts α}, ↑s = ↑t → s = t
· 使用定理 `Set.singleton_prod_singleton`：singleton_prod_singleton : ({a} : Set α) ×
ˢ ({b} : Set β) = {(a, b)}
-/
theorem singleton_prod_singleton (x : α) (y : β) :
    ({x} ×ˢ {y} : NonemptyCompacts (α × β)) = {(x, y)} :=
  NonemptyCompacts.ext Set.singleton_prod_singleton

/-- `TopologicalSpace.NonemptyCompacts.toCompacts` as an order embedding. -/
/-
**TopologicalSpace.NonemptyCompacts.toCompactsOrderEmbedding** 是 Mathlib 中的一个定义，
位于命名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：toCompactsOrderEmbedding : NonemptyCompacts α ↪o Compacts α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TopologicalSpace.NonemptyCompacts.toCompacts` as an order embedding.
-/
def toCompactsOrderEmbedding : NonemptyCompacts α ↪o Compacts α :=
  .ofMapLEIff toCompacts fun _ _ => .rfl

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.coe_toCompactsOrderEmbedding** 是 Mathlib 中的一
个定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：coe_toCompactsOrderEmbedding : ⇑(toCompactsOrderEmbedding (α
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toCompactsOrderEmbedding : ⇑(toCompactsOrderEmbedding (α := α)) = toCompacts :=
  rfl

end NonemptyCompacts

/-! ### Positive compact sets -/

/-- The type of compact sets with nonempty interior of a topological space.
See also `TopologicalSpace.Compacts` and `TopologicalSpace.NonemptyCompacts`. -/
/-
**TopologicalSpace.PositiveCompacts** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopologicalSpac
e`。
形式化陈述：(α : Type u_4) → [TopologicalSpace α] → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of compact sets with nonempty interior of a topological space.
See also `TopologicalSpace.Compacts` and `TopologicalSpace.NonemptyCompacts`.
-/
structure PositiveCompacts (α : Type*) [TopologicalSpace α] extends Compacts α where
  interior_nonempty' : (interior carrier).Nonempty

namespace PositiveCompacts

/-
**TopologicalSpace.PositiveCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.PositiveCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (PositiveCompacts α) α where
  coe s := s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr
/-
**TopologicalSpace.PositiveCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.PositiveCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (PositiveCompacts α) := .ofSetLike (PositiveCompacts α) α

/-- See Note [custom simps projection]. -/
/-
**TopologicalSpace.PositiveCompacts.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `Topolog
icalSpace.PositiveCompacts.Simps`。
形式化陈述：{α : Type u_1} → [inst : TopologicalSpace α] → TopologicalSpace.PositiveCo
mpacts α → Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.coe (s : PositiveCompacts α) : Set α := s

initialize_simps_projections PositiveCompacts (carrier → coe, as_prefix coe, as_prefix toCompacts)
/-
**TopologicalSpace.PositiveCompacts.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
icalSpace.PositiveCompacts`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] (s : TopologicalSpace.Positiv
eCompacts α), IsCompact ↑s
参数：s : TopologicalSpace.PositiveCompacts α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
-/
protected theorem isCompact (s : PositiveCompacts α) : IsCompact (s : Set α) :=
  s.isCompact'
/-
**TopologicalSpace.PositiveCompacts.interior_nonempty** 是 Mathlib 中的一个定理，位于命名空间 
`TopologicalSpace.PositiveCompacts`。
形式化陈述：interior_nonempty (s : PositiveCompacts α) : (interior (s : Set α)).Nonemp
ty
参数：s : PositiveCompacts α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.PositiveCompacts.interior_nonempty'`：∀ {α : Type u_4} [
inst : TopologicalSpace α] (self : TopologicalSpace.PositiveCompacts α),   (inte
rior self.carrier).Nonempty
-/
theorem interior_nonempty (s : PositiveCompacts α) : (interior (s : Set α)).Nonempty :=
  s.interior_nonempty'
/-
**TopologicalSpace.PositiveCompacts.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace.PositiveCompacts`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] (s : TopologicalSpace.Positiv
eCompacts α), (↑s).Nonempty
参数：s : TopologicalSpace.PositiveCompacts α；↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `TopologicalSpace.PositiveCompacts.interior_nonempty`：interior_nonempty (
s : PositiveCompacts α) : (interior (s : Set α)).Nonempty
-/
protected theorem nonempty (s : PositiveCompacts α) : (s : Set α).Nonempty :=
  s.interior_nonempty.mono interior_subset

/-- Reinterpret a positive compact as a nonempty compact. -/
/-
**TopologicalSpace.PositiveCompacts.toNonemptyCompacts** 是 Mathlib 中的一个定义，位于命名空间
 `TopologicalSpace.PositiveCompacts`。
形式化陈述：toNonemptyCompacts (s : PositiveCompacts α) : NonemptyCompacts α
参数：s : PositiveCompacts α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.PositiveCompacts.nonempty`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] (s : TopologicalSpace.PositiveCompacts α), (↑s).Nonempty

--- 原说明 ---
Reinterpret a positive compact as a nonempty compact.
-/
def toNonemptyCompacts (s : PositiveCompacts α) : NonemptyCompacts α :=
  ⟨s.toCompacts, s.nonempty⟩

@[ext]
/-
**TopologicalSpace.PositiveCompacts.ext** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.PositiveCompacts`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {s t : TopologicalSpace.Posit
iveCompacts α}, ↑s = ↑t → s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
-/
protected theorem ext {s t : PositiveCompacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/-
**TopologicalSpace.PositiveCompacts.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.PositiveCompacts`。
形式化陈述：coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s
参数：s : Compacts α；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl
/-
**TopologicalSpace.PositiveCompacts.carrier_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `To
pologicalSpace.PositiveCompacts`。
形式化陈述：carrier_eq_coe (s : PositiveCompacts α) : s.carrier = s
参数：s : PositiveCompacts α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem carrier_eq_coe (s : PositiveCompacts α) : s.carrier = s :=
  rfl

@[simp]
/-
**TopologicalSpace.PositiveCompacts.coe_toCompacts** 是 Mathlib 中的一个定理，位于命名空间 `To
pologicalSpace.PositiveCompacts`。
形式化陈述：coe_toCompacts (s : PositiveCompacts α) : (s.toCompacts : Set α) = s
参数：s : PositiveCompacts α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toCompacts (s : PositiveCompacts α) : (s.toCompacts : Set α) = s :=
  rfl
/-
**TopologicalSpace.PositiveCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.PositiveCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (PositiveCompacts α) :=
  ⟨fun s t =>
    ⟨s.toCompacts ⊔ t.toCompacts,
      s.interior_nonempty.mono <| interior_mono subset_union_left⟩⟩
/-
**TopologicalSpace.PositiveCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.PositiveCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace α] [Nonempty α] : Top (PositiveCompacts α) :=
  ⟨⟨⊤, interior_univ.symm.subst univ_nonempty⟩⟩
/-
**TopologicalSpace.PositiveCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.PositiveCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (PositiveCompacts α) :=
  fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ ↦ rfl
/-
**TopologicalSpace.PositiveCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.PositiveCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace α] [Nonempty α] : OrderTop (PositiveCompacts α) :=
  fast_instance% OrderTop.lift ((↑) : _ → Set α) (fun _ _ => id) rfl

@[simp]
/-
**TopologicalSpace.PositiveCompacts.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `Topologic
alSpace.PositiveCompacts`。
形式化陈述：coe_sup (s t : PositiveCompacts α) : (↑(s ⊔ t) : Set α) = ↑s union ↑t
参数：s t : PositiveCompacts α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (s t : PositiveCompacts α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t :=
  rfl

@[simp]
/-
**TopologicalSpace.PositiveCompacts.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Topologic
alSpace.PositiveCompacts`。
形式化陈述：coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : PositiveCompacts α) : Set α
) = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : PositiveCompacts α) : Set α) = univ :=
  rfl

/-- The image of a positive compact set under a continuous open map. -/
/-
**TopologicalSpace.PositiveCompacts.map** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSp
ace.PositiveCompacts`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : TopologicalSpace α] →     
  [inst_1 : TopologicalSpace β] →         (f : α → β) →           Continuous f →
 IsOpenMap f → TopologicalSpace.PositiveCompacts α → TopologicalSpace.PositiveCo
mpacts β
参数：f : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a positive compact set under a continuous open map.
-/
protected def map (f : α → β) (hf : Continuous f) (hf' : IsOpenMap f) (K : PositiveCompacts α) :
    PositiveCompacts β :=
  { Compacts.map f hf K.toCompacts with
    interior_nonempty' :=
      (K.interior_nonempty'.image _).mono (hf'.image_interior_subset K.toCompacts) }

@[simp, norm_cast]
/-
**TopologicalSpace.PositiveCompacts.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Topologic
alSpace.PositiveCompacts`。
形式化陈述：coe_map {f : α -> β} (hf : Continuous f) (hf' : IsOpenMap f) (s : Positive
Compacts α) : (s.map f hf hf' : Set β) = f '' s
参数：hf : Continuous f；hf' : IsOpenMap f；s : PositiveCompacts α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map {f : α → β} (hf : Continuous f) (hf' : IsOpenMap f) (s : PositiveCompacts α) :
    (s.map f hf hf' : Set β) = f '' s :=
  rfl

@[simp]
/-
**TopologicalSpace.PositiveCompacts.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.PositiveCompacts`。
形式化陈述：map_id (K : PositiveCompacts α) : K.map id continuous_id IsOpenMap.id = K
参数：K : PositiveCompacts α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.PositiveCompacts.ext`：∀ {α : Type u_1} [inst : Topologi
calSpace α] {s t : TopologicalSpace.PositiveCompacts α}, ↑s = ↑t → s = t
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `IsOpenMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenMap id
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem map_id (K : PositiveCompacts α) : K.map id continuous_id IsOpenMap.id = K :=
  PositiveCompacts.ext <| Set.image_id _
/-
**TopologicalSpace.PositiveCompacts.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace.PositiveCompacts`。
形式化陈述：map_comp (f : β -> γ) (g : α -> β) (hf : Continuous f) (hg : Continuous g)
 (hf' : IsOpenMap f) (hg' : IsOpenMap g) (K : PositiveCompacts α) : K.map (f ∘ g
) (hf.comp hg) (hf'.comp hg') = (K.map g hg hg').map f hf hf'
参数：f : β -> γ；g : α -> β；hf : Continuous f；hg : Continuous g；hf' : IsOpenMap f；h
g' : IsOpenMap g；K : PositiveCompacts α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.PositiveCompacts.ext`：∀ {α : Type u_1} [inst : Topologi
calSpace α] {s t : TopologicalSpace.PositiveCompacts α}, ↑s = ↑t → s = t
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
theorem map_comp (f : β → γ) (g : α → β) (hf : Continuous f) (hg : Continuous g) (hf' : IsOpenMap f)
    (hg' : IsOpenMap g) (K : PositiveCompacts α) :
    K.map (f ∘ g) (hf.comp hg) (hf'.comp hg') = (K.map g hg hg').map f hf hf' :=
  PositiveCompacts.ext <| Set.image_comp _ _ _
/-
**TopologicalSpace.PositiveCompacts._root_.exists_positiveCompacts_subset** 是 Ma
thlib 中的一个定理，位于命名空间 `TopologicalSpace.PositiveCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.exists_positiveCompacts_subset [LocallyCompactSpace α] {U : Set α} (ho : IsOpen U)
    (hn : U.Nonempty) : ∃ K : PositiveCompacts α, ↑K ⊆ U :=
  let ⟨x, hx⟩ := hn
  let ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset ho hx
  ⟨⟨⟨K, hKc⟩, ⟨x, hxK⟩⟩, hKU⟩
/-
**TopologicalSpace.PositiveCompacts._root_.IsOpen.exists_positiveCompacts_closur
e_subset** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.PositiveCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.exists_positiveCompacts_closure_subset [R1Space α] [LocallyCompactSpace α]
    {U : Set α} (ho : IsOpen U) (hn : U.Nonempty) : ∃ K : PositiveCompacts α, closure ↑K ⊆ U :=
  let ⟨K, hKU⟩ := exists_positiveCompacts_subset ho hn
  ⟨K, K.isCompact.closure_subset_of_isOpen ho hKU⟩
/-
**TopologicalSpace.PositiveCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.PositiveCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace α] [Nonempty α] : Inhabited (PositiveCompacts α) :=
  ⟨⊤⟩

/-- In a nonempty locally compact space, there exists a compact set with nonempty interior. -/
/-
**TopologicalSpace.PositiveCompacts.nonempty'** 是 Mathlib 中的一个实例，位于命名空间 `Topolog
icalSpace.PositiveCompacts`。
形式化陈述：nonempty' [WeaklyLocallyCompactSpace α] [Nonempty α] : Nonempty (PositiveC
ompacts α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x

--- 原说明 ---
In a nonempty locally compact space, there exists a compact set with nonempty in
terior.
-/
instance nonempty' [WeaklyLocallyCompactSpace α] [Nonempty α] : Nonempty (PositiveCompacts α) := by
  inhabit α
  rcases exists_compact_mem_nhds (default : α) with ⟨K, hKc, hK⟩
  exact ⟨⟨K, hKc⟩, _, mem_interior_iff_mem_nhds.2 hK⟩

/-- The product of two `TopologicalSpace.PositiveCompacts`, as a `TopologicalSpace.PositiveCompacts`
in the product space. -/
/-
**TopologicalSpace.PositiveCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.PositiveCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two `TopologicalSpace.PositiveCompacts`, as a `TopologicalSpace.P
ositiveCompacts`
in the product space.
-/
instance : SProd (PositiveCompacts α) (PositiveCompacts β) (PositiveCompacts (α × β)) where
  sprod K L :=
    { toCompacts := K.toCompacts ×ˢ L.toCompacts
      interior_nonempty' := by
        simp only [Compacts.carrier_eq_coe, Compacts.coe_prod, interior_prod_eq]
        exact K.interior_nonempty.prod L.interior_nonempty }

@[simp]
/-
**TopologicalSpace.PositiveCompacts.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace.PositiveCompacts`。
形式化陈述：coe_prod (K : PositiveCompacts α) (L : PositiveCompacts β) : (K ×ˢ L : Pos
itiveCompacts (α × β)) = (K : Set α) ×ˢ (L : Set β)
参数：K : PositiveCompacts α；L : PositiveCompacts β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (K : PositiveCompacts α) (L : PositiveCompacts β) :
    (K ×ˢ L : PositiveCompacts (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

end PositiveCompacts

/-! ### Compact open sets -/

/-- The type of compact open sets of a topological space. This is useful in non-Hausdorff contexts,
in particular spectral spaces. -/
/-
**TopologicalSpace.CompactOpens** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopologicalSpace`。
形式化陈述：(α : Type u_4) → [TopologicalSpace α] → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of compact open sets of a topological space. This is useful in non-Haus
dorff contexts,
in particular spectral spaces.
-/
structure CompactOpens (α : Type*) [TopologicalSpace α] extends Compacts α where
  isOpen' : IsOpen carrier

namespace CompactOpens

/-
**TopologicalSpace.CompactOpens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Com
pactOpens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (CompactOpens α) α where
  coe s := s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr
/-
**TopologicalSpace.CompactOpens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Com
pactOpens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (CompactOpens α) := .ofSetLike (CompactOpens α) α

/-- See Note [custom simps projection]. -/
/-
**TopologicalSpace.CompactOpens.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `Topological
Space.CompactOpens.Simps`。
形式化陈述：{α : Type u_1} → [inst : TopologicalSpace α] → TopologicalSpace.CompactOpe
ns α → Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.coe (s : CompactOpens α) : Set α := s

initialize_simps_projections CompactOpens (carrier → coe, as_prefix coe, as_prefix toCompacts)
/-
**TopologicalSpace.CompactOpens.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.CompactOpens`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] (s : TopologicalSpace.Compact
Opens α), IsCompact ↑s
参数：s : TopologicalSpace.CompactOpens α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
-/
protected theorem isCompact (s : CompactOpens α) : IsCompact (s : Set α) :=
  s.isCompact'
/-
**TopologicalSpace.CompactOpens.isOpen** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpa
ce.CompactOpens`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] (s : TopologicalSpace.Compact
Opens α), IsOpen ↑s
参数：s : TopologicalSpace.CompactOpens α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.CompactOpens.isOpen'`：∀ {α : Type u_4} [inst : Topologi
calSpace α] (self : TopologicalSpace.CompactOpens α), IsOpen self.carrier
-/
protected theorem isOpen (s : CompactOpens α) : IsOpen (s : Set α) :=
  s.isOpen'

/-- Reinterpret a compact open as an open. -/
@[simps]
/-
**TopologicalSpace.CompactOpens.toOpens** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSp
ace.CompactOpens`。
形式化陈述：toOpens (s : CompactOpens α) : Opens α
参数：s : CompactOpens α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.CompactOpens.isOpen`：∀ {α : Type u_1} [inst : Topologic
alSpace α] (s : TopologicalSpace.CompactOpens α), IsOpen ↑s

--- 原说明 ---
Reinterpret a compact open as an open.
-/
def toOpens (s : CompactOpens α) : Opens α := ⟨s, s.isOpen⟩

/-- Reinterpret a compact open as a clopen. -/
@[simps]
/-
**TopologicalSpace.CompactOpens.toClopens** 是 Mathlib 中的一个定义，位于命名空间 `Topological
Space.CompactOpens`。
形式化陈述：toClopens [T2Space α] (s : CompactOpens α) : Clopens α
参数：s : CompactOpens α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a compact open as a clopen.
-/
def toClopens [T2Space α] (s : CompactOpens α) : Clopens α :=
  ⟨s, s.isCompact.isClosed, s.isOpen⟩

@[ext]
/-
**TopologicalSpace.CompactOpens.ext** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
CompactOpens`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {s t : TopologicalSpace.Compa
ctOpens α}, ↑s = ↑t → s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
-/
protected theorem ext {s t : CompactOpens α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/-
**TopologicalSpace.CompactOpens.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpa
ce.CompactOpens`。
形式化陈述：coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s
参数：s : Compacts α；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl
/-
**TopologicalSpace.CompactOpens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Com
pactOpens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (CompactOpens α) :=
  ⟨fun s t => ⟨s.toCompacts ⊔ t.toCompacts, s.isOpen.union t.isOpen⟩⟩
/-
**TopologicalSpace.CompactOpens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Com
pactOpens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (CompactOpens α) where bot := ⟨⊥, isOpen_empty⟩
/-
**TopologicalSpace.CompactOpens.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.CompactOpens`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] (s t : TopologicalSpace.Compa
ctOpens α), ↑(s ⊔ t) = ↑s ∪ ↑t
参数：s t : TopologicalSpace.CompactOpens α；s ⊔ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_sup (s t : CompactOpens α) : ↑(s ⊔ t) = (s ∪ t : Set α) := rfl
/-
**TopologicalSpace.CompactOpens.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.CompactOpens`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α], ↑⊥ = ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_bot : ↑(⊥ : CompactOpens α) = (∅ : Set α) := rfl
/-
**TopologicalSpace.CompactOpens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Com
pactOpens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (CompactOpens α) :=
  fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup
/-
**TopologicalSpace.CompactOpens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Com
pactOpens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (CompactOpens α) :=
  fast_instance% OrderBot.lift ((↑) : _ → Set α) (fun _ _ => id) coe_bot

@[simp]
/-
**TopologicalSpace.CompactOpens.coe_finsetSup** 是 Mathlib 中的一个引理，位于命名空间 `Topolog
icalSpace.CompactOpens`。
形式化陈述：coe_finsetSup {ι : Type*} {f : ι -> CompactOpens α} {s : Finset ι} : (↑(s.
sup f) : Set α) = ⋃ i in s, f i
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
lemma coe_finsetSup {ι : Type*} {f : ι → CompactOpens α} {s : Finset ι} :
    (↑(s.sup f) : Set α) = ⋃ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on <;> simp [*]
/-
**TopologicalSpace.CompactOpens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Com
pactOpens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (CompactOpens α) :=
  ⟨⊥⟩

section Inf
variable [QuasiSeparatedSpace α]

/-
**TopologicalSpace.CompactOpens.instInf** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSp
ace.CompactOpens`。
形式化陈述：instInf : Min (CompactOpens α) where min U V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInf : Min (CompactOpens α) where
  min U V :=
    ⟨⟨U ∩ V, QuasiSeparatedSpace.inter_isCompact U.1.1 V.1.1 U.2 U.1.2 V.2 V.1.2⟩, U.2.inter V.2⟩
/-
**TopologicalSpace.CompactOpens.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.CompactOpens`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : QuasiSeparatedSpace
 α] (s t : TopologicalSpace.CompactOpens α),   ↑(s ⊓ t) = ↑s ∩ ↑t
参数：s t : TopologicalSpace.CompactOpens α；s ⊓ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inf (s t : CompactOpens α) : ↑(s ⊓ t) = (s ∩ t : Set α) := rfl
/-
**TopologicalSpace.CompactOpens.instSemilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `To
pologicalSpace.CompactOpens`。
形式化陈述：instSemilatticeInf : SemilatticeInf (CompactOpens α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeInf : SemilatticeInf (CompactOpens α) :=
  fast_instance% SetLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

end Inf

section SDiff
variable [T2Space α]

/-
**TopologicalSpace.CompactOpens.instSDiff** 是 Mathlib 中的一个实例，位于命名空间 `Topological
Space.CompactOpens`。
形式化陈述：instSDiff : SDiff (CompactOpens α) where sdiff s t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSDiff : SDiff (CompactOpens α) where
  sdiff s t := ⟨⟨s \ t, s.isCompact.diff t.isOpen⟩, s.isOpen.sdiff t.isCompact.isClosed⟩
/-
**TopologicalSpace.CompactOpens.coe_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.CompactOpens`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : T2Space α] (s t : T
opologicalSpace.CompactOpens α),   ↑(s \ t) = ↑s \ ↑t
参数：s t : TopologicalSpace.CompactOpens α；s \ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_sdiff (s t : CompactOpens α) : ↑(s \ t) = (s \ t : Set α) := rfl
/-
**TopologicalSpace.CompactOpens.instGeneralizedBooleanAlgebra** 是 Mathlib 中的一个实例
，位于命名空间 `TopologicalSpace.CompactOpens`。
形式化陈述：instGeneralizedBooleanAlgebra : GeneralizedBooleanAlgebra (CompactOpens α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instGeneralizedBooleanAlgebra : GeneralizedBooleanAlgebra (CompactOpens α) :=
  fast_instance% SetLike.coe_injective.generalizedBooleanAlgebra _
    .rfl .rfl coe_sup coe_inf coe_bot coe_sdiff

end SDiff

section Top
variable [CompactSpace α]

/-
**TopologicalSpace.CompactOpens.instTop** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSp
ace.CompactOpens`。
形式化陈述：instTop : Top (CompactOpens α) where top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
instance instTop : Top (CompactOpens α) where top := ⟨⊤, isOpen_univ⟩
/-
**TopologicalSpace.CompactOpens.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.CompactOpens`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : CompactSpace α], ↑⊤
 = Set.univ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_top : ↑(⊤ : CompactOpens α) = (univ : Set α) := rfl
/-
**TopologicalSpace.CompactOpens.instBoundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `Topo
logicalSpace.CompactOpens`。
形式化陈述：instBoundedOrder : BoundedOrder (CompactOpens α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBoundedOrder : BoundedOrder (CompactOpens α) :=
  fast_instance% BoundedOrder.lift ((↑) : _ → Set α) (fun _ _ => id) coe_top coe_bot

section Compl
variable [T2Space α]

/-
**TopologicalSpace.CompactOpens.instCompl** 是 Mathlib 中的一个实例，位于命名空间 `Topological
Space.CompactOpens`。
形式化陈述：instCompl : Compl (CompactOpens α) where compl s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCompl : Compl (CompactOpens α) where
  compl s := ⟨⟨sᶜ, s.isOpen.isClosed_compl.isCompact⟩, s.isCompact.isClosed.isOpen_compl⟩
/-
**TopologicalSpace.CompactOpens.instHImp** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalS
pace.CompactOpens`。
形式化陈述：instHImp : HImp (CompactOpens α) where himp s t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHImp : HImp (CompactOpens α) where
  himp s t := ⟨⟨s ⇨ t, IsClosed.isCompact
    (by simpa [himp_eq] using t.isCompact.isClosed.union s.isOpen.isClosed_compl)⟩,
    by simpa [himp_eq] using t.isOpen.union s.isCompact.isClosed.isOpen_compl⟩
/-
**TopologicalSpace.CompactOpens.coe_compl** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.CompactOpens`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : CompactSpace α] [in
st_2 : T2Space α]   (s : TopologicalSpace.CompactOpens α), ↑sᶜ = (↑s)ᶜ
参数：s : TopologicalSpace.CompactOpens α；↑s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_compl (s : CompactOpens α) : ↑sᶜ = (sᶜ : Set α) := rfl
/-
**TopologicalSpace.CompactOpens.coe_himp** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.CompactOpens`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : CompactSpace α] [in
st_2 : T2Space α]   (s t : TopologicalSpace.CompactOpens α), ↑(s ⇨ t) = ↑s ⇨ ↑t
参数：s t : TopologicalSpace.CompactOpens α；s ⇨ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_himp (s t : CompactOpens α) : ↑(s ⇨ t) = (s ⇨ t : Set α) := rfl
/-
**TopologicalSpace.CompactOpens.instBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `To
pologicalSpace.CompactOpens`。
形式化陈述：instBooleanAlgebra : BooleanAlgebra (CompactOpens α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBooleanAlgebra : BooleanAlgebra (CompactOpens α) :=
  fast_instance% SetLike.coe_injective.booleanAlgebra _
    .rfl .rfl coe_sup coe_inf coe_top coe_bot coe_compl coe_sdiff coe_himp

end Top.Compl

/-- The image of a compact open under a continuous open map. -/
@[simps toCompacts]
/-
**TopologicalSpace.CompactOpens.map** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.
CompactOpens`。
形式化陈述：map (f : α -> β) (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens
 α) : CompactOpens β
参数：f : α -> β；hf : Continuous f；hf' : IsOpenMap f；s : CompactOpens α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a compact open under a continuous open map.
-/
def map (f : α → β) (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α) : CompactOpens β :=
  ⟨s.toCompacts.map f hf, hf' _ s.isOpen⟩

@[simp, norm_cast]
/-
**TopologicalSpace.CompactOpens.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.CompactOpens`。
形式化陈述：coe_map {f : α -> β} (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactO
pens α) : (s.map f hf hf' : Set β) = f '' s
参数：hf : Continuous f；hf' : IsOpenMap f；s : CompactOpens α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map {f : α → β} (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α) :
    (s.map f hf hf' : Set β) = f '' s :=
  rfl

@[simp]
/-
**TopologicalSpace.CompactOpens.map_id** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpa
ce.CompactOpens`。
形式化陈述：map_id (K : CompactOpens α) : K.map id continuous_id IsOpenMap.id = K
参数：K : CompactOpens α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.CompactOpens.ext`：∀ {α : Type u_1} [inst : TopologicalS
pace α] {s t : TopologicalSpace.CompactOpens α}, ↑s = ↑t → s = t
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `IsOpenMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenMap id
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem map_id (K : CompactOpens α) : K.map id continuous_id IsOpenMap.id = K :=
  CompactOpens.ext <| Set.image_id _
/-
**TopologicalSpace.CompactOpens.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.CompactOpens`。
形式化陈述：map_comp (f : β -> γ) (g : α -> β) (hf : Continuous f) (hg : Continuous g)
 (hf' : IsOpenMap f) (hg' : IsOpenMap g) (K : CompactOpens α) : K.map (f ∘ g) (h
f.comp hg) (hf'.comp hg') = (K.map g hg hg').map f hf hf'
参数：f : β -> γ；g : α -> β；hf : Continuous f；hg : Continuous g；hf' : IsOpenMap f；h
g' : IsOpenMap g；K : CompactOpens α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.CompactOpens.ext`：∀ {α : Type u_1} [inst : TopologicalS
pace α] {s t : TopologicalSpace.CompactOpens α}, ↑s = ↑t → s = t
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
theorem map_comp (f : β → γ) (g : α → β) (hf : Continuous f) (hg : Continuous g) (hf' : IsOpenMap f)
    (hg' : IsOpenMap g) (K : CompactOpens α) :
    K.map (f ∘ g) (hf.comp hg) (hf'.comp hg') = (K.map g hg hg').map f hf hf' :=
  CompactOpens.ext <| Set.image_comp _ _ _

/-- The product of two `TopologicalSpace.CompactOpens`, as a `TopologicalSpace.CompactOpens` in the
product space. -/
/-
**TopologicalSpace.CompactOpens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Com
pactOpens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two `TopologicalSpace.CompactOpens`, as a `TopologicalSpace.Compa
ctOpens` in the
product space.
-/
instance : SProd (CompactOpens α) (CompactOpens β) (CompactOpens (α × β)) where
  sprod K L := { K.toCompacts ×ˢ L.toCompacts with isOpen' := K.isOpen.prod L.isOpen }

@[simp]
/-
**TopologicalSpace.CompactOpens.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.CompactOpens`。
形式化陈述：coe_prod (K : CompactOpens α) (L : CompactOpens β) : (K ×ˢ L : CompactOpen
s (α × β)) = (K : Set α) ×ˢ (L : Set β)
参数：K : CompactOpens α；L : CompactOpens β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (K : CompactOpens α) (L : CompactOpens β) :
    (K ×ˢ L : CompactOpens (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

end CompactOpens

end TopologicalSpace

