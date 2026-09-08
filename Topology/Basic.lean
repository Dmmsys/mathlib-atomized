/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Lattice
public import Mathlib.Topology.Defs.Filter

/-!
# Openness and closedness of a set

This file provides lemmas relating to the predicates `IsOpen` and `IsClosed` of a set endowed with
a topology.

## Implementation notes

Topology in mathlib heavily uses filters (even more than in Bourbaki). See explanations in
<https://leanprover-community.github.io/theories/topology.html>.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

## Tags

topological space
-/

@[expose] public section

open Set Filter Topology

universe u v

/-- A constructor for topologies by specifying the closed sets,
and showing that they satisfy the appropriate conditions. -/
@[instance_reducible]
/-
**TopologicalSpace.ofClosed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TopologicalSpace.ofClosed {X : Type u} (T : Set (Set X)) (empty_mem : ∅ in
 T) (sInter_mem : forall A, A subseteq T -> ⋂₀ A in T) (union_mem : forall A, A 
in T -> forall B, B in T -> A union B in T) : TopologicalSpace X where IsOpen X
参数：T : Set (Set X)；empty_mem : ∅ in T；sInter_mem : forall A, A subseteq T -> ⋂₀ 
A in T；union_mem : forall A, A in T -> forall B, B in T -> A union B in T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for topologies by specifying the closed sets,
and showing that they satisfy the appropriate conditions.
-/
def TopologicalSpace.ofClosed {X : Type u} (T : Set (Set X)) (empty_mem : ∅ ∈ T)
    (sInter_mem : ∀ A, A ⊆ T → ⋂₀ A ∈ T)
    (union_mem : ∀ A, A ∈ T → ∀ B, B ∈ T → A ∪ B ∈ T) : TopologicalSpace X where
  IsOpen X := Xᶜ ∈ T
  isOpen_univ := by simp [empty_mem]
  isOpen_inter s t hs ht := by simpa only [compl_inter] using union_mem sᶜ hs tᶜ ht
  isOpen_sUnion s hs := by
    simp only [Set.compl_sUnion]
    exact sInter_mem (compl '' s) fun z ⟨y, hy, hz⟩ => hz ▸ hs y hy

section TopologicalSpace

variable {X : Type u} {ι : Sort v} {α : Type*} {x : X} {s s₁ s₂ t : Set X} {p p₁ p₂ : X → Prop}

/-
**isOpen_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOpen_mk {p h₁ h₂ h₃} : IsOpen[⟨p, h₁, h₂, h₃⟩] s ↔ p s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isOpen_mk {p h₁ h₂ h₃} : IsOpen[⟨p, h₁, h₂, h₃⟩] s ↔ p s := Iff.rfl

@[ext (iff := false)]
/-
**TopologicalSpace.ext** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace`。
形式化陈述：∀ {X : Type u} {f g : TopologicalSpace X}, IsOpen = IsOpen → f = g
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem TopologicalSpace.ext :
    ∀ {f g : TopologicalSpace X}, IsOpen[f] = IsOpen[g] → f = g
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl
/-
**TopologicalSpace.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace`。
形式化陈述：∀ {X : Type u} {t t' : TopologicalSpace X}, t = t' ↔ ∀ (s : Set X), IsOpen
 s ↔ IsOpen s
参数：s : Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `TopologicalSpace.ext`：∀ {X : Type u} {f g : TopologicalSpace X}, IsOpen 
= IsOpen → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem TopologicalSpace.ext_iff {t t' : TopologicalSpace X} :
    t = t' ↔ ∀ s, IsOpen[t] s ↔ IsOpen[t'] s :=
  ⟨fun h _ => h ▸ Iff.rfl, fun h => by ext; exact h _⟩
/-
**isOpen_fold** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_fold {t : TopologicalSpace X} : t.IsOpen s = IsOpen[t] s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isOpen_fold {t : TopologicalSpace X} : t.IsOpen s = IsOpen[t] s :=
  rfl

variable [TopologicalSpace X]
/-
**isOpen_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i)) : IsOpen (⋃ i,
 f i)
参数：h : forall i, IsOpen (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_sUnion`：isOpen_sUnion {s : Set (Set X)} (h : forall t in s, IsOpe
n t) : IsOpen (⋃₀ s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem isOpen_iUnion {f : ι → Set X} (h : ∀ i, IsOpen (f i)) : IsOpen (⋃ i, f i) :=
  isOpen_sUnion (forall_mem_range.2 h)
/-
**isOpen_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall i in s, IsOpen (f 
i)) : IsOpen (⋃ i in s, f i)
参数：h : forall i in s, IsOpen (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
-/
theorem isOpen_biUnion {s : Set α} {f : α → Set X} (h : ∀ i ∈ s, IsOpen (f i)) :
    IsOpen (⋃ i ∈ s, f i) :=
  isOpen_iUnion fun i => isOpen_iUnion fun hi => h i hi
/-
**IsOpen.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s₁ union s₂)
参数：h₁ : IsOpen s₁；h₂ : IsOpen s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bool.forall_bool`：∀ {p : Bool → Prop}, (∀ (b : Bool), p b) ↔ p false ∧ p
 true
-/
theorem IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s₁ ∪ s₂) := by
  rw [union_eq_iUnion]; exact isOpen_iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)
/-
**isOpen_iff_of_cover** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOpen_iff_of_cover {f : α -> Set X} (ho : forall i, IsOpen (f i)) (hU : (
⋃ i, f i) = univ) : IsOpen s ↔ forall i, IsOpen (f i inter s)
参数：ho : forall i, IsOpen (f i)；hU : (⋃ i, f i) = univ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
-/
lemma isOpen_iff_of_cover {f : α → Set X} (ho : ∀ i, IsOpen (f i)) (hU : (⋃ i, f i) = univ) :
    IsOpen s ↔ ∀ i, IsOpen (f i ∩ s) := by
  refine ⟨fun h i ↦ (ho i).inter h, fun h ↦ ?_⟩
  rw [← s.inter_univ, inter_comm, ← hU, iUnion_inter]
  exact isOpen_iUnion fun i ↦ h i
/-
**isOpen_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_empty`：sUnion_empty : ⋃₀ ∅ = (∅ : Set α)
· 使用定理 `isOpen_sUnion`：isOpen_sUnion {s : Set (Set X)} (h : forall t in s, IsOpe
n t) : IsOpen (⋃₀ s)
-/
@[simp] theorem isOpen_empty : IsOpen (∅ : Set X) := by
  rw [← sUnion_empty]; exact isOpen_sUnion fun a => False.elim
/-
**Set.Finite.isOpen_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isOpen_sInter {s : Set (Set X)} (hs : s.Finite) (h : forall t i
n s, IsOpen t) : IsOpen (⋂₀ s)
参数：Set X；hs : s.Finite；h : forall t in s, IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_empty`：sInter_empty : ⋂₀ ∅ = (univ : Set α)
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Set.sInter_insert`：sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ inse
rt s T = s inter ⋂₀ T
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Set.Finite.isOpen_sInter {s : Set (Set X)} (hs : s.Finite) (h : ∀ t ∈ s, IsOpen t) :
    IsOpen (⋂₀ s) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => rw [sInter_empty]; exact isOpen_univ
  | insert _ _ ih =>
    simp only [sInter_insert, forall_mem_insert] at h ⊢
    exact h.1.inter (ih h.2)
/-
**Set.Finite.isOpen_biInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isOpen_biInter {s : Set α} {f : α -> Set X} (hs : s.Finite) (h 
: forall i in s, IsOpen (f i)) : IsOpen (⋂ i in s, f i)
参数：hs : s.Finite；h : forall i in s, IsOpen (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isOpen_sInter`：Set.Finite.isOpen_sInter {s : Set (Set X)} (hs
 : s.Finite) (h : forall t in s, IsOpen t) : IsOpen (⋂₀ s)
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
-/
theorem Set.Finite.isOpen_biInter {s : Set α} {f : α → Set X} (hs : s.Finite)
    (h : ∀ i ∈ s, IsOpen (f i)) :
    IsOpen (⋂ i ∈ s, f i) :=
  sInter_image f s ▸ (hs.image _).isOpen_sInter (forall_mem_image.2 h)
/-
**isOpen_iInter_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_iInter_of_finite [Finite ι] {s : ι -> Set X} (h : forall i, IsOpen 
(s i)) : IsOpen (⋂ i, s i)
参数：h : forall i, IsOpen (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isOpen_sInter`：Set.Finite.isOpen_sInter {s : Set (Set X)} (hs
 : s.Finite) (h : forall t in s, IsOpen t) : IsOpen (⋂₀ s)
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem isOpen_iInter_of_finite [Finite ι] {s : ι → Set X} (h : ∀ i, IsOpen (s i)) :
    IsOpen (⋂ i, s i) :=
  (finite_range _).isOpen_sInter (forall_mem_range.2 h)
/-
**isOpen_biInter_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_biInter_finset {s : Finset α} {f : α -> Set X} (h : forall i in s, 
IsOpen (f i)) : IsOpen (⋂ i in s, f i)
参数：h : forall i in s, IsOpen (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isOpen_biInter`：Set.Finite.isOpen_biInter {s : Set α} {f : α 
-> Set X} (hs : s.Finite) (h : forall i in s, IsOpen (f i)) : IsOpen (⋂ i in s, 
f i)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem isOpen_biInter_finset {s : Finset α} {f : α → Set X} (h : ∀ i ∈ s, IsOpen (f i)) :
    IsOpen (⋂ i ∈ s, f i) :=
  s.finite_toSet.isOpen_biInter h

@[simp]
/-
**isOpen_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_const {p : Prop} : IsOpen { _x : X | p }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem isOpen_const {p : Prop} : IsOpen { _x : X | p } := by by_cases p <;> simp [*]
/-
**IsOpen.and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.and : IsOpen { x | p₁ x } -> IsOpen { x | p₂ x } -> IsOpen { x | p₁
 x ∧ p₂ x }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
-/
theorem IsOpen.and : IsOpen { x | p₁ x } → IsOpen { x | p₂ x } → IsOpen { x | p₁ x ∧ p₂ x } :=
  IsOpen.inter
/-
**isOpen_compl_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X], IsOpen sᶜ ↔ IsClos
ed s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
-/
@[simp] theorem isOpen_compl_iff : IsOpen sᶜ ↔ IsClosed s :=
  ⟨fun h => ⟨h⟩, fun h => h.isOpen_compl⟩
/-
**TopologicalSpace.ext_iff_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TopologicalSpace.ext_iff_isClosed {X} {t₁ t₂ : TopologicalSpace X} : t₁ = 
t₂ ↔ forall s, IsClosed[t₁] s ↔ IsClosed[t₂] s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.ext_iff`：∀ {X : Type u} {t t' : TopologicalSpace X}, t 
= t' ↔ ∀ (s : Set X), IsOpen s ↔ IsOpen s
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem TopologicalSpace.ext_iff_isClosed {X} {t₁ t₂ : TopologicalSpace X} :
    t₁ = t₂ ↔ ∀ s, IsClosed[t₁] s ↔ IsClosed[t₂] s := by
  rw [TopologicalSpace.ext_iff, compl_surjective.forall]
  simp only [@isOpen_compl_iff _ _ t₁, @isOpen_compl_iff _ _ t₂]

alias ⟨_, TopologicalSpace.ext_isClosed⟩ := TopologicalSpace.ext_iff_isClosed
/-
**isClosed_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_const {p : Prop} : IsClosed { _x : X | p }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_const`：isOpen_const {p : Prop} : IsOpen { _x : X | p }
-/
theorem isClosed_const {p : Prop} : IsClosed { _x : X | p } := ⟨isOpen_const (p := ¬p)⟩

@[simp, closedness ., grind .]
/-
**isClosed_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_empty : IsClosed (∅ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_const`：isClosed_const {p : Prop} : IsClosed { _x : X | p }
-/
theorem isClosed_empty : IsClosed (∅ : Set X) := isClosed_const

@[simp, closedness ., grind .]
/-
**isClosed_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_univ : IsClosed (univ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_const`：isClosed_const {p : Prop} : IsClosed { _x : X | p }
-/
theorem isClosed_univ : IsClosed (univ : Set X) := isClosed_const

@[closedness .]
/-
**IsOpen.isLocallyClosed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocallyClosed s
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
lemma IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocallyClosed s :=
  ⟨_, _, hs, isClosed_univ, (inter_univ _).symm⟩

@[closedness .]
/-
**IsClosed.isLocallyClosed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.isLocallyClosed (hs : IsClosed s) : IsLocallyClosed s
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
lemma IsClosed.isLocallyClosed (hs : IsClosed s) : IsLocallyClosed s :=
  ⟨_, _, isOpen_univ, hs, (univ_inter _).symm⟩

@[closedness .]
/-
**IsClosed.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.union : IsClosed s₁ -> IsClosed s₂ -> IsClosed (s₁ union s₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
-/
theorem IsClosed.union : IsClosed s₁ → IsClosed s₂ → IsClosed (s₁ ∪ s₂) := by
  simpa only [← isOpen_compl_iff, compl_union] using IsOpen.inter

@[closedness .]
/-
**isClosed_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_sInter {s : Set (Set X)} : (forall t in s, IsClosed t) -> IsClose
d (⋂₀ s)
参数：Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_sInter`：compl_sInter (S : Set (Set α)) : (⋂₀ S)ᶜ = ⋃₀ (compl '
' S)
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
-/
theorem isClosed_sInter {s : Set (Set X)} : (∀ t ∈ s, IsClosed t) → IsClosed (⋂₀ s) := by
  simpa only [← isOpen_compl_iff, compl_sInter, sUnion_image] using isOpen_biUnion

@[closedness .]
/-
**isClosed_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClosed (f i)) : IsClosed
 (⋂ i, f i)
参数：h : forall i, IsClosed (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_sInter`：isClosed_sInter {s : Set (Set X)} : (forall t in s, IsC
losed t) -> IsClosed (⋂₀ s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem isClosed_iInter {f : ι → Set X} (h : ∀ i, IsClosed (f i)) : IsClosed (⋂ i, f i) :=
  isClosed_sInter <| forall_mem_range.2 h
/-
**isClosed_biInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_biInter {s : Set α} {f : α -> Set X} (h : forall i in s, IsClosed
 (f i)) : IsClosed (⋂ i in s, f i)
参数：h : forall i in s, IsClosed (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
-/
theorem isClosed_biInter {s : Set α} {f : α → Set X} (h : ∀ i ∈ s, IsClosed (f i)) :
    IsClosed (⋂ i ∈ s, f i) :=
  isClosed_iInter fun i => isClosed_iInter <| h i

@[simp]
/-
**isClosed_compl_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpen s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpen s := by
  rw [← isOpen_compl_iff, compl_compl]

alias ⟨_, IsOpen.isClosed_compl⟩ := isClosed_compl_iff
/-
**IsOpen.sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.sdiff (h₁ : IsOpen s) (h₂ : IsClosed t) : IsOpen (s \ t)
参数：h₁ : IsOpen s；h₂ : IsClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
-/
theorem IsOpen.sdiff (h₁ : IsOpen s) (h₂ : IsClosed t) : IsOpen (s \ t) :=
  IsOpen.inter h₁ h₂.isOpen_compl

@[closedness .]
/-
**IsClosed.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : IsClosed (s₁ inter 
s₂)
参数：h₁ : IsClosed s₁；h₂ : IsClosed s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
-/
theorem IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : IsClosed (s₁ ∩ s₂) := by
  rw [← isOpen_compl_iff] at *
  rw [compl_inter]
  exact IsOpen.union h₁ h₂

@[closedness .]
/-
**IsClosed.sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.sdiff (h₁ : IsClosed s) (h₂ : IsOpen t) : IsClosed (s \ t)
参数：h₁ : IsClosed s；h₂ : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
-/
theorem IsClosed.sdiff (h₁ : IsClosed s) (h₂ : IsOpen t) : IsClosed (s \ t) :=
  IsClosed.inter h₁ (isClosed_compl_iff.mpr h₂)
/-
**Set.Finite.isClosed_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isClosed_biUnion {s : Set α} {f : α -> Set X} (hs : s.Finite) (
h : forall i in s, IsClosed (f i)) : IsClosed (⋃ i in s, f i)
参数：hs : s.Finite；h : forall i in s, IsClosed (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Finite.isOpen_biInter`：Set.Finite.isOpen_biInter {s : Set α} {f : α 
-> Set X} (hs : s.Finite) (h : forall i in s, IsOpen (f i)) : IsOpen (⋂ i in s, 
f i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem Set.Finite.isClosed_biUnion {s : Set α} {f : α → Set X} (hs : s.Finite)
    (h : ∀ i ∈ s, IsClosed (f i)) :
    IsClosed (⋃ i ∈ s, f i) := by
  simp only [← isOpen_compl_iff, compl_iUnion] at *
  exact hs.isOpen_biInter h
/-
**isClosed_biUnion_finset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_biUnion_finset {s : Finset α} {f : α -> Set X} (h : forall i in s
, IsClosed (f i)) : IsClosed (⋃ i in s, f i)
参数：h : forall i in s, IsClosed (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isClosed_biUnion`：Set.Finite.isClosed_biUnion {s : Set α} {f 
: α -> Set X} (hs : s.Finite) (h : forall i in s, IsClosed (f i)) : IsClosed (⋃ 
i in s, f i)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
lemma isClosed_biUnion_finset {s : Finset α} {f : α → Set X} (h : ∀ i ∈ s, IsClosed (f i)) :
    IsClosed (⋃ i ∈ s, f i) :=
  s.finite_toSet.isClosed_biUnion h

@[closedness .]
/-
**isClosed_iUnion_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_iUnion_of_finite [Finite ι] {s : ι -> Set X} (h : forall i, IsClo
sed (s i)) : IsClosed (⋃ i, s i)
参数：h : forall i, IsClosed (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `isOpen_iInter_of_finite`：isOpen_iInter_of_finite [Finite ι] {s : ι -> Se
t X} (h : forall i, IsOpen (s i)) : IsOpen (⋂ i, s i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem isClosed_iUnion_of_finite [Finite ι] {s : ι → Set X} (h : ∀ i, IsClosed (s i)) :
    IsClosed (⋃ i, s i) := by
  simp only [← isOpen_compl_iff, compl_iUnion] at *
  exact isOpen_iInter_of_finite h

@[closedness .]
/-
**isClosed_imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_imp {p q : X -> Prop} (hp : IsOpen { x | p x }) (hq : IsClosed { 
x | q x }) : IsClosed { x | p x -> q x }
参数：hp : IsOpen { x | p x }；hq : IsClosed { x | q x }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsClosed.union`：IsClosed.union : IsClosed s₁ -> IsClosed s₂ -> IsClosed 
(s₁ union s₂)
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
-/
theorem isClosed_imp {p q : X → Prop} (hp : IsOpen { x | p x }) (hq : IsClosed { x | q x }) :
    IsClosed { x | p x → q x } := by
  simpa only [imp_iff_not_or] using! hp.isClosed_compl.union hq
/-
**IsClosed.not** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.not : IsClosed { a | p a } -> IsOpen { a | ¬p a }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
-/
theorem IsClosed.not : IsClosed { a | p a } → IsOpen { a | ¬p a } :=
  isOpen_compl_iff.mpr

@[closedness .]
/-
**IsClosed.and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.and : IsClosed { x | p₁ x } -> IsClosed { x | p₂ x } -> IsClosed 
{ x | p₁ x ∧ p₂ x }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
-/
theorem IsClosed.and :
    IsClosed { x | p₁ x } → IsClosed { x | p₂ x } → IsClosed { x | p₁ x ∧ p₂ x } :=
  IsClosed.inter

/-!
### Limits of filters in topological spaces

In this section we define functions that return a limit of a filter (or of a function along a
filter), if it exists, and a random point otherwise. These functions are rarely used in Mathlib,
most of the theorems are written using `Filter.Tendsto`. One of the reasons is that
`Filter.limUnder f g = x` is not equivalent to `Filter.Tendsto g f (𝓝 x)` unless the codomain is a
Hausdorff space and `g` has a limit along `f`.
-/

section lim

/-- If a filter `f` is majorated by some `𝓝 x`, then it is majorated by `𝓝 (Filter.lim f)`. We
formulate this lemma with a `[Nonempty X]` argument of `lim` derived from `h` to make it useful for
types without a `[Nonempty X]` instance. Because of the built-in proof irrelevance, Lean will unify
this instance with any other instance. -/
/-
**le_nhds_lim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_nhds_lim {f : Filter X} (h : exists x, f <= 𝓝 x) : f <= 𝓝 (@lim _ _ h.n
onempty f)
参数：h : exists x, f <= 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.epsilon_spec`：∀ {α : Sort u} {p : α → Prop} (hex : ∃ y, p y), 
p (Classical.epsilon p)

--- 原说明 ---
If a filter `f` is majorated by some `𝓝 x`, then it is majorated by `𝓝 (Filter.l
im f)`. We
formulate this lemma with a `[Nonempty X]` argument of `lim` derived from `h` to
 make it useful for
types without a `[Nonempty X]` instance. Because of the built-in proof irrelevan
ce, Lean will unify
this instance with any other instance.
-/
theorem le_nhds_lim {f : Filter X} (h : ∃ x, f ≤ 𝓝 x) : f ≤ 𝓝 (@lim _ _ h.nonempty f) :=
  Classical.epsilon_spec h

/-- If `g` tends to some `𝓝 x` along `f`, then it tends to `𝓝 (Filter.limUnder f g)`. We formulate
this lemma with a `[Nonempty X]` argument of `lim` derived from `h` to make it useful for types
without a `[Nonempty X]` instance. Because of the built-in proof irrelevance, Lean will unify this
/-
**with** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance with any other instance. -/
/-
**tendsto_nhds_limUnder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhds_limUnder {f : Filter α} {g : α -> X} (h : exists x, Tendsto g
 f (𝓝 x)) : Tendsto g f (𝓝 (@limUnder _ _ _ h.nonempty f g))
参数：h : exists x, Tendsto g f (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_nhds_lim`：le_nhds_lim {f : Filter X} (h : exists x, f <= 𝓝 x) : f <= 
𝓝 (@lim _ _ h.nonempty f)

--- 原说明 ---
If `g` tends to some `𝓝 x` along `f`, then it tends to `𝓝 (Filter.limUnder f g)`
. We formulate
this lemma with a `[Nonempty X]` argument of `lim` derived from `h` to make it u
seful for types
without a `[Nonempty X]` instance. Because of the built-in proof irrelevance, Le
an will unify this
instance with any other instance.
-/
theorem tendsto_nhds_limUnder {f : Filter α} {g : α → X} (h : ∃ x, Tendsto g f (𝓝 x)) :
    Tendsto g f (𝓝 (@limUnder _ _ _ h.nonempty f g)) :=
  le_nhds_lim h
/-
**limUnder_of_not_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：limUnder_of_not_tendsto [hX : Nonempty X] {f : Filter α} {g : α -> X} (h :
 ¬ exists x, Tendsto g f (𝓝 x)) : limUnder f g = Classical.choice hX
参数：h : ¬ exists x, Tendsto g f (𝓝 x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem limUnder_of_not_tendsto [hX : Nonempty X] {f : Filter α} {g : α → X}
    (h : ¬ ∃ x, Tendsto g f (𝓝 x)) :
    limUnder f g = Classical.choice hX := by
  simp_rw [Tendsto] at h
  simp_rw [limUnder, lim, Classical.epsilon, Classical.strongIndefiniteDescription, dif_neg h]

end lim

end TopologicalSpace

