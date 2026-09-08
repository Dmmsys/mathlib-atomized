/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Compactness.NhdsKer

/-!
# Alexandrov-discrete topological spaces

This file defines Alexandrov-discrete spaces, aka finitely generated spaces.

A space is Alexandrov-discrete if the (arbitrary) intersection of open sets is open. As such,
the intersection of all neighborhoods of a set is a neighborhood itself. Hence every set has a
minimal neighborhood, which we call the *neighborhoods kernel* of the set.

## Main declarations

* `AlexandrovDiscrete`: Prop-valued typeclass for a topological space to be Alexandrov-discrete

## Tags

Alexandroff, discrete, finitely generated, fg space
-/

public section

open Filter Set TopologicalSpace Topology

/-- A topological space is **Alexandrov-discrete** or **finitely generated** if the intersection of
a family of open sets is open. -/
@[mk_iff]
/-
**AlexandrovDiscrete** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is **Alexandrov-discrete** or **finitely generated** if the 
intersection of
a family of open sets is open.
-/
class AlexandrovDiscrete (α : Type*) [TopologicalSpace α] : Prop where
  /-- The intersection of a family of open sets is an open set. Use `isOpen_sInter` in the root
  namespace instead. -/
  protected isOpen_sInter : ∀ S : Set (Set α), (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S)

variable {ι : Sort*} {κ : ι → Sort*} {α β : Type*}
section
variable [TopologicalSpace α] [TopologicalSpace β]

/-
**alexandrovDiscrete_iff_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α],   AlexandrovDiscrete α ↔ ∀ (
S : Set (Set α)), (∀ s ∈ S, IsClosed s) → IsClosed (⋃₀ S)
参数：S : Set (Set α)；∀ s ∈ S, IsClosed s；⋃₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Function.Surjective.image_surjective`：∀ {α : Type u_1} {β : Type u_2} {f
 : α → β}, Function.Surjective f → Function.Surjective (Set.image f)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma alexandrovDiscrete_iff_isClosed :
    AlexandrovDiscrete α ↔ ∀ S : Set (Set α), (∀ s ∈ S, IsClosed s) → IsClosed (⋃₀ S) := by
  conv_lhs => tactic =>
    simp_rw +singlePass [alexandrovDiscrete_iff, compl_surjective.image_surjective.forall,
      forall_mem_image, ← compl_sUnion, isOpen_compl_iff]
/-
**IndiscreteTopology.toAlexandrovDiscrete** 是 Mathlib 中的一个实例，位于命名空间 `instead.`。
形式化陈述：IndiscreteTopology.toAlexandrovDiscrete [IndiscreteTopology α] : Alexandro
vDiscrete α where isOpen_sInter
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IndiscreteTopology.toAlexandrovDiscrete [IndiscreteTopology α] : AlexandrovDiscrete α where
  isOpen_sInter := by grind [isOpen_iff]
/-
**DiscreteTopology.toAlexandrovDiscrete** 是 Mathlib 中的一个实例，位于命名空间 `instead.`。
形式化陈述：DiscreteTopology.toAlexandrovDiscrete [DiscreteTopology α] : AlexandrovDis
crete α where isOpen_sInter _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
-/
instance DiscreteTopology.toAlexandrovDiscrete [DiscreteTopology α] : AlexandrovDiscrete α where
  isOpen_sInter _ _ := isOpen_discrete _
/-
**Finite.toAlexandrovDiscrete** 是 Mathlib 中的一个实例，位于命名空间 `instead.`。
形式化陈述：Finite.toAlexandrovDiscrete [Finite α] : AlexandrovDiscrete α where isOpen
_sInter S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isOpen_sInter`：Set.Finite.isOpen_sInter {s : Set (Set X)} (hs
 : s.Finite) (h : forall t in s, IsOpen t) : IsOpen (⋂₀ s)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
instance Finite.toAlexandrovDiscrete [Finite α] : AlexandrovDiscrete α where
  isOpen_sInter S := (toFinite S).isOpen_sInter

section AlexandrovDiscrete
variable [AlexandrovDiscrete α] {S : Set (Set α)} {f : ι → Set α}

/-
**isOpen_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {S : S
et (Set α)},   (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S)
参数：Set α；∀ s ∈ S, IsOpen s；⋂₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlexandrovDiscrete.isOpen_sInter`：∀ {α : Type u_1} {inst : TopologicalSp
ace α} [self : AlexandrovDiscrete α] (S : Set (Set α)),   (∀ s ∈ S, IsOpen s) → 
IsOpen (⋂₀ S)
-/
lemma isOpen_sInter : (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S) := AlexandrovDiscrete.isOpen_sInter _
/-
**isOpen_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] {f : ι → Set α},   (∀ (i : ι), IsOpen (f i)) → IsOpen (⋂ i, f i)
参数：∀ (i : ι), IsOpen (f i)；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_sInter`：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovD
iscrete α] {S : Set (Set α)},   (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
lemma isOpen_iInter (hf : ∀ i, IsOpen (f i)) : IsOpen (⋂ i, f i) :=
  isOpen_sInter <| forall_mem_range.2 hf
/-
**isOpen_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] {f : ι → Set α},   (∀ (i : ι), IsOpen (f i)) → IsOpen (⋂ i, f i)
参数：∀ (i : ι), IsOpen (f i)；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_sInter`：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovD
iscrete α] {S : Set (Set α)},   (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
lemma isOpen_iInter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsOpen (f i j)) :
    IsOpen (⋂ i, ⋂ j, f i j) :=
  isOpen_iInter fun _ ↦ isOpen_iInter <| hf _
/-
**isClosed_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {S : S
et (Set α)},   (∀ s ∈ S, IsClosed s) → IsClosed (⋃₀ S)
参数：Set α；∀ s ∈ S, IsClosed s；⋃₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `alexandrovDiscrete_iff_isClosed`：∀ {α : Type u_3} [inst : TopologicalSpa
ce α],   AlexandrovDiscrete α ↔ ∀ (S : Set (Set α)), (∀ s ∈ S, IsClosed s) → IsC
losed (⋃₀ S)
-/
lemma isClosed_sUnion (hS : ∀ s ∈ S, IsClosed s) : IsClosed (⋃₀ S) :=
  alexandrovDiscrete_iff_isClosed.mp inferInstance S hS
/-
**isClosed_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] {f : ι → Set α},   (∀ (i : ι), IsClosed (f i)) → IsClosed (⋃ i, f i)
参数：∀ (i : ι), IsClosed (f i)；⋃ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_sUnion`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Alexandro
vDiscrete α] {S : Set (Set α)},   (∀ s ∈ S, IsClosed s) → IsClosed (⋃₀ S)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
lemma isClosed_iUnion (hf : ∀ i, IsClosed (f i)) : IsClosed (⋃ i, f i) :=
  isClosed_sUnion <| forall_mem_range.2 hf
/-
**isClosed_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] {f : ι → Set α},   (∀ (i : ι), IsClosed (f i)) → IsClosed (⋃ i, f i)
参数：∀ (i : ι), IsClosed (f i)；⋃ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_sUnion`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Alexandro
vDiscrete α] {S : Set (Set α)},   (∀ s ∈ S, IsClosed s) → IsClosed (⋃₀ S)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
lemma isClosed_iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsClosed (f i j)) :
    IsClosed (⋃ i, ⋃ j, f i j) :=
  isClosed_iUnion fun _ ↦ isClosed_iUnion <| hf _
/-
**isClopen_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {S : S
et (Set α)},   (∀ s ∈ S, IsClopen s) → IsClopen (⋂₀ S)
参数：Set α；∀ s ∈ S, IsClopen s；⋂₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_sInter`：isClosed_sInter {s : Set (Set X)} : (forall t in s, IsC
losed t) -> IsClosed (⋂₀ s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isOpen_sInter`：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovD
iscrete α] {S : Set (Set α)},   (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isClopen_sInter (hS : ∀ s ∈ S, IsClopen s) : IsClopen (⋂₀ S) :=
  ⟨isClosed_sInter fun s hs ↦ (hS s hs).1, isOpen_sInter fun s hs ↦ (hS s hs).2⟩
/-
**isClopen_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] {f : ι → Set α},   (∀ (i : ι), IsClopen (f i)) → IsClopen (⋂ i, f i)
参数：∀ (i : ι), IsClopen (f i)；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isOpen_iInter`：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace 
α] [AlexandrovDiscrete α] {f : ι → Set α},   (∀ (i : ι), IsOpen (f i)) → IsOpen 
(⋂ …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isClopen_iInter (hf : ∀ i, IsClopen (f i)) : IsClopen (⋂ i, f i) :=
  ⟨isClosed_iInter fun i ↦ (hf i).1, isOpen_iInter fun i ↦ (hf i).2⟩
/-
**isClopen_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] {f : ι → Set α},   (∀ (i : ι), IsClopen (f i)) → IsClopen (⋂ i, f i)
参数：∀ (i : ι), IsClopen (f i)；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isOpen_iInter`：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace 
α] [AlexandrovDiscrete α] {f : ι → Set α},   (∀ (i : ι), IsOpen (f i)) → IsOpen 
(⋂ …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isClopen_iInter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsClopen (f i j)) :
    IsClopen (⋂ i, ⋂ j, f i j) :=
  isClopen_iInter fun _ ↦ isClopen_iInter <| hf _
/-
**isClopen_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {S : S
et (Set α)},   (∀ s ∈ S, IsClopen s) → IsClopen (⋃₀ S)
参数：Set α；∀ s ∈ S, IsClopen s；⋃₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_sUnion`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Alexandro
vDiscrete α] {S : Set (Set α)},   (∀ s ∈ S, IsClosed s) → IsClosed (⋃₀ S)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isOpen_sUnion`：isOpen_sUnion {s : Set (Set X)} (h : forall t in s, IsOpe
n t) : IsOpen (⋃₀ s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isClopen_sUnion (hS : ∀ s ∈ S, IsClopen s) : IsClopen (⋃₀ S) :=
  ⟨isClosed_sUnion fun s hs ↦ (hS s hs).1, isOpen_sUnion fun s hs ↦ (hS s hs).2⟩
/-
**isClopen_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] {f : ι → Set α},   (∀ (i : ι), IsClopen (f i)) → IsClopen (⋃ i, f i)
参数：∀ (i : ι), IsClopen (f i)；⋃ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_iUnion`：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpac
e α] [AlexandrovDiscrete α] {f : ι → Set α},   (∀ (i : ι), IsClosed (f i)) → IsC
losed…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isClopen_iUnion (hf : ∀ i, IsClopen (f i)) : IsClopen (⋃ i, f i) :=
  ⟨isClosed_iUnion fun i ↦ (hf i).1, isOpen_iUnion fun i ↦ (hf i).2⟩
/-
**isClopen_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] {f : ι → Set α},   (∀ (i : ι), IsClopen (f i)) → IsClopen (⋃ i, f i)
参数：∀ (i : ι), IsClopen (f i)；⋃ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_iUnion`：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpac
e α] [AlexandrovDiscrete α] {f : ι → Set α},   (∀ (i : ι), IsClosed (f i)) → IsC
losed…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isClopen_iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsClopen (f i j)) :
    IsClopen (⋃ i, ⋃ j, f i j) :=
  isClopen_iUnion fun _ ↦ isClopen_iUnion <| hf _
/-
**interior_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] (f : ι → Set α),   interior (⋂ i, f i) = ⋂ i, interior (f i)
参数：f : ι → Set α；⋂ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.iInter_mono`：iInter_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋂ i, s i subseteq ⋂ i, t i
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `isOpen_iInter`：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace 
α] [AlexandrovDiscrete α] {f : ι → Set α},   (∀ (i : ι), IsOpen (f i)) → IsOpen 
(⋂ …
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
lemma interior_iInter (f : ι → Set α) : interior (⋂ i, f i) = ⋂ i, interior (f i) :=
  (interior_maximal (iInter_mono fun _ ↦ interior_subset) <| isOpen_iInter fun _ ↦
    isOpen_interior).antisymm' <| subset_iInter fun _ ↦ interior_mono <| iInter_subset _ _
/-
**interior_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] (S : S
et (Set α)),   interior (⋂₀ S) = ⋂ s ∈ S, interior s
参数：S : Set (Set α)；⋂₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `interior_iInter`：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpac
e α] [AlexandrovDiscrete α] (f : ι → Set α),   interior (⋂ i, f i) = ⋂ i, interi
or (f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma interior_sInter (S : Set (Set α)) : interior (⋂₀ S) = ⋂ s ∈ S, interior s := by
  simp_rw [sInter_eq_biInter, interior_iInter]
/-
**closure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] (f : ι → Set α),   closure (⋃ i, f i) = ⋃ i, closure (f i)
参数：f : ι → Set α；⋃ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `interior_iInter`：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpac
e α] [AlexandrovDiscrete α] (f : ι → Set α),   interior (⋂ i, f i) = ⋂ i, interi
or (f…
-/
lemma closure_iUnion (f : ι → Set α) : closure (⋃ i, f i) = ⋃ i, closure (f i) :=
  compl_injective <| by
    simpa only [← interior_compl, compl_iUnion] using interior_iInter fun i ↦ (f i)ᶜ
/-
**closure_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] (S : S
et (Set α)),   closure (⋃₀ S) = ⋃ s ∈ S, closure s
参数：S : Set (Set α)；⋃₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `closure_iUnion`：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace
 α] [AlexandrovDiscrete α] (f : ι → Set α),   closure (⋃ i, f i) = ⋃ i, closure 
(f i…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma closure_sUnion (S : Set (Set α)) : closure (⋃₀ S) = ⋃ s ∈ S, closure s := by
  simp_rw [sUnion_eq_biUnion, closure_iUnion]

end AlexandrovDiscrete

/-
**Topology.IsInducing.alexandrovDiscrete** 是 Mathlib 中的一个引理，位于命名空间 `instead.`。
形式化陈述：Topology.IsInducing.alexandrovDiscrete [AlexandrovDiscrete α] {f : β -> α}
 (h : IsInducing f) : AlexandrovDiscrete β where isOpen_sInter S hS
参数：h : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.isOpen_iff`：isOpen_iff (hf : IsInducing f) {s : Set 
X} : IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `isOpen_iInter₂`：∀ {ι : Sort u_1} {κ : ι → Sort u_2} {α : Type u_3} [inst
 : TopologicalSpace α] [AlexandrovDiscrete α]   {f : (i : ι) → κ i → Set α}, (∀ 
(i :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_iInter`：preimage_iInter {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma Topology.IsInducing.alexandrovDiscrete [AlexandrovDiscrete α] {f : β → α} (h : IsInducing f) :
    AlexandrovDiscrete β where
  isOpen_sInter S hS := by
    simp_rw [h.isOpen_iff] at hS ⊢
    choose U hU htU using hS
    refine ⟨_, isOpen_iInter₂ hU, ?_⟩
    simp_rw [preimage_iInter, htU, sInter_eq_biInter]

end

/-
**AlexandrovDiscrete.sup** 是 Mathlib 中的一个引理，位于命名空间 `instead.`。
形式化陈述：AlexandrovDiscrete.sup {t₁ t₂ : TopologicalSpace α} (_ : @AlexandrovDiscre
te α t₁) (_ : @AlexandrovDiscrete α t₂) : @AlexandrovDiscrete α (t₁ ⊔ t₂)
参数：_ : @AlexandrovDiscrete α t₁；_ : @AlexandrovDiscrete α t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_sInter`：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovD
iscrete α] {S : Set (Set α)},   (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma AlexandrovDiscrete.sup {t₁ t₂ : TopologicalSpace α} (_ : @AlexandrovDiscrete α t₁)
    (_ : @AlexandrovDiscrete α t₂) :
    @AlexandrovDiscrete α (t₁ ⊔ t₂) :=
  @AlexandrovDiscrete.mk α (t₁ ⊔ t₂) fun _S hS ↦
    ⟨@isOpen_sInter _ t₁ _ _ fun _s hs ↦ (hS _ hs).1, isOpen_sInter fun _s hs ↦ (hS _ hs).2⟩
/-
**alexandrovDiscrete_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} {t : ι → TopologicalSpace α}, (∀ (i : ι), 
AlexandrovDiscrete α) → AlexandrovDiscrete α
参数：∀ (i : ι), AlexandrovDiscrete α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iSup_iff`：isOpen_iSup_iff {s : Set α} : IsOpen[⨆ i, t i] s ↔ fora
ll i, IsOpen[t i] s
· 使用定理 `isOpen_sInter`：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovD
iscrete α] {S : Set (Set α)},   (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma alexandrovDiscrete_iSup {t : ι → TopologicalSpace α} (_ : ∀ i, @AlexandrovDiscrete α (t i)) :
    @AlexandrovDiscrete α (⨆ i, t i) :=
  @AlexandrovDiscrete.mk α (⨆ i, t i)
    fun _S hS ↦ isOpen_iSup_iff.2
      fun i ↦ @isOpen_sInter _ (t i) _ _
        fun _s hs ↦ isOpen_iSup_iff.1 (hS _ hs) _

section
variable [TopologicalSpace α] [TopologicalSpace β] [AlexandrovDiscrete α] [AlexandrovDiscrete β]
  {s t : Set α} {a : α}

/-
**isOpen_nhdsKer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {s : S
et α}, IsOpen (nhdsKer s)
参数：nhdsKer s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nhdsKer_def`：nhdsKer_def (s : Set X) : nhdsKer s = ⋂₀ {t : Set X | IsOpe
n t ∧ s subseteq t}
· 使用定理 `isOpen_sInter`：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovD
iscrete α] {S : Set (Set α)},   (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
@[simp] lemma isOpen_nhdsKer : IsOpen (nhdsKer s) := by
  rw [nhdsKer_def]; exact isOpen_sInter fun _ ↦ And.left
/-
**nhdsKer_mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {s : S
et α}, nhdsKer s ∈ nhdsSet s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `isOpen_nhdsKer`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Alexandrov
Discrete α] {s : Set α}, IsOpen (nhdsKer s)
· 使用引理 `subset_nhdsKer`：subset_nhdsKer : s subseteq nhdsKer s
-/
lemma nhdsKer_mem_nhdsSet : nhdsKer s ∈ 𝓝ˢ s := isOpen_nhdsKer.mem_nhdsSet.2 subset_nhdsKer
/-
**nhdsKer_eq_iff_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {s : S
et α}, nhdsKer s = s ↔ IsOpen s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_nhdsKer`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Alexandrov
Discrete α] {s : Set α}, IsOpen (nhdsKer s)
· 使用引理 `IsOpen.nhdsKer_eq`：IsOpen.nhdsKer_eq (h : IsOpen s) : nhdsKer s = s
-/
@[simp] lemma nhdsKer_eq_iff_isOpen : nhdsKer s = s ↔ IsOpen s :=
  ⟨fun h ↦ h ▸ isOpen_nhdsKer, IsOpen.nhdsKer_eq⟩
/-
**nhdsKer_subset_iff_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {s : S
et α}, nhdsKer s ⊆ s ↔ IsOpen s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `nhdsKer_eq_iff_isOpen`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Ale
xandrovDiscrete α] {s : Set α}, nhdsKer s = s ↔ IsOpen s
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma nhdsKer_subset_iff_isOpen : nhdsKer s ⊆ s ↔ IsOpen s := by
  simp only [nhdsKer_eq_iff_isOpen.symm, Subset.antisymm_iff, subset_nhdsKer, and_true]
/-
**nhdsKer_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {s t :
 Set α},   nhdsKer s ⊆ t ↔ ∃ U, IsOpen U ∧ s ⊆ U ∧ U ⊆ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_nhdsKer`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Alexandrov
Discrete α] {s : Set α}, IsOpen (nhdsKer s)
· 使用引理 `subset_nhdsKer`：subset_nhdsKer : s subseteq nhdsKer s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `nhdsKer_minimal`：nhdsKer_minimal (h₁ : s subseteq t) (h₂ : IsOpen t) : n
hdsKer s subseteq t
-/
lemma nhdsKer_subset_iff : nhdsKer s ⊆ t ↔ ∃ U, IsOpen U ∧ s ⊆ U ∧ U ⊆ t :=
  ⟨fun h ↦ ⟨nhdsKer s, isOpen_nhdsKer, subset_nhdsKer, h⟩,
    fun ⟨_U, hU, hsU, hUt⟩ ↦ (nhdsKer_minimal hsU hU).trans hUt⟩
/-
**nhdsKer_subset_iff_mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {s t :
 Set α}, nhdsKer s ⊆ t ↔ t ∈ nhdsSet s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `nhdsKer_subset_iff`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Alexan
drovDiscrete α] {s t : Set α},   nhdsKer s ⊆ t ↔ ∃ U, IsOpen U ∧ s ⊆ U ∧ U ⊆ t
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mem_nhdsSet_iff_exists`：mem_nhdsSet_iff_exists : s in 𝓝ˢ t ↔ exists U : 
Set X, IsOpen U ∧ t subseteq U ∧ U subseteq s
-/
lemma nhdsKer_subset_iff_mem_nhdsSet : nhdsKer s ⊆ t ↔ t ∈ 𝓝ˢ s :=
  nhdsKer_subset_iff.trans mem_nhdsSet_iff_exists.symm
/-
**nhdsKer_singleton_subset_iff_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {t : S
et α} {a : α}, nhdsKer {a} ⊆ t ↔ t ∈ nhds a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nhdsKer_singleton_subset_iff_mem_nhds : nhdsKer {a} ⊆ t ↔ t ∈ 𝓝 a := by
  simp [nhdsKer_subset_iff_mem_nhdsSet]
/-
**gc_nhdsKer_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α], Galoi
sConnection nhdsKer interior
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma gc_nhdsKer_interior : GaloisConnection (nhdsKer : Set α → Set α) interior :=
  fun s t ↦ by simp [nhdsKer_subset_iff, subset_interior_iff]
/-
**principal_nhdsKer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] (s : S
et α),   Filter.principal (nhdsKer s) = nhdsSet s
参数：s : Set α；nhdsKer s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsSet_nhdsKer`：∀ {X : Type u_2} [inst : TopologicalSpace X] (s : Set X
), nhdsSet (nhdsKer s) = nhdsSet s
· 使用定理 `IsOpen.nhdsSet_eq`：∀ {X : Type u_2} [inst : TopologicalSpace X] {s : Set
 X}, IsOpen s → nhdsSet s = Filter.principal s
· 使用定理 `isOpen_nhdsKer`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Alexandrov
Discrete α] {s : Set α}, IsOpen (nhdsKer s)
-/
@[simp] lemma principal_nhdsKer (s : Set α) : 𝓟 (nhdsKer s) = 𝓝ˢ s := by
  rw [← nhdsSet_nhdsKer, isOpen_nhdsKer.nhdsSet_eq]
/-
**principal_nhdsKer_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] (a : α
), Filter.principal (nhdsKer {a}) = nhds a
参数：a : α；nhdsKer {a}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `principal_nhdsKer`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Alexand
rovDiscrete α] (s : Set α),   Filter.principal (nhdsKer s) = nhdsSet s
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
-/
lemma principal_nhdsKer_singleton (a : α) : 𝓟 (nhdsKer {a}) = 𝓝 a := by
  rw [principal_nhdsKer, nhdsSet_singleton]
/-
**nhdsSet_basis_nhdsKer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] (s : S
et α),   (nhdsSet s).HasBasis (fun x => True) fun x => nhdsKer s
参数：s : Set α；nhdsSet s；fun x => True。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.hasBasis_principal`：hasBasis_principal (t : Set α) : (𝓟 t).HasBas
is (fun _ : Unit => True) fun _ => t
· 使用定理 `principal_nhdsKer`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Alexand
rovDiscrete α] (s : Set α),   Filter.principal (nhdsKer s) = nhdsSet s
-/
lemma nhdsSet_basis_nhdsKer (s : Set α) :
    (𝓝ˢ s).HasBasis (fun _ : Unit => True) (fun _ => nhdsKer s) :=
  principal_nhdsKer s ▸ hasBasis_principal (nhdsKer s)
/-
**nhds_basis_nhdsKer_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] (a : α
),   (nhds a).HasBasis (fun x => True) fun x => nhdsKer {a}
参数：a : α；nhds a；fun x => True。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.hasBasis_principal`：hasBasis_principal (t : Set α) : (𝓟 t).HasBas
is (fun _ : Unit => True) fun _ => t
· 使用定理 `principal_nhdsKer_singleton`：∀ {α : Type u_3} [inst : TopologicalSpace α
] [AlexandrovDiscrete α] (a : α), Filter.principal (nhdsKer {a}) = nhds a
-/
lemma nhds_basis_nhdsKer_singleton (a : α) :
    (𝓝 a).HasBasis (fun _ : Unit => True) (fun _ => nhdsKer {a}) :=
  principal_nhdsKer_singleton a ▸ hasBasis_principal (nhdsKer {a})
/-
**isOpen_iff_forall_specializes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {s : S
et α},   IsOpen s ↔ ∀ (x y : α), x ⤳ y → y ∈ s → x ∈ s
参数：x y : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isOpen_iff_forall_specializes : IsOpen s ↔ ∀ x y, x ⤳ y → y ∈ s → x ∈ s := by
  simp only [← nhdsKer_subset_iff_isOpen, Set.subset_def, mem_nhdsKer_iff_specializes, exists_imp,
    and_imp, @forall_comm (_ ⤳ _)]

omit [AlexandrovDiscrete α] in
/-
**alexandrovDiscrete_iff_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α], AlexandrovDiscrete α ↔ ∀ (a 
: α), nhds a = Filter.principal (nhdsKer {a})
参数：a : α；nhdsKer {a}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `principal_nhdsKer_singleton`：∀ {α : Type u_3} [inst : TopologicalSpace α
] [AlexandrovDiscrete α] (a : α), Filter.principal (nhdsKer {a}) = nhds a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `Set.nonempty_biUnion`：nonempty_biUnion {t : Set α} {s : α -> Set β} : (⋃
 i in t, s i).Nonempty ↔ exists i in t, (s i).Nonempty
· 使用定理 `Set.inter_iUnion₂`：inter_iUnion₂ (s : Set α) (t : forall i, κ i -> Set α
) : (s inter ⋃ (i) (j), t i j) = ⋃ (i) (j), s inter t i j
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.mem_sUnion_of_mem`：mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (S
et α)} (hx : x in t) (ht : t in S) : x in ⋃₀ S
-/
lemma alexandrovDiscrete_iff_nhds : AlexandrovDiscrete α ↔ (∀ a : α, 𝓝 a = 𝓟 (nhdsKer {a})) where
  mp _ a := principal_nhdsKer_singleton a |>.symm
  mpr hα := by
    simp only [alexandrovDiscrete_iff_isClosed, isClosed_iff_clusterPt, ClusterPt, funext hα,
      inf_principal, principal_neBot_iff]
    intro S hS a ha
    rw [sUnion_eq_biUnion, inter_iUnion₂, nonempty_biUnion] at ha
    obtain ⟨s, hs, has⟩ := ha
    specialize hS s hs a has
    exact mem_sUnion_of_mem hS hs
/-
**alexandrovDiscrete_coinduced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {β : T
ype u_5} {f : α → β}, AlexandrovDiscrete β
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_coinduced`：isOpen_coinduced {t : TopologicalSpace α} {s : Set β} 
{f : α -> β} : IsOpen[t.coinduced f] s ↔ IsOpen (f ⁻¹' s)
· 使用定理 `Set.preimage_sInter`：preimage_sInter {f : α -> β} {s : Set (Set β)} : f 
⁻¹' ⋂₀ s = ⋂ t in s, f ⁻¹' t
· 使用定理 `isOpen_iInter₂`：∀ {ι : Sort u_1} {κ : ι → Sort u_2} {α : Type u_3} [inst
 : TopologicalSpace α] [AlexandrovDiscrete α]   {f : (i : ι) → κ i → Set α}, (∀ 
(i :…
-/
lemma alexandrovDiscrete_coinduced {β : Type*} {f : α → β} :
    @AlexandrovDiscrete β (coinduced f ‹_›) :=
  @AlexandrovDiscrete.mk β (coinduced f ‹_›) fun S hS ↦ by
    rw [isOpen_coinduced, preimage_sInter]; exact isOpen_iInter₂ hS
/-
**AlexandrovDiscrete.toFirstCountable** 是 Mathlib 中的一个实例，位于命名空间 `instead.`。
形式化陈述：AlexandrovDiscrete.toFirstCountable : FirstCountableTopology α where nhds_
generated_countable a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.countable_singleton`：∀ {α : Type u} (a : α), {a}.Countable
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.generate_singleton`：∀ {α : Type u} (s : Set α), Filter.generate {
s} = Filter.principal s
· 使用定理 `principal_nhdsKer`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Alexand
rovDiscrete α] (s : Set α),   Filter.principal (nhdsKer s) = nhdsSet s
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance AlexandrovDiscrete.toFirstCountable : FirstCountableTopology α where
  nhds_generated_countable a := ⟨{nhdsKer {a}}, countable_singleton _, by simp⟩
/-
**AlexandrovDiscrete.toLocallyCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 `instead.`。
形式化陈述：AlexandrovDiscrete.toLocallyCompactSpace : LocallyCompactSpace α where loc
al_compact_nhds a _U hU
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_nhdsKer`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Alexandrov
Discrete α] {s : Set α}, IsOpen (nhdsKer s)
· 使用引理 `subset_nhdsKer`：subset_nhdsKer : s subseteq nhdsKer s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nhdsKer_singleton_subset_iff_mem_nhds`：∀ {α : Type u_3} [inst : Topologi
calSpace α] [AlexandrovDiscrete α] {t : Set α} {a : α}, nhdsKer {a} ⊆ t ↔ t ∈ nh
ds a
· 使用定理 `IsCompact.nhdsKer`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s : Set
 X}, IsCompact s → IsCompact (nhdsKer s)
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
-/
instance AlexandrovDiscrete.toLocallyCompactSpace : LocallyCompactSpace α where
  local_compact_nhds a _U hU := ⟨nhdsKer {a},
    isOpen_nhdsKer.mem_nhds <| subset_nhdsKer <| mem_singleton _,
      nhdsKer_singleton_subset_iff_mem_nhds.2 hU, isCompact_singleton.nhdsKer⟩
/-
**Subtype.instAlexandrovDiscrete** 是 Mathlib 中的一个实例，位于命名空间 `instead.`。
形式化陈述：Subtype.instAlexandrovDiscrete {p : α -> Prop} : AlexandrovDiscrete {a // 
p a}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.alexandrovDiscrete`：Topology.IsInducing.alexandrovDi
screte [AlexandrovDiscrete α] {f : β -> α} (h : IsInducing f) : AlexandrovDiscre
te β where isOpen_sInter S h…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
-/
instance Subtype.instAlexandrovDiscrete {p : α → Prop} : AlexandrovDiscrete {a // p a} :=
  IsInducing.subtypeVal.alexandrovDiscrete
/-
**Quotient.instAlexandrovDiscrete** 是 Mathlib 中的一个实例，位于命名空间 `instead.`。
形式化陈述：Quotient.instAlexandrovDiscrete {s : Setoid α} : AlexandrovDiscrete (Quoti
ent s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `alexandrovDiscrete_coinduced`：∀ {α : Type u_3} [inst : TopologicalSpace 
α] [AlexandrovDiscrete α] {β : Type u_5} {f : α → β}, AlexandrovDiscrete β
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
-/
instance Quotient.instAlexandrovDiscrete {s : Setoid α} : AlexandrovDiscrete (Quotient s) :=
  alexandrovDiscrete_coinduced
/-
**Sum.instAlexandrovDiscrete** 是 Mathlib 中的一个实例，位于命名空间 `instead.`。
形式化陈述：Sum.instAlexandrovDiscrete : AlexandrovDiscrete (α oplus β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlexandrovDiscrete.sup`：AlexandrovDiscrete.sup {t₁ t₂ : TopologicalSpace
 α} (_ : @AlexandrovDiscrete α t₁) (_ : @AlexandrovDiscrete α t₂) : @AlexandrovD
iscrete α (t…
· 使用定理 `alexandrovDiscrete_coinduced`：∀ {α : Type u_3} [inst : TopologicalSpace 
α] [AlexandrovDiscrete α] {β : Type u_5} {f : α → β}, AlexandrovDiscrete β
-/
instance Sum.instAlexandrovDiscrete : AlexandrovDiscrete (α ⊕ β) :=
  alexandrovDiscrete_coinduced.sup alexandrovDiscrete_coinduced
/-
**Sigma.instAlexandrovDiscrete** 是 Mathlib 中的一个实例，位于命名空间 `instead.`。
形式化陈述：Sigma.instAlexandrovDiscrete {ι : Type*} {X : ι -> Type*} [forall i, Topol
ogicalSpace (X i)] [forall i, AlexandrovDiscrete (X i)] : AlexandrovDiscrete (Σ 
i, X i)
参数：X i；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `alexandrovDiscrete_iSup`：∀ {ι : Sort u_1} {α : Type u_3} {t : ι → Topolo
gicalSpace α}, (∀ (i : ι), AlexandrovDiscrete α) → AlexandrovDiscrete α
· 使用定理 `alexandrovDiscrete_coinduced`：∀ {α : Type u_3} [inst : TopologicalSpace 
α] [AlexandrovDiscrete α] {β : Type u_5} {f : α → β}, AlexandrovDiscrete β
-/
instance Sigma.instAlexandrovDiscrete {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, AlexandrovDiscrete (X i)] : AlexandrovDiscrete (Σ i, X i) :=
  alexandrovDiscrete_iSup fun _ ↦ alexandrovDiscrete_coinduced
/-
**Prod.instAlexandrovDiscrete** 是 Mathlib 中的一个实例，位于命名空间 `instead.`。
形式化陈述：Prod.instAlexandrovDiscrete : AlexandrovDiscrete (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.prod_principal_principal`：prod_principal_principal {s : Set α} {t
 : Set β} : 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `nhdsKer_pair`：nhdsKer_pair {X Y : Type*} [TopologicalSpace X] [Topologic
alSpace Y] (x : X) (y : Y) : nhdsKer {(x, y)} = nhdsKer {x} ×ˢ nhdsKer {y}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance Prod.instAlexandrovDiscrete : AlexandrovDiscrete (α × β) := by
  simp_rw [alexandrovDiscrete_iff_nhds, Prod.forall, nhds_prod_eq, ← principal_nhdsKer_singleton,
    prod_principal_principal, nhdsKer_pair, forall_true_iff]
/-
**Pi.instAlexandrovDiscreteOfFinite** 是 Mathlib 中的一个实例，位于命名空间 `instead.`。
形式化陈述：Pi.instAlexandrovDiscreteOfFinite {ι : Type*} [Finite ι] {X : ι -> Type*} 
[Π i, TopologicalSpace (X i)] [forall i, AlexandrovDiscrete (X i)] : AlexandrovD
iscrete (Π i, X i)
参数：X i；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.pi_principal`：pi_principal [Finite ι] (s : (i : ι) -> Set (α i)) 
: pi (fun i => 𝓟 (s i)) = 𝓟 (univ.pi s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `nhdsKer_singleton_pi`：nhdsKer_singleton_pi {ι : Type*} {X : ι -> Type*} 
[Π (i : ι), TopologicalSpace (X i)] (p : Π (i : ι), X i) : nhdsKer {p} = univ.pi
 (fun i =>…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
instance Pi.instAlexandrovDiscreteOfFinite {ι : Type*} [Finite ι] {X : ι → Type*}
    [Π i, TopologicalSpace (X i)] [∀ i, AlexandrovDiscrete (X i)] :
    AlexandrovDiscrete (Π i, X i) := by
  simp_rw [alexandrovDiscrete_iff_nhds, nhds_pi, ← principal_nhdsKer_singleton,
    pi_principal, nhdsKer_singleton_pi, forall_true_iff]

end

