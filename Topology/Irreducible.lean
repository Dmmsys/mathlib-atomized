/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Order.Minimal
public import Mathlib.Order.Zorn
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Topology.WithTopology

/-!
# Irreducibility in topological spaces

## Main definitions

* `IrreducibleSpace`: a typeclass applying to topological spaces, stating that the space
  is nonempty and does not admit a nontrivial pair of disjoint opens.
* `IsIrreducible`: for a nonempty set in a topological space, the property that the set is an
  irreducible space in the subspace topology.

## On the definition of irreducible and connected sets/spaces

In informal mathematics, irreducible spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `IsPreirreducible`.
In other words, the only difference is whether the empty space counts as irreducible.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.

-/

@[expose] public section

open Set Topology

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Preirreducible

/-- A preirreducible set `s` is one where there is no non-trivial pair of disjoint opens on `s`. -/
/-
**IsPreirreducible** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsPreirreducible (s : Set X) : Prop
参数：s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preirreducible set `s` is one where there is no non-trivial pair of disjoint o
pens on `s`.
-/
def IsPreirreducible (s : Set X) : Prop :=
  ∀ u v : Set X, IsOpen u → IsOpen v → (s ∩ u).Nonempty → (s ∩ v).Nonempty → (s ∩ (u ∩ v)).Nonempty

/-- An irreducible set `s` is one that is nonempty and
where there is no non-trivial pair of disjoint opens on `s`. -/
@[stacks 004V "(1) as predicate on subsets of a space"]
/-
**IsIrreducible** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsIrreducible (s : Set X) : Prop
参数：s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An irreducible set `s` is one that is nonempty and
where there is no non-trivial pair of disjoint opens on `s`.
-/
def IsIrreducible (s : Set X) : Prop :=
  s.Nonempty ∧ IsPreirreducible s
/-
**IsIrreducible.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIrreducible.nonempty (h : IsIrreducible s) : s.Nonempty
参数：h : IsIrreducible s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsIrreducible.nonempty (h : IsIrreducible s) : s.Nonempty :=
  h.1
/-
**IsIrreducible.isPreirreducible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIrreducible.isPreirreducible (h : IsIrreducible s) : IsPreirreducible s
参数：h : IsIrreducible s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsIrreducible.isPreirreducible (h : IsIrreducible s) : IsPreirreducible s :=
  h.2
/-
**isPreirreducible_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreirreducible_empty : IsPreirreducible (∅ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isPreirreducible_empty : IsPreirreducible (∅ : Set X) := fun _ _ _ _ _ ⟨_, h1, _⟩ =>
  h1.elim
/-
**Set.Subsingleton.isPreirreducible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.isPreirreducible (hs : s.Subsingleton) : IsPreirreducible
 s
参数：hs : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Set.Subsingleton.isPreirreducible (hs : s.Subsingleton) : IsPreirreducible s :=
  fun _u _v _ _ ⟨_x, hxs, hxu⟩ ⟨y, hys, hyv⟩ => ⟨y, hys, hs hxs hys ▸ hxu, hyv⟩
/-
**isPreirreducible_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreirreducible_singleton {x} : IsPreirreducible ({x} : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.isPreirreducible`：Set.Subsingleton.isPreirreducible (hs
 : s.Subsingleton) : IsPreirreducible s
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem isPreirreducible_singleton {x} : IsPreirreducible ({x} : Set X) :=
  subsingleton_singleton.isPreirreducible
/-
**isIrreducible_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIrreducible_singleton {x} : IsIrreducible ({x} : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `isPreirreducible_singleton`：isPreirreducible_singleton {x} : IsPreirredu
cible ({x} : Set X)
-/
theorem isIrreducible_singleton {x} : IsIrreducible ({x} : Set X) :=
  ⟨singleton_nonempty x, isPreirreducible_singleton⟩
/-
**isPreirreducible_iff_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreirreducible_iff_closure : IsPreirreducible (closure s) ↔ IsPreirreduc
ible s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₄_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {p q : (a : α) → (b : β
 a)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_inter_open_nonempty_iff`：closure_inter_open_nonempty_iff (h : Is
Open t) : (closure s inter t).Nonempty ↔ (s inter t).Nonempty
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isPreirreducible_iff_closure : IsPreirreducible (closure s) ↔ IsPreirreducible s :=
  forall₄_congr fun u v hu hv => by
    iterate 3 rw [closure_inter_open_nonempty_iff]
    exacts [hu.inter hv, hv, hu]

@[stacks 004W "(1)"]
/-
**isIrreducible_iff_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIrreducible_iff_closure : IsIrreducible (closure s) ↔ IsIrreducible s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `closure_nonempty_iff`：closure_nonempty_iff : (closure s).Nonempty ↔ s.No
nempty
· 使用定理 `isPreirreducible_iff_closure`：isPreirreducible_iff_closure : IsPreirredu
cible (closure s) ↔ IsPreirreducible s
-/
theorem isIrreducible_iff_closure : IsIrreducible (closure s) ↔ IsIrreducible s :=
  and_congr closure_nonempty_iff isPreirreducible_iff_closure

protected alias ⟨_, IsPreirreducible.closure⟩ := isPreirreducible_iff_closure

protected alias ⟨_, IsIrreducible.closure⟩ := isIrreducible_iff_closure
/-
**exists_preirreducible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_preirreducible (s : Set X) (H : IsPreirreducible s) : exists t : Se
t X, IsPreirreducible t ∧ s subseteq t ∧ forall u, IsPreirreducible u -> t subse
teq u -> u = t
参数：s : Set X；H : IsPreirreducible s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_subset_nonempty`：zorn_subset_nonempty (S : Set (Set α)) (H : forall
 c subseteq S, IsChain (· subseteq ·) c -> c.Nonempty -> exists ub in S, forall 
s in c, s …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_sUnion`：mem_sUnion {x : α} {S : Set (Set α)} : x in ⋃₀ S ↔ exist
s t in S, x in t
· 使用定理 `IsChain.total`：IsChain.total (h : IsChain r s) (hx : x in s) (hy : y in 
s) : x ≺ y ∨ y ≺ x
· 使用定理 `Set.mem_sUnion_of_mem`：mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (S
et α)} (hx : x in t) (ht : t in S) : x in ⋃₀ S
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Maximal.eq_of_subset`：Maximal.eq_of_subset (h : Maximal P s) (ht : P t) 
(hst : s subseteq t) : s = t
-/
theorem exists_preirreducible (s : Set X) (H : IsPreirreducible s) :
    ∃ t : Set X, IsPreirreducible t ∧ s ⊆ t ∧ ∀ u, IsPreirreducible u → t ⊆ u → u = t :=
  let ⟨m, hsm, hm⟩ :=
    zorn_subset_nonempty { t : Set X | IsPreirreducible t }
      (fun c hc hcc _ =>
        ⟨⋃₀ c, fun u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩ =>
          let ⟨p, hpc, hyp⟩ := mem_sUnion.1 hy
          let ⟨q, hqc, hxq⟩ := mem_sUnion.1 hx
          Or.casesOn (hcc.total hpc hqc)
            (fun hpq : p ⊆ q =>
              let ⟨x, hxp, hxuv⟩ := hc hqc u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
              ⟨x, mem_sUnion_of_mem hxp hqc, hxuv⟩)
            fun hqp : q ⊆ p =>
            let ⟨x, hxp, hxuv⟩ := hc hpc u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
            ⟨x, mem_sUnion_of_mem hxp hpc, hxuv⟩,
          fun _ hxc => subset_sUnion_of_mem hxc⟩)
      s H
  ⟨m, hm.prop, hsm, fun _u hu hmu => (hm.eq_of_subset hu hmu).symm⟩

/-- The set of irreducible components of a topological space. -/
@[stacks 004V "(2)"]
/-
**irreducibleComponents** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：irreducibleComponents (X : Type*) [TopologicalSpace X] : Set (Set X)
参数：X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of irreducible components of a topological space.
-/
def irreducibleComponents (X : Type*) [TopologicalSpace X] : Set (Set X) :=
  {s | Maximal IsIrreducible s}

@[stacks 004W "(2)"]
/-
**isClosed_of_mem_irreducibleComponents** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_of_mem_irreducibleComponents (s) (H : s in irreducibleComponents 
X) : IsClosed s
参数：s；H : s in irreducibleComponents X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_eq_iff_isClosed`：closure_eq_iff_isClosed : closure s = s ↔ IsClo
sed s
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsIrreducible.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s :
 Set X}, IsIrreducible s → IsIrreducible (closure s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isClosed_of_mem_irreducibleComponents (s) (H : s ∈ irreducibleComponents X) :
    IsClosed s := by
  rw [← closure_eq_iff_isClosed, eq_comm]
  exact subset_closure.antisymm (H.2 H.1.closure subset_closure)
/-
**irreducibleComponents_eq_maximals_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irreducibleComponents_eq_maximals_closed (X : Type*) [TopologicalSpace X] 
: irreducibleComponents X = { s | Maximal (fun x => IsClosed x ∧ IsIrreducible x
) s}
参数：X : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `isClosed_of_mem_irreducibleComponents`：isClosed_of_mem_irreducibleCompon
ents (s) (H : s in irreducibleComponents X) : IsClosed s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsIrreducible.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s :
 Set X}, IsIrreducible s → IsIrreducible (closure s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem irreducibleComponents_eq_maximals_closed (X : Type*) [TopologicalSpace X] :
    irreducibleComponents X = { s | Maximal (fun x ↦ IsClosed x ∧ IsIrreducible x) s} := by
  ext s
  constructor
  · intro H
    exact ⟨⟨isClosed_of_mem_irreducibleComponents _ H, H.1⟩, fun x h e => H.2 h.2 e⟩
  · intro H
    refine ⟨H.1.2, fun x h e => ?_⟩
    have : closure x ≤ s := H.2 ⟨isClosed_closure, h.closure⟩ (e.trans subset_closure)
    exact le_trans subset_closure this

@[stacks 004W "(3)"]
/-
**exists_mem_irreducibleComponents_subset_of_isIrreducible** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：exists_mem_irreducibleComponents_subset_of_isIrreducible (s : Set X) (hs :
 IsIrreducible s) : exists u in irreducibleComponents X, s subseteq u
参数：s : Set X；hs : IsIrreducible s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_preirreducible`：exists_preirreducible (s : Set X) (H : IsPreirred
ucible s) : exists t : Set X, IsPreirreducible t ∧ s subseteq t ∧ forall u, IsPr
eirreducibl…
· 使用定理 `IsIrreducible.isPreirreducible`：IsIrreducible.isPreirreducible (h : IsIr
reducible s) : IsPreirreducible s
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma exists_mem_irreducibleComponents_subset_of_isIrreducible (s : Set X) (hs : IsIrreducible s) :
    ∃ u ∈ irreducibleComponents X, s ⊆ u := by
  obtain ⟨u, hu⟩ := exists_preirreducible s hs.isPreirreducible
  use u, ⟨⟨hs.left.mono hu.right.left,hu.left⟩,fun _ h hl => (hu.right.right _ h.right hl).le⟩
  exact hu.right.left

/-- A maximal irreducible set that contains a given point. -/
@[stacks 004W "(4)"]
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**irreducibleComponent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：irreducibleComponent (x : X) : Set X
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def irreducibleComponent (x : X) : Set X :=
  Classical.choose (exists_preirreducible {x} isPreirreducible_singleton)
/-
**irreducibleComponent_property** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irreducibleComponent_property (x : X) : IsPreirreducible (irreducibleCompo
nent x) ∧ {x} subseteq irreducibleComponent x ∧ forall u, IsPreirreducible u -> 
irreducibleComponent x subseteq u -> u = irreducibleComponent x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `exists_preirreducible`：exists_preirreducible (s : Set X) (H : IsPreirred
ucible s) : exists t : Set X, IsPreirreducible t ∧ s subseteq t ∧ forall u, IsPr
eirreducibl…
· 使用定理 `isPreirreducible_singleton`：isPreirreducible_singleton {x} : IsPreirredu
cible ({x} : Set X)
-/
theorem irreducibleComponent_property (x : X) :
    IsPreirreducible (irreducibleComponent x) ∧
      {x} ⊆ irreducibleComponent x ∧
        ∀ u, IsPreirreducible u → irreducibleComponent x ⊆ u → u = irreducibleComponent x :=
  Classical.choose_spec (exists_preirreducible {x} isPreirreducible_singleton)

@[stacks 004W "(4)"]
/-
**mem_irreducibleComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_irreducibleComponent {x : X} : x in irreducibleComponent x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `irreducibleComponent_property`：irreducibleComponent_property (x : X) : I
sPreirreducible (irreducibleComponent x) ∧ {x} subseteq irreducibleComponent x ∧
 forall u, IsPreirr…
-/
theorem mem_irreducibleComponent {x : X} : x ∈ irreducibleComponent x :=
  singleton_subset_iff.1 (irreducibleComponent_property x).2.1
/-
**isIrreducible_irreducibleComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIrreducible_irreducibleComponent {x : X} : IsIrreducible (irreducibleCom
ponent x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_irreducibleComponent`：mem_irreducibleComponent {x : X} : x in irredu
cibleComponent x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `irreducibleComponent_property`：irreducibleComponent_property (x : X) : I
sPreirreducible (irreducibleComponent x) ∧ {x} subseteq irreducibleComponent x ∧
 forall u, IsPreirr…
-/
theorem isIrreducible_irreducibleComponent {x : X} : IsIrreducible (irreducibleComponent x) :=
  ⟨⟨x, mem_irreducibleComponent⟩, (irreducibleComponent_property x).1⟩
/-
**eq_irreducibleComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_irreducibleComponent {x : X} : IsPreirreducible s -> irreducibleCompone
nt x subseteq s -> s = irreducibleComponent x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `irreducibleComponent_property`：irreducibleComponent_property (x : X) : I
sPreirreducible (irreducibleComponent x) ∧ {x} subseteq irreducibleComponent x ∧
 forall u, IsPreirr…
-/
theorem eq_irreducibleComponent {x : X} :
    IsPreirreducible s → irreducibleComponent x ⊆ s → s = irreducibleComponent x :=
  (irreducibleComponent_property x).2.2 _
/-
**irreducibleComponent_mem_irreducibleComponents** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irreducibleComponent_mem_irreducibleComponents (x : X) : irreducibleCompon
ent x in irreducibleComponents X
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isIrreducible_irreducibleComponent`：isIrreducible_irreducibleComponent {
x : X} : IsIrreducible (irreducibleComponent x)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `eq_irreducibleComponent`：eq_irreducibleComponent {x : X} : IsPreirreduci
ble s -> irreducibleComponent x subseteq s -> s = irreducibleComponent x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem irreducibleComponent_mem_irreducibleComponents (x : X) :
    irreducibleComponent x ∈ irreducibleComponents X :=
  ⟨isIrreducible_irreducibleComponent, fun _ h₁ h₂ => (eq_irreducibleComponent h₁.2 h₂).le⟩
/-
**isClosed_irreducibleComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_irreducibleComponent {x : X} : IsClosed (irreducibleComponent x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_of_mem_irreducibleComponents`：isClosed_of_mem_irreducibleCompon
ents (s) (H : s in irreducibleComponents X) : IsClosed s
· 使用定理 `irreducibleComponent_mem_irreducibleComponents`：irreducibleComponent_mem
_irreducibleComponents (x : X) : irreducibleComponent x in irreducibleComponents
 X
-/
theorem isClosed_irreducibleComponent {x : X} : IsClosed (irreducibleComponent x) :=
  isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents x)

/-- A preirreducible space is one where there is no non-trivial pair of disjoint opens. -/
@[mk_iff]
/-
**PreirreducibleSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_3) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preirreducible space is one where there is no non-trivial pair of disjoint ope
ns.
-/
class PreirreducibleSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a preirreducible space, `Set.univ` is a preirreducible set. -/
  isPreirreducible_univ : IsPreirreducible (univ : Set X)

/-- An irreducible space is one that is nonempty
and where there is no non-trivial pair of disjoint opens. -/
@[stacks 004V "(1) as predicate on a space"]
/-
**IrreducibleSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_3) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An irreducible space is one that is nonempty
and where there is no non-trivial pair of disjoint opens.
-/
class IrreducibleSpace (X : Type*) [TopologicalSpace X] : Prop extends PreirreducibleSpace X where
  toNonempty : Nonempty X

-- see Note [lower instance priority]
attribute [instance 50] IrreducibleSpace.toNonempty
/-
**IrreducibleSpace.isIrreducible_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IrreducibleSpace.isIrreducible_univ (X : Type*) [TopologicalSpace X] [Irre
ducibleSpace X] : IsIrreducible (univ : Set X)
参数：X : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `IrreducibleSpace.toNonempty`：∀ {X : Type u_3} {inst : TopologicalSpace X
} [self : IrreducibleSpace X], Nonempty X
· 使用定理 `PreirreducibleSpace.isPreirreducible_univ`：∀ {X : Type u_3} {inst : Topo
logicalSpace X} [self : PreirreducibleSpace X], IsPreirreducible Set.univ
· 使用定理 `IrreducibleSpace.toPreirreducibleSpace`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : IrreducibleSpace X], PreirreducibleSpace X
-/
theorem IrreducibleSpace.isIrreducible_univ (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] :
    IsIrreducible (univ : Set X) :=
  ⟨univ_nonempty, PreirreducibleSpace.isPreirreducible_univ⟩
/-
**irreducibleSpace_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irreducibleSpace_def (X : Type*) [TopologicalSpace X] : IrreducibleSpace X
 ↔ IsIrreducible (⊤ : Set X)
参数：X : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IrreducibleSpace.isIrreducible_univ`：IrreducibleSpace.isIrreducible_univ
 (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] : IsIrreducible (univ : S
et X)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem irreducibleSpace_def (X : Type*) [TopologicalSpace X] :
    IrreducibleSpace X ↔ IsIrreducible (⊤ : Set X) :=
  ⟨@IrreducibleSpace.isIrreducible_univ X _, fun h =>
    haveI : PreirreducibleSpace X := ⟨h.2⟩
    ⟨⟨h.1.some⟩⟩⟩
/-
**PreirreducibleSpace.of_forall_nonempty_inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PreirreducibleSpace.of_forall_nonempty_inter (H : forall ⦃U V : Set X⦄, Is
Open U -> IsOpen V -> U.Nonempty -> V.Nonempty -> (U inter V).Nonempty) : Preirr
educibleSpace X where isPreirreducible_univ _
参数：H : forall ⦃U V : Set X⦄, IsOpen U -> IsOpen V -> U.Nonempty -> V.Nonempty ->
 (U inter V).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma PreirreducibleSpace.of_forall_nonempty_inter
    (H : ∀ ⦃U V : Set X⦄, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty → (U ∩ V).Nonempty) :
    PreirreducibleSpace X where
  isPreirreducible_univ _ := by simp_all
/-
**nonempty_preirreducible_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_preirreducible_inter [PreirreducibleSpace X] : IsOpen s -> IsOpen
 t -> s.Nonempty -> t.Nonempty -> (s inter t).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `PreirreducibleSpace.isPreirreducible_univ`：∀ {X : Type u_3} {inst : Topo
logicalSpace X} [self : PreirreducibleSpace X], IsPreirreducible Set.univ
-/
theorem nonempty_preirreducible_inter [PreirreducibleSpace X] :
    IsOpen s → IsOpen t → s.Nonempty → t.Nonempty → (s ∩ t).Nonempty := by
  simpa only [univ_inter, univ_subset_iff] using
    @PreirreducibleSpace.isPreirreducible_univ X _ _ s t

/-- In a (pre)irreducible space, a nonempty open set is dense. -/
/-
**IsOpen.dense** 是 Mathlib 中的一个定理，位于命名空间 `IsOpen`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {s : Set X} [PreirreducibleSp
ace X], IsOpen s → s.Nonempty → Dense s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dense_iff_inter_open`：dense_iff_inter_open : Dense s ↔ forall U, IsOpen 
U -> U.Nonempty -> (U inter s).Nonempty
· 使用定理 `nonempty_preirreducible_inter`：nonempty_preirreducible_inter [Preirreduc
ibleSpace X] : IsOpen s -> IsOpen t -> s.Nonempty -> t.Nonempty -> (s inter t).N
onempty

--- 原说明 ---
In a (pre)irreducible space, a nonempty open set is dense.
-/
protected theorem IsOpen.dense [PreirreducibleSpace X] (ho : IsOpen s) (hne : s.Nonempty) :
    Dense s :=
  dense_iff_inter_open.2 fun _t hto htne => nonempty_preirreducible_inter hto ho htne hne
/-
**IsOpenMap.denseRange_of_isPreirreducibleSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpenMap.denseRange_of_isPreirreducibleSpace {U X : Type*} [TopologicalSp
ace U] [Nonempty U] [TopologicalSpace X] (f : U -> X) (hf : IsOpenMap f) [Preirr
educibleSpace X] : DenseRange f
参数：f : U -> X；hf : IsOpenMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.dense`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s : Set X} [
PreirreducibleSpace X], IsOpen s → s.Nonempty → Dense s
· 使用定理 `IsOpenMap.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → IsOpen (S
et.range f)
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
lemma IsOpenMap.denseRange_of_isPreirreducibleSpace {U X : Type*} [TopologicalSpace U]
    [Nonempty U] [TopologicalSpace X] (f : U → X) (hf : IsOpenMap f) [PreirreducibleSpace X] :
    DenseRange f :=
  hf.isOpen_range.dense (Set.range_nonempty f)
/-
**IsPreirreducible.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreirreducible.image (H : IsPreirreducible s) (f : X -> Y) (hf : Continu
ousOn f s) : IsPreirreducible (f '' s)
参数：H : IsPreirreducible s；f : X -> Y；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff'`：continuousOn_iff' : ContinuousOn f s ↔ forall t : Set
 β, IsOpen t -> exists u, IsOpen u ∧ f ⁻¹' t inter s = u inter s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.mem_of_mem_inter_left`：mem_of_mem_inter_left {x : α} {a b : Set α} (
h : x in a inter b) : x in a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem IsPreirreducible.image (H : IsPreirreducible s) (f : X → Y) (hf : ContinuousOn f s) :
    IsPreirreducible (f '' s) := by
  rintro u v hu hv ⟨_, ⟨⟨x, hx, rfl⟩, hxu⟩⟩ ⟨_, ⟨⟨y, hy, rfl⟩, hyv⟩⟩
  rw [← mem_preimage] at hxu hyv
  rcases continuousOn_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
  rcases continuousOn_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
  have := H u' v' hu' hv'
  rw [inter_comm s u', ← u'_eq] at this
  rw [inter_comm s v', ← v'_eq] at this
  rcases this ⟨x, hxu, hx⟩ ⟨y, hyv, hy⟩ with ⟨x, hxs, hxu', hxv'⟩
  refine ⟨f x, mem_image_of_mem f hxs, ?_, ?_⟩
  all_goals
    rw [← mem_preimage]
    apply mem_of_mem_inter_left
    show x ∈ _ ∩ s
    simp [*]

@[stacks 0379]
/-
**IsIrreducible.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIrreducible.image (H : IsIrreducible s) (f : X -> Y) (hf : ContinuousOn 
f s) : IsIrreducible (f '' s)
参数：H : IsIrreducible s；f : X -> Y；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `IsIrreducible.nonempty`：IsIrreducible.nonempty (h : IsIrreducible s) : s
.Nonempty
· 使用定理 `IsPreirreducible.image`：IsPreirreducible.image (H : IsPreirreducible s) 
(f : X -> Y) (hf : ContinuousOn f s) : IsPreirreducible (f '' s)
· 使用定理 `IsIrreducible.isPreirreducible`：IsIrreducible.isPreirreducible (h : IsIr
reducible s) : IsPreirreducible s
-/
theorem IsIrreducible.image (H : IsIrreducible s) (f : X → Y) (hf : ContinuousOn f s) :
    IsIrreducible (f '' s) :=
  ⟨H.nonempty.image _, H.isPreirreducible.image f hf⟩
/-
**Subtype.preirreducibleSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.preirreducibleSpace (h : IsPreirreducible s) : PreirreducibleSpace
 s where isPreirreducible_univ
参数：h : IsPreirreducible s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem Subtype.preirreducibleSpace (h : IsPreirreducible s) : PreirreducibleSpace s where
  isPreirreducible_univ := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ ⟨⟨x, hxs⟩, -, hxu⟩ ⟨⟨y, hys⟩, -, hyv⟩
    rcases h u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩ with ⟨x, hxs, ⟨hxu, hxv⟩⟩
    exact ⟨⟨x, hxs⟩, ⟨Set.mem_univ _, ⟨hxu, hxv⟩⟩⟩
/-
**Subtype.irreducibleSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.irreducibleSpace (h : IsIrreducible s) : IrreducibleSpace s where 
isPreirreducible_univ
参数：h : IsIrreducible s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.preirreducibleSpace`：Subtype.preirreducibleSpace (h : IsPreirred
ucible s) : PreirreducibleSpace s where isPreirreducible_univ
· 使用定理 `IsIrreducible.isPreirreducible`：IsIrreducible.isPreirreducible (h : IsIr
reducible s) : IsPreirreducible s
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `IsIrreducible.nonempty`：IsIrreducible.nonempty (h : IsIrreducible s) : s
.Nonempty
-/
theorem Subtype.irreducibleSpace (h : IsIrreducible s) : IrreducibleSpace s where
  isPreirreducible_univ :=
    (Subtype.preirreducibleSpace h.isPreirreducible).isPreirreducible_univ
  toNonempty := h.nonempty.to_subtype
/-
**IsPreirreducible.of_subtype** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsPreirreducible.of_subtype [PreirreducibleSpace s] : IsPreirreducible s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `IsPreirreducible.image`：IsPreirreducible.image (H : IsPreirreducible s) 
(f : X -> Y) (hf : ContinuousOn f s) : IsPreirreducible (f '' s)
· 使用定理 `PreirreducibleSpace.isPreirreducible_univ`：∀ {X : Type u_3} {inst : Topo
logicalSpace X} [self : PreirreducibleSpace X], IsPreirreducible Set.univ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
lemma IsPreirreducible.of_subtype [PreirreducibleSpace s] : IsPreirreducible s := by
  rw [← Subtype.range_coe (s := s), ← Set.image_univ]
  refine PreirreducibleSpace.isPreirreducible_univ.image Subtype.val ?_
  exact continuous_subtype_val.continuousOn
/-
**IsIrreducible.of_subtype** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIrreducible.of_subtype [IrreducibleSpace s] : IsIrreducible s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.of_subtype`：∀ {α : Type u} {s : Set α} [Nonempty ↑s], s.Non
empty
· 使用定理 `IrreducibleSpace.toNonempty`：∀ {X : Type u_3} {inst : TopologicalSpace X
} [self : IrreducibleSpace X], Nonempty X
· 使用引理 `IsPreirreducible.of_subtype`：IsPreirreducible.of_subtype [Preirreducible
Space s] : IsPreirreducible s
· 使用定理 `IrreducibleSpace.toPreirreducibleSpace`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : IrreducibleSpace X], PreirreducibleSpace X
-/
lemma IsIrreducible.of_subtype [IrreducibleSpace s] : IsIrreducible s := by
  exact ⟨.of_subtype, .of_subtype⟩
/-
**isPreirreducible_iff_preirreducibleSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreirreducible_iff_preirreducibleSpace : IsPreirreducible s ↔ Preirreduc
ibleSpace s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.preirreducibleSpace`：Subtype.preirreducibleSpace (h : IsPreirred
ucible s) : PreirreducibleSpace s where isPreirreducible_univ
· 使用引理 `IsPreirreducible.of_subtype`：IsPreirreducible.of_subtype [Preirreducible
Space s] : IsPreirreducible s
-/
theorem isPreirreducible_iff_preirreducibleSpace :
    IsPreirreducible s ↔ PreirreducibleSpace s :=
  ⟨Subtype.preirreducibleSpace, fun _ ↦ .of_subtype⟩
/-
**isIrreducible_iff_irreducibleSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIrreducible_iff_irreducibleSpace : IsIrreducible s ↔ IrreducibleSpace s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.irreducibleSpace`：Subtype.irreducibleSpace (h : IsIrreducible s)
 : IrreducibleSpace s where isPreirreducible_univ
· 使用引理 `IsIrreducible.of_subtype`：IsIrreducible.of_subtype [IrreducibleSpace s] 
: IsIrreducible s
-/
theorem isIrreducible_iff_irreducibleSpace :
    IsIrreducible s ↔ IrreducibleSpace s :=
  ⟨Subtype.irreducibleSpace, fun _ ↦ .of_subtype⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [Subsingleton X] : PreirreducibleSpace X :=
  ⟨(Set.subsingleton_univ_iff.mpr ‹_›).isPreirreducible⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [IndiscreteTopology X] : PreirreducibleSpace X where
  isPreirreducible_univ u v := by
    simp only [IndiscreteTopology.isOpen_iff, univ_inter]
    rintro ⟨h | h⟩ <;> simp_all

/-- An infinite type with cofinite topology is an irreducible topological space. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An infinite type with cofinite topology is an irreducible topological space.
-/
instance (priority := 100) {X} [Infinite X] : IrreducibleSpace (CofiniteTopology X) where
  isPreirreducible_univ u v := by
    simp only [CofiniteTopology.isOpen_iff, univ_inter]
    intro hu hv hu' hv'
    simpa only [compl_union, compl_compl] using ((hu hu').union (hv hv')).infinite_compl.nonempty
  toNonempty := inferInstance
/-
**irreducibleComponents_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irreducibleComponents_eq_singleton [IrreducibleSpace X] : irreducibleCompo
nents X = {univ}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsGreatest.maximal_iff`：∀ {α : Type u_2} {a x : α} {s : Set α} [inst : P
artialOrder α], IsGreatest s a → (Maximal (fun x => x ∈ s) x ↔ x = a)
· 使用定理 `IrreducibleSpace.isIrreducible_univ`：IrreducibleSpace.isIrreducible_univ
 (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] : IsIrreducible (univ : S
et X)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem irreducibleComponents_eq_singleton [IrreducibleSpace X] :
    irreducibleComponents X = {univ} :=
  Set.ext fun _ ↦ IsGreatest.maximal_iff (s := {s : Set X | IsIrreducible s})
    ⟨IrreducibleSpace.isIrreducible_univ X, fun _ _ ↦ Set.subset_univ _⟩

/-- A set `s` is irreducible if and only if
for every finite collection of open sets all of whose members intersect `s`,
`s` also intersects the intersection of the entire collection
(i.e., there is an element of `s` contained in every member of the collection). -/
/-
**isIrreducible_iff_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIrreducible_iff_sInter : IsIrreducible s ↔ forall (U : Finset (Set X)), 
(forall u in U, IsOpen u) -> (forall u in U, (s inter u).Nonempty) -> (s inter ⋂
₀ ↑U).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.sInter_empty`：sInter_empty : ⋂₀ ∅ = (univ : Set α)
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `IsIrreducible.nonempty`：IsIrreducible.nonempty (h : IsIrreducible s) : s
.Nonempty
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Set.sInter_insert`：sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ inse
rt s T = s inter ⋂₀ T
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.forall_mem_insert`：forall_mem_insert (a : α) (s : Finset α) (p : 
α -> Prop) : (forall x, x in insert a s -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `Set.Finite.isOpen_sInter`：Set.Finite.isOpen_sInter {s : Set (Set X)} (hs
 : s.Finite) (h : forall t in s, IsOpen t) : IsOpen (⋂₀ s)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.sInter_singleton`：sInter_singleton (s : Set α) : ⋂₀ {s} = s

--- 原说明 ---
A set `s` is irreducible if and only if
for every finite collection of open sets all of whose members intersect `s`,
`s` also intersects the intersection of the entire collection
(i.e., there is an element of `s` contained in every member of the collection).
-/
theorem isIrreducible_iff_sInter :
    IsIrreducible s ↔
      ∀ (U : Finset (Set X)), (∀ u ∈ U, IsOpen u) → (∀ u ∈ U, (s ∩ u).Nonempty) →
        (s ∩ ⋂₀ ↑U).Nonempty := by
  refine ⟨fun h U hu hU => ?_, fun h => ⟨?_, ?_⟩⟩
  · induction U using Finset.induction_on with
    | empty => simpa using h.nonempty
    | insert u U _ IH =>
      rw [Finset.coe_insert, sInter_insert]
      rw [Finset.forall_mem_insert] at hu hU
      exact h.2 _ _ hu.1 (U.finite_toSet.isOpen_sInter hu.2) hU.1 (IH hu.2 hU.2)
  · simpa using h ∅
  · intro u v hu hv hu' hv'
    simpa [*] using h {u, v}

/-- A set is preirreducible if and only if
for every cover by two closed sets, it is contained in one of the two covering sets. -/
/-
**isPreirreducible_iff_isClosed_union_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreirreducible_iff_isClosed_union_isClosed : IsPreirreducible s ↔ forall
 z₁ z₂ : Set X, IsClosed z₁ -> IsClosed z₂ -> s subseteq z₁ union z₂ -> s subset
eq z₁ ∨ s subseteq z₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A set is preirreducible if and only if
for every cover by two closed sets, it is contained in one of the two covering s
ets.
-/
theorem isPreirreducible_iff_isClosed_union_isClosed :
    IsPreirreducible s ↔
      ∀ z₁ z₂ : Set X, IsClosed z₁ → IsClosed z₂ → s ⊆ z₁ ∪ z₂ → s ⊆ z₁ ∨ s ⊆ z₂ := by
  refine compl_surjective.forall.trans <| forall_congr' fun z₁ => compl_surjective.forall.trans <|
    forall_congr' fun z₂ => ?_
  simp only [isOpen_compl_iff, ← compl_union, inter_compl_nonempty_iff]
  refine forall₂_congr fun _ _ => ?_
  rw [← and_imp, ← not_or, not_imp_not]

/-- A set is irreducible if and only if for every cover by a finite collection of closed sets, it is
contained in one of the members of the collection. -/
/-
**isIrreducible_iff_sUnion_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIrreducible_iff_sUnion_isClosed : IsIrreducible s ↔ forall t : Finset (S
et X), (forall z in t, IsClosed z) -> (s subseteq ⋃₀ ↑t) -> exists z in t, s sub
seteq z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.forall_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β),
 q b)
· 使用定理 `compl_involutive`：compl_involutive : Function.Involutive (compl : α -> α
)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a

--- 原说明 ---
A set is irreducible if and only if for every cover by a finite collection of cl
osed sets, it is
contained in one of the members of the collection.
-/
theorem isIrreducible_iff_sUnion_isClosed :
    IsIrreducible s ↔
      ∀ t : Finset (Set X), (∀ z ∈ t, IsClosed z) → (s ⊆ ⋃₀ ↑t) → ∃ z ∈ t, s ⊆ z := by
  simp only [isIrreducible_iff_sInter]
  refine ((@compl_involutive (Set X) _).toPerm _).finsetCongr.forall_congr fun {t} => ?_
  simp_rw [Equiv.finsetCongr_apply, Finset.forall_mem_map, Finset.mem_map, Finset.coe_map,
    sUnion_image, Equiv.coe_toEmbedding, Function.Involutive.coe_toPerm, isClosed_compl_iff,
    exists_exists_and_eq_and]
  refine forall_congr' fun _ => Iff.trans ?_ not_imp_not
  simp only [not_exists, not_and, ← compl_iInter₂, ← sInter_eq_biInter,
    subset_compl_iff_disjoint_right, not_disjoint_iff_nonempty_inter]

/-- A nonempty open subset of a preirreducible subspace is dense in the subspace. -/
/-
**subset_closure_inter_of_isPreirreducible_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：subset_closure_inter_of_isPreirreducible_of_isOpen {S U : Set X} (hS : IsP
reirreducible S) (hU : IsOpen U) (h : (S inter U).Nonempty) : S subseteq closure
 (S inter U)
参数：hS : IsPreirreducible S；hU : IsOpen U；h : (S inter U).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_compl_nonempty_iff`：inter_compl_nonempty_iff {s t : Set α} : (
s inter tᶜ).Nonempty ↔ ¬s subseteq t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
A nonempty open subset of a preirreducible subspace is dense in the subspace.
-/
theorem subset_closure_inter_of_isPreirreducible_of_isOpen {S U : Set X} (hS : IsPreirreducible S)
    (hU : IsOpen U) (h : (S ∩ U).Nonempty) : S ⊆ closure (S ∩ U) := by
  by_contra h'
  obtain ⟨x, h₁, h₂, h₃⟩ :=
    hS _ (closure (S ∩ U))ᶜ hU isClosed_closure.isOpen_compl h (inter_compl_nonempty_iff.mpr h')
  exact h₃ (subset_closure ⟨h₁, h₂⟩)

/-- A set is preirreducible iff every nonempty open subset of a
preirreducible subspace is dense in the subspace. -/
/-
**isPreirreducible_iff_subset_closure_inter_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreirreducible_iff_subset_closure_inter_open (S : Set X) : IsPreirreduci
ble S ↔ (forall U : Set X, IsOpen U -> (S inter U).Nonempty -> S subseteq closur
e (S inter U))
参数：S : Set X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure_inter_of_isPreirreducible_of_isOpen`：subset_closure_inter
_of_isPreirreducible_of_isOpen {S U : Set X} (hS : IsPreirreducible S) (hU : IsO
pen U) (h : (S inter U).Nonempty) : S su…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)

--- 原说明 ---
A set is preirreducible iff every nonempty open subset of a
preirreducible subspace is dense in the subspace.
-/
theorem isPreirreducible_iff_subset_closure_inter_open (S : Set X) :
    IsPreirreducible S ↔
      (∀ U : Set X, IsOpen U → (S ∩ U).Nonempty → S ⊆ closure (S ∩ U)) := by
  refine ⟨fun h _ ↦ ?_, fun h ↦ ?_⟩
  · exact subset_closure_inter_of_isPreirreducible_of_isOpen h
  · intro a b ha hb ⟨p, pS, pa⟩ bS
    by_contra! h0
    suffices p ∉ closure (S ∩ b) from this <| (h b hb bS) pS
    simp only [closure, mem_sInter, mem_ofPred_eq, and_imp, not_forall, exists_prop]
    use aᶜ
    grind [isClosed_compl_iff, subset_compl_iff_disjoint_left, disjoint_iff_inter_eq_empty]

/-- A space is preirreducible iff all nonempty open sets are dense. -/
/-
**preirreducibleSpace_iff_open_dense** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preirreducibleSpace_iff_open_dense (X : Type*) [TopologicalSpace X] : Prei
rreducibleSpace X ↔ forall ⦃U : Set X⦄, IsOpen U -> U.Nonempty -> Dense U
参数：X : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `preirreducibleSpace_iff`：∀ (X : Type u_3) [inst : TopologicalSpace X], P
reirreducibleSpace X ↔ IsPreirreducible Set.univ
· 使用定理 `isPreirreducible_iff_subset_closure_inter_open`：isPreirreducible_iff_sub
set_closure_inter_open (S : Set X) : IsPreirreducible S ↔ (forall U : Set X, IsO
pen U -> (S inter U).Nonempty -> S s…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
A space is preirreducible iff all nonempty open sets are dense.
-/
theorem preirreducibleSpace_iff_open_dense (X : Type*) [TopologicalSpace X] :
    PreirreducibleSpace X ↔ ∀ ⦃U : Set X⦄, IsOpen U → U.Nonempty → Dense U := by
  rw [preirreducibleSpace_iff, isPreirreducible_iff_subset_closure_inter_open]
  simp only [univ_inter, univ_subset_iff, Dense]
  grind
/-
**sUnion_irreducibleComponents** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sUnion_irreducibleComponents : ⋃₀ irreducibleComponents X = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Set.mem_sUnion_of_mem`：mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (S
et α)} (hx : x in t) (ht : t in S) : x in ⋃₀ S
· 使用定理 `mem_irreducibleComponent`：mem_irreducibleComponent {x : X} : x in irredu
cibleComponent x
· 使用定理 `irreducibleComponent_mem_irreducibleComponents`：irreducibleComponent_mem
_irreducibleComponents (x : X) : irreducibleComponent x in irreducibleComponents
 X
-/
theorem sUnion_irreducibleComponents : ⋃₀ irreducibleComponents X = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ Set.mem_sUnion_of_mem mem_irreducibleComponent
    (irreducibleComponent_mem_irreducibleComponents x)
/-
**mem_of_subset_sUnion_irreducibleComponents** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_of_subset_sUnion_irreducibleComponents (Z : Set X) (hZ : Z in irreduci
bleComponents X) (S : Set (Set X)) (hS : S.Finite) (hSα : S subseteq irreducible
Components X) (hZS : Z subseteq ⋃₀ S) : Z in S
参数：Z : Set X；hZ : Z in irreducibleComponents X；S : Set (Set X)；hS : S.Finite；hSα
 : S subseteq irreducibleComponents X；hZS : Z subseteq ⋃₀ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIrreducible_iff_sUnion_isClosed`：isIrreducible_iff_sUnion_isClosed : I
sIrreducible s ↔ forall t : Finset (Set X), (forall z in t, IsClosed z) -> (s su
bseteq ⋃₀ ↑t) -> exists…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isClosed_of_mem_irreducibleComponents`：isClosed_of_mem_irreducibleCompon
ents (s) (H : s in irreducibleComponents X) : IsClosed s
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mem_of_subset_sUnion_irreducibleComponents (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (S : Set (Set X)) (hS : S.Finite) (hSα : S ⊆ irreducibleComponents X) (hZS : Z ⊆ ⋃₀ S) :
    Z ∈ S := by
  obtain ⟨W, hWS, hZW⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ.1 hS.toFinset
    (fun W hW ↦ isClosed_of_mem_irreducibleComponents W (hSα (hS.mem_toFinset.mp hW)))
    (hS.coe_toFinset.symm ▸ hZS)
  rw [hS.mem_toFinset] at hWS
  rwa [Set.Subset.antisymm hZW (hZ.2 (hSα hWS).1 hZW)]
/-
**closure_sUnion_irreducibleComponents_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：closure_sUnion_irreducibleComponents_sdiff_singleton (hX : (irreducibleCom
ponents X).Finite) (Z : Set X) (hZ : Z in irreducibleComponents X) : closure (⋃₀
 (irreducibleComponents X \ {Z}))ᶜ = Z
参数：hX : (irreducibleComponents X).Finite；Z : Set X；hZ : Z in irreducibleComponen
ts X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_subset_iff_union`：compl_subset_iff_union {s t : Set α} : sᶜ su
bseteq t ↔ s union t = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_singleton`：sUnion_singleton (s : Set α) : ⋃₀ {s} = s
· 使用定理 `Set.sUnion_union`：sUnion_union (S T : Set (Set α)) : ⋃₀ (S union T) = ⋃₀
 S union ⋃₀ T
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `sUnion_irreducibleComponents`：sUnion_irreducibleComponents : ⋃₀ irreduci
bleComponents X = Set.univ
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `isClosed_of_mem_irreducibleComponents`：isClosed_of_mem_irreducibleCompon
ents (s) (H : s in irreducibleComponents X) : IsClosed s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `subset_closure_inter_of_isPreirreducible_of_isOpen`：subset_closure_inter
_of_isPreirreducible_of_isOpen {S U : Set X} (hS : IsPreirreducible S) (hU : IsO
pen U) (h : (S inter U).Nonempty) : S su…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Set.Finite.isClosed_biUnion`：Set.Finite.isClosed_biUnion {s : Set α} {f 
: α -> Set X} (hs : s.Finite) (h : forall i in s, IsClosed (f i)) : IsClosed (⋃ 
i in s, f i)
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用定理 `Set.inter_compl_nonempty_iff`：inter_compl_nonempty_iff {s t : Set α} : (
s inter tᶜ).Nonempty ↔ ¬s subseteq t
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `mem_of_subset_sUnion_irreducibleComponents`：mem_of_subset_sUnion_irreduc
ibleComponents (Z : Set X) (hZ : Z in irreducibleComponents X) (S : Set (Set X))
 (hS : S.Finite) (hSα : S subset…
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.notMem_sdiff_of_mem`：notMem_sdiff_of_mem {s t : Set α} {x : α} (hx :
 x in t) : x ∉ s \ t
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem closure_sUnion_irreducibleComponents_sdiff_singleton
    (hX : (irreducibleComponents X).Finite) (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    closure (⋃₀ (irreducibleComponents X \ {Z}))ᶜ = Z := by
  have h : (⋃₀ (irreducibleComponents X \ {Z}))ᶜ ⊆ Z := by
    rw [Set.compl_subset_iff_union, ← Set.sUnion_singleton Z, ← Set.sUnion_union,
      Set.sUnion_singleton, Set.sdiff_union_of_subset, sUnion_irreducibleComponents]
    rwa [Set.singleton_subset_iff]
  apply Set.Subset.antisymm
  · rwa [(isClosed_of_mem_irreducibleComponents Z hZ).closure_subset_iff]
  · rw [← Set.inter_eq_right.mpr h]
    apply subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2
    · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hX.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
    · rw [Set.inter_compl_nonempty_iff]
      exact mt (mem_of_subset_sUnion_irreducibleComponents Z hZ _ hX.sdiff Set.sdiff_subset)
        (Set.notMem_sdiff_of_mem (Set.mem_singleton Z))

/-- If `∅ ≠ U ⊆ S ⊆ t` such that `U` is open and `t` is preirreducible, then `S` is irreducible. -/
/-
**IsPreirreducible.subset_irreducible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreirreducible.subset_irreducible {S U : Set X} (ht : IsPreirreducible t
) (hU : U.Nonempty) (hU' : IsOpen U) (h₁ : U subseteq S) (h₂ : S subseteq t) : I
sIrreducible S
参数：ht : IsPreirreducible t；hU : U.Nonempty；hU' : IsOpen U；h₁ : U subseteq S；h₂ :
 S subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIrreducible_iff_sInter`：isIrreducible_iff_sInter : IsIrreducible s ↔ f
orall (U : Finset (Set X)), (forall u in U, IsOpen u) -> (forall u in U, (s inte
r u).Nonempty)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.sInter_insert`：sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ inse
rt s T = s inter ⋂₀ T
· 使用定理 `Set.sInter_singleton`：sInter_singleton (s : Set α) : ⋂₀ {s} = s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `∅ ≠ U ⊆ S ⊆ t` such that `U` is open and `t` is preirreducible, then `S` is 
irreducible.
-/
theorem IsPreirreducible.subset_irreducible {S U : Set X} (ht : IsPreirreducible t)
    (hU : U.Nonempty) (hU' : IsOpen U) (h₁ : U ⊆ S) (h₂ : S ⊆ t) : IsIrreducible S := by
  obtain ⟨z, hz⟩ := hU
  replace ht : IsIrreducible t := ⟨⟨z, h₂ (h₁ hz)⟩, ht⟩
  refine ⟨⟨z, h₁ hz⟩, ?_⟩
  rintro u v hu hv ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
  obtain ⟨x, -, hx'⟩ : Set.Nonempty (t ∩ ⋂₀ ↑({U, u, v} : Finset (Set X))) := by
    refine isIrreducible_iff_sInter.mp ht {U, u, v} ?_ ?_
    · simp [*]
    · intro U H
      simp only [Finset.mem_insert, Finset.mem_singleton] at H
      rcases H with (rfl | rfl | rfl)
      exacts [⟨z, h₂ (h₁ hz), hz⟩, ⟨x, h₂ hx, hx'⟩, ⟨y, h₂ hy, hy'⟩]
  replace hx' : x ∈ U ∧ x ∈ u ∧ x ∈ v := by simpa using hx'
  exact ⟨x, h₁ hx'.1, hx'.2⟩
/-
**IsPreirreducible.open_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreirreducible.open_subset {U : Set X} (ht : IsPreirreducible t) (hU : I
sOpen U) (hU' : U subseteq t) : IsPreirreducible U
参数：ht : IsPreirreducible t；hU : IsOpen U；hU' : U subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `isPreirreducible_empty`：isPreirreducible_empty : IsPreirreducible (∅ : S
et X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsPreirreducible.subset_irreducible`：IsPreirreducible.subset_irreducible
 {S U : Set X} (ht : IsPreirreducible t) (hU : U.Nonempty) (hU' : IsOpen U) (h₁ 
: U subseteq S) (h₂ : S s…
-/
theorem IsPreirreducible.open_subset {U : Set X} (ht : IsPreirreducible t) (hU : IsOpen U)
    (hU' : U ⊆ t) : IsPreirreducible U :=
  U.eq_empty_or_nonempty.elim (fun h => h.symm ▸ isPreirreducible_empty) fun h =>
    (ht.subset_irreducible h hU (fun _ => id) hU').2
/-
**IsPreirreducible.interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreirreducible.interior (ht : IsPreirreducible t) : IsPreirreducible (in
terior t)
参数：ht : IsPreirreducible t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreirreducible.open_subset`：IsPreirreducible.open_subset {U : Set X} (
ht : IsPreirreducible t) (hU : IsOpen U) (hU' : U subseteq t) : IsPreirreducible
 U
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem IsPreirreducible.interior (ht : IsPreirreducible t) : IsPreirreducible (interior t) :=
  ht.open_subset isOpen_interior interior_subset

section

open Set.Notation

@[stacks 004Z]
/-
**IsPreirreducible.preimage_of_dense_isPreirreducible_fiber** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：IsPreirreducible.preimage_of_dense_isPreirreducible_fiber {V : Set Y} (hV 
: IsPreirreducible V) (f : X -> Y) (hf' : IsOpenMap f) (hf'' : V subseteq closur
e (V inter { x | IsPreirreducible (f ⁻¹' {x}) })) : IsPreirreducible (f ⁻¹' V)
参数：hV : IsPreirreducible V；f : X -> Y；hf' : IsOpenMap f；hf'' : V subseteq closur
e (V inter { x | IsPreirreducible (f ⁻¹' {x}) })。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall o, IsOpen o -
> x in o -> (o inter s).Nonempty
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsPreirreducible.preimage_of_dense_isPreirreducible_fiber
    {V : Set Y} (hV : IsPreirreducible V) (f : X → Y) (hf' : IsOpenMap f)
    (hf'' : V ⊆ closure (V ∩ { x | IsPreirreducible (f ⁻¹' {x}) })) :
    IsPreirreducible (f ⁻¹' V) := by
  rintro U₁ U₂ hU₁ hU₂ ⟨x, hxV, hxU₁⟩ ⟨y, hyV, hyU₂⟩
  obtain ⟨z, hzV, hz₁, hz₂⟩ :=
    hV _ _ (hf' _ hU₁) (hf' _ hU₂) ⟨f x, hxV, x, hxU₁, rfl⟩ ⟨f y, hyV, y, hyU₂, rfl⟩
  obtain ⟨z, ⟨⟨z₁, hz₁, e₁⟩, ⟨z₂, hz₂, e₂⟩⟩, hzV, hz⟩ :=
    mem_closure_iff.mp (hf'' hzV) _ ((hf' _ hU₁).inter (hf' _ hU₂)) ⟨hz₁, hz₂⟩
  obtain ⟨z₃, hz₃, hz₃'⟩ := hz _ _ hU₁ hU₂ ⟨z₁, e₁, hz₁⟩ ⟨z₂, e₂, hz₂⟩
  refine ⟨z₃, show f z₃ ∈ _ from (show f z₃ = z from hz₃) ▸ hzV, hz₃'⟩
/-
**IsPreirreducible.preimage_of_isPreirreducible_fiber** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：IsPreirreducible.preimage_of_isPreirreducible_fiber {V : Set Y} (hV : IsPr
eirreducible V) (f : X -> Y) (hf' : IsOpenMap f) (hf'' : forall x, IsPreirreduci
ble (f ⁻¹' {x})) : IsPreirreducible (f ⁻¹' V)
参数：hV : IsPreirreducible V；f : X -> Y；hf' : IsOpenMap f；hf'' : forall x, IsPreir
reducible (f ⁻¹' {x})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsPreirreducible.preimage_of_dense_isPreirreducible_fiber`：IsPreirreduci
ble.preimage_of_dense_isPreirreducible_fiber {V : Set Y} (hV : IsPreirreducible 
V) (f : X -> Y) (hf' : IsOpenMap f) (hf'' : V s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
lemma IsPreirreducible.preimage_of_isPreirreducible_fiber
    {V : Set Y} (hV : IsPreirreducible V)
    (f : X → Y) (hf' : IsOpenMap f) (hf'' : ∀ x, IsPreirreducible (f ⁻¹' {x})) :
    IsPreirreducible (f ⁻¹' V) := by
  refine hV.preimage_of_dense_isPreirreducible_fiber f hf' ?_
  simp [hf'', subset_closure]
/-
**IsPreirreducible.preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsPreirreducible.preimage (ht : IsPreirreducible t) {f : Y -> X} (hf : IsO
penEmbedding f) : IsPreirreducible (f ⁻¹' t)
参数：ht : IsPreirreducible t；hf : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsPreirreducible.preimage_of_isPreirreducible_fiber`：IsPreirreducible.pr
eimage_of_isPreirreducible_fiber {V : Set Y} (hV : IsPreirreducible V) (f : X ->
 Y) (hf' : IsOpenMap f) (hf'' : forall x,…
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `Set.Subsingleton.isPreirreducible`：Set.Subsingleton.isPreirreducible (hs
 : s.Subsingleton) : IsPreirreducible s
· 使用定理 `Set.Subsingleton.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
s : Set β}, s.Subsingleton → Function.Injective f → (f ⁻¹' s).Subsingleton
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
-/
lemma IsPreirreducible.preimage (ht : IsPreirreducible t) {f : Y → X} (hf : IsOpenEmbedding f) :
    IsPreirreducible (f ⁻¹' t) :=
  ht.preimage_of_isPreirreducible_fiber f hf.isOpenMap
    fun _ ↦ (subsingleton_singleton.preimage hf.injective).isPreirreducible
/-
**IsIrreducible.preimage_of_isPreirreducible_fiber** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIrreducible.preimage_of_isPreirreducible_fiber (ht : IsIrreducible t) (f
 : Y -> X) (hf₂ : IsOpenMap f) (hf₃ : forall x, IsPreirreducible (f ⁻¹' {x})) (h
 : (t inter Set.range f).Nonempty) : IsIrreducible (f ⁻¹' t)
参数：ht : IsIrreducible t；f : Y -> X；hf₂ : IsOpenMap f；hf₃ : forall x, IsPreirredu
cible (f ⁻¹' {x})；h : (t inter Set.range f).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsPreirreducible.preimage_of_isPreirreducible_fiber`：IsPreirreducible.pr
eimage_of_isPreirreducible_fiber {V : Set Y} (hV : IsPreirreducible V) (f : X ->
 Y) (hf' : IsOpenMap f) (hf'' : forall x,…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsIrreducible.preimage_of_isPreirreducible_fiber (ht : IsIrreducible t)
    (f : Y → X) (hf₂ : IsOpenMap f) (hf₃ : ∀ x, IsPreirreducible (f ⁻¹' {x}))
    (h : (t ∩ Set.range f).Nonempty) :
    IsIrreducible (f ⁻¹' t) := by
  refine ⟨?_, IsPreirreducible.preimage_of_isPreirreducible_fiber ht.2 f hf₂ hf₃⟩
  obtain ⟨-, hx, x, rfl⟩ := h
  exact ⟨x, hx⟩
/-
**IsIrreducible.preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIrreducible.preimage (ht : IsIrreducible t) {f : Y -> X} (hf : IsOpenEmb
edding f) (h : (t inter Set.range f).Nonempty) : IsIrreducible (f ⁻¹' t)
参数：ht : IsIrreducible t；hf : IsOpenEmbedding f；h : (t inter Set.range f).Nonempt
y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIrreducible.preimage_of_isPreirreducible_fiber`：IsIrreducible.preimage
_of_isPreirreducible_fiber (ht : IsIrreducible t) (f : Y -> X) (hf₂ : IsOpenMap 
f) (hf₃ : forall x, IsPreirreducible (…
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `Set.Subsingleton.isPreirreducible`：Set.Subsingleton.isPreirreducible (hs
 : s.Subsingleton) : IsPreirreducible s
· 使用定理 `Set.Subsingleton.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
s : Set β}, s.Subsingleton → Function.Injective f → (f ⁻¹' s).Subsingleton
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
-/
lemma IsIrreducible.preimage (ht : IsIrreducible t) {f : Y → X}
    (hf : IsOpenEmbedding f) (h : (t ∩ Set.range f).Nonempty) : IsIrreducible (f ⁻¹' t) := by
  refine ht.preimage_of_isPreirreducible_fiber f hf.isOpenMap
    (fun _ ↦ (subsingleton_singleton.preimage hf.injective).isPreirreducible) h
/-
**Topology.IsOpenEmbedding.preirreducibleSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.preirreducibleSpace {f : Y -> X} (hf : Topology.I
sOpenEmbedding f) [PreirreducibleSpace X] : PreirreducibleSpace Y where isPreirr
educible_univ
参数：hf : Topology.IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用引理 `IsPreirreducible.preimage`：IsPreirreducible.preimage (ht : IsPreirreduci
ble t) {f : Y -> X} (hf : IsOpenEmbedding f) : IsPreirreducible (f ⁻¹' t)
· 使用定理 `PreirreducibleSpace.isPreirreducible_univ`：∀ {X : Type u_3} {inst : Topo
logicalSpace X} [self : PreirreducibleSpace X], IsPreirreducible Set.univ
-/
lemma Topology.IsOpenEmbedding.preirreducibleSpace {f : Y → X} (hf : Topology.IsOpenEmbedding f)
    [PreirreducibleSpace X] :
    PreirreducibleSpace Y where
  isPreirreducible_univ := by
    rw [← Set.preimage_univ]
    exact .preimage PreirreducibleSpace.isPreirreducible_univ hf
/-
**Topology.IsOpenEmbedding.irreducibleSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.irreducibleSpace {f : Y -> X} (hf : Topology.IsOp
enEmbedding f) [IrreducibleSpace X] [Nonempty Y] : IrreducibleSpace Y where toNo
nempty
参数：hf : Topology.IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsOpenEmbedding.preirreducibleSpace`：Topology.IsOpenEmbedding.p
reirreducibleSpace {f : Y -> X} (hf : Topology.IsOpenEmbedding f) [Preirreducibl
eSpace X] : PreirreducibleSpace Y …
· 使用定理 `IrreducibleSpace.toPreirreducibleSpace`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : IrreducibleSpace X], PreirreducibleSpace X
-/
lemma Topology.IsOpenEmbedding.irreducibleSpace {f : Y → X} (hf : Topology.IsOpenEmbedding f)
    [IrreducibleSpace X] [Nonempty Y] :
    IrreducibleSpace Y where
  toNonempty := ‹_›
  __ := hf.preirreducibleSpace
/-
**preimage_mem_irreducibleComponents_of_isPreirreducible_fiber** 是 Mathlib 中的一个引
理，位于命名空间 ``。
形式化陈述：preimage_mem_irreducibleComponents_of_isPreirreducible_fiber (ht : t in ir
reducibleComponents X) {f : Y -> X} (hf₁ : Continuous f) (hf₂ : IsOpenMap f) (hf
₃ : forall x, IsPreirreducible (f ⁻¹' {x})) (h : (t inter range f).Nonempty) : f
 ⁻¹' t in irreducibleComponents Y
参数：ht : t in irreducibleComponents X；hf₁ : Continuous f；hf₂ : IsOpenMap f；hf₃ : 
forall x, IsPreirreducible (f ⁻¹' {x})；h : (t inter range f).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIrreducible.preimage_of_isPreirreducible_fiber`：IsIrreducible.preimage
_of_isPreirreducible_fiber (ht : IsIrreducible t) (f : Y -> X) (hf₂ : IsOpenMap 
f) (hf₃ : forall x, IsPreirreducible (…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsIrreducible.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s :
 Set X}, IsIrreducible s → IsIrreducible (closure s)
· 使用定理 `IsIrreducible.image`：IsIrreducible.image (H : IsIrreducible s) (f : X ->
 Y) (hf : ContinuousOn f s) : IsIrreducible (f '' s)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `subset_closure_inter_of_isPreirreducible_of_isOpen`：subset_closure_inter
_of_isPreirreducible_of_isOpen {S U : Set X} (hS : IsPreirreducible S) (hU : IsO
pen U) (h : (S inter U).Nonempty) : S su…
· 使用定理 `IsOpenMap.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → IsOpen (S
et.range f)
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
lemma preimage_mem_irreducibleComponents_of_isPreirreducible_fiber
    (ht : t ∈ irreducibleComponents X) {f : Y → X} (hf₁ : Continuous f) (hf₂ : IsOpenMap f)
    (hf₃ : ∀ x, IsPreirreducible (f ⁻¹' {x})) (h : (t ∩ range f).Nonempty) :
    f ⁻¹' t ∈ irreducibleComponents Y := by
  refine ⟨ht.1.preimage_of_isPreirreducible_fiber f hf₂ hf₃ h, fun u hu htu ↦ image_subset_iff.mp
    (subset_closure.trans (ht.2 (hu.image f hf₁.continuousOn).closure ?_))⟩
  suffices t ≤ closure (f '' f ⁻¹' t) from this.trans (closure_mono (image_mono htu))
  rw [image_preimage_eq_inter_range]
  exact subset_closure_inter_of_isPreirreducible_of_isOpen ht.1.2 hf₂.isOpen_range h
/-
**preimage_mem_irreducibleComponents** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preimage_mem_irreducibleComponents (ht : t in irreducibleComponents X) {f 
: Y -> X} (hf : IsOpenEmbedding f) (h : (t inter Set.range f).Nonempty) : f ⁻¹' 
t in irreducibleComponents Y
参数：ht : t in irreducibleComponents X；hf : IsOpenEmbedding f；h : (t inter Set.ran
ge f).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `preimage_mem_irreducibleComponents_of_isPreirreducible_fiber`：preimage_m
em_irreducibleComponents_of_isPreirreducible_fiber (ht : t in irreducibleCompone
nts X) {f : Y -> X} (hf₁ : Continuous f) (hf₂ : Is…
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `Set.Subsingleton.isPreirreducible`：Set.Subsingleton.isPreirreducible (hs
 : s.Subsingleton) : IsPreirreducible s
· 使用定理 `Set.Subsingleton.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
s : Set β}, s.Subsingleton → Function.Injective f → (f ⁻¹' s).Subsingleton
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
-/
lemma preimage_mem_irreducibleComponents (ht : t ∈ irreducibleComponents X) {f : Y → X}
    (hf : IsOpenEmbedding f) (h : (t ∩ Set.range f).Nonempty) :
    f ⁻¹' t ∈ irreducibleComponents Y := by
  refine preimage_mem_irreducibleComponents_of_isPreirreducible_fiber ht hf.continuous hf.isOpenMap
    (fun _ ↦ (subsingleton_singleton.preimage hf.injective).isPreirreducible) h
/-
**closure_image_preimage_of_isPreirreducible** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：closure_image_preimage_of_isPreirreducible (f : Y -> X) (h : IsOpenMap f) 
(s : Set X) (hne : (f ⁻¹' s).Nonempty) (hs : IsPreirreducible s) (hs' : IsClosed
 s) : closure (f '' f ⁻¹' s) = s
参数：f : Y -> X；h : IsOpenMap f；s : Set X；hne : (f ⁻¹' s).Nonempty；hs : IsPreirred
ucible s；hs' : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `subset_closure_inter_of_isPreirreducible_of_isOpen`：subset_closure_inter
_of_isPreirreducible_of_isOpen {S U : Set X} (hS : IsPreirreducible S) (hU : IsO
pen U) (h : (S inter U).Nonempty) : S su…
· 使用定理 `IsOpenMap.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → IsOpen (S
et.range f)
· 使用定理 `Set.nonempty_of_nonempty_preimage`：nonempty_of_nonempty_preimage {s : Se
t β} {f : α -> β} (hf : (f ⁻¹' s).Nonempty) : s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
lemma closure_image_preimage_of_isPreirreducible (f : Y → X) (h : IsOpenMap f) (s : Set X)
    (hne : (f ⁻¹' s).Nonempty) (hs : IsPreirreducible s) (hs' : IsClosed s) :
    closure (f '' f ⁻¹' s) = s := by
  refine subset_antisymm (closure_minimal (by simp) hs') ?_
  refine subset_trans (subset_closure_inter_of_isPreirreducible_of_isOpen hs h.isOpen_range ?_) ?_
  · exact Set.nonempty_of_nonempty_preimage (f := f) (by simpa)
  · gcongr
    grind

variable (f : X → Y) (hf₁ : Continuous f) (hf₂ : IsOpenMap f)
variable (hf₃ : ∀ x, IsPreirreducible (f ⁻¹' {x})) (hf₄ : Function.Surjective f)

include hf₁ hf₂ hf₃ hf₄
/-
**image_mem_irreducibleComponents_of_isPreirreducible_fiber** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：image_mem_irreducibleComponents_of_isPreirreducible_fiber {V : Set X} (hV 
: V in irreducibleComponents X) : f '' V in irreducibleComponents Y
参数：hV : V in irreducibleComponents X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIrreducible.image`：IsIrreducible.image (H : IsIrreducible s) (f : X ->
 Y) (hf : ContinuousOn f s) : IsIrreducible (f '' s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `IsPreirreducible.preimage_of_isPreirreducible_fiber`：IsPreirreducible.pr
eimage_of_isPreirreducible_fiber {V : Set Y} (hV : IsPreirreducible V) (f : X ->
 Y) (hf' : IsOpenMap f) (hf'' : forall x,…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
lemma image_mem_irreducibleComponents_of_isPreirreducible_fiber
    {V : Set X} (hV : V ∈ irreducibleComponents X) :
    f '' V ∈ irreducibleComponents Y :=
  ⟨hV.1.image _ hf₁.continuousOn, fun Z hZ hWZ ↦ by
    have := hV.2 ⟨(by obtain ⟨x, hx⟩ := hV.1.1; exact ⟨x, hWZ ⟨x, hx, rfl⟩⟩),
      hZ.2.preimage_of_isPreirreducible_fiber f hf₂ hf₃⟩ (Set.image_subset_iff.mp hWZ)
    rw [← Set.image_preimage_eq Z hf₄]
    exact Set.image_mono this⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `f : X → Y` is continuous, open, and has irreducible fibers, then it induces an
bijection between irreducible components -/
@[stacks 037A]
/-
**irreducibleComponentsEquivOfIsPreirreducibleFiber** 是 Mathlib 中的一个定义，位于命名空间 ``
。
形式化陈述：irreducibleComponentsEquivOfIsPreirreducibleFiber : irreducibleComponents 
Y ≃o irreducibleComponents X where invFun W
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X → Y` is continuous, open, and has irreducible fibers, then it induces 
an
bijection between irreducible components
-/
def irreducibleComponentsEquivOfIsPreirreducibleFiber :
    irreducibleComponents Y ≃o irreducibleComponents X where
  invFun W := ⟨f '' W.1,
    image_mem_irreducibleComponents_of_isPreirreducible_fiber f hf₁ hf₂ hf₃ hf₄ W.2⟩
  toFun W := ⟨f ⁻¹' W.1,
    preimage_mem_irreducibleComponents_of_isPreirreducible_fiber W.2 hf₁ hf₂ hf₃
      (by simp [hf₄.range_eq, W.2.1.1])⟩
  right_inv W := Subtype.ext <| by
    refine (Set.subset_preimage_image _ _).antisymm' (W.2.2 ?_ (Set.subset_preimage_image _ _))
    refine ⟨?_, (W.2.1.image _ hf₁.continuousOn).2.preimage_of_isPreirreducible_fiber _ hf₂ hf₃⟩
    obtain ⟨x, hx⟩ := W.2.1.1
    exact ⟨_, x, hx, rfl⟩
  left_inv _ := Subtype.ext <| Set.image_preimage_eq _ hf₄
  map_rel_iff' {W Z} := by
    refine ⟨fun H ↦ ?_, Set.preimage_mono⟩
    simpa only [Equiv.coe_fn_mk, Set.image_preimage_eq _ hf₄] using! Set.image_mono (f := f) H

end

/-
**IsDiscrete.subsingleton_of_isPreirreducible** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDiscrete.subsingleton_of_isPreirreducible (hs : IsDiscrete s) (hs' : IsP
reirreducible s) : s.Subsingleton
参数：hs : IsDiscrete s；hs' : IsPreirreducible s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isDiscrete_iff_forall_mem_exists_isOpen`：isDiscrete_iff_forall_mem_exist
s_isOpen {s : Set Y} : IsDiscrete s ↔ forall y in s, exists u, IsOpen u ∧ u inte
r s = {y}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma IsDiscrete.subsingleton_of_isPreirreducible (hs : IsDiscrete s) (hs' : IsPreirreducible s) :
    s.Subsingleton := by
  intro x hxs y hys
  obtain ⟨U, hU, hUx⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hs x hxs
  obtain ⟨V, hV, hVy⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hs y hys
  obtain ⟨z, hz⟩ := hs' _ _ hU hV ⟨x, by grind⟩ ⟨y, by grind⟩
  exact (hUx.le (by grind)).symm.trans (b := z) (hVy.le (by grind))

end Preirreducible

/-
**Function.Surjective.preirreducibleSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Surjective.preirreducibleSpace {f : X -> Y} (hfc : Continuous f) 
(hf : Function.Surjective f) [PreirreducibleSpace X] : PreirreducibleSpace Y whe
re isPreirreducible_univ
参数：hfc : Continuous f；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `IsPreirreducible.image`：IsPreirreducible.image (H : IsPreirreducible s) 
(f : X -> Y) (hf : ContinuousOn f s) : IsPreirreducible (f '' s)
· 使用定理 `PreirreducibleSpace.isPreirreducible_univ`：∀ {X : Type u_3} {inst : Topo
logicalSpace X} [self : PreirreducibleSpace X], IsPreirreducible Set.univ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
lemma Function.Surjective.preirreducibleSpace {f : X → Y} (hfc : Continuous f)
    (hf : Function.Surjective f) [PreirreducibleSpace X] : PreirreducibleSpace Y where
  isPreirreducible_univ := by
    rw [← hf.range_eq, ← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ).image _ hfc.continuousOn
/-
**Function.Surjective.irreducibleSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Surjective.irreducibleSpace {f : X -> Y} (hfc : Continuous f) (hf
 : Function.Surjective f) [IrreducibleSpace X] : IrreducibleSpace Y where isPrei
rreducible_univ
参数：hfc : Continuous f；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `IsPreirreducible.image`：IsPreirreducible.image (H : IsPreirreducible s) 
(f : X -> Y) (hf : ContinuousOn f s) : IsPreirreducible (f '' s)
· 使用定理 `PreirreducibleSpace.isPreirreducible_univ`：∀ {X : Type u_3} {inst : Topo
logicalSpace X} [self : PreirreducibleSpace X], IsPreirreducible Set.univ
· 使用定理 `IrreducibleSpace.toPreirreducibleSpace`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : IrreducibleSpace X], PreirreducibleSpace X
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `IrreducibleSpace.toNonempty`：∀ {X : Type u_3} {inst : TopologicalSpace X
} [self : IrreducibleSpace X], Nonempty X
-/
lemma Function.Surjective.irreducibleSpace {f : X → Y} (hfc : Continuous f)
    (hf : Function.Surjective f) [IrreducibleSpace X] : IrreducibleSpace Y where
  isPreirreducible_univ := by
    rw [← hf.range_eq, ← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ).image _ hfc.continuousOn
  toNonempty := Nonempty.map f inferInstance
/-
**Homeomorph.irreducibleSpace_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Homeomorph.irreducibleSpace_iff (e : X ≃ₜ Y) : IrreducibleSpace X ↔ Irredu
cibleSpace Y
参数：e : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Surjective.irreducibleSpace`：Function.Surjective.irreducibleSpa
ce {f : X -> Y} (hfc : Continuous f) (hf : Function.Surjective f) [IrreducibleSp
ace X] : IrreducibleSpace …
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
-/
lemma Homeomorph.irreducibleSpace_iff
    (e : X ≃ₜ Y) : IrreducibleSpace X ↔ IrreducibleSpace Y :=
  ⟨fun _ ↦ e.surjective.irreducibleSpace e.continuous,
    fun _ ↦ e.symm.surjective.irreducibleSpace e.symm.continuous⟩
