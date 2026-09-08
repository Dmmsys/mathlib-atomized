/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Baire spaces

A topological space is called a *Baire space*
if a countable intersection of dense open subsets is dense.
Baire theorems say that all completely metrizable spaces
and all locally compact regular spaces are Baire spaces.
We prove the theorems in `Mathlib/Topology/Baire/CompleteMetrizable`
and `Mathlib/Topology/Baire/LocallyCompactRegular`.

In this file we prove some lemmas about Baire spaces.

The good concept underlying the theorems is that of a Gδ set, i.e., a countable intersection
of open sets. Then Baire theorem can also be formulated as the fact that a countable
intersection of dense Gδ sets is a dense Gδ set. We deduce this version from Baire property.
We also prove the important consequence that, if the space is
covered by a countable union of closed sets, then the union of their interiors is dense.

We also prove that in Baire spaces, the `residual` sets are exactly those containing a dense Gδ set.
-/

public section


noncomputable section

open scoped Topology
open Filter Set TopologicalSpace

variable {X α : Type*} {ι : Sort*}

section BaireTheorem

variable [TopologicalSpace X]

/-- The intersection of finitely many open dense sets is dense. -/
/-
**Set.Finite.dense_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.dense_sInter {s : Set (Set X)} (hs : s.Finite) (ho : forall t i
n s, IsOpen t) (hd : forall t in s, Dense t) : Dense (⋂₀ s)
参数：Set X；hs : s.Finite；ho : forall t in s, IsOpen t；hd : forall t in s, Dense t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_empty`：sInter_empty : ⋂₀ ∅ = (univ : Set α)
· 使用定理 `Set.sInter_insert`：sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ inse
rt s T = s inter ⋂₀ T
· 使用定理 `Dense.inter_of_isOpen_right`：Dense.inter_of_isOpen_right (hs : Dense s) 
(ht : Dense t) (hto : IsOpen t) : Dense (s inter t)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Finite.isOpen_sInter`：Set.Finite.isOpen_sInter {s : Set (Set X)} (hs
 : s.Finite) (h : forall t in s, IsOpen t) : IsOpen (⋂₀ s)

--- 原说明 ---
The intersection of finitely many open dense sets is dense.
-/
theorem Set.Finite.dense_sInter {s : Set (Set X)} (hs : s.Finite)
    (ho : ∀ t ∈ s, IsOpen t) (hd : ∀ t ∈ s, Dense t) : Dense (⋂₀ s) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp [sInter_empty]
  | insert ha hsf ih =>
    simp only [sInter_insert, forall_mem_insert] at hd ⊢
    refine hd.1.inter_of_isOpen_right ?_ (hsf.isOpen_sInter (fun y hy => ho y (Or.inr hy)))
    exact ih ((fun y hy => ho y (Or.inr hy))) (fun y hy => hd.2 y hy)

/-- A finite set is Baire. -/
/-
**baire_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：baire_of_finite [Finite X] : BaireSpace X where baire_property f _ _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.dense_sInter`：Set.Finite.dense_sInter {s : Set (Set X)} (hs :
 s.Finite) (ho : forall t in s, IsOpen t) (hd : forall t in s, Dense t) : Dense 
(⋂₀ s)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x

--- 原说明 ---
A finite set is Baire.
-/
theorem baire_of_finite [Finite X] : BaireSpace X where
  baire_property f _ _ := sInter_range f ▸ (toFinite (range f)).dense_sInter (by grind) (by grind)

variable [BaireSpace X]

/-- Definition of a Baire space. -/
/-
**dense_iInter_of_isOpen_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_iInter_of_isOpen_nat {f : Nat -> Set X} (ho : forall n, IsOpen (f n)
) (hd : forall n, Dense (f n)) : Dense (⋂ n, f n)
参数：ho : forall n, IsOpen (f n)；hd : forall n, Dense (f n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BaireSpace.baire_property`：∀ {X : Type u_1} {inst : TopologicalSpace X} 
[self : BaireSpace X] (f : ℕ → Set X),   (∀ (n : ℕ), IsOpen (f n)) → (∀ (n : ℕ),
 Dense (f n)) →…

--- 原说明 ---
Definition of a Baire space.
-/
theorem dense_iInter_of_isOpen_nat {f : ℕ → Set X} (ho : ∀ n, IsOpen (f n))
    (hd : ∀ n, Dense (f n)) : Dense (⋂ n, f n) :=
  BaireSpace.baire_property f ho hd

/-- A dense Gδ subset of a Baire space is Baire. -/
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A dense Gδ subset of a Baire space is Baire.
-/
theorem IsGδ.baireSpace_of_dense {s : Set X} (hG : IsGδ s) (hd : Dense s) : BaireSpace s := by
  constructor
  intro f hof hdf
  obtain ⟨V, hV⟩ : ∃ V : ℕ → Set X, (∀ n, IsOpen (V n)) ∧ s = ⋂ n, V n := eq_iInter_nat hG
  choose g hg1 hg2 hg3 using fun n => exists_open_dense_of_open_dense_subtype hd (hof n) (hdf n)
  have h_inter_dense : Dense (⋂ n, g n ∩ V n) := BaireSpace.baire_property (fun n ↦ g n ∩ V n)
    (fun n => (hg1 n).inter (hV.1 n))
    (fun n => (hg2 n).inter_of_isOpen_left (hd.mono (by simp [hV.2, iInter_subset])) (hg1 n))
  have h_inter_eq : ⋂ n, g n ∩ V n = ⋂ n, f n := by ext; simp_all; grind
  exact Subtype.dense_iff.mpr fun a _ ↦ h_inter_eq ▸ h_inter_dense a

/-- If `p : Y → X` is an open embedding and `X` is a Baire space, then `Y` is a Baire space. -/
/-
**Topology.IsOpenEmbedding.baireSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.baireSpace {Y : Type*} [TopologicalSpace Y] {p : 
Y -> X} (hp : Topology.IsOpenEmbedding p) : BaireSpace Y
参数：hp : Topology.IsOpenEmbedding p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Continuous.range_subset_closure_image_dense`：Continuous.range_subset_clo
sure_image_dense {f : X -> Y} (hf : Continuous f) (hs : Dense s) : range f subse
teq closure (f '' s)
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用定理 `subset_refl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] (a : α), a ⊆ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_union`：closure_union : closure (s union t) = closure s union clo
sure t
· 使用定理 `dense_iInter_of_isOpen_nat`：dense_iInter_of_isOpen_nat {f : Nat -> Set X
} (ho : forall n, IsOpen (f n)) (hd : forall n, Dense (f n)) : Dense (⋂ n, f n)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `imp_iff_or_not`：imp_iff_or_not {b a : Prop} : b -> a ↔ a ∨ ¬b
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `p : Y → X` is an open embedding and `X` is a Baire space, then `Y` is a Bair
e space.
-/
theorem Topology.IsOpenEmbedding.baireSpace {Y : Type*} [TopologicalSpace Y] {p : Y → X}
    (hp : Topology.IsOpenEmbedding p) : BaireSpace Y := by
  constructor
  intro f hof hdf
  let s := range p
  let c := fun n : ℕ => p '' f n ∪ (closure s)ᶜ
  have c_open (n : ℕ) : IsOpen (c n) := IsOpen.union (hp.isOpenMap (f n) (hof n))
    isClosed_closure.isOpen_compl
  have c_dense (n : ℕ) : Dense (c n) := by
    rw [dense_iff_closure_eq, subset_antisymm_iff]
    have : univ ⊆ closure (c n) := calc
      _ ⊆ (interior (closure s)) ∪ (interior (closure s))ᶜ := by grind
      _ ⊆ closure s ∪ (interior (closure s))ᶜ := by gcongr; exact interior_subset
      _ ⊆ closure (p '' f n) ∪ (interior (closure s))ᶜ := union_subset_union
          (closure_minimal (hp.continuous.range_subset_closure_image_dense (hdf n))
          isClosed_closure) (subset_refl (interior (closure s))ᶜ)
      _ ⊆ closure (p '' f n) ∪ closure ((closure s)ᶜ) := union_subset_union (by simp) (by simp)
      _ = closure (c n) := closure_union.symm
    grind
  have c_inter_dense : Dense (⋂ n, c n) := dense_iInter_of_isOpen_nat c_open c_dense
  have c_inter_eq : ⋂ n, f n = p ⁻¹' (⋂ n, c n) := by
    ext x
    simp only [mem_iInter, mem_preimage, mem_union, mem_compl_iff, c]
    refine ⟨fun h i => by grind, fun h i => ?_⟩
    exact hp.injective.mem_set_image.mp (imp_iff_or_not.mpr (h i)
      (subset_closure (mem_range_self x)))
  exact c_inter_eq ▸ Dense.preimage c_inter_dense hp.isOpenMap

/-- An open subset of a Baire space is Baire. -/
/-
**IsOpen.baireSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.baireSpace {s : Set X} (hO : IsOpen s) : BaireSpace s
参数：hO : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.baireSpace`：Topology.IsOpenEmbedding.baireSpace
 {Y : Type*} [TopologicalSpace Y] {p : Y -> X} (hp : Topology.IsOpenEmbedding p)
 : BaireSpace Y
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)

--- 原说明 ---
An open subset of a Baire space is Baire.
-/
theorem IsOpen.baireSpace {s : Set X} (hO : IsOpen s) : BaireSpace s :=
  hO.isOpenEmbedding_subtypeVal.baireSpace

/-- If `f` is an open quotient map and `X` is Baire, then `Y` is Baire. -/
/-
**IsOpenQuotientMap.baireSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenQuotientMap.baireSpace {Y : Type*} [TopologicalSpace Y] {f : X -> Y}
 (hf : IsOpenQuotientMap f) : BaireSpace Y
参数：hf : IsOpenQuotientMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dense_iInter_of_isOpen_nat`：dense_iInter_of_isOpen_nat {f : Nat -> Set X
} (ho : forall n, IsOpen (f n)) (hd : forall n, Dense (f n)) : Dense (⋂ n, f n)
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `IsOpenQuotientMap.continuous`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Continuous f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpenQuotientMap.dense_preimage_iff`：dense_preimage_iff (h : IsOpenQuot
ientMap f) {s : Set Y} : Dense (f ⁻¹' s) ↔ Dense s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If `f` is an open quotient map and `X` is Baire, then `Y` is Baire.
-/
theorem IsOpenQuotientMap.baireSpace {Y : Type*} [TopologicalSpace Y] {f : X → Y}
    (hf : IsOpenQuotientMap f) : BaireSpace Y := by
  constructor
  intro u hou hdu
  have := dense_iInter_of_isOpen_nat (fun n => hf.continuous.isOpen_preimage (u n) (hou n))
    (fun n => (IsOpenQuotientMap.dense_preimage_iff hf).mpr (hdu n))
  simp_all [← preimage_iInter, IsOpenQuotientMap.dense_preimage_iff]

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with ⋂₀. -/
/-
**dense_sInter_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_sInter_of_isOpen {S : Set (Set X)} (ho : forall s in S, IsOpen s) (h
S : S.Countable) (hd : forall s in S, Dense s) : Dense (⋂₀ S)
参数：Set X；ho : forall s in S, IsOpen s；hS : S.Countable；hd : forall s in S, Dense
 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_empty`：sInter_empty : ⋂₀ ∅ = (univ : Set α)
· 使用定理 `Set.Countable.exists_eq_range`：∀ {α : Type u} {s : Set α}, s.Countable →
 s.Nonempty → ∃ f, s = Set.range f
· 使用定理 `dense_iInter_of_isOpen_nat`：dense_iInter_of_isOpen_nat {f : Nat -> Set X
} (ho : forall n, IsOpen (f n)) (hd : forall n, Dense (f n)) : Dense (⋂ n, f n)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Baire theorem: a countable intersection of dense open sets is dense. Formulated 
here with ⋂₀.
-/
theorem dense_sInter_of_isOpen {S : Set (Set X)} (ho : ∀ s ∈ S, IsOpen s) (hS : S.Countable)
    (hd : ∀ s ∈ S, Dense s) : Dense (⋂₀ S) := by
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  · rcases hS.exists_eq_range h with ⟨f, rfl⟩
    exact dense_iInter_of_isOpen_nat (forall_mem_range.1 ho) (forall_mem_range.1 hd)

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with
an index set which is a countable set in any type. -/
/-
**dense_biInter_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_biInter_of_isOpen {S : Set α} {f : α -> Set X} (ho : forall s in S, 
IsOpen (f s)) (hS : S.Countable) (hd : forall s in S, Dense (f s)) : Dense (⋂ s 
in S, f s)
参数：ho : forall s in S, IsOpen (f s)；hS : S.Countable；hd : forall s in S, Dense (
f s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `dense_sInter_of_isOpen`：dense_sInter_of_isOpen {S : Set (Set X)} (ho : f
orall s in S, IsOpen s) (hS : S.Countable) (hd : forall s in S, Dense s) : Dense
 (⋂₀ S)
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable

--- 原说明 ---
Baire theorem: a countable intersection of dense open sets is dense. Formulated 
here with
an index set which is a countable set in any type.
-/
theorem dense_biInter_of_isOpen {S : Set α} {f : α → Set X} (ho : ∀ s ∈ S, IsOpen (f s))
    (hS : S.Countable) (hd : ∀ s ∈ S, Dense (f s)) : Dense (⋂ s ∈ S, f s) := by
  rw [← sInter_image]
  refine dense_sInter_of_isOpen ?_ (hS.image _) ?_ <;> rwa [forall_mem_image]

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with
an index set which is a countable type. -/
@[wikidata Q1052678]
/-
**dense_iInter_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_iInter_of_isOpen [Countable ι] {f : ι -> Set X} (ho : forall i, IsOp
en (f i)) (hd : forall i, Dense (f i)) : Dense (⋂ s, f s)
参数：ho : forall i, IsOpen (f i)；hd : forall i, Dense (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dense_sInter_of_isOpen`：dense_sInter_of_isOpen {S : Set (Set X)} (ho : f
orall s in S, IsOpen s) (hS : S.Countable) (hd : forall s in S, Dense s) : Dense
 (⋂₀ S)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable

--- 原说明 ---
Baire theorem: a countable intersection of dense open sets is dense. Formulated 
here with
an index set which is a countable type.
-/
theorem dense_iInter_of_isOpen [Countable ι] {f : ι → Set X} (ho : ∀ i, IsOpen (f i))
    (hd : ∀ i, Dense (f i)) : Dense (⋂ s, f s) :=
  dense_sInter_of_isOpen (forall_mem_range.2 ho) (countable_range _) (forall_mem_range.2 hd)

/-- A set is residual (comeagre) if and only if it includes a dense `Gδ` set. -/
/-
**mem_residual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_residual {s : Set X} : s in residual X ↔ exists t subseteq s, IsGδ t ∧
 Dense t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_residual_iff`：mem_residual_iff {s : Set X} : s in residual X ↔ exist
s S : Set (Set X), (forall t in S, IsOpen t) ∧ (forall t in S, Dense t) ∧ S.Coun
table …
· 使用定理 `dense_sInter_of_isOpen`：dense_sInter_of_isOpen {S : Set (Set X)} (ho : f
orall s in S, IsOpen s) (hS : S.Countable) (hd : forall s in S, Dense s) : Dense
 (⋂₀ S)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `residual_of_dense_Gδ`：residual_of_dense_Gδ {s : Set X} (ho : IsGδ s) (hd
 : Dense s) : s in residual X

--- 原说明 ---
A set is residual (comeagre) if and only if it includes a dense `Gδ` set.
-/
theorem mem_residual {s : Set X} : s ∈ residual X ↔ ∃ t ⊆ s, IsGδ t ∧ Dense t := by
  constructor
  · rw [mem_residual_iff]
    rintro ⟨S, hSo, hSd, Sct, Ss⟩
    refine ⟨_, Ss, ⟨_, fun t ht => hSo _ ht, Sct, rfl⟩, ?_⟩
    exact dense_sInter_of_isOpen hSo Sct hSd
  rintro ⟨t, ts, ho, hd⟩
  exact mem_of_superset (residual_of_dense_Gδ ho hd) ts

/-- A property holds on a residual (comeagre) set if and only if it holds on some dense `Gδ` set. -/
/-
**eventually_residual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_residual {p : X -> Prop} : (forallᶠ x in residual X, p x) ↔ exi
sts t : Set X, IsGδ t ∧ Dense t ∧ forall x in t, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
A property holds on a residual (comeagre) set if and only if it holds on some de
nse `Gδ` set.
-/
theorem eventually_residual {p : X → Prop} :
    (∀ᶠ x in residual X, p x) ↔ ∃ t : Set X, IsGδ t ∧ Dense t ∧ ∀ x ∈ t, p x := by
  simp only [Filter.Eventually, mem_residual, subset_def, mem_ofPred_eq]
  tauto
/-
**dense_of_mem_residual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_of_mem_residual {s : Set X} (hs : s in residual X) : Dense s
参数：hs : s in residual X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_residual`：mem_residual {s : Set X} : s in residual X ↔ exists t subs
eteq s, IsGδ t ∧ Dense t
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
-/
theorem dense_of_mem_residual {s : Set X} (hs : s ∈ residual X) : Dense s :=
  let ⟨_, hts, _, hd⟩ := mem_residual.1 hs
  hd.mono hts

/--
In a Baire space, every nonempty open set is non‐meagre,
that is, it cannot be written as a countable union of nowhere‐dense sets.
-/
/-
**not_isMeagre_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isMeagre_of_isOpen {s : Set X} (hs : IsOpen s) (hne : s.Nonempty) : ¬ 
IsMeagre s
参数：hs : IsOpen s；hne : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.inter_open_nonempty`：∀ {X : Type u} [inst : TopologicalSpace X] {s
 : Set X},   Dense s → ∀ (U : Set X), IsOpen U → U.Nonempty → (U ∩ s).Nonempty
· 使用定理 `dense_of_mem_residual`：dense_of_mem_residual {s : Set X} (hs : s in resi
dual X) : Dense s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMeagre.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : Set X),
 IsMeagre s = (sᶜ ∈ residual X)

--- 原说明 ---
In a Baire space, every nonempty open set is non‐meagre,
that is, it cannot be written as a countable union of nowhere‐dense sets.
-/
theorem not_isMeagre_of_isOpen {s : Set X} (hs : IsOpen s) (hne : s.Nonempty) : ¬ IsMeagre s := by
  intro h
  obtain ⟨x, hx, hxc⟩ :=
    (dense_of_mem_residual (by rwa [IsMeagre] at h)).inter_open_nonempty s hs hne
  exact hxc hx

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with ⋂₀. -/
/-
**dense_sInter_of_G** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated he
re with ⋂₀.
-/
theorem dense_sInter_of_Gδ {S : Set (Set X)} (ho : ∀ s ∈ S, IsGδ s) (hS : S.Countable)
    (hd : ∀ s ∈ S, Dense s) : Dense (⋂₀ S) :=
  dense_of_mem_residual ((countable_sInter_mem hS).mpr
    (fun _ hs => residual_of_dense_Gδ (ho _ hs) (hd _ hs)))

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is a countable type. -/
/-
**dense_iInter_of_G** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated he
re with
an index set which is a countable type.
-/
theorem dense_iInter_of_Gδ [Countable ι] {f : ι → Set X} (ho : ∀ s, IsGδ (f s))
    (hd : ∀ s, Dense (f s)) : Dense (⋂ s, f s) :=
  dense_sInter_of_Gδ (forall_mem_range.2 ‹_›) (countable_range _) (forall_mem_range.2 ‹_›)

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is a countable set in any type. -/
/-
**dense_biInter_of_G** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated he
re with
an index set which is a countable set in any type.
-/
theorem dense_biInter_of_Gδ {S : Set α} {f : ∀ x ∈ S, Set X} (ho : ∀ s (H : s ∈ S), IsGδ (f s H))
    (hS : S.Countable) (hd : ∀ s (H : s ∈ S), Dense (f s H)) : Dense (⋂ s ∈ S, f s ‹_›) := by
  rw [biInter_eq_iInter]
  have := hS.to_subtype
  exact dense_iInter_of_Gδ (fun s => ho s s.2) fun s => hd s s.2

/-- Baire theorem: the intersection of two dense Gδ sets is dense. -/
/-
**Dense.inter_of_G** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Baire theorem: the intersection of two dense Gδ sets is dense.
-/
theorem Dense.inter_of_Gδ {s t : Set X} (hs : IsGδ s) (ht : IsGδ t) (hsc : Dense s)
    (htc : Dense t) : Dense (s ∩ t) := by
  rw [inter_eq_iInter]
  apply dense_iInter_of_Gδ <;> simp [Bool.forall_bool, *]

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with `⋃`. -/
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a countable family of closed sets cover a dense `Gδ` set, then the union of t
heir interiors
is dense. Formulated here with `⋃`.
-/
theorem IsGδ.dense_iUnion_interior_of_closed [Countable ι] {s : Set X} (hs : IsGδ s) (hd : Dense s)
    {f : ι → Set X} (hc : ∀ i, IsClosed (f i)) (hU : s ⊆ ⋃ i, f i) :
    Dense (⋃ i, interior (f i)) := by
  let g i := (frontier (f i))ᶜ
  have hgo : ∀ i, IsOpen (g i) := fun i => isClosed_frontier.isOpen_compl
  have hgd : Dense (⋂ i, g i) := by
    refine dense_iInter_of_isOpen hgo fun i x => ?_
    rw [closure_compl, interior_frontier (hc _)]
    exact id
  refine (hd.inter_of_Gδ hs (.iInter_of_isOpen fun i => (hgo i)) hgd).mono ?_
  rintro x ⟨hxs, hxg⟩
  rw [mem_iInter] at hxg
  rcases mem_iUnion.1 (hU hxs) with ⟨i, hi⟩
  exact mem_iUnion.2 ⟨i, self_sdiff_frontier (f i) ▸ ⟨hi, hxg _⟩⟩

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with a union over a countable set in any type. -/
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a countable family of closed sets cover a dense `Gδ` set, then the union of t
heir interiors
is dense. Formulated here with a union over a countable set in any type.
-/
theorem IsGδ.dense_biUnion_interior_of_closed {t : Set α} {s : Set X} (hs : IsGδ s) (hd : Dense s)
    (ht : t.Countable) {f : α → Set X} (hc : ∀ i ∈ t, IsClosed (f i)) (hU : s ⊆ ⋃ i ∈ t, f i) :
    Dense (⋃ i ∈ t, interior (f i)) := by
  have := ht.to_subtype
  simp only [biUnion_eq_iUnion, SetCoe.forall'] at *
  exact hs.dense_iUnion_interior_of_closed hd hc hU

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with `⋃₀`. -/
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a countable family of closed sets cover a dense `Gδ` set, then the union of t
heir interiors
is dense. Formulated here with `⋃₀`.
-/
theorem IsGδ.dense_sUnion_interior_of_closed {T : Set (Set X)} {s : Set X} (hs : IsGδ s)
    (hd : Dense s) (hc : T.Countable) (hc' : ∀ t ∈ T, IsClosed t) (hU : s ⊆ ⋃₀ T) :
    Dense (⋃ t ∈ T, interior t) :=
  hs.dense_biUnion_interior_of_closed hd hc hc' <| by rwa [← sUnion_eq_biUnion]

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is a countable set in any type. -/
/-
**dense_biUnion_interior_of_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_biUnion_interior_of_closed {S : Set α} {f : α -> Set X} (hc : forall
 s in S, IsClosed (f s)) (hS : S.Countable) (hU : ⋃ s in S, f s = univ) : Dense 
(⋃ s in S, interior (f s))
参数：hc : forall s in S, IsClosed (f s)；hS : S.Countable；hU : ⋃ s in S, f s = univ
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGδ.dense_biUnion_interior_of_closed`：IsGδ.dense_biUnion_interior_of_cl
osed {t : Set α} {s : Set X} (hs : IsGδ s) (hd : Dense s) (ht : t.Countable) {f 
: α -> Set X} (hc : forall …
· 使用定理 `IsGδ.univ`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsGδ Set.univ
· 使用定理 `dense_univ`：dense_univ : Dense (univ : Set X)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a

--- 原说明 ---
Baire theorem: if countably many closed sets cover the whole space, then their i
nteriors
are dense. Formulated here with an index set which is a countable set in any typ
e.
-/
theorem dense_biUnion_interior_of_closed {S : Set α} {f : α → Set X} (hc : ∀ s ∈ S, IsClosed (f s))
    (hS : S.Countable) (hU : ⋃ s ∈ S, f s = univ) : Dense (⋃ s ∈ S, interior (f s)) :=
  IsGδ.univ.dense_biUnion_interior_of_closed dense_univ hS hc hU.ge

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with `⋃₀`. -/
/-
**dense_sUnion_interior_of_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_sUnion_interior_of_closed {S : Set (Set X)} (hc : forall s in S, IsC
losed s) (hS : S.Countable) (hU : ⋃₀ S = univ) : Dense (⋃ s in S, interior s)
参数：Set X；hc : forall s in S, IsClosed s；hS : S.Countable；hU : ⋃₀ S = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGδ.dense_sUnion_interior_of_closed`：IsGδ.dense_sUnion_interior_of_clos
ed {T : Set (Set X)} {s : Set X} (hs : IsGδ s) (hd : Dense s) (hc : T.Countable)
 (hc' : forall t in T, IsC…
· 使用定理 `IsGδ.univ`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsGδ Set.univ
· 使用定理 `dense_univ`：dense_univ : Dense (univ : Set X)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a

--- 原说明 ---
Baire theorem: if countably many closed sets cover the whole space, then their i
nteriors
are dense. Formulated here with `⋃₀`.
-/
theorem dense_sUnion_interior_of_closed {S : Set (Set X)} (hc : ∀ s ∈ S, IsClosed s)
    (hS : S.Countable) (hU : ⋃₀ S = univ) : Dense (⋃ s ∈ S, interior s) :=
  IsGδ.univ.dense_sUnion_interior_of_closed dense_univ hS hc hU.ge

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is a countable type. -/
/-
**dense_iUnion_interior_of_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_iUnion_interior_of_closed [Countable ι] {f : ι -> Set X} (hc : foral
l i, IsClosed (f i)) (hU : ⋃ i, f i = univ) : Dense (⋃ i, interior (f i))
参数：hc : forall i, IsClosed (f i)；hU : ⋃ i, f i = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGδ.dense_iUnion_interior_of_closed`：IsGδ.dense_iUnion_interior_of_clos
ed [Countable ι] {s : Set X} (hs : IsGδ s) (hd : Dense s) {f : ι -> Set X} (hc :
 forall i, IsClosed (f i))…
· 使用定理 `IsGδ.univ`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsGδ Set.univ
· 使用定理 `dense_univ`：dense_univ : Dense (univ : Set X)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a

--- 原说明 ---
Baire theorem: if countably many closed sets cover the whole space, then their i
nteriors
are dense. Formulated here with an index set which is a countable type.
-/
theorem dense_iUnion_interior_of_closed [Countable ι] {f : ι → Set X} (hc : ∀ i, IsClosed (f i))
    (hU : ⋃ i, f i = univ) : Dense (⋃ i, interior (f i)) :=
  IsGδ.univ.dense_iUnion_interior_of_closed dense_univ hc hU.ge

variable [Nonempty X]

/-- One of the most useful consequences of Baire theorem: if a countable union of closed sets
covers the space, then one of the sets has nonempty interior. -/
/-
**nonempty_interior_of_iUnion_of_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_interior_of_iUnion_of_closed [Countable ι] {f : ι -> Set X} (hc :
 forall i, IsClosed (f i)) (hU : ⋃ i, f i = univ) : exists i, (interior <| f i).
Nonempty
参数：hc : forall i, IsClosed (f i)；hU : ⋃ i, f i = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.nonempty`：Dense.nonempty [h : Nonempty X] (hs : Dense s) : s.Nonem
pty
· 使用定理 `dense_iUnion_interior_of_closed`：dense_iUnion_interior_of_closed [Counta
ble ι] {f : ι -> Set X} (hc : forall i, IsClosed (f i)) (hU : ⋃ i, f i = univ) :
 Dense (⋃ i, interior…

--- 原说明 ---
One of the most useful consequences of Baire theorem: if a countable union of cl
osed sets
covers the space, then one of the sets has nonempty interior.
-/
theorem nonempty_interior_of_iUnion_of_closed [Countable ι] {f : ι → Set X}
    (hc : ∀ i, IsClosed (f i)) (hU : ⋃ i, f i = univ) : ∃ i, (interior <| f i).Nonempty := by
  simpa using (dense_iUnion_interior_of_closed hc hU).nonempty

/-- In a nonempty Baire space, any dense `Gδ` set is not meagre. -/
/-
**not_isMeagre_of_isG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a nonempty Baire space, any dense `Gδ` set is not meagre.
-/
theorem not_isMeagre_of_isGδ_of_dense {s : Set X} (hs : IsGδ s) (hd : Dense s) :
    ¬ IsMeagre s := by
  intro h
  rcases mem_residual.1 h with ⟨t, hts, htG, hd'⟩
  rcases (hd.inter_of_Gδ hs htG hd').nonempty with ⟨x, hx₁, hx₂⟩
  exact hts hx₂ hx₁

/-- In a nonempty Baire space, a residual set is not meagre. -/
/-
**not_isMeagre_of_mem_residual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isMeagre_of_mem_residual {s : Set X} (hs : s in residual X) : ¬ IsMeag
re s
参数：hs : s in residual X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_residual`：mem_residual {s : Set X} : s in residual X ↔ exists t subs
eteq s, IsGδ t ∧ Dense t
· 使用定理 `not_isMeagre_of_isGδ_of_dense`：not_isMeagre_of_isGδ_of_dense {s : Set X}
 (hs : IsGδ s) (hd : Dense s) : ¬ IsMeagre s
· 使用引理 `IsMeagre.mono`：IsMeagre.mono {s t : Set X} (hts : t subseteq s) (hs : Is
Meagre s) : IsMeagre t

--- 原说明 ---
In a nonempty Baire space, a residual set is not meagre.
-/
theorem not_isMeagre_of_mem_residual {s : Set X} (hs : s ∈ residual X) :
    ¬ IsMeagre s := by
  rcases (mem_residual (X := X)).1 hs with ⟨t, ht_sub, htGδ, ht_dense⟩
  intro hs_meagre
  exact not_isMeagre_of_isGδ_of_dense (X := X) htGδ ht_dense (hs_meagre.mono ht_sub)

end BaireTheorem

