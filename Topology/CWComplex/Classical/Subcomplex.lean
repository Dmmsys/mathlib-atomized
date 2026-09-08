/-
Copyright (c) 2025 Floris van Doorn and Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Hannah Scholz
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Subcomplexes

In this file we discuss subcomplexes of CW complexes.
The definition of subcomplexes is in the file `Mathlib/Topology/CWComplex/Classical/Basic.lean`.

## Main results
* `RelCWComplex.Subcomplex.instRelCWComplex`: a subcomplex of a (relative) CW complex is again a
  (relative) CW complex.

## References
* [K. Jänich, *Topology*][Janich1984]
-/

@[expose] public section

noncomputable section

open Metric Set

namespace Topology

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}

@[alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.closedCell_subset_of_mem** 是 Mathlib 中的一个定理，位
于命名空间 `Topology.RelCWComplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [T2Space X] [inst 
: Topology.RelCWComplex C D]   (E : Topology.RelCWComplex.Subcomplex C) {n : ℕ} 
{i : Topology.RelCWComplex.cell C n},   i ∈ E.I n → Topology.RelCWComplex.closed
Cell n i ⊆ ↑E
参数：E : Topology.RelCWComplex.Subcomplex C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.RelCWComplex.closure_openCell_eq_closedCell`：∀ {X : Type u_1} [
t : TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] [T2Spac
e X] {n : ℕ}   {j : Topology.RelCWComplex.…
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用引理 `Topology.RelCWComplex.Subcomplex.closed`：closed (E : Subcomplex C) : IsC
losed (E : Set X)
· 使用引理 `Topology.RelCWComplex.Subcomplex.union`：union (E : Subcomplex C) : D uni
on ⋃ (n : Nat) (j : E.I n), openCell (C
· 使用定理 `Set.subset_union_of_subset_right`：subset_union_of_subset_right {s u : Se
t α} (h : s subseteq u) (t : Set α) : s subseteq t union u
· 使用定理 `Set.subset_iUnion_of_subset`：subset_iUnion_of_subset {s : Set α} {t : ι 
-> Set α} (i : ι) (h : s subseteq t i) : s subseteq ⋃ i, t i
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
-/
lemma RelCWComplex.Subcomplex.closedCell_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (hi : i ∈ E.I n) :
    closedCell n i ⊆ E := by
  rw [← closure_openCell_eq_closedCell, E.closed.closure_subset_iff, ← E.union]
  apply subset_union_of_subset_right
  exact subset_iUnion_of_subset n
    (subset_iUnion (fun (j : ↑(E.I n)) ↦ openCell (C := C) n j) ⟨i, hi⟩)

@[alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.openCell_subset_of_mem** 是 Mathlib 中的一个定理，位于命
名空间 `Topology.RelCWComplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [T2Space X] [inst 
: Topology.RelCWComplex C D]   (E : Topology.RelCWComplex.Subcomplex C) {n : ℕ} 
{i : Topology.RelCWComplex.cell C n},   i ∈ E.I n → Topology.RelCWComplex.openCe
ll n i ⊆ ↑E
参数：E : Topology.RelCWComplex.Subcomplex C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Topology.RelCWComplex.openCell_subset_closedCell`：∀ {X : Type u_1} [t : 
TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (
i : Topology.RelCWComplex.cell C n), T…
· 使用定理 `Topology.RelCWComplex.Subcomplex.closedCell_subset_of_mem`：∀ {X : Type u
_1} [t : TopologicalSpace X] {C D : Set X} [T2Space X] [inst : Topology.RelCWCom
plex C D]   (E : Topology.RelCWComplex.Subcompl…
-/
lemma RelCWComplex.Subcomplex.openCell_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (hi : i ∈ E.I n) :
    openCell n i ⊆ E :=
  (openCell_subset_closedCell n i).trans (closedCell_subset_of_mem E hi)

@[alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.cellFrontier_subset_of_mem** 是 Mathlib 中的一个定理
，位于命名空间 `Topology.RelCWComplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [T2Space X] [inst 
: Topology.RelCWComplex C D]   (E : Topology.RelCWComplex.Subcomplex C) {n : ℕ} 
{i : Topology.RelCWComplex.cell C n},   i ∈ E.I n → Topology.RelCWComplex.cellFr
ontier n i ⊆ ↑E
参数：E : Topology.RelCWComplex.Subcomplex C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Topology.RelCWComplex.cellFrontier_subset_closedCell`：∀ {X : Type u_1} [
t : TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)
   (i : Topology.RelCWComplex.cell C n), T…
· 使用定理 `Topology.RelCWComplex.Subcomplex.closedCell_subset_of_mem`：∀ {X : Type u
_1} [t : TopologicalSpace X] {C D : Set X} [T2Space X] [inst : Topology.RelCWCom
plex C D]   (E : Topology.RelCWComplex.Subcompl…
-/
lemma RelCWComplex.Subcomplex.cellFrontier_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (hi : i ∈ E.I n) :
    cellFrontier n i ⊆ E :=
  (cellFrontier_subset_closedCell n i).trans (closedCell_subset_of_mem E hi)

/-- A subcomplex is the union of its closed cells and its base. -/
/-
**Topology.RelCWComplex.Subcomplex.union_closedCell** 是 Mathlib 中的一个定理，位于命名空间 `T
opology.RelCWComplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [T2Space X] [inst 
: Topology.RelCWComplex C D]   (E : Topology.RelCWComplex.Subcomplex C), D ∪ ⋃ n
, ⋃ j, Topology.RelCWComplex.closedCell n ↑j = ↑E
参数：E : Topology.RelCWComplex.Subcomplex C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Topology.RelCWComplex.Subcomplex.base_subset`：∀ {X : Type u_1} [t : Topo
logicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   (E : Topology
.RelCWComplex.Subcomplex C), D ⊆ ↑…
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Topology.RelCWComplex.Subcomplex.closedCell_subset_of_mem`：∀ {X : Type u
_1} [t : TopologicalSpace X] {C D : Set X} [T2Space X] [inst : Topology.RelCWCom
plex C D]   (E : Topology.RelCWComplex.Subcompl…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.RelCWComplex.Subcomplex.union`：union (E : Subcomplex C) : D uni
on ⋃ (n : Nat) (j : E.I n), openCell (C
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
· 使用定理 `Topology.RelCWComplex.openCell_subset_closedCell`：∀ {X : Type u_1} [t : 
TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (
i : Topology.RelCWComplex.cell C n), T…

--- 原说明 ---
A subcomplex is the union of its closed cells and its base.
-/
lemma RelCWComplex.Subcomplex.union_closedCell [T2Space X] [RelCWComplex C D] (E : Subcomplex C) :
    D ∪ ⋃ (n : ℕ) (j : E.I n), closedCell (C := C) n j = E := by
  apply subset_antisymm
  · apply union_subset E.base_subset
    exact iUnion₂_subset fun n i ↦ closedCell_subset_of_mem E i.2
  · rw [← E.union]
    apply union_subset_union_right
    apply iUnion₂_mono fun n i ↦ ?_
    exact openCell_subset_closedCell (C := C) n i

/-- A subcomplex is the union of its closed cells. -/
/-
**Topology.CWComplex.Subcomplex.union_closedCell** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logy.CWComplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [T2Space X] [inst : 
Topology.CWComplex C]   (E : Topology.RelCWComplex.Subcomplex C), ⋃ n, ⋃ j, Topo
logy.RelCWComplex.closedCell n ↑j = ↑E
参数：E : Topology.RelCWComplex.Subcomplex C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `Topology.RelCWComplex.Subcomplex.union_closedCell`：∀ {X : Type u_1} [t :
 TopologicalSpace X] {C D : Set X} [T2Space X] [inst : Topology.RelCWComplex C D
]   (E : Topology.RelCWComplex.Subcompl…

--- 原说明 ---
A subcomplex is the union of its closed cells.
-/
lemma CWComplex.Subcomplex.union_closedCell [T2Space X] [CWComplex C] (E : Subcomplex C) :
    ⋃ (n : ℕ) (j : E.I n), closedCell (C := C) n j = E :=
  (empty_union _).symm.trans (RelCWComplex.Subcomplex.union_closedCell E)

@[alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.disjoint_openCell_subcomplex_of_not_mem** 是 M
athlib 中的一个定理，位于命名空间 `Topology.RelCWComplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D]   (E : Topology.RelCWComplex.Subcomplex C) {n : ℕ} {i : Topolog
y.RelCWComplex.cell C n},   i ∉ E.I n → Disjoint (Topology.RelCWComplex.openCell
 n i) ↑E
参数：E : Topology.RelCWComplex.Subcomplex C；Topology.RelCWComplex.openCell n i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Topology.RelCWComplex.disjointBase`：∀ {X : Type u_1} [t : TopologicalSpa
ce X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (i : Topology.R
elCWComplex.cell C n), D…
· 使用定理 `Topology.RelCWComplex.disjoint_openCell_of_ne`：∀ {X : Type u_1} [t : Top
ologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] {n m : ℕ}   {i
 : Topology.RelCWComplex.cell C n} …
-/
lemma RelCWComplex.Subcomplex.disjoint_openCell_subcomplex_of_not_mem [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (h : i ∉ E.I n) : Disjoint (openCell n i) E := by
  simp_rw [← union, disjoint_union_right, disjoint_iUnion_right]
  exact ⟨disjointBase n i , fun _ _ ↦ disjoint_openCell_of_ne (by lia)⟩

open scoped Classical in
/-- A subcomplex is again a CW complex. -/
@[simps]
/-
**Topology.RelCWComplex.Subcomplex.instRelCWComplex** 是 Mathlib 中的一个定义，位于命名空间 `T
opology.RelCWComplex.Subcomplex`。
形式化陈述：{X : Type u_1} →   [t : TopologicalSpace X] →     {C D : Set X} →       [T
2Space X] →         [inst : Topology.RelCWComplex C D] → (E : Topology.RelCWComp
lex.Subcomplex C) → Topology.RelCWComplex (↑E) D
参数：E : Topology.RelCWComplex.Subcomplex C；↑E。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.isClosedBase`：∀ {X : Type u} {inst : TopologicalSp
ace X} (C : Set X) {D : outParam (Set X)} [self : Topology.RelCWComplex C D],   
IsClosed D
· 使用定理 `Topology.RelCWComplex.Subcomplex.union_closedCell`：∀ {X : Type u_1} [t :
 TopologicalSpace X] {C D : Set X} [T2Space X] [inst : Topology.RelCWComplex C D
]   (E : Topology.RelCWComplex.Subcompl…

--- 原说明 ---
A subcomplex is again a CW complex.
-/
instance RelCWComplex.Subcomplex.instRelCWComplex [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) : RelCWComplex E D where
  cell n := E.I n
  map n i := map (C := C) n i
  source_eq n i := source_eq (C := C) n i
  continuousOn n i := continuousOn (C := C) n i
  continuousOn_symm n i := continuousOn_symm (C := C) n i
  pairwiseDisjoint' := by
    intro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
    refine @pairwiseDisjoint' _ _ C D _ ⟨n, i⟩ trivial ⟨m, j⟩ trivial ?_
    exact Function.injective_id.sigma_map (fun _ ↦ Subtype.val_injective) |>.ne hne
  disjointBase' n i := disjointBase' (C := C) n i
  mapsTo := by
    intro n i
    rcases cellFrontier_subset_finite_openCell (C := C) n i with ⟨J, hJ⟩
    use fun m ↦ Finset.preimage (J m) Subtype.val Subtype.val_injective.injOn
    rw [mapsTo_iff_image_subset]
    intro x hx
    specialize hJ hx
    simp_rw [iUnion_coe_set, mem_union, mem_iUnion, Finset.mem_preimage, exists_prop,
      Decidable.or_iff_not_imp_left] at hJ ⊢
    intro h
    specialize hJ h
    obtain ⟨m, hmn, j, hj, hxj⟩ := hJ
    suffices j ∈ E.I m from ⟨m, hmn, j, this, hj, openCell_subset_closedCell _ _ hxj⟩
    have : x ∈ (E : Set X) := E.cellFrontier_subset_of_mem i.2 hx
    by_contra hj'
    exact E.disjoint_openCell_subcomplex_of_not_mem hj' |>.notMem_of_mem_left hxj this
  closed' A hA h := by
    apply isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
      (subset_trans hA (subset_complex (C := C) E)) h.2
    intro n _ j
    by_cases hj : j ∈ E.I n
    · exact Or.intro_right _ (h.1 n ⟨j, hj⟩)
    · exact Or.intro_left _ ((disjoint_openCell_subcomplex_of_not_mem E hj).symm.mono_left hA)
  isClosedBase := isClosedBase (C := C)
  union' := union_closedCell E

/-- A subcomplex is again a CW complex. -/
/-
**Topology.CWComplex.Subcomplex.instCWComplex** 是 Mathlib 中的一个定义，位于命名空间 `Topolog
y.CWComplex.Subcomplex`。
形式化陈述：{X : Type u_1} →   [t : TopologicalSpace X] →     {C : Set X} →       [T2S
pace X] → [inst : Topology.CWComplex C] → (E : Topology.RelCWComplex.Subcomplex 
C) → Topology.CWComplex ↑E
参数：E : Topology.RelCWComplex.Subcomplex C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subcomplex is again a CW complex.
-/
instance CWComplex.Subcomplex.instCWComplex [T2Space X] [CWComplex C] (E : Subcomplex C) :
    CWComplex (E : Set X) :=
  RelCWComplex.toCWComplex (E : Set X)

@[simp]
/-
**Topology.CWComplex.Subcomplex.cell_def** 是 Mathlib 中的一个定理，位于命名空间 `Topology.CWC
omplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : T2Space X] [
inst_1 : Topology.CWComplex C]   (E : Topology.RelCWComplex.Subcomplex C) (n : ℕ
), Topology.RelCWComplex.cell (↑E) n = ↑(E.I n)
参数：E : Topology.RelCWComplex.Subcomplex C；n : ℕ；↑E；E.I n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma CWComplex.Subcomplex.cell_def [T2Space X] [CWComplex C] (E : Subcomplex C)
    (n : ℕ) : cell (E : Set X) n = E.I (C := C) n :=
  rfl

@[simp]
/-
**Topology.CWComplex.Subcomplex.map_def** 是 Mathlib 中的一个定理，位于命名空间 `Topology.CWCo
mplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : T2Space X] [
inst_1 : Topology.CWComplex C]   (E : Topology.RelCWComplex.Subcomplex C) (n : ℕ
) (i : ↑(E.I n)),   Topology.RelCWComplex.map n i = Topology.RelCWComplex.map n 
↑i
参数：E : Topology.RelCWComplex.Subcomplex C；n : ℕ；i : ↑(E.I n)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma CWComplex.Subcomplex.map_def [T2Space X] [CWComplex C] (E : Subcomplex C) (n : ℕ)
    (i : E.I n) : map (C := E) n i = map (C := C) n i :=
  rfl

@[simp]
/-
**Topology.RelCWComplex.Subcomplex.openCell_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gy.RelCWComplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D]   (E : Topology.RelCWComplex.Subcomplex C)
 (n : ℕ) (i : ↑(E.I n)),   Topology.RelCWComplex.openCell n i = Topology.RelCWCo
mplex.openCell n ↑i
参数：E : Topology.RelCWComplex.Subcomplex C；n : ℕ；i : ↑(E.I n)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RelCWComplex.Subcomplex.openCell_eq [T2Space X] [RelCWComplex C D] (E : Subcomplex C) (n : ℕ)
    (i : E.I n) : openCell (C := E) n i = openCell n (i : cell C n) := by
  rfl

@[simp]
/-
**Topology.RelCWComplex.Subcomplex.closedCell_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logy.RelCWComplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D]   (E : Topology.RelCWComplex.Subcomplex C)
 (n : ℕ) (i : ↑(E.I n)),   Topology.RelCWComplex.closedCell n i = Topology.RelCW
Complex.closedCell n ↑i
参数：E : Topology.RelCWComplex.Subcomplex C；n : ℕ；i : ↑(E.I n)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RelCWComplex.Subcomplex.closedCell_eq [T2Space X] [RelCWComplex C D] (E : Subcomplex C)
    (n : ℕ) (i : E.I n) : closedCell (C := E) n i = closedCell n (i : cell C n) := by
  rfl

@[simp]
/-
**Topology.RelCWComplex.Subcomplex.cellFrontier_eq** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.RelCWComplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D]   (E : Topology.RelCWComplex.Subcomplex C)
 (n : ℕ) (i : ↑(E.I n)),   Topology.RelCWComplex.cellFrontier n i = Topology.Rel
CWComplex.cellFrontier n ↑i
参数：E : Topology.RelCWComplex.Subcomplex C；n : ℕ；i : ↑(E.I n)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RelCWComplex.Subcomplex.cellFrontier_eq [T2Space X] [RelCWComplex C D] (E : Subcomplex C)
    (n : ℕ) (i : E.I n) : cellFrontier (C := E) n i = cellFrontier n (i : cell C n) := by
  rfl

@[alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.finiteType_subcomplex_of_finiteType** 是 Mathl
ib 中的一个定理，位于命名空间 `Topology.RelCWComplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D]   [Topology.RelCWComplex.FiniteType C] (E 
: Topology.RelCWComplex.Subcomplex C), Topology.RelCWComplex.FiniteType ↑E
参数：E : Topology.RelCWComplex.Subcomplex C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.FiniteType.finite_cell`：∀ {X : Type u} {inst : Top
ologicalSpace X} {C D : Set X} {inst_1 : Topology.RelCWComplex C D}   [self : To
pology.RelCWComplex.FiniteType C] …
-/
instance RelCWComplex.Subcomplex.finiteType_subcomplex_of_finiteType [T2Space X]
    [RelCWComplex C D] [FiniteType C] (E : Subcomplex C) : FiniteType (E : Set X) where
  finite_cell n :=
    let _ := FiniteType.finite_cell (C := C) (D := D) n
    Subtype.finite

@[alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.finiteDimensional_subcomplex_of_finiteDimensi
onal** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCWComplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D]   [Topology.RelCWComplex.FiniteDimensional
 C] (E : Topology.RelCWComplex.Subcomplex C),   Topology.RelCWComplex.FiniteDime
nsional ↑E
参数：E : Topology.RelCWComplex.Subcomplex C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Topology.RelCWComplex.FiniteDimensional.eventually_isEmpty_cell`：∀ {X : 
Type u} {inst : TopologicalSpace X} {C D : Set X} {inst_1 : Topology.RelCWComple
x C D}   [self : Topology.RelCWComplex.FiniteDimensio…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
instance RelCWComplex.Subcomplex.finiteDimensional_subcomplex_of_finiteDimensional
    [T2Space X] [RelCWComplex C D] [FiniteDimensional C] (E : Subcomplex C) :
    FiniteDimensional (E : Set X) where
  eventually_isEmpty_cell := by
    filter_upwards [FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)] with n hn
    simp [isEmpty_subtype]

/-- A subcomplex of a finite CW complex is again finite. -/
@[alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.finite_subcomplex_of_finite** 是 Mathlib 中的一个定
理，位于命名空间 `Topology.RelCWComplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D]   [Topology.RelCWComplex.Finite C] (E : To
pology.RelCWComplex.Subcomplex C), Topology.RelCWComplex.Finite ↑E
参数：E : Topology.RelCWComplex.Subcomplex C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.finite_of_finiteDimensional_finiteType`：∀ {X : Typ
e u_1} [inst : TopologicalSpace X] (C : Set X) {D : Set X} [inst_1 : Topology.Re
lCWComplex C D]   [Topology.RelCWComplex.FiniteDim…
· 使用定理 `Topology.RelCWComplex.Subcomplex.finiteDimensional_subcomplex_of_finiteD
imensional`：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Sp
ace X] [inst_1 : Topology.RelCWComplex C D]   [Topology.RelCWComplex.Fin…
· 使用定理 `Topology.RelCWComplex.Finite.toFiniteDimensional`：∀ {X : Type u_1} {inst
 : TopologicalSpace X} {C D : Set X} {inst_1 : Topology.RelCWComplex C D}   [sel
f : Topology.RelCWComplex.Finite C], T…
· 使用定理 `Topology.RelCWComplex.Subcomplex.finiteType_subcomplex_of_finiteType`：∀ 
{X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1
 : Topology.RelCWComplex C D]   [Topology.RelCWComplex.Fin…
· 使用定理 `Topology.RelCWComplex.Finite.toFiniteType`：∀ {X : Type u_1} {inst : Topo
logicalSpace X} {C D : Set X} {inst_1 : Topology.RelCWComplex C D}   [self : Top
ology.RelCWComplex.Finite C], T…

--- 原说明 ---
A subcomplex of a finite CW complex is again finite.
-/
instance RelCWComplex.Subcomplex.finite_subcomplex_of_finite [T2Space X] [RelCWComplex C D]
    [Finite C] (E : Subcomplex C) : Finite (E : Set X) :=
  finite_of_finiteDimensional_finiteType _

end Topology

