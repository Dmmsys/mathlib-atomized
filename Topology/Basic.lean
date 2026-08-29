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
/--
Definition of `TopologicalSpace.ofClosed` / `TopologicalSpace.ofClosed` 的定义

English:
definition TopologicalSpace.ofClosed
  signature: {X : Type u} (T : Set (Set X)) (empty_mem : ∅ in T)
  body: Xᶜ in T
  isOpen_univ := by simp [empty_mem]
  isOpen_inter s t hs ht := by simpa only [compl_inter] using union_mem sᶜ hs tᶜ ht
  isOpen_sUnion s hs := by
    simp only [Set.compl_sUnion]
    exact sInter_mem (compl '' s) fun z ⟨y, hy, hz⟩ => hz ▸ hs y hy

中文:
定义 拓扑空间.ofClosed
  签名: {X : 类型u} (T : 集合 (集合 X)) (empty_mem : ∅ in T)
  定义体: Xᶜ in T
  isOpen_univ := by simp [empty_mem]
  isOpen_inter s t hs ht := by simpa only [compl_inter] using union_mem sᶜ hs tᶜ ht
  isOpen_sUnion s hs := by
    simp only [Set.compl_sUnion]
    exact sInter_mem (compl '' s) fun z ⟨y, hy, hz⟩ => hz ▸ hs y hy
-/
def TopologicalSpace.ofClosed {X : Type u} (T : Set (Set X)) (empty_mem : ∅ in T)
    (sInter_mem : forall A, A subseteq T -> ⋂₀ A in T)
    (union_mem : forall A, A in T -> forall B, B in T -> A union B in T) : TopologicalSpace X where
  IsOpen X := Xᶜ in T
  isOpen_univ := by simp [empty_mem]
  isOpen_inter s t hs ht := by simpa only [compl_inter] using union_mem sᶜ hs tᶜ ht
  isOpen_sUnion s hs := by
    simp only [Set.compl_sUnion]
    exact sInter_mem (compl '' s) fun z ⟨y, hy, hz⟩ => hz ▸ hs y hy

section TopologicalSpace

variable {X : Type u} {ι : Sort v} {α : Type*} {x : X} {s s₁ s₂ t : Set X} {p p₁ p₂ : X -> Prop}

/--
lemma `isOpen_mk` / 引理 `isOpen_mk`

English:
lemma isOpen_mk
  given: {p h₁ h₂ h₃}
  statement: IsOpen[⟨p, h₁, h₂, h₃⟩] s ↔ p s
  proof: Iff.rfl

@[ext (iff := false)]

中文:
引理 isOpen_mk
  条件: {p h₁ h₂ h₃}
  结论: 是开集[⟨p, h₁, h₂, h₃⟩] s ↔ p s
  证明: Iff.rfl

@[ext (iff := false)]

Depends on / 依赖: Iff.rfl
-/
lemma isOpen_mk {p h₁ h₂ h₃} : IsOpen[⟨p, h₁, h₂, h₃⟩] s ↔ p s := Iff.rfl

@[ext (iff := false)]
/--
theorem `TopologicalSpace.ext` / 定理 `TopologicalSpace.ext`

English:
theorem TopologicalSpace.ext

中文:
定理 拓扑空间.ext
-/
protected theorem TopologicalSpace.ext :
    forall {f g : TopologicalSpace X}, IsOpen[f] = IsOpen[g] -> f = g
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

/--
theorem `TopologicalSpace.ext_iff` / 定理 `TopologicalSpace.ext_iff`

English:
theorem TopologicalSpace.ext_iff
  given: {t t' : TopologicalSpace X}
  proof: ⟨fun h _ => h ▸ Iff.rfl, fun h => by ext; exact h _⟩

中文:
定理 拓扑空间.ext_iff
  条件: {t t' : 拓扑空间 X}
  证明: ⟨fun h _ => h ▸ Iff.rfl, fun h => by ext; exact h _⟩
-/
protected theorem TopologicalSpace.ext_iff {t t' : TopologicalSpace X} :
    t = t' ↔ forall s, IsOpen[t] s ↔ IsOpen[t'] s :=
  ⟨fun h _ => h ▸ Iff.rfl, fun h => by ext; exact h _⟩

/--
theorem `isOpen_fold` / 定理 `isOpen_fold`

English:
theorem isOpen_fold
  given: {t : TopologicalSpace X}
  statement: t.IsOpen s = IsOpen[t] s
  proof: rfl

中文:
定理 isOpen_fold
  条件: {t : 拓扑空间 X}
  结论: t.是开集 s = 是开集[t] s
  证明: rfl
-/
theorem isOpen_fold {t : TopologicalSpace X} : t.IsOpen s = IsOpen[t] s :=
  rfl

variable [TopologicalSpace X]

/--
theorem `isOpen_iUnion` / 定理 `isOpen_iUnion`

English:
theorem isOpen_iUnion
  given: {f : ι -> Set X} (h : forall i, IsOpen (f i))
  statement: IsOpen (⋃ i, f i)
  proof: isOpen_sUnion (forall_mem_range.2 h)

中文:
定理 isOpen_iUnion
  条件: {f : ι -> 集合 X} (h : 对任意 i, 是开集 (f i))
  结论: 是开集 (⋃ i, f i)
  证明: isOpen_sUnion (forall_mem_range.2 h)

Depends on / 依赖: forall_mem_range, isOpen_sUnion
-/
theorem isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i)) : IsOpen (⋃ i, f i) :=
  isOpen_sUnion (forall_mem_range.2 h)

/--
theorem `isOpen_biUnion` / 定理 `isOpen_biUnion`

English:
theorem isOpen_biUnion
  given: {s : Set α} {f : α -> Set X} (h : forall i in s, IsOpen (f i))
  proof: isOpen_iUnion fun i => isOpen_iUnion fun hi => h i hi

中文:
定理 isOpen_biUnion
  条件: {s : 集合 α} {f : α -> 集合 X} (h : 对任意 i in s, 是开集 (f i))
  证明: isOpen_iUnion fun i => isOpen_iUnion fun hi => h i hi

Depends on / 依赖: isOpen_iUnion
-/
theorem isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall i in s, IsOpen (f i)) :
    IsOpen (⋃ i in s, f i) :=
  isOpen_iUnion fun i => isOpen_iUnion fun hi => h i hi

/--
theorem `IsOpen.union` / 定理 `IsOpen.union`

English:
theorem IsOpen.union
  given: (h₁ : IsOpen s₁) (h₂ : IsOpen s₂)
  statement: IsOpen (s₁ union s₂)
  proof: by
  rw [union_eq_iUnion]; exact isOpen_iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)

中文:
定理 是开集.union
  条件: (h₁ : 是开集 s₁) (h₂ : 是开集 s₂)
  结论: 是开集 (s₁ union s₂)
  证明: by
  rw [union_eq_iUnion]; exact isOpen_iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)

Depends on / 依赖: Bool.forall_bool, forall_bool, isOpen_iUnion, union_eq_iUnion
-/
theorem IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s₁ union s₂) := by
  rw [union_eq_iUnion]; exact isOpen_iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)

/--
lemma `isOpen_iff_of_cover` / 引理 `isOpen_iff_of_cover`

English:
lemma isOpen_iff_of_cover
  given: {f : α -> Set X} (ho : forall i, IsOpen (f i)) (hU : (⋃ i, f i) = univ)
  proof: by
  refine ⟨fun h i => (ho i).inter h, fun h => ?_⟩
  rw [← s.inter_univ]; rw [inter_comm]; rw [← hU]; rw [iUnion_inter]
  exact isOpen_iUnion fun i => h i

中文:
引理 isOpen_iff_of_cover
  条件: {f : α -> 集合 X} (ho : 对任意 i, 是开集 (f i)) (hU : (⋃ i, f i) = univ)
  证明: by
  refine ⟨fun h i => (ho i).inter h, fun h => ?_⟩
  rw [← s.inter_univ]; rw [inter_comm]; rw [← hU]; rw [iUnion_inter]
  exact isOpen_iUnion fun i => h i

Depends on / 依赖: iUnion_inter, inter_comm, inter_univ, isOpen_iUnion, s.inter_univ
-/
lemma isOpen_iff_of_cover {f : α -> Set X} (ho : forall i, IsOpen (f i)) (hU : (⋃ i, f i) = univ) :
    IsOpen s ↔ forall i, IsOpen (f i inter s) := by
  refine ⟨fun h i => (ho i).inter h, fun h => ?_⟩
  rw [← s.inter_univ]; rw [inter_comm]; rw [← hU]; rw [iUnion_inter]
  exact isOpen_iUnion fun i => h i

/--
theorem `isOpen_empty` / 定理 `isOpen_empty`

English:
theorem isOpen_empty
  statement: IsOpen (∅ : Set X)
  proof: by
  rw [← sUnion_empty]; exact isOpen_sUnion fun a => False.elim

中文:
定理 isOpen_empty
  结论: 是开集 (∅ : 集合 X)
  证明: by
  rw [← sUnion_empty]; exact isOpen_sUnion fun a => False.elim
-/
@[simp] theorem isOpen_empty : IsOpen (∅ : Set X) := by
  rw [← sUnion_empty]; exact isOpen_sUnion fun a => False.elim

/--
theorem `Set.Finite.isOpen_sInter` / 定理 `Set.Finite.isOpen_sInter`

English:
theorem Set.Finite.isOpen_sInter
  given: {s : Set (Set X)} (hs : s.Finite) (h : forall t in s, IsOpen t)
  proof: by
  induction s, hs using Set.Finite.induction_on with
  | empty => rw [sInter_empty]; exact isOpen_univ
  | insert _ _ ih =>
    simp only [sInter_insert, forall_mem_insert] at h ⊢
    exact h.1.inter (ih h.2)

中文:
定理 集合.有限.isOpen_s整数er
  条件: {s : 集合 (集合 X)} (hs : s.有限) (h : 对任意 t in s, 是开集 t)
  证明: by
  induction s, hs using Set.Finite.induction_on with
  | empty => rw [sInter_empty]; exact isOpen_univ
  | insert _ _ ih =>
    simp only [sInter_insert, forall_mem_insert] at h ⊢
    exact h.1.inter (ih h.2)

Depends on / 依赖: Finite, Set.Finite.induction_on, forall_mem_insert, induction_on, insert, isOpen_univ, sInter_empty, sInter_insert
-/
theorem Set.Finite.isOpen_sInter {s : Set (Set X)} (hs : s.Finite) (h : forall t in s, IsOpen t) :
    IsOpen (⋂₀ s) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => rw [sInter_empty]; exact isOpen_univ
  | insert _ _ ih =>
    simp only [sInter_insert, forall_mem_insert] at h ⊢
    exact h.1.inter (ih h.2)

/--
theorem `Set.Finite.isOpen_biInter` / 定理 `Set.Finite.isOpen_biInter`

English:
theorem Set.Finite.isOpen_biInter
  statement: {s : Set α} {f : α -> Set X} (hs : s.Finite)
  proof: sInter_image f s ▸ (hs.image _).isOpen_sInter (forall_mem_image.2 h)

中文:
定理 集合.有限.isOpen_bi整数er
  结论: {s : 集合 α} {f : α -> 集合 X} (hs : s.有限)
  证明: sInter_image f s ▸ (hs.image _).isOpen_sInter (forall_mem_image.2 h)

Depends on / 依赖: forall_mem_image, hs.image, isOpen_sInter, sInter_image
-/
theorem Set.Finite.isOpen_biInter {s : Set α} {f : α -> Set X} (hs : s.Finite)
    (h : forall i in s, IsOpen (f i)) :
    IsOpen (⋂ i in s, f i) :=
  sInter_image f s ▸ (hs.image _).isOpen_sInter (forall_mem_image.2 h)

/--
theorem `isOpen_iInter_of_finite` / 定理 `isOpen_iInter_of_finite`

English:
theorem isOpen_iInter_of_finite
  given: [Finite ι] {s : ι -> Set X} (h : forall i, IsOpen (s i))
  proof: (finite_range _).isOpen_sInter (forall_mem_range.2 h)

中文:
定理 isOpen_i整数er_of_finite
  条件: [有限 ι] {s : ι -> 集合 X} (h : 对任意 i, 是开集 (s i))
  证明: (finite_range _).isOpen_sInter (forall_mem_range.2 h)

Depends on / 依赖: finite_range, forall_mem_range, isOpen_sInter
-/
theorem isOpen_iInter_of_finite [Finite ι] {s : ι -> Set X} (h : forall i, IsOpen (s i)) :
    IsOpen (⋂ i, s i) :=
  (finite_range _).isOpen_sInter (forall_mem_range.2 h)

/--
theorem `isOpen_biInter_finset` / 定理 `isOpen_biInter_finset`

English:
theorem isOpen_biInter_finset
  given: {s : Finset α} {f : α -> Set X} (h : forall i in s, IsOpen (f i))
  proof: s.finite_toSet.isOpen_biInter h

@[simp]

中文:
定理 isOpen_bi整数er_finset
  条件: {s : 有限集 α} {f : α -> 集合 X} (h : 对任意 i in s, 是开集 (f i))
  证明: s.finite_toSet.isOpen_biInter h

@[simp]

Depends on / 依赖: finite_toSet, isOpen_biInter, s.finite_toSet.isOpen_biInter
-/
theorem isOpen_biInter_finset {s : Finset α} {f : α -> Set X} (h : forall i in s, IsOpen (f i)) :
    IsOpen (⋂ i in s, f i) :=
  s.finite_toSet.isOpen_biInter h

@[simp]
/--
theorem `isOpen_const` / 定理 `isOpen_const`

English:
theorem isOpen_const
  given: {p : Prop}
  statement: IsOpen { _x : X | p }
  proof: by by_cases p <;> simp [*]

中文:
定理 isOpen_const
  条件: {p : 命题}
  结论: 是开集 { _x : X | p }
  证明: by by_cases p <;> simp [*]
-/
theorem isOpen_const {p : Prop} : IsOpen { _x : X | p } := by by_cases p <;> simp [*]

/--
theorem `IsOpen.and` / 定理 `IsOpen.and`

English:
theorem IsOpen.and
  statement: IsOpen { x | p₁ x } -> IsOpen { x | p₂ x } -> IsOpen { x | p₁ x ∧ p₂ x }
  proof: IsOpen.inter

中文:
定理 是开集.and
  结论: 是开集 { x | p₁ x } -> 是开集 { x | p₂ x } -> 是开集 { x | p₁ x ∧ p₂ x }
  证明: IsOpen.inter

Depends on / 依赖: IsOpen, IsOpen.inter
-/
theorem IsOpen.and : IsOpen { x | p₁ x } -> IsOpen { x | p₂ x } -> IsOpen { x | p₁ x ∧ p₂ x } :=
  IsOpen.inter

/--
theorem `isOpen_compl_iff` / 定理 `isOpen_compl_iff`

English:
theorem isOpen_compl_iff
  statement: IsOpen sᶜ ↔ IsClosed s
  proof: ⟨fun h => ⟨h⟩, fun h => h.isOpen_compl⟩

中文:
定理 isOpen_compl_iff
  结论: 是开集 sᶜ ↔ 是闭集 s
  证明: ⟨fun h => ⟨h⟩, fun h => h.isOpen_compl⟩
-/
@[simp] theorem isOpen_compl_iff : IsOpen sᶜ ↔ IsClosed s :=
  ⟨fun h => ⟨h⟩, fun h => h.isOpen_compl⟩

/--
theorem `TopologicalSpace.ext_iff_isClosed` / 定理 `TopologicalSpace.ext_iff_isClosed`

English:
theorem TopologicalSpace.ext_iff_isClosed
  given: {X} {t₁ t₂ : TopologicalSpace X}
  proof: by
  rw [TopologicalSpace.ext_iff]; rw [compl_surjective.forall]
  simp only [@isOpen_compl_iff _ _ t₁, @isOpen_compl_iff _ _ t₂]

alias ⟨_, TopologicalSpace.ext_isClosed⟩ := TopologicalSpace.ext_iff_isClosed

中文:
定理 拓扑空间.ext_iff_isClosed
  条件: {X} {t₁ t₂ : 拓扑空间 X}
  证明: by
  rw [TopologicalSpace.ext_iff]; rw [compl_surjective.forall]
  simp only [@isOpen_compl_iff _ _ t₁, @isOpen_compl_iff _ _ t₂]

alias ⟨_, TopologicalSpace.ext_isClosed⟩ := TopologicalSpace.ext_iff_isClosed

Depends on / 依赖: TopologicalSpace, TopologicalSpace.ext_iff, compl_surjective, compl_surjective.forall, ext_iff, isOpen_compl_iff
-/
theorem TopologicalSpace.ext_iff_isClosed {X} {t₁ t₂ : TopologicalSpace X} :
    t₁ = t₂ ↔ forall s, IsClosed[t₁] s ↔ IsClosed[t₂] s := by
  rw [TopologicalSpace.ext_iff]; rw [compl_surjective.forall]
  simp only [@isOpen_compl_iff _ _ t₁, @isOpen_compl_iff _ _ t₂]

alias ⟨_, TopologicalSpace.ext_isClosed⟩ := TopologicalSpace.ext_iff_isClosed

/--
theorem `isClosed_const` / 定理 `isClosed_const`

English:
theorem isClosed_const
  given: {p : Prop}
  statement: IsClosed { _x : X | p }
  proof: ⟨isOpen_const (p := ¬p)⟩

@[simp, closedness ., grind .]

中文:
定理 isClosed_const
  条件: {p : 命题}
  结论: 是闭集 { _x : X | p }
  证明: ⟨isOpen_const (p := ¬p)⟩

@[simp, closedness ., grind .]

Depends on / 依赖: isOpen_const
-/
theorem isClosed_const {p : Prop} : IsClosed { _x : X | p } := ⟨isOpen_const (p := ¬p)⟩

@[simp, closedness ., grind .]
/--
theorem `isClosed_empty` / 定理 `isClosed_empty`

English:
theorem isClosed_empty
  statement: IsClosed (∅ : Set X)
  proof: isClosed_const

@[simp, closedness ., grind .]

中文:
定理 isClosed_empty
  结论: 是闭集 (∅ : 集合 X)
  证明: isClosed_const

@[simp, closedness ., grind .]

Depends on / 依赖: isClosed_const
-/
theorem isClosed_empty : IsClosed (∅ : Set X) := isClosed_const

@[simp, closedness ., grind .]
/--
theorem `isClosed_univ` / 定理 `isClosed_univ`

English:
theorem isClosed_univ
  statement: IsClosed (univ : Set X)
  proof: isClosed_const

@[closedness .]

中文:
定理 isClosed_univ
  结论: 是闭集 (univ : 集合 X)
  证明: isClosed_const

@[closedness .]

Depends on / 依赖: isClosed_const
-/
theorem isClosed_univ : IsClosed (univ : Set X) := isClosed_const

@[closedness .]
/--
lemma `IsOpen.isLocallyClosed` / 引理 `IsOpen.isLocallyClosed`

English:
lemma IsOpen.isLocallyClosed
  given: (hs : IsOpen s)
  statement: IsLocallyClosed s
  proof: ⟨_, _, hs, isClosed_univ, (inter_univ _).symm⟩

@[closedness .]

中文:
引理 是开集.isLocallyClosed
  条件: (hs : 是开集 s)
  结论: IsLocallyClosed s
  证明: ⟨_, _, hs, isClosed_univ, (inter_univ _).symm⟩

@[closedness .]

Depends on / 依赖: inter_univ, isClosed_univ
-/
lemma IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocallyClosed s :=
  ⟨_, _, hs, isClosed_univ, (inter_univ _).symm⟩

@[closedness .]
/--
lemma `IsClosed.isLocallyClosed` / 引理 `IsClosed.isLocallyClosed`

English:
lemma IsClosed.isLocallyClosed
  given: (hs : IsClosed s)
  statement: IsLocallyClosed s
  proof: ⟨_, _, isOpen_univ, hs, (univ_inter _).symm⟩

@[closedness .]

中文:
引理 是闭集.isLocallyClosed
  条件: (hs : 是闭集 s)
  结论: IsLocallyClosed s
  证明: ⟨_, _, isOpen_univ, hs, (univ_inter _).symm⟩

@[closedness .]

Depends on / 依赖: isOpen_univ, univ_inter
-/
lemma IsClosed.isLocallyClosed (hs : IsClosed s) : IsLocallyClosed s :=
  ⟨_, _, isOpen_univ, hs, (univ_inter _).symm⟩

@[closedness .]
/--
theorem `IsClosed.union` / 定理 `IsClosed.union`

English:
theorem IsClosed.union
  statement: IsClosed s₁ -> IsClosed s₂ -> IsClosed (s₁ union s₂)
  proof: by
  simpa only [← isOpen_compl_iff, compl_union] using IsOpen.inter

@[closedness .]

中文:
定理 是闭集.union
  结论: 是闭集 s₁ -> 是闭集 s₂ -> 是闭集 (s₁ union s₂)
  证明: by
  simpa only [← isOpen_compl_iff, compl_union] using IsOpen.inter

@[closedness .]

Depends on / 依赖: IsOpen, IsOpen.inter, compl_union, isOpen_compl_iff
-/
theorem IsClosed.union : IsClosed s₁ -> IsClosed s₂ -> IsClosed (s₁ union s₂) := by
  simpa only [← isOpen_compl_iff, compl_union] using IsOpen.inter

@[closedness .]
/--
theorem `isClosed_sInter` / 定理 `isClosed_sInter`

English:
theorem isClosed_sInter
  given: {s : Set (Set X)}
  statement: (forall t in s, IsClosed t) -> IsClosed (⋂₀ s)
  proof: by
  simpa only [← isOpen_compl_iff, compl_sInter, sUnion_image] using isOpen_biUnion

@[closedness .]

中文:
定理 isClosed_s整数er
  条件: {s : 集合 (集合 X)}
  结论: (对任意 t in s, 是闭集 t) -> 是闭集 (⋂₀ s)
  证明: by
  simpa only [← isOpen_compl_iff, compl_sInter, sUnion_image] using isOpen_biUnion

@[closedness .]

Depends on / 依赖: compl_sInter, isOpen_biUnion, isOpen_compl_iff, sUnion_image
-/
theorem isClosed_sInter {s : Set (Set X)} : (forall t in s, IsClosed t) -> IsClosed (⋂₀ s) := by
  simpa only [← isOpen_compl_iff, compl_sInter, sUnion_image] using isOpen_biUnion

@[closedness .]
/--
theorem `isClosed_iInter` / 定理 `isClosed_iInter`

English:
theorem isClosed_iInter
  given: {f : ι -> Set X} (h : forall i, IsClosed (f i))
  statement: IsClosed (⋂ i, f i)
  proof: isClosed_sInter forall_mem_range.2 h

中文:
定理 isClosed_i整数er
  条件: {f : ι -> 集合 X} (h : 对任意 i, 是闭集 (f i))
  结论: 是闭集 (⋂ i, f i)
  证明: isClosed_sInter forall_mem_range.2 h

Depends on / 依赖: forall_mem_range, isClosed_sInter
-/
theorem isClosed_iInter {f : ι -> Set X} (h : forall i, IsClosed (f i)) : IsClosed (⋂ i, f i) :=
isClosed_sInter forall_mem_range.2 h

/--
theorem `isClosed_biInter` / 定理 `isClosed_biInter`

English:
theorem isClosed_biInter
  given: {s : Set α} {f : α -> Set X} (h : forall i in s, IsClosed (f i))
  proof: isClosed_iInter fun i => isClosed_iInter h i

@[simp]

中文:
定理 isClosed_bi整数er
  条件: {s : 集合 α} {f : α -> 集合 X} (h : 对任意 i in s, 是闭集 (f i))
  证明: isClosed_iInter fun i => isClosed_iInter h i

@[simp]

Depends on / 依赖: isClosed_iInter
-/
theorem isClosed_biInter {s : Set α} {f : α -> Set X} (h : forall i in s, IsClosed (f i)) :
    IsClosed (⋂ i in s, f i) :=
isClosed_iInter fun i => isClosed_iInter h i

@[simp]
/--
theorem `isClosed_compl_iff` / 定理 `isClosed_compl_iff`

English:
theorem isClosed_compl_iff
  given: {s : Set X}
  statement: IsClosed sᶜ ↔ IsOpen s
  proof: by
  rw [← isOpen_compl_iff]; rw [compl_compl]

alias ⟨_, IsOpen.isClosed_compl⟩ := isClosed_compl_iff

中文:
定理 isClosed_compl_iff
  条件: {s : 集合 X}
  结论: 是闭集 sᶜ ↔ 是开集 s
  证明: by
  rw [← isOpen_compl_iff]; rw [compl_compl]

alias ⟨_, IsOpen.isClosed_compl⟩ := isClosed_compl_iff

Depends on / 依赖: compl_compl, isOpen_compl_iff
-/
theorem isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpen s := by
  rw [← isOpen_compl_iff]; rw [compl_compl]

alias ⟨_, IsOpen.isClosed_compl⟩ := isClosed_compl_iff

/--
theorem `IsOpen.sdiff` / 定理 `IsOpen.sdiff`

English:
theorem IsOpen.sdiff
  given: (h₁ : IsOpen s) (h₂ : IsClosed t)
  statement: IsOpen (s \ t)
  proof: IsOpen.inter h₁ h₂.isOpen_compl

@[closedness .]

中文:
定理 是开集.sdiff
  条件: (h₁ : 是开集 s) (h₂ : 是闭集 t)
  结论: 是开集 (s \ t)
  证明: IsOpen.inter h₁ h₂.isOpen_compl

@[closedness .]

Depends on / 依赖: IsOpen, IsOpen.inter, isOpen_compl
-/
theorem IsOpen.sdiff (h₁ : IsOpen s) (h₂ : IsClosed t) : IsOpen (s \ t) :=
  IsOpen.inter h₁ h₂.isOpen_compl

@[closedness .]
/--
theorem `IsClosed.inter` / 定理 `IsClosed.inter`

English:
theorem IsClosed.inter
  given: (h₁ : IsClosed s₁) (h₂ : IsClosed s₂)
  statement: IsClosed (s₁ inter s₂)
  proof: by
  rw [← isOpen_compl_iff] at *
  rw [compl_inter]
  exact IsOpen.union h₁ h₂

@[closedness .]

中文:
定理 是闭集.inter
  条件: (h₁ : 是闭集 s₁) (h₂ : 是闭集 s₂)
  结论: 是闭集 (s₁ inter s₂)
  证明: by
  rw [← isOpen_compl_iff] at *
  rw [compl_inter]
  exact IsOpen.union h₁ h₂

@[closedness .]

Depends on / 依赖: IsOpen, IsOpen.union, compl_inter, isOpen_compl_iff
-/
theorem IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : IsClosed (s₁ inter s₂) := by
  rw [← isOpen_compl_iff] at *
  rw [compl_inter]
  exact IsOpen.union h₁ h₂

@[closedness .]
/--
theorem `IsClosed.sdiff` / 定理 `IsClosed.sdiff`

English:
theorem IsClosed.sdiff
  given: (h₁ : IsClosed s) (h₂ : IsOpen t)
  statement: IsClosed (s \ t)
  proof: IsClosed.inter h₁ (isClosed_compl_iff.mpr h₂)

中文:
定理 是闭集.sdiff
  条件: (h₁ : 是闭集 s) (h₂ : 是开集 t)
  结论: 是闭集 (s \ t)
  证明: IsClosed.inter h₁ (isClosed_compl_iff.mpr h₂)

Depends on / 依赖: IsClosed, IsClosed.inter, isClosed_compl_iff, isClosed_compl_iff.mpr
-/
theorem IsClosed.sdiff (h₁ : IsClosed s) (h₂ : IsOpen t) : IsClosed (s \ t) :=
  IsClosed.inter h₁ (isClosed_compl_iff.mpr h₂)

/--
theorem `Set.Finite.isClosed_biUnion` / 定理 `Set.Finite.isClosed_biUnion`

English:
theorem Set.Finite.isClosed_biUnion
  statement: {s : Set α} {f : α -> Set X} (hs : s.Finite)
  proof: by
  simp only [← isOpen_compl_iff, compl_iUnion] at *
  exact hs.isOpen_biInter h

中文:
定理 集合.有限.isClosed_biUnion
  结论: {s : 集合 α} {f : α -> 集合 X} (hs : s.有限)
  证明: by
  simp only [← isOpen_compl_iff, compl_iUnion] at *
  exact hs.isOpen_biInter h

Depends on / 依赖: compl_iUnion, hs.isOpen_biInter, isOpen_biInter, isOpen_compl_iff
-/
theorem Set.Finite.isClosed_biUnion {s : Set α} {f : α -> Set X} (hs : s.Finite)
    (h : forall i in s, IsClosed (f i)) :
    IsClosed (⋃ i in s, f i) := by
  simp only [← isOpen_compl_iff, compl_iUnion] at *
  exact hs.isOpen_biInter h

/--
lemma `isClosed_biUnion_finset` / 引理 `isClosed_biUnion_finset`

English:
lemma isClosed_biUnion_finset
  given: {s : Finset α} {f : α -> Set X} (h : forall i in s, IsClosed (f i))
  proof: s.finite_toSet.isClosed_biUnion h

@[closedness .]

中文:
引理 isClosed_biUnion_finset
  条件: {s : 有限集 α} {f : α -> 集合 X} (h : 对任意 i in s, 是闭集 (f i))
  证明: s.finite_toSet.isClosed_biUnion h

@[closedness .]

Depends on / 依赖: finite_toSet, isClosed_biUnion, s.finite_toSet.isClosed_biUnion
-/
lemma isClosed_biUnion_finset {s : Finset α} {f : α -> Set X} (h : forall i in s, IsClosed (f i)) :
    IsClosed (⋃ i in s, f i) :=
  s.finite_toSet.isClosed_biUnion h

@[closedness .]
/--
theorem `isClosed_iUnion_of_finite` / 定理 `isClosed_iUnion_of_finite`

English:
theorem isClosed_iUnion_of_finite
  given: [Finite ι] {s : ι -> Set X} (h : forall i, IsClosed (s i))
  proof: by
  simp only [← isOpen_compl_iff, compl_iUnion] at *
  exact isOpen_iInter_of_finite h

@[closedness .]

中文:
定理 isClosed_iUnion_of_finite
  条件: [有限 ι] {s : ι -> 集合 X} (h : 对任意 i, 是闭集 (s i))
  证明: by
  simp only [← isOpen_compl_iff, compl_iUnion] at *
  exact isOpen_iInter_of_finite h

@[closedness .]

Depends on / 依赖: compl_iUnion, isOpen_compl_iff, isOpen_iInter_of_finite
-/
theorem isClosed_iUnion_of_finite [Finite ι] {s : ι -> Set X} (h : forall i, IsClosed (s i)) :
    IsClosed (⋃ i, s i) := by
  simp only [← isOpen_compl_iff, compl_iUnion] at *
  exact isOpen_iInter_of_finite h

@[closedness .]
/--
theorem `isClosed_imp` / 定理 `isClosed_imp`

English:
theorem isClosed_imp
  given: {p q : X -> Prop} (hp : IsOpen { x | p x }) (hq : IsClosed { x | q x })
  proof: by
  simpa only [imp_iff_not_or] using! hp.isClosed_compl.union hq

中文:
定理 isClosed_imp
  条件: {p q : X -> 命题} (hp : 是开集 { x | p x }) (hq : 是闭集 { x | q x })
  证明: by
  simpa only [imp_iff_not_or] using! hp.isClosed_compl.union hq

Depends on / 依赖: hp.isClosed_compl.union, imp_iff_not_or, isClosed_compl
-/
theorem isClosed_imp {p q : X -> Prop} (hp : IsOpen { x | p x }) (hq : IsClosed { x | q x }) :
    IsClosed { x | p x -> q x } := by
  simpa only [imp_iff_not_or] using! hp.isClosed_compl.union hq

/--
theorem `IsClosed.not` / 定理 `IsClosed.not`

English:
theorem IsClosed.not
  statement: IsClosed { a | p a } -> IsOpen { a | ¬p a }
  proof: isOpen_compl_iff.mpr

@[closedness .]

中文:
定理 是闭集.not
  结论: 是闭集 { a | p a } -> 是开集 { a | ¬p a }
  证明: isOpen_compl_iff.mpr

@[closedness .]

Depends on / 依赖: isOpen_compl_iff, isOpen_compl_iff.mpr
-/
theorem IsClosed.not : IsClosed { a | p a } -> IsOpen { a | ¬p a } :=
  isOpen_compl_iff.mpr

@[closedness .]
/--
theorem `IsClosed.and` / 定理 `IsClosed.and`

English:
theorem IsClosed.and
  proof: IsClosed.inter

中文:
定理 是闭集.and
  证明: IsClosed.inter

Depends on / 依赖: IsClosed, IsClosed.inter
-/
theorem IsClosed.and :
    IsClosed { x | p₁ x } -> IsClosed { x | p₂ x } -> IsClosed { x | p₁ x ∧ p₂ x } :=
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

/--
theorem `le_nhds_lim` / 定理 `le_nhds_lim`

English:
theorem le_nhds_lim
  given: {f : Filter X} (h : exists x, f <= 𝓝 x)
  statement: f <= 𝓝 (@lim _ _ h.nonempty f)
  proof: Classical.epsilon_spec h

中文:
定理 le_nhds_lim
  条件: {f : 滤子 X} (h : 存在 x, f <= 𝓝 x)
  结论: f <= 𝓝 (@lim _ _ h.nonempty f)
  证明: Classical.epsilon_spec h

Depends on / 依赖: Classical, Classical.epsilon_spec, epsilon_spec
-/
theorem le_nhds_lim {f : Filter X} (h : exists x, f <= 𝓝 x) : f <= 𝓝 (@lim _ _ h.nonempty f) :=
  Classical.epsilon_spec h

/--
theorem `tendsto_nhds_limUnder` / 定理 `tendsto_nhds_limUnder`

English:
theorem tendsto_nhds_limUnder
  given: {f : Filter α} {g : α -> X} (h : exists x, Tendsto g f (𝓝 x))
  proof: le_nhds_lim h

中文:
定理 tendsto_nhds_limUnder
  条件: {f : 滤子 α} {g : α -> X} (h : 存在 x, 收敛 g f (𝓝 x))
  证明: le_nhds_lim h

Depends on / 依赖: le_nhds_lim
-/
theorem tendsto_nhds_limUnder {f : Filter α} {g : α -> X} (h : exists x, Tendsto g f (𝓝 x)) :
    Tendsto g f (𝓝 (@limUnder _ _ _ h.nonempty f g)) :=
  le_nhds_lim h

/--
theorem `limUnder_of_not_tendsto` / 定理 `limUnder_of_not_tendsto`

English:
theorem limUnder_of_not_tendsto
  statement: [hX : Nonempty X] {f : Filter α} {g : α -> X}
  proof: by
  simp_rw [Tendsto] at h
  simp_rw [limUnder, lim, Classical.epsilon, Classical.strongIndefiniteDescription, dif_neg h]

中文:
定理 limUnder_of_not_tendsto
  结论: [hX : 非空 X] {f : 滤子 α} {g : α -> X}
  证明: by
  simp_rw [Tendsto] at h
  simp_rw [limUnder, lim, Classical.epsilon, Classical.strongIndefiniteDescription, dif_neg h]

Depends on / 依赖: Classical, Classical.epsilon, Classical.strongIndefiniteDescription, Tendsto, dif_neg, epsilon, limUnder, simp_rw, strongIndefiniteDescription
-/
theorem limUnder_of_not_tendsto [hX : Nonempty X] {f : Filter α} {g : α -> X}
    (h : ¬ exists x, Tendsto g f (𝓝 x)) :
    limUnder f g = Classical.choice hX := by
  simp_rw [Tendsto] at h
  simp_rw [limUnder, lim, Classical.epsilon, Classical.strongIndefiniteDescription, dif_neg h]

end lim

end TopologicalSpace
