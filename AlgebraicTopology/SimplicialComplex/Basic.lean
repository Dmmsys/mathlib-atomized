/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Order.UpperLower.Relative

/-!
# Abstract Simplicial complexes

In this file, we define abstract simplicial complexes.
An abstract simplicial complex is a downwards-closed collection of nonempty finite sets containing
every singleton. These are defined first defining `PreAbstractSimplicialComplex`,
which does not require the presence of singletons, and then defining `AbstractSimplicialComplex` as
an extension.

This is related to the geometrical notion of simplicial complexes, which are then defined under the
name `Geometry.SimplicialComplex` using affine combinations in another file.

## Main declarations

* `PreAbstractSimplicialComplex ι`: An abstract simplicial complex with vertices of type `ι`.
* `AbstractSimplicialComplex ι`: An abstract simplicial complex with vertices of type `ι` which
  contains all singletons.

## Notation

* `s ∈ K` means that `s` is a face of `K`. This notation arises from a `SetLike` instance.
* `K ≤ L` means that the faces of `K` are faces of `L`.

-/

@[expose] public section


open Finset Set

variable (ι : Type*)

/-- An abstract simplicial complex is a collection of nonempty finite sets of points ("faces")
which is downwards closed, i.e., any nonempty subset of a face is also a face.
-/
@[ext]
/--
Definition of `PreAbstractSimplicialComplex` / `PreAbstractSimplicialComplex` 的定义

English:
structure PreAbstractSimplicialComplex
  parameters: where
  axioms and operations (2):
    - faces : Set (Finset ι)
    - isRelLowerSet_faces : IsRelLowerSet faces Finset.Nonempty

中文:
结构 PreAbstractSimplicialComplex
  参数: where
  公理与运算 (2 个):
    - faces : Set (Finset ι)
    - isRelLowerSet_faces : IsRelLowerSet faces Finset.Nonempty
-/
structure PreAbstractSimplicialComplex where
  /-- the faces of this simplicial complex: currently, given by their spanning vertices -/
  faces : Set (Finset ι)
  /-- Faces are nonempty and downward closed: a non-empty subset of its spanning vertices spans
  another face. -/
  isRelLowerSet_faces : IsRelLowerSet faces Finset.Nonempty

namespace PreAbstractSimplicialComplex

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (PreAbstractSimplicialComplex ι) (Finset ι)
  body: K.faces
  coe_injective K _ _ := by
    cases K
    congr

中文:
实例 :
  签名: SetLike (PreAbstractSimplicialComplex ι) (Finset ι)
  定义体: K.faces
  coe_injective K _ _ := by
    cases K
    congr

Depends on / 依赖: K.faces
-/
instance : SetLike (PreAbstractSimplicialComplex ι) (Finset ι) where
  coe K := K.faces
  coe_injective K _ _ := by
    cases K
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (PreAbstractSimplicialComplex ι)
  body: { faces := K.faces inter L.faces
      isRelLowerSet_faces := IsRelLowerSet.inter K.isRelLowerSet_faces L.isRelLowerSet_faces }

中文:
实例 :
  签名: Min (PreAbstractSimplicialComplex ι)
  定义体: { faces := K.faces inter L.faces
      isRelLowerSet_faces := IsRelLowerSet.inter K.isRelLowerSet_faces L.isRelLowerSet_faces }

Depends on / 依赖: IsRelLowerSet, IsRelLowerSet.inter, K.faces, K.isRelLowerSet_faces, L.faces, L.isRelLowerSet_faces, isRelLowerSet_faces
-/
instance : Min (PreAbstractSimplicialComplex ι) where
  min K L :=
    { faces := K.faces inter L.faces
      isRelLowerSet_faces := IsRelLowerSet.inter K.isRelLowerSet_faces L.isRelLowerSet_faces }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (PreAbstractSimplicialComplex ι)
  body: { faces := K.faces union L.faces
      isRelLowerSet_faces := IsRelLowerSet.union K.isRelLowerSet_faces L.isRelLowerSet_faces }

中文:
实例 :
  签名: Max (PreAbstractSimplicialComplex ι)
  定义体: { faces := K.faces union L.faces
      isRelLowerSet_faces := IsRelLowerSet.union K.isRelLowerSet_faces L.isRelLowerSet_faces }

Depends on / 依赖: IsRelLowerSet, IsRelLowerSet.union, K.faces, K.isRelLowerSet_faces, L.faces, L.isRelLowerSet_faces, isRelLowerSet_faces
-/
instance : Max (PreAbstractSimplicialComplex ι) where
  max K L :=
    { faces := K.faces union L.faces
      isRelLowerSet_faces := IsRelLowerSet.union K.isRelLowerSet_faces L.isRelLowerSet_faces }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (PreAbstractSimplicialComplex ι)
  body: K.faces subseteq L.faces

中文:
实例 :
  签名: LE (PreAbstractSimplicialComplex ι)
  定义体: K.faces subseteq L.faces

Depends on / 依赖: K.faces, L.faces, subseteq
-/
instance : LE (PreAbstractSimplicialComplex ι) where
  le K L := K.faces subseteq L.faces

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LT (PreAbstractSimplicialComplex ι)
  body: K.faces ⊂ L.faces

中文:
实例 :
  签名: LT (PreAbstractSimplicialComplex ι)
  定义体: K.faces ⊂ L.faces

Depends on / 依赖: K.faces, L.faces
-/
instance : LT (PreAbstractSimplicialComplex ι) where
  lt K L := K.faces ⊂ L.faces

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsConcreteLE (PreAbstractSimplicialComplex ι) (Finset ι)
  body: .rfl

中文:
实例 :
  签名: IsConcreteLE (PreAbstractSimplicialComplex ι) (Finset ι)
  定义体: .rfl
-/
instance : IsConcreteLE (PreAbstractSimplicialComplex ι) (Finset ι) where
  coe_subset_coe' := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (PreAbstractSimplicialComplex ι)
  body: PartialOrder.lift (fun K => K.faces) (fun _ _ => PreAbstractSimplicialComplex.ext)

中文:
实例 :
  签名: PartialOrder (PreAbstractSimplicialComplex ι)
  定义体: PartialOrder.lift (fun K => K.faces) (fun _ _ => PreAbstractSimplicialComplex.ext)

Depends on / 依赖: K.faces, PartialOrder, PartialOrder.lift, PreAbstractSimplicialComplex, PreAbstractSimplicialComplex.ext
-/
instance : PartialOrder (PreAbstractSimplicialComplex ι) :=
  PartialOrder.lift (fun K => K.faces) (fun _ _ => PreAbstractSimplicialComplex.ext)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (PreAbstractSimplicialComplex ι)
  body: { faces := ⋃ K in s, K.faces
      isRelLowerSet_faces := IsRelLowerSet.iUnion₂ fun K _ => K.isRelLowerSet_faces }

中文:
实例 :
  签名: SupSet (PreAbstractSimplicialComplex ι)
  定义体: { faces := ⋃ K in s, K.faces
      isRelLowerSet_faces := IsRelLowerSet.iUnion₂ fun K _ => K.isRelLowerSet_faces }

Depends on / 依赖: IsRelLowerSet, IsRelLowerSet.iUnion, K.faces, K.isRelLowerSet_faces, isRelLowerSet_faces
-/
instance : SupSet (PreAbstractSimplicialComplex ι) where
  sSup s :=
    { faces := ⋃ K in s, K.faces
      isRelLowerSet_faces := IsRelLowerSet.iUnion₂ fun K _ => K.isRelLowerSet_faces }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (PreAbstractSimplicialComplex ι)
  body: { faces := (⋂ K in s, K.faces) inter { t | t.Nonempty }
      isRelLowerSet_faces := fun {_} ⟨hx, hn⟩ => by
        grind [IsRelLowerSet.mem_of_le, isRelLowerSet_faces, mem_iInter] }

中文:
实例 :
  签名: InfSet (PreAbstractSimplicialComplex ι)
  定义体: { faces := (⋂ K in s, K.faces) inter { t | t.Nonempty }
      isRelLowerSet_faces := fun {_} ⟨hx, hn⟩ => by
        grind [IsRelLowerSet.mem_of_le, isRelLowerSet_faces, mem_iInter] }

Depends on / 依赖: IsRelLowerSet, IsRelLowerSet.mem_of_le, K.faces, Nonempty, isRelLowerSet_faces, mem_iInter, mem_of_le, t.Nonempty
-/
instance : InfSet (PreAbstractSimplicialComplex ι) where
  sInf s :=
    { faces := (⋂ K in s, K.faces) inter { t | t.Nonempty }
      isRelLowerSet_faces := fun {_} ⟨hx, hn⟩ => by
        grind [IsRelLowerSet.mem_of_le, isRelLowerSet_faces, mem_iInter] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (PreAbstractSimplicialComplex ι)
  body: { faces := { s | s.Nonempty }
      isRelLowerSet_faces := fun {_} hs => ⟨hs, fun _ _ ht => ht⟩ }

中文:
实例 :
  签名: Top (PreAbstractSimplicialComplex ι)
  定义体: { faces := { s | s.Nonempty }
      isRelLowerSet_faces := fun {_} hs => ⟨hs, fun _ _ ht => ht⟩ }

Depends on / 依赖: Nonempty, isRelLowerSet_faces, s.Nonempty
-/
instance : Top (PreAbstractSimplicialComplex ι) where
  top :=
    { faces := { s | s.Nonempty }
      isRelLowerSet_faces := fun {_} hs => ⟨hs, fun _ _ ht => ht⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (PreAbstractSimplicialComplex ι)
  body: { faces := { _s | False }
      isRelLowerSet_faces := isRelLowerSet_empty }

中文:
实例 :
  签名: Bot (PreAbstractSimplicialComplex ι)
  定义体: { faces := { _s | False }
      isRelLowerSet_faces := isRelLowerSet_empty }

Depends on / 依赖: isRelLowerSet_empty, isRelLowerSet_faces
-/
instance : Bot (PreAbstractSimplicialComplex ι) where
  bot :=
    { faces := { _s | False }
      isRelLowerSet_faces := isRelLowerSet_empty }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSemilatticeSup (PreAbstractSimplicialComplex ι)
  body: .of_image SetLike.coe_subset_coe isLUB_biSup

中文:
实例 :
  签名: CompleteSemilatticeSup (PreAbstractSimplicialComplex ι)
  定义体: .of_image SetLike.coe_subset_coe isLUB_biSup

Depends on / 依赖: SetLike, SetLike.coe_subset_coe, coe_subset_coe, isLUB_biSup, of_image
-/
instance : CompleteSemilatticeSup (PreAbstractSimplicialComplex ι) where
  isLUB_sSup _ := .of_image SetLike.coe_subset_coe isLUB_biSup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSemilatticeInf (PreAbstractSimplicialComplex ι)
  body: ⟨fun _ hK => Set.inter_subset_left.trans (Set.biInter_subset_of_mem hK),
      fun K hK _ ht => ⟨Set.mem_iInter₂.mpr fun _ hL => hK hL ht, (K.isRelLowerSet_faces ht).1⟩⟩

中文:
实例 :
  签名: CompleteSemilatticeInf (PreAbstractSimplicialComplex ι)
  定义体: ⟨fun _ hK => Set.inter_subset_left.trans (Set.biInter_subset_of_mem hK),
      fun K hK _ ht => ⟨Set.mem_iInter₂.mpr fun _ hL => hK hL ht, (K.isRelLowerSet_faces ht).1⟩⟩

Depends on / 依赖: K.isRelLowerSet_faces, Set.biInter_subset_of_mem, Set.inter_subset_left.trans, Set.mem_iInter, biInter_subset_of_mem, inter_subset_left, isRelLowerSet_faces
-/
instance : CompleteSemilatticeInf (PreAbstractSimplicialComplex ι) where
  isGLB_sInf _ :=
    ⟨fun _ hK => Set.inter_subset_left.trans (Set.biInter_subset_of_mem hK),
      fun K hK _ ht => ⟨Set.mem_iInter₂.mpr fun _ hL => hK hL ht, (K.isRelLowerSet_faces ht).1⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (PreAbstractSimplicialComplex ι)
  body: min
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ := Set.subset_inter
  sup := max
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ hK hL := Set.union_subset hK hL
  le_top K _ ht := (K.isR

中文:
实例 :
  签名: CompleteLattice (PreAbstractSimplicialComplex ι)
  定义体: min
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ := Set.subset_inter
  sup := max
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ hK hL := Set.union_subset hK hL
  le_top K _ ht := (K.isR
-/
instance : CompleteLattice (PreAbstractSimplicialComplex ι) where
  inf := min
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ := Set.subset_inter
  sup := max
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ hK hL := Set.union_subset hK hL
  le_top K _ ht := (K.isRelLowerSet_faces ht).1
  bot_le _ _ ht := ht.elim

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {α β : Type*} [DecidableEq β] (K : PreAbstractSimplicialComplex α) (f : α -> β)
  body: K.faces.image (fun s => s.image f)
  isRelLowerSet_faces := fun {x} h => by
    simp only [Set.mem_image] at h ⊢
    obtain ⟨s', hs', rfl⟩ := h
    constructor
    · exact Finset.image_nonempty.mpr (K.isRelLowerSet_faces hs').1
    · intro t hts ht
      obtain ⟨t', ht', rfl⟩ := Finset.subset_image_

中文:
定义 map
  签名: {α β : 类型} [DecidableEq β] (K : PreAbstractSimplicialComplex α) (f : α -> β)
  定义体: K.faces.image (fun s => s.image f)
  isRelLowerSet_faces := fun {x} h => by
    simp only [Set.mem_image] at h ⊢
    obtain ⟨s', hs', rfl⟩ := h
    constructor
    · exact Finset.image_nonempty.mpr (K.isRelLowerSet_faces hs').1
    · intro t hts ht
      obtain ⟨t', ht', rfl⟩ := Finset.subset_image_

Depends on / 依赖: K.faces.image, s.image
-/
def map {α β : Type*} [DecidableEq β] (K : PreAbstractSimplicialComplex α) (f : α -> β) :
    PreAbstractSimplicialComplex β where
  faces := K.faces.image (fun s => s.image f)
  isRelLowerSet_faces := fun {x} h => by
    simp only [Set.mem_image] at h ⊢
    obtain ⟨s', hs', rfl⟩ := h
    constructor
    · exact Finset.image_nonempty.mpr (K.isRelLowerSet_faces hs').1
    · intro t hts ht
      obtain ⟨t', ht', rfl⟩ := Finset.subset_image_iff.mp hts
      exact ⟨t', (K.isRelLowerSet_faces hs').2 ht' (Finset.image_nonempty.mp ht), rfl⟩

end PreAbstractSimplicialComplex


/--
An `AbstractSimplicialComplex` is a `PreAbstractSimplicialComplex` which contains all singletons.
-/
@[ext]
/--
Definition of `AbstractSimplicialComplex` / `AbstractSimplicialComplex` 的定义

English:
structure AbstractSimplicialComplex
  parameters: extends PreAbstractSimplicialComplex ι
  extends: PreAbstractSimplicialComplex ι
  axioms and operations (1):
    - singleton_mem : forall v : ι, {v} in faces

中文:
结构 AbstractSimplicialComplex
  参数: extends PreAbstractSimplicialComplex ι
  继承: PreAbstractSimplicialComplex ι
  公理与运算 (1 个):
    - singleton_mem : 对任意 v : ι, {v} in faces
-/
structure AbstractSimplicialComplex extends PreAbstractSimplicialComplex ι where
  /-- every singleton is a face -/
  singleton_mem : forall v : ι, {v} in faces

/--
Definition of `PreAbstractSimplicialComplex.toAbstractSimplicialComplex` / `PreAbstractSimplicialComplex.toAbstractSimplicialComplex` 的定义

English:
definition PreAbstractSimplicialComplex.toAbstractSimplicialComplex
  body: { K with singleton_mem := h }

中文:
定义 PreAbstractSimplicialComplex.toAbstractSimplicialComplex
  定义体: { K with singleton_mem := h }

Depends on / 依赖: singleton_mem
-/
def PreAbstractSimplicialComplex.toAbstractSimplicialComplex
    (K : PreAbstractSimplicialComplex ι) (h : forall v : ι, {v} in K.faces) :
    AbstractSimplicialComplex ι :=
  { K with singleton_mem := h }

/--
Definition of `PreAbstractSimplicialComplex.addSingletons` / `PreAbstractSimplicialComplex.addSingletons` 的定义

English:
definition PreAbstractSimplicialComplex.addSingletons
  body: { faces := K.faces union { s | exists v, s = {v} }
    isRelLowerSet_faces := IsRelLowerSet.union K.isRelLowerSet_faces (fun {x} ⟨v, hv⟩ => by
      constructor
      · rw [hv]; exact Finset.singleton_nonempty _
      · intro t hts ht
        cases Finset.subset_singleton_iff.mp (hv ▸ hts) with
    

中文:
定义 PreAbstractSimplicialComplex.addSingletons
  定义体: { faces := K.faces union { s | exists v, s = {v} }
    isRelLowerSet_faces := IsRelLowerSet.union K.isRelLowerSet_faces (fun {x} ⟨v, hv⟩ => by
      constructor
      · rw [hv]; exact Finset.singleton_nonempty _
      · intro t hts ht
        cases Finset.subset_singleton_iff.mp (hv ▸ hts) with
    

Depends on / 依赖: Finset, Finset.singleton_nonempty, Finset.subset_singleton_iff.mp, IsRelLowerSet, IsRelLowerSet.union, K.faces, K.isRelLowerSet_faces, Or.inr, ht.ne_empty, isRelLowerSet_faces, ne_empty, singleton_mem, singleton_nonempty, subset_singleton_iff
-/
def PreAbstractSimplicialComplex.addSingletons
    (K : PreAbstractSimplicialComplex ι) :
    AbstractSimplicialComplex ι :=
  { faces := K.faces union { s | exists v, s = {v} }
    isRelLowerSet_faces := IsRelLowerSet.union K.isRelLowerSet_faces (fun {x} ⟨v, hv⟩ => by
      constructor
      · rw [hv]; exact Finset.singleton_nonempty _
      · intro t hts ht
        cases Finset.subset_singleton_iff.mp (hv ▸ hts) with
        | inl h => exact (ht.ne_empty h).elim
        | inr h => exact ⟨v, h⟩)
    singleton_mem v := Or.inr ⟨v, rfl⟩ }

namespace AbstractSimplicialComplex

variable {ι}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (AbstractSimplicialComplex ι) (Finset ι)
  body: K.faces
  coe_injective _ _ _ := by
    ext
    grind

中文:
实例 :
  签名: SetLike (AbstractSimplicialComplex ι) (Finset ι)
  定义体: K.faces
  coe_injective _ _ _ := by
    ext
    grind

Depends on / 依赖: K.faces
-/
instance : SetLike (AbstractSimplicialComplex ι) (Finset ι) where
  coe K := K.faces
  coe_injective _ _ _ := by
    ext
    grind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (AbstractSimplicialComplex ι)
  body: { K.toPreAbstractSimplicialComplex ⊓ L.toPreAbstractSimplicialComplex with
      singleton_mem v := ⟨K.singleton_mem v, L.singleton_mem v⟩ }

中文:
实例 :
  签名: Min (AbstractSimplicialComplex ι)
  定义体: { K.toPreAbstractSimplicialComplex ⊓ L.toPreAbstractSimplicialComplex with
      singleton_mem v := ⟨K.singleton_mem v, L.singleton_mem v⟩ }

Depends on / 依赖: K.singleton_mem, K.toPreAbstractSimplicialComplex, L.singleton_mem, L.toPreAbstractSimplicialComplex, singleton_mem, toPreAbstractSimplicialComplex
-/
instance : Min (AbstractSimplicialComplex ι) where
  min K L :=
    { K.toPreAbstractSimplicialComplex ⊓ L.toPreAbstractSimplicialComplex with
      singleton_mem v := ⟨K.singleton_mem v, L.singleton_mem v⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (AbstractSimplicialComplex ι)
  body: { K.toPreAbstractSimplicialComplex ⊔ L.toPreAbstractSimplicialComplex with
      singleton_mem v := Or.inl (K.singleton_mem v) }

中文:
实例 :
  签名: Max (AbstractSimplicialComplex ι)
  定义体: { K.toPreAbstractSimplicialComplex ⊔ L.toPreAbstractSimplicialComplex with
      singleton_mem v := Or.inl (K.singleton_mem v) }

Depends on / 依赖: K.singleton_mem, K.toPreAbstractSimplicialComplex, L.toPreAbstractSimplicialComplex, Or.inl, singleton_mem, toPreAbstractSimplicialComplex
-/
instance : Max (AbstractSimplicialComplex ι) where
  max K L :=
    { K.toPreAbstractSimplicialComplex ⊔ L.toPreAbstractSimplicialComplex with
      singleton_mem v := Or.inl (K.singleton_mem v) }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (AbstractSimplicialComplex ι)
  body: K.faces subseteq L.faces

中文:
实例 :
  签名: LE (AbstractSimplicialComplex ι)
  定义体: K.faces subseteq L.faces

Depends on / 依赖: K.faces, L.faces, subseteq
-/
instance : LE (AbstractSimplicialComplex ι) where
  le K L := K.faces subseteq L.faces

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LT (AbstractSimplicialComplex ι)
  body: K.faces ⊂ L.faces

中文:
实例 :
  签名: LT (AbstractSimplicialComplex ι)
  定义体: K.faces ⊂ L.faces

Depends on / 依赖: K.faces, L.faces
-/
instance : LT (AbstractSimplicialComplex ι) where
  lt K L := K.faces ⊂ L.faces

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsConcreteLE (AbstractSimplicialComplex ι) (Finset ι)
  body: .rfl

中文:
实例 :
  签名: IsConcreteLE (AbstractSimplicialComplex ι) (Finset ι)
  定义体: .rfl
-/
instance : IsConcreteLE (AbstractSimplicialComplex ι) (Finset ι) where
  coe_subset_coe' := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (AbstractSimplicialComplex ι)
  body: PartialOrder.lift (fun K => K.faces) (fun _ _ => AbstractSimplicialComplex.ext)

中文:
实例 :
  签名: PartialOrder (AbstractSimplicialComplex ι)
  定义体: PartialOrder.lift (fun K => K.faces) (fun _ _ => AbstractSimplicialComplex.ext)

Depends on / 依赖: AbstractSimplicialComplex, AbstractSimplicialComplex.ext, K.faces, PartialOrder, PartialOrder.lift
-/
instance : PartialOrder (AbstractSimplicialComplex ι) :=
  PartialOrder.lift (fun K => K.faces) (fun _ _ => AbstractSimplicialComplex.ext)

/--
theorem `toPreAbstractSimplicialComplex_injective` / 定理 `toPreAbstractSimplicialComplex_injective`

English:
theorem toPreAbstractSimplicialComplex_injective
  proof: fun _ _ h => AbstractSimplicialComplex.ext (congrArg PreAbstractSimplicialComplex.faces h)

@[simp]

中文:
定理 toPreAbstractSimplicialComplex_injective
  证明: fun _ _ h => AbstractSimplicialComplex.ext (congrArg PreAbstractSimplicialComplex.faces h)

@[simp]
-/
theorem toPreAbstractSimplicialComplex_injective :
    Function.Injective (toPreAbstractSimplicialComplex (ι := ι)) :=
  fun _ _ h => AbstractSimplicialComplex.ext (congrArg PreAbstractSimplicialComplex.faces h)

@[simp]
/--
theorem `toPreAbstractSimplicialComplex_le_iff` / 定理 `toPreAbstractSimplicialComplex_le_iff`

English:
theorem toPreAbstractSimplicialComplex_le_iff
  given: {K L : AbstractSimplicialComplex ι}
  proof: Iff.rfl

@[simp]

中文:
定理 toPreAbstractSimplicialComplex_le_iff
  条件: {K L : AbstractSimplicialComplex ι}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem toPreAbstractSimplicialComplex_le_iff {K L : AbstractSimplicialComplex ι} :
    K.toPreAbstractSimplicialComplex <= L.toPreAbstractSimplicialComplex ↔ K <= L :=
  Iff.rfl

@[simp]
/--
theorem `toPreAbstractSimplicialComplex_lt_iff` / 定理 `toPreAbstractSimplicialComplex_lt_iff`

English:
theorem toPreAbstractSimplicialComplex_lt_iff
  given: {K L : AbstractSimplicialComplex ι}
  proof: Iff.rfl

中文:
定理 toPreAbstractSimplicialComplex_lt_iff
  条件: {K L : AbstractSimplicialComplex ι}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toPreAbstractSimplicialComplex_lt_iff {K L : AbstractSimplicialComplex ι} :
    K.toPreAbstractSimplicialComplex < L.toPreAbstractSimplicialComplex ↔ K < L :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (AbstractSimplicialComplex ι)
  body: { faces := (⋃ K in s, K.faces) union { t | exists v, t = {v} }
      isRelLowerSet_faces := IsRelLowerSet.union
        (IsRelLowerSet.iUnion₂ fun K _ => K.isRelLowerSet_faces)
        (fun {x} ⟨v, hv⟩ => by
          constructor
          · rw [hv]; exact Finset.singleton_nonempty _
          · int

中文:
实例 :
  签名: SupSet (AbstractSimplicialComplex ι)
  定义体: { faces := (⋃ K in s, K.faces) union { t | exists v, t = {v} }
      isRelLowerSet_faces := IsRelLowerSet.union
        (IsRelLowerSet.iUnion₂ fun K _ => K.isRelLowerSet_faces)
        (fun {x} ⟨v, hv⟩ => by
          constructor
          · rw [hv]; exact Finset.singleton_nonempty _
          · int

Depends on / 依赖: Finset, Finset.singleton_nonempty, Finset.subset_singleton_iff.mp, IsRelLowerSet, IsRelLowerSet.iUnion, IsRelLowerSet.union, K.faces, K.isRelLowerSet_faces, Or.inr, ht.ne_empty, isRelLowerSet_faces, ne_empty, singleton_mem, singleton_nonempty, subset_singleton_iff
-/
instance : SupSet (AbstractSimplicialComplex ι) where
  sSup s :=
    { faces := (⋃ K in s, K.faces) union { t | exists v, t = {v} }
      isRelLowerSet_faces := IsRelLowerSet.union
        (IsRelLowerSet.iUnion₂ fun K _ => K.isRelLowerSet_faces)
        (fun {x} ⟨v, hv⟩ => by
          constructor
          · rw [hv]; exact Finset.singleton_nonempty _
          · intro t hts ht
            cases Finset.subset_singleton_iff.mp (hv ▸ hts) with
            | inl h => exact (ht.ne_empty h).elim
            | inr h => exact ⟨v, h⟩)
      singleton_mem v := Or.inr ⟨v, rfl⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (AbstractSimplicialComplex ι)
  body: { faces := (⋂ K in s, K.faces) inter { t | t.Nonempty }
      isRelLowerSet_faces := fun {_} ⟨hx, hn⟩ => by
        grind [IsRelLowerSet.mem_of_le, PreAbstractSimplicialComplex.isRelLowerSet_faces,
          mem_iInter]
      singleton_mem v := by
        grind [Set.mem_iInter, Finset.singleton_none

中文:
实例 :
  签名: InfSet (AbstractSimplicialComplex ι)
  定义体: { faces := (⋂ K in s, K.faces) inter { t | t.Nonempty }
      isRelLowerSet_faces := fun {_} ⟨hx, hn⟩ => by
        grind [IsRelLowerSet.mem_of_le, PreAbstractSimplicialComplex.isRelLowerSet_faces,
          mem_iInter]
      singleton_mem v := by
        grind [Set.mem_iInter, Finset.singleton_none

Depends on / 依赖: Finset, Finset.singleton_nonempty, IsRelLowerSet, IsRelLowerSet.mem_of_le, K.faces, Nonempty, PreAbstractSimplicialComplex, PreAbstractSimplicialComplex.isRelLowerSet_faces, Set.mem_iInter, isRelLowerSet_faces, mem_iInter, mem_of_le, singleton_mem, singleton_nonempty, t.Nonempty
-/
instance : InfSet (AbstractSimplicialComplex ι) where
  sInf s :=
    { faces := (⋂ K in s, K.faces) inter { t | t.Nonempty }
      isRelLowerSet_faces := fun {_} ⟨hx, hn⟩ => by
        grind [IsRelLowerSet.mem_of_le, PreAbstractSimplicialComplex.isRelLowerSet_faces,
          mem_iInter]
      singleton_mem v := by
        grind [Set.mem_iInter, Finset.singleton_nonempty, singleton_mem] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (AbstractSimplicialComplex ι)
  body: { (⊤ : PreAbstractSimplicialComplex ι) with
      singleton_mem _ := Finset.singleton_nonempty _ }

中文:
实例 :
  签名: Top (AbstractSimplicialComplex ι)
  定义体: { (⊤ : PreAbstractSimplicialComplex ι) with
      singleton_mem _ := Finset.singleton_nonempty _ }

Depends on / 依赖: Finset, Finset.singleton_nonempty, PreAbstractSimplicialComplex, singleton_mem, singleton_nonempty
-/
instance : Top (AbstractSimplicialComplex ι) where
  top :=
    { (⊤ : PreAbstractSimplicialComplex ι) with
      singleton_mem _ := Finset.singleton_nonempty _ }

/--
lemma `top_toPreAbstractSimplicialComplex` / 引理 `top_toPreAbstractSimplicialComplex`

English:
lemma top_toPreAbstractSimplicialComplex
  proof: rfl

中文:
引理 top_toPreAbstractSimplicialComplex
  证明: rfl
-/
lemma top_toPreAbstractSimplicialComplex :
    (⊤ : AbstractSimplicialComplex ι).toPreAbstractSimplicialComplex = ⊤ :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (AbstractSimplicialComplex ι)
  body: { faces := { s | exists v, s = {v} }
      isRelLowerSet_faces := fun {x} ⟨v, hv⟩ => by
        constructor
        · rw [hv]; exact Finset.singleton_nonempty _
        · intro t hts ht
          cases Finset.subset_singleton_iff.mp (hv ▸ hts) with
          | inl h => exact (ht.ne_empty h).elim
   

中文:
实例 :
  签名: Bot (AbstractSimplicialComplex ι)
  定义体: { faces := { s | exists v, s = {v} }
      isRelLowerSet_faces := fun {x} ⟨v, hv⟩ => by
        constructor
        · rw [hv]; exact Finset.singleton_nonempty _
        · intro t hts ht
          cases Finset.subset_singleton_iff.mp (hv ▸ hts) with
          | inl h => exact (ht.ne_empty h).elim
   

Depends on / 依赖: Finset, Finset.singleton_nonempty, Finset.subset_singleton_iff.mp, ht.ne_empty, isRelLowerSet_faces, ne_empty, singleton_mem, singleton_nonempty, subset_singleton_iff
-/
instance : Bot (AbstractSimplicialComplex ι) where
  bot :=
    { faces := { s | exists v, s = {v} }
      isRelLowerSet_faces := fun {x} ⟨v, hv⟩ => by
        constructor
        · rw [hv]; exact Finset.singleton_nonempty _
        · intro t hts ht
          cases Finset.subset_singleton_iff.mp (hv ▸ hts) with
          | inl h => exact (ht.ne_empty h).elim
          | inr h => exact ⟨v, h⟩
      singleton_mem v := ⟨v, rfl⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSemilatticeSup (AbstractSimplicialComplex ι)
  body: by
    constructor
    · intro K hK _ ht
      exact Or.inl (Set.mem_biUnion hK ht)
    · intro L hL _ ht
      cases ht with
      | inl ht =>
        simp only [Set.mem_iUnion] at ht
        obtain ⟨K, hK, htK⟩ := ht
        exact hL hK htK
      | inr ht =>
        obtain ⟨v, hv⟩ := ht
        ex

中文:
实例 :
  签名: CompleteSemilatticeSup (AbstractSimplicialComplex ι)
  定义体: by
    constructor
    · intro K hK _ ht
      exact Or.inl (Set.mem_biUnion hK ht)
    · intro L hL _ ht
      cases ht with
      | inl ht =>
        simp only [Set.mem_iUnion] at ht
        obtain ⟨K, hK, htK⟩ := ht
        exact hL hK htK
      | inr ht =>
        obtain ⟨v, hv⟩ := ht
        ex

Depends on / 依赖: L.singleton_mem, Or.inl, Set.mem_biUnion, Set.mem_iUnion, mem_biUnion, mem_iUnion, singleton_mem
-/
instance : CompleteSemilatticeSup (AbstractSimplicialComplex ι) where
  isLUB_sSup _ := by
    constructor
    · intro K hK _ ht
      exact Or.inl (Set.mem_biUnion hK ht)
    · intro L hL _ ht
      cases ht with
      | inl ht =>
        simp only [Set.mem_iUnion] at ht
        obtain ⟨K, hK, htK⟩ := ht
        exact hL hK htK
      | inr ht =>
        obtain ⟨v, hv⟩ := ht
        exact hv ▸ L.singleton_mem v

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSemilatticeInf (AbstractSimplicialComplex ι)
  body: ⟨fun _ hK => Set.inter_subset_left.trans (Set.biInter_subset_of_mem hK),
      fun K hK _ ht => ⟨Set.mem_iInter₂.mpr fun _ hL => hK hL ht, (K.isRelLowerSet_faces ht).1⟩⟩

中文:
实例 :
  签名: CompleteSemilatticeInf (AbstractSimplicialComplex ι)
  定义体: ⟨fun _ hK => Set.inter_subset_left.trans (Set.biInter_subset_of_mem hK),
      fun K hK _ ht => ⟨Set.mem_iInter₂.mpr fun _ hL => hK hL ht, (K.isRelLowerSet_faces ht).1⟩⟩

Depends on / 依赖: K.isRelLowerSet_faces, Set.biInter_subset_of_mem, Set.inter_subset_left.trans, Set.mem_iInter, biInter_subset_of_mem, inter_subset_left, isRelLowerSet_faces
-/
instance : CompleteSemilatticeInf (AbstractSimplicialComplex ι) where
  isGLB_sInf _ :=
    ⟨fun _ hK => Set.inter_subset_left.trans (Set.biInter_subset_of_mem hK),
      fun K hK _ ht => ⟨Set.mem_iInter₂.mpr fun _ hL => hK hL ht, (K.isRelLowerSet_faces ht).1⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (AbstractSimplicialComplex ι)
  body: min
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ := Set.subset_inter
  sup := max
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ := Set.union_subset
  le_top K _ ht := (K.isRelLowerSet_f

中文:
实例 :
  签名: CompleteLattice (AbstractSimplicialComplex ι)
  定义体: min
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ := Set.subset_inter
  sup := max
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ := Set.union_subset
  le_top K _ ht := (K.isRelLowerSet_f
-/
instance : CompleteLattice (AbstractSimplicialComplex ι) where
  inf := min
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ := Set.subset_inter
  sup := max
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ := Set.union_subset
  le_top K _ ht := (K.isRelLowerSet_faces ht).1
  bot_le K _ ht := by
    obtain ⟨v, hv⟩ := ht
    exact hv ▸ K.singleton_mem v

end AbstractSimplicialComplex

end
