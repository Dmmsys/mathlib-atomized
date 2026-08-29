/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.BooleanAlgebra

/-!
# Sets in sigma types

This file defines `Set.sigma`, the indexed sum of sets.
-/

@[expose] public section

namespace Set

variable {ι ι' : Type*} {α : ι -> Type*} {s s₁ s₂ : Set ι} {t t₁ t₂ : forall i, Set (α i)}
  {u : Set (Σ i, α i)} {x : Σ i, α i} {i j : ι} {a : α i}

@[simp]
/--
theorem `range_sigmaMk` / 定理 `range_sigmaMk`

English:
theorem range_sigmaMk
  given: (i : ι)
  statement: range (Sigma.mk i : α i -> Sigma α) = Sigma.fst ⁻¹' {i}
  proof: by grind

中文:
定理 range_sigmaMk
  条件: (i : ι)
  结论: range (Sigma.mk i : α i -> Sigma α) = Sigma.fst ⁻¹' {i}
  证明: by grind
-/
theorem range_sigmaMk (i : ι) : range (Sigma.mk i : α i -> Sigma α) = Sigma.fst ⁻¹' {i} := by grind

/--
theorem `preimage_image_sigmaMk_of_ne` / 定理 `preimage_image_sigmaMk_of_ne`

English:
theorem preimage_image_sigmaMk_of_ne
  given: (h : i != j) (s : Set (α j))
  proof: by grind

中文:
定理 preimage_image_sigmaMk_of_ne
  条件: (h : i != j) (s : Set (α j))
  证明: by grind
-/
theorem preimage_image_sigmaMk_of_ne (h : i != j) (s : Set (α j)) :
    Sigma.mk i ⁻¹' Sigma.mk j '' s = ∅ := by grind

/--
theorem `image_sigmaMk_preimage_sigmaMap_subset` / 定理 `image_sigmaMk_preimage_sigmaMap_subset`

English:
theorem image_sigmaMk_preimage_sigmaMap_subset
  statement: {β : ι' -> Type*} (f : ι -> ι')
  proof: image_subset_iff.2 fun x hx => ⟨g i x, hx, rfl⟩

中文:
定理 image_sigmaMk_preimage_sigmaMap_subset
  结论: {β : ι' -> 类型} (f : ι -> ι')
  证明: image_subset_iff.2 fun x hx => ⟨g i x, hx, rfl⟩

Depends on / 依赖: image_subset_iff
-/
theorem image_sigmaMk_preimage_sigmaMap_subset {β : ι' -> Type*} (f : ι -> ι')
    (g : forall i, α i -> β (f i)) (i : ι) (s : Set (β (f i))) :
    Sigma.mk i '' g i ⁻¹' s subseteq Sigma.map f g ⁻¹' Sigma.mk (f i) '' s :=
  image_subset_iff.2 fun x hx => ⟨g i x, hx, rfl⟩

/--
theorem `image_sigmaMk_preimage_sigmaMap` / 定理 `image_sigmaMk_preimage_sigmaMap`

English:
theorem image_sigmaMk_preimage_sigmaMap
  statement: {β : ι' -> Type*} {f : ι -> ι'} (hf : Function.Injective f)
  proof: by
  refine (image_sigmaMk_preimage_sigmaMap_subset f g i s).antisymm ?_
  rintro ⟨j, x⟩ ⟨y, hys, hxy⟩
  simp only [hf.eq_iff, Sigma.map, Sigma.ext_iff] at hxy
  grind

中文:
定理 image_sigmaMk_preimage_sigmaMap
  结论: {β : ι' -> 类型} {f : ι -> ι'} (hf : Function.Injective f)
  证明: by
  refine (image_sigmaMk_preimage_sigmaMap_subset f g i s).antisymm ?_
  rintro ⟨j, x⟩ ⟨y, hys, hxy⟩
  simp only [hf.eq_iff, Sigma.map, Sigma.ext_iff] at hxy
  grind

Depends on / 依赖: Sigma.ext_iff, Sigma.map, antisymm, eq_iff, ext_iff, hf.eq_iff, image_sigmaMk_preimage_sigmaMap_subset
-/
theorem image_sigmaMk_preimage_sigmaMap {β : ι' -> Type*} {f : ι -> ι'} (hf : Function.Injective f)
    (g : forall i, α i -> β (f i)) (i : ι) (s : Set (β (f i))) :
    Sigma.mk i '' g i ⁻¹' s = Sigma.map f g ⁻¹' Sigma.mk (f i) '' s := by
  refine (image_sigmaMk_preimage_sigmaMap_subset f g i s).antisymm ?_
  rintro ⟨j, x⟩ ⟨y, hys, hxy⟩
  simp only [hf.eq_iff, Sigma.map, Sigma.ext_iff] at hxy
  grind

/--
Definition of `sigma` / `sigma` 的定义

English:
definition sigma
  signature: (s : Set ι) (t : forall i, Set (α i))
  body: {x | x.1 in s ∧ x.2 in t x.1}

中文:
定义 sigma
  签名: (s : Set ι) (t : 对任意 i, Set (α i))
  定义体: {x | x.1 in s ∧ x.2 in t x.1}
-/
protected def sigma (s : Set ι) (t : forall i, Set (α i)) : Set (Σ i, α i) := {x | x.1 in s ∧ x.2 in t x.1}

/--
theorem `mem_sigma_iff` / 定理 `mem_sigma_iff`

English:
theorem mem_sigma_iff
  statement: x in s.sigma t ↔ x.1 in s ∧ x.2 in t x.1
  proof: Iff.rfl

中文:
定理 mem_sigma_iff
  结论: x in s.sigma t ↔ x.1 in s ∧ x.2 in t x.1
  证明: Iff.rfl
-/
@[simp, grind =] theorem mem_sigma_iff : x in s.sigma t ↔ x.1 in s ∧ x.2 in t x.1 := Iff.rfl

/--
theorem `mk_sigma_iff` / 定理 `mk_sigma_iff`

English:
theorem mk_sigma_iff
  statement: (⟨i, a⟩ : Σ i, α i) in s.sigma t ↔ i in s ∧ a in t i
  proof: Iff.rfl

中文:
定理 mk_sigma_iff
  结论: (⟨i, a⟩ : Σ i, α i) in s.sigma t ↔ i in s ∧ a in t i
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mk_sigma_iff : (⟨i, a⟩ : Σ i, α i) in s.sigma t ↔ i in s ∧ a in t i := Iff.rfl

/--
theorem `mk_mem_sigma` / 定理 `mk_mem_sigma`

English:
theorem mk_mem_sigma
  given: (hi : i in s) (ha : a in t i)
  statement: (⟨i, a⟩ : Σ i, α i) in s.sigma t
  proof: ⟨hi, ha⟩

中文:
定理 mk_mem_sigma
  条件: (hi : i in s) (ha : a in t i)
  结论: (⟨i, a⟩ : Σ i, α i) in s.sigma t
  证明: ⟨hi, ha⟩
-/
theorem mk_mem_sigma (hi : i in s) (ha : a in t i) : (⟨i, a⟩ : Σ i, α i) in s.sigma t := ⟨hi, ha⟩

/--
theorem `sigma_mono` / 定理 `sigma_mono`

English:
theorem sigma_mono
  given: (hs : s₁ subseteq s₂) (ht : forall i, t₁ i subseteq t₂ i)
  statement: s₁.sigma t₁ subseteq s₂.sigma t₂
  proof: fun _ hx =>
  ⟨hs hx.1, ht _ hx.2⟩

中文:
定理 sigma_mono
  条件: (hs : s₁ subseteq s₂) (ht : 对任意 i, t₁ i subseteq t₂ i)
  结论: s₁.sigma t₁ subseteq s₂.sigma t₂
  证明: fun _ hx =>
  ⟨hs hx.1, ht _ hx.2⟩
-/
theorem sigma_mono (hs : s₁ subseteq s₂) (ht : forall i, t₁ i subseteq t₂ i) : s₁.sigma t₁ subseteq s₂.sigma t₂ := fun _ hx =>
  ⟨hs hx.1, ht _ hx.2⟩

/--
theorem `sigma_subset_iff` / 定理 `sigma_subset_iff`

English:
theorem sigma_subset_iff
  proof: by grind

中文:
定理 sigma_subset_iff
  证明: by grind
-/
theorem sigma_subset_iff :
    s.sigma t subseteq u ↔ forall ⦃i⦄, i in s -> forall ⦃a⦄, a in t i -> (⟨i, a⟩ : Σ i, α i) in u := by grind

/--
theorem `forall_sigma_iff` / 定理 `forall_sigma_iff`

English:
theorem forall_sigma_iff
  given: {p : (Σ i, α i) -> Prop}
  proof: by grind

中文:
定理 forall_sigma_iff
  条件: {p : (Σ i, α i) -> 命题}
  证明: by grind
-/
theorem forall_sigma_iff {p : (Σ i, α i) -> Prop} :
    (forall x in s.sigma t, p x) ↔ forall ⦃i⦄, i in s -> forall ⦃a⦄, a in t i -> p ⟨i, a⟩ := by grind

/--
theorem `exists_sigma_iff` / 定理 `exists_sigma_iff`

English:
theorem exists_sigma_iff
  given: {p : (Σ i, α i) -> Prop}
  proof: by grind

中文:
定理 exists_sigma_iff
  条件: {p : (Σ i, α i) -> 命题}
  证明: by grind
-/
theorem exists_sigma_iff {p : (Σ i, α i) -> Prop} :
    (exists x in s.sigma t, p x) ↔ exists i in s, exists a in t i, p ⟨i, a⟩ := by grind

/--
theorem `sigma_empty` / 定理 `sigma_empty`

English:
theorem sigma_empty
  statement: s.sigma (fun i => (∅ : Set (α i))) = ∅
  proof: by grind

中文:
定理 sigma_empty
  结论: s.sigma (fun i => (∅ : Set (α i))) = ∅
  证明: by grind
-/
@[simp] theorem sigma_empty : s.sigma (fun i => (∅ : Set (α i))) = ∅ := by grind

/--
theorem `empty_sigma` / 定理 `empty_sigma`

English:
theorem empty_sigma
  statement: (∅ : Set ι).sigma t = ∅
  proof: by grind

中文:
定理 empty_sigma
  结论: (∅ : Set ι).sigma t = ∅
  证明: by grind
-/
@[simp] theorem empty_sigma : (∅ : Set ι).sigma t = ∅ := by grind

/--
theorem `univ_sigma_univ` / 定理 `univ_sigma_univ`

English:
theorem univ_sigma_univ
  statement: (@univ ι).sigma (fun _ => @univ (α i)) = univ
  proof: by grind

@[simp]

中文:
定理 univ_sigma_univ
  结论: (@univ ι).sigma (fun _ => @univ (α i)) = univ
  证明: by grind

@[simp]
-/
theorem univ_sigma_univ : (@univ ι).sigma (fun _ => @univ (α i)) = univ := by grind

@[simp]
/--
theorem `sigma_univ` / 定理 `sigma_univ`

English:
theorem sigma_univ
  statement: s.sigma (fun _ => univ : forall i, Set (α i)) = Sigma.fst ⁻¹' s
  proof: by grind

中文:
定理 sigma_univ
  结论: s.sigma (fun _ => univ : 对任意 i, Set (α i)) = Sigma.fst ⁻¹' s
  证明: by grind
-/
theorem sigma_univ : s.sigma (fun _ => univ : forall i, Set (α i)) = Sigma.fst ⁻¹' s := by grind

/--
theorem `univ_sigma_preimage_mk` / 定理 `univ_sigma_preimage_mk`

English:
theorem univ_sigma_preimage_mk
  given: (s : Set (Σ i, α i))
  proof: by grind

@[simp]

中文:
定理 univ_sigma_preimage_mk
  条件: (s : Set (Σ i, α i))
  证明: by grind

@[simp]
-/
@[simp] theorem univ_sigma_preimage_mk (s : Set (Σ i, α i)) :
    (univ : Set ι).sigma (fun i => Sigma.mk i ⁻¹' s) = s := by grind

@[simp]
/--
theorem `singleton_sigma` / 定理 `singleton_sigma`

English:
theorem singleton_sigma
  statement: ({i} : Set ι).sigma t = Sigma.mk i '' t i
  proof: by grind

@[simp]

中文:
定理 singleton_sigma
  结论: ({i} : Set ι).sigma t = Sigma.mk i '' t i
  证明: by grind

@[simp]
-/
theorem singleton_sigma : ({i} : Set ι).sigma t = Sigma.mk i '' t i := by grind

@[simp]
/--
theorem `sigma_singleton` / 定理 `sigma_singleton`

English:
theorem sigma_singleton
  given: {a : forall i, α i}
  proof: by grind

中文:
定理 sigma_singleton
  条件: {a : 对任意 i, α i}
  证明: by grind
-/
theorem sigma_singleton {a : forall i, α i} :
    s.sigma (fun i => ({a i} : Set (α i))) = (fun i => Sigma.mk i <| a i) '' s := by grind

/--
theorem `singleton_sigma_singleton` / 定理 `singleton_sigma_singleton`

English:
theorem singleton_sigma_singleton
  given: {a : forall i, α i}
  proof: by grind

@[simp]

中文:
定理 singleton_sigma_singleton
  条件: {a : 对任意 i, α i}
  证明: by grind

@[simp]
-/
theorem singleton_sigma_singleton {a : forall i, α i} :
    (({i} : Set ι).sigma fun i => ({a i} : Set (α i))) = {⟨i, a i⟩} := by grind

@[simp]
/--
theorem `union_sigma` / 定理 `union_sigma`

English:
theorem union_sigma
  statement: (s₁ union s₂).sigma t = s₁.sigma t union s₂.sigma t
  proof: by grind

@[simp]

中文:
定理 union_sigma
  结论: (s₁ union s₂).sigma t = s₁.sigma t union s₂.sigma t
  证明: by grind

@[simp]
-/
theorem union_sigma : (s₁ union s₂).sigma t = s₁.sigma t union s₂.sigma t := by grind

@[simp]
/--
theorem `sigma_union` / 定理 `sigma_union`

English:
theorem sigma_union
  statement: s.sigma (fun i => t₁ i union t₂ i) = s.sigma t₁ union s.sigma t₂
  proof: by grind

中文:
定理 sigma_union
  结论: s.sigma (fun i => t₁ i union t₂ i) = s.sigma t₁ union s.sigma t₂
  证明: by grind
-/
theorem sigma_union : s.sigma (fun i => t₁ i union t₂ i) = s.sigma t₁ union s.sigma t₂ := by grind

/--
theorem `sigma_inter_sigma` / 定理 `sigma_inter_sigma`

English:
theorem sigma_inter_sigma
  statement: s₁.sigma t₁ inter s₂.sigma t₂ = (s₁ inter s₂).sigma fun i => t₁ i inter t₂ i
  proof: by
  grind

中文:
定理 sigma_inter_sigma
  结论: s₁.sigma t₁ inter s₂.sigma t₂ = (s₁ inter s₂).sigma fun i => t₁ i inter t₂ i
  证明: by
  grind
-/
theorem sigma_inter_sigma : s₁.sigma t₁ inter s₂.sigma t₂ = (s₁ inter s₂).sigma fun i => t₁ i inter t₂ i := by
  grind

variable {β : Type*} [CompleteLattice β]

/--
theorem `_root_.biSup_sigma` / 定理 `_root_.biSup_sigma`

English:
theorem _root_.biSup_sigma
  given: (s : Set ι) (t : forall i, Set (α i)) (f : Sigma α -> β)
  proof: eq_of_forall_ge_iff fun _ => ⟨by simp_all, by simp_all⟩

中文:
定理 _root_.biSup_sigma
  条件: (s : Set ι) (t : 对任意 i, Set (α i)) (f : Sigma α -> β)
  证明: eq_of_forall_ge_iff fun _ => ⟨by simp_all, by simp_all⟩

Depends on / 依赖: eq_of_forall_ge_iff
-/
theorem _root_.biSup_sigma (s : Set ι) (t : forall i, Set (α i)) (f : Sigma α -> β) :
    ⨆ ij in s.sigma t, f ij = ⨆ (i in s) (j in t i), f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun _ => ⟨by simp_all, by simp_all⟩

/--
theorem `_root_.biSup_sigma'` / 定理 `_root_.biSup_sigma'`

English:
theorem _root_.biSup_sigma'
  given: (s : Set ι) (t : forall i, Set (α i)) (f : forall i, α i -> β)
  proof: Eq.symm (biSup_sigma _ _ _)

中文:
定理 _root_.biSup_sigma'
  条件: (s : Set ι) (t : 对任意 i, Set (α i)) (f : 对任意 i, α i -> β)
  证明: Eq.symm (biSup_sigma _ _ _)

Depends on / 依赖: Eq.symm, biSup_sigma
-/
theorem _root_.biSup_sigma' (s : Set ι) (t : forall i, Set (α i)) (f : forall i, α i -> β) :
    ⨆ (i in s) (j in t i), f i j = ⨆ ij in s.sigma t, f ij.fst ij.snd :=
  Eq.symm (biSup_sigma _ _ _)

/--
theorem `_root_.biInf_sigma` / 定理 `_root_.biInf_sigma`

English:
theorem _root_.biInf_sigma
  given: (s : Set ι) (t : forall i, Set (α i)) (f : Sigma α -> β)
  proof: biSup_sigma (β := βᵒᵈ) _ _ _

中文:
定理 _root_.biInf_sigma
  条件: (s : Set ι) (t : 对任意 i, Set (α i)) (f : Sigma α -> β)
  证明: biSup_sigma (β := βᵒᵈ) _ _ _

Depends on / 依赖: biSup_sigma
-/
theorem _root_.biInf_sigma (s : Set ι) (t : forall i, Set (α i)) (f : Sigma α -> β) :
    ⨅ ij in s.sigma t, f ij = ⨅ (i in s) (j in t i), f ⟨i, j⟩ :=
  biSup_sigma (β := βᵒᵈ) _ _ _

/--
theorem `_root_.biInf_sigma'` / 定理 `_root_.biInf_sigma'`

English:
theorem _root_.biInf_sigma'
  given: (s : Set ι) (t : forall i, Set (α i)) (f : forall i, α i -> β)
  proof: Eq.symm (biInf_sigma _ _ _)

中文:
定理 _root_.biInf_sigma'
  条件: (s : Set ι) (t : 对任意 i, Set (α i)) (f : 对任意 i, α i -> β)
  证明: Eq.symm (biInf_sigma _ _ _)

Depends on / 依赖: Eq.symm, biInf_sigma
-/
theorem _root_.biInf_sigma' (s : Set ι) (t : forall i, Set (α i)) (f : forall i, α i -> β) :
    ⨅ (i in s) (j in t i), f i j = ⨅ ij in s.sigma t, f ij.fst ij.snd :=
  Eq.symm (biInf_sigma _ _ _)

variable {β : Type*}

/--
theorem `biUnion_sigma` / 定理 `biUnion_sigma`

English:
theorem biUnion_sigma
  given: (s : Set ι) (t : forall i, Set (α i)) (f : Sigma α -> Set β)
  proof: biSup_sigma _ _ _

中文:
定理 biUnion_sigma
  条件: (s : Set ι) (t : 对任意 i, Set (α i)) (f : Sigma α -> Set β)
  证明: biSup_sigma _ _ _

Depends on / 依赖: biSup_sigma
-/
theorem biUnion_sigma (s : Set ι) (t : forall i, Set (α i)) (f : Sigma α -> Set β) :
    ⋃ ij in s.sigma t, f ij = ⋃ i in s, ⋃ j in t i, f ⟨i, j⟩ :=
  biSup_sigma _ _ _

/--
theorem `biUnion_sigma'` / 定理 `biUnion_sigma'`

English:
theorem biUnion_sigma'
  given: (s : Set ι) (t : forall i, Set (α i)) (f : forall i, α i -> Set β)
  proof: biSup_sigma' _ _ _

中文:
定理 biUnion_sigma'
  条件: (s : Set ι) (t : 对任意 i, Set (α i)) (f : 对任意 i, α i -> Set β)
  证明: biSup_sigma' _ _ _

Depends on / 依赖: biSup_sigma
-/
theorem biUnion_sigma' (s : Set ι) (t : forall i, Set (α i)) (f : forall i, α i -> Set β) :
    ⋃ i in s, ⋃ j in t i, f i j = ⋃ ij in s.sigma t, f ij.fst ij.snd :=
  biSup_sigma' _ _ _

/--
theorem `biInter_sigma` / 定理 `biInter_sigma`

English:
theorem biInter_sigma
  given: (s : Set ι) (t : forall i, Set (α i)) (f : Sigma α -> Set β)
  proof: biInf_sigma _ _ _

中文:
定理 biInter_sigma
  条件: (s : Set ι) (t : 对任意 i, Set (α i)) (f : Sigma α -> Set β)
  证明: biInf_sigma _ _ _

Depends on / 依赖: biInf_sigma
-/
theorem biInter_sigma (s : Set ι) (t : forall i, Set (α i)) (f : Sigma α -> Set β) :
    ⋂ ij in s.sigma t, f ij = ⋂ i in s, ⋂ j in t i, f ⟨i, j⟩ :=
  biInf_sigma _ _ _

/--
theorem `biInter_sigma'` / 定理 `biInter_sigma'`

English:
theorem biInter_sigma'
  given: (s : Set ι) (t : forall i, Set (α i)) (f : forall i, α i -> Set β)
  proof: biInf_sigma' _ _ _

中文:
定理 biInter_sigma'
  条件: (s : Set ι) (t : 对任意 i, Set (α i)) (f : 对任意 i, α i -> Set β)
  证明: biInf_sigma' _ _ _

Depends on / 依赖: biInf_sigma
-/
theorem biInter_sigma' (s : Set ι) (t : forall i, Set (α i)) (f : forall i, α i -> Set β) :
    ⋂ i in s, ⋂ j in t i, f i j = ⋂ ij in s.sigma t, f ij.fst ij.snd :=
  biInf_sigma' _ _ _

variable {β : ι -> Type*}

/--
theorem `insert_sigma` / 定理 `insert_sigma`

English:
theorem insert_sigma
  statement: (insert i s).sigma t = Sigma.mk i '' t i union s.sigma t
  proof: by grind

中文:
定理 insert_sigma
  结论: (insert i s).sigma t = Sigma.mk i '' t i union s.sigma t
  证明: by grind
-/
theorem insert_sigma : (insert i s).sigma t = Sigma.mk i '' t i union s.sigma t := by grind

/--
theorem `sigma_insert` / 定理 `sigma_insert`

English:
theorem sigma_insert
  given: {a : forall i, α i}
  proof: by grind

中文:
定理 sigma_insert
  条件: {a : 对任意 i, α i}
  证明: by grind
-/
theorem sigma_insert {a : forall i, α i} :
    s.sigma (fun i => insert (a i) (t i)) = (fun i => ⟨i, a i⟩) '' s union s.sigma t := by grind

/--
theorem `sigma_preimage_eq` / 定理 `sigma_preimage_eq`

English:
theorem sigma_preimage_eq
  given: {f : ι' -> ι} {g : forall i, β i -> α i}
  proof: rfl

中文:
定理 sigma_preimage_eq
  条件: {f : ι' -> ι} {g : 对任意 i, β i -> α i}
  证明: rfl
-/
theorem sigma_preimage_eq {f : ι' -> ι} {g : forall i, β i -> α i} :
    (f ⁻¹' s).sigma (fun i => g (f i) ⁻¹' t (f i)) =
      (fun p : Σ i, β (f i) => Sigma.mk _ (g _ p.2)) ⁻¹' s.sigma t := rfl

/--
theorem `sigma_preimage_left` / 定理 `sigma_preimage_left`

English:
theorem sigma_preimage_left
  given: {f : ι' -> ι}
  proof: rfl

中文:
定理 sigma_preimage_left
  条件: {f : ι' -> ι}
  证明: rfl
-/
theorem sigma_preimage_left {f : ι' -> ι} :
    ((f ⁻¹' s).sigma fun i => t (f i)) = (fun p : Σ i, α (f i) => Sigma.mk _ p.2) ⁻¹' s.sigma t :=
  rfl

/--
theorem `sigma_preimage_right` / 定理 `sigma_preimage_right`

English:
theorem sigma_preimage_right
  given: {g : forall i, β i -> α i}
  proof: rfl

中文:
定理 sigma_preimage_right
  条件: {g : 对任意 i, β i -> α i}
  证明: rfl
-/
theorem sigma_preimage_right {g : forall i, β i -> α i} :
    (s.sigma fun i => g i ⁻¹' t i) = (fun p : Σ i, β i => Sigma.mk p.1 (g _ p.2)) ⁻¹' s.sigma t :=
  rfl

/--
theorem `preimage_sigmaMap_sigma` / 定理 `preimage_sigmaMap_sigma`

English:
theorem preimage_sigmaMap_sigma
  statement: {α' : ι' -> Type*} (f : ι -> ι') (g : forall i, α i -> α' (f i))
  proof: rfl

@[simp]

中文:
定理 preimage_sigmaMap_sigma
  结论: {α' : ι' -> 类型} (f : ι -> ι') (g : 对任意 i, α i -> α' (f i))
  证明: rfl

@[simp]
-/
theorem preimage_sigmaMap_sigma {α' : ι' -> Type*} (f : ι -> ι') (g : forall i, α i -> α' (f i))
    (s : Set ι') (t : forall i, Set (α' i)) :
    Sigma.map f g ⁻¹' s.sigma t = (f ⁻¹' s).sigma fun i => g i ⁻¹' t (f i) := rfl

@[simp]
/--
theorem `mk_preimage_sigma` / 定理 `mk_preimage_sigma`

English:
theorem mk_preimage_sigma
  given: (hi : i in s)
  statement: Sigma.mk i ⁻¹' s.sigma t = t i
  proof: by grind

@[simp]

中文:
定理 mk_preimage_sigma
  条件: (hi : i in s)
  结论: Sigma.mk i ⁻¹' s.sigma t = t i
  证明: by grind

@[simp]
-/
theorem mk_preimage_sigma (hi : i in s) : Sigma.mk i ⁻¹' s.sigma t = t i := by grind

@[simp]
/--
theorem `mk_preimage_sigma_eq_empty` / 定理 `mk_preimage_sigma_eq_empty`

English:
theorem mk_preimage_sigma_eq_empty
  given: (hi : i ∉ s)
  statement: Sigma.mk i ⁻¹' s.sigma t = ∅
  proof: by grind

中文:
定理 mk_preimage_sigma_eq_empty
  条件: (hi : i ∉ s)
  结论: Sigma.mk i ⁻¹' s.sigma t = ∅
  证明: by grind
-/
theorem mk_preimage_sigma_eq_empty (hi : i ∉ s) : Sigma.mk i ⁻¹' s.sigma t = ∅ := by grind

/--
theorem `mk_preimage_sigma_eq_if` / 定理 `mk_preimage_sigma_eq_if`

English:
theorem mk_preimage_sigma_eq_if
  given: [DecidablePred (· in s)]
  proof: by grind

中文:
定理 mk_preimage_sigma_eq_if
  条件: [DecidablePred (· in s)]
  证明: by grind
-/
theorem mk_preimage_sigma_eq_if [DecidablePred (· in s)] :
    Sigma.mk i ⁻¹' s.sigma t = if i in s then t i else ∅ := by grind

/--
theorem `mk_preimage_sigma_fn_eq_if` / 定理 `mk_preimage_sigma_fn_eq_if`

English:
theorem mk_preimage_sigma_fn_eq_if
  given: {β : Type*} [DecidablePred (· in s)] (g : β -> α i)
  proof: by grind

中文:
定理 mk_preimage_sigma_fn_eq_if
  条件: {β : 类型} [DecidablePred (· in s)] (g : β -> α i)
  证明: by grind
-/
theorem mk_preimage_sigma_fn_eq_if {β : Type*} [DecidablePred (· in s)] (g : β -> α i) :
    (fun b => Sigma.mk i (g b)) ⁻¹' s.sigma t = if i in s then g ⁻¹' t i else ∅ := by grind

/--
theorem `sigma_univ_range_eq` / 定理 `sigma_univ_range_eq`

English:
theorem sigma_univ_range_eq
  given: {f : forall i, α i -> β i}
  proof: ext by simp [range, Sigma.forall]

中文:
定理 sigma_univ_range_eq
  条件: {f : 对任意 i, α i -> β i}
  证明: ext by simp [range, Sigma.forall]

Depends on / 依赖: Sigma.forall
-/
theorem sigma_univ_range_eq {f : forall i, α i -> β i} :
    (univ : Set ι).sigma (fun i => range (f i)) = range fun x : Σ i, α i => ⟨x.1, f _ x.2⟩ :=
ext by simp [range, Sigma.forall]

/--
theorem `Nonempty.sigma` / 定理 `Nonempty.sigma`

English:
theorem Nonempty.sigma
  proof: fun ⟨i, hi⟩ h =>
  let ⟨a, ha⟩ := h i
  ⟨⟨i, a⟩, hi, ha⟩

中文:
定理 Nonempty.sigma
  证明: fun ⟨i, hi⟩ h =>
  let ⟨a, ha⟩ := h i
  ⟨⟨i, a⟩, hi, ha⟩
-/
protected theorem Nonempty.sigma :
    s.Nonempty -> (forall i, (t i).Nonempty) -> (s.sigma t).Nonempty := fun ⟨i, hi⟩ h =>
  let ⟨a, ha⟩ := h i
  ⟨⟨i, a⟩, hi, ha⟩

/--
theorem `Nonempty.sigma_fst` / 定理 `Nonempty.sigma_fst`

English:
theorem Nonempty.sigma_fst
  statement: (s.sigma t).Nonempty -> s.Nonempty
  proof: fun ⟨x, hx⟩ => ⟨x.1, hx.1⟩

中文:
定理 Nonempty.sigma_fst
  结论: (s.sigma t).Nonempty -> s.Nonempty
  证明: fun ⟨x, hx⟩ => ⟨x.1, hx.1⟩
-/
theorem Nonempty.sigma_fst : (s.sigma t).Nonempty -> s.Nonempty := fun ⟨x, hx⟩ => ⟨x.1, hx.1⟩

/--
theorem `Nonempty.sigma_snd` / 定理 `Nonempty.sigma_snd`

English:
theorem Nonempty.sigma_snd
  statement: (s.sigma t).Nonempty -> exists i in s, (t i).Nonempty
  proof: fun ⟨x, hx⟩ => ⟨x.1, hx.1, x.2, hx.2⟩

中文:
定理 Nonempty.sigma_snd
  结论: (s.sigma t).Nonempty -> 存在 i in s, (t i).Nonempty
  证明: fun ⟨x, hx⟩ => ⟨x.1, hx.1, x.2, hx.2⟩
-/
theorem Nonempty.sigma_snd : (s.sigma t).Nonempty -> exists i in s, (t i).Nonempty :=
  fun ⟨x, hx⟩ => ⟨x.1, hx.1, x.2, hx.2⟩

/--
theorem `sigma_nonempty_iff` / 定理 `sigma_nonempty_iff`

English:
theorem sigma_nonempty_iff
  statement: (s.sigma t).Nonempty ↔ exists i in s, (t i).Nonempty
  proof: ⟨Nonempty.sigma_snd, fun ⟨i, hi, a, ha⟩ => ⟨⟨i, a⟩, hi, ha⟩⟩

中文:
定理 sigma_nonempty_iff
  结论: (s.sigma t).Nonempty ↔ 存在 i in s, (t i).Nonempty
  证明: ⟨Nonempty.sigma_snd, fun ⟨i, hi, a, ha⟩ => ⟨⟨i, a⟩, hi, ha⟩⟩

Depends on / 依赖: Nonempty, Nonempty.sigma_snd, sigma_snd
-/
theorem sigma_nonempty_iff : (s.sigma t).Nonempty ↔ exists i in s, (t i).Nonempty :=
  ⟨Nonempty.sigma_snd, fun ⟨i, hi, a, ha⟩ => ⟨⟨i, a⟩, hi, ha⟩⟩

/--
theorem `sigma_eq_empty_iff` / 定理 `sigma_eq_empty_iff`

English:
theorem sigma_eq_empty_iff
  statement: s.sigma t = ∅ ↔ forall i in s, t i = ∅
  proof: not_nonempty_iff_eq_empty.symm.trans
sigma_nonempty_iff.not.trans by
      simp only [not_nonempty_iff_eq_empty, not_and, not_exists]

中文:
定理 sigma_eq_empty_iff
  结论: s.sigma t = ∅ ↔ 对任意 i in s, t i = ∅
  证明: not_nonempty_iff_eq_empty.symm.trans
sigma_nonempty_iff.not.trans by
      simp only [not_nonempty_iff_eq_empty, not_and, not_exists]

Depends on / 依赖: not_and, not_exists, not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty.symm.trans, sigma_nonempty_iff, sigma_nonempty_iff.not.trans
-/
theorem sigma_eq_empty_iff : s.sigma t = ∅ ↔ forall i in s, t i = ∅ :=
not_nonempty_iff_eq_empty.symm.trans
sigma_nonempty_iff.not.trans by
      simp only [not_nonempty_iff_eq_empty, not_and, not_exists]

/--
theorem `image_sigmaMk_subset_sigma_left` / 定理 `image_sigmaMk_subset_sigma_left`

English:
theorem image_sigmaMk_subset_sigma_left
  given: {a : forall i, α i} (ha : forall i, a i in t i)
  proof: image_subset_iff.2 fun _ hi => ⟨hi, ha _⟩

中文:
定理 image_sigmaMk_subset_sigma_left
  条件: {a : 对任意 i, α i} (ha : 对任意 i, a i in t i)
  证明: image_subset_iff.2 fun _ hi => ⟨hi, ha _⟩

Depends on / 依赖: image_subset_iff
-/
theorem image_sigmaMk_subset_sigma_left {a : forall i, α i} (ha : forall i, a i in t i) :
    (fun i => Sigma.mk i (a i)) '' s subseteq s.sigma t :=
  image_subset_iff.2 fun _ hi => ⟨hi, ha _⟩

/--
theorem `image_sigmaMk_subset_sigma_right` / 定理 `image_sigmaMk_subset_sigma_right`

English:
theorem image_sigmaMk_subset_sigma_right
  given: (hi : i in s)
  statement: Sigma.mk i '' t i subseteq s.sigma t
  proof: image_subset_iff.2 fun _ => And.intro hi

中文:
定理 image_sigmaMk_subset_sigma_right
  条件: (hi : i in s)
  结论: Sigma.mk i '' t i subseteq s.sigma t
  证明: image_subset_iff.2 fun _ => And.intro hi

Depends on / 依赖: And.intro, image_subset_iff
-/
theorem image_sigmaMk_subset_sigma_right (hi : i in s) : Sigma.mk i '' t i subseteq s.sigma t :=
  image_subset_iff.2 fun _ => And.intro hi

/--
theorem `sigma_subset_preimage_fst` / 定理 `sigma_subset_preimage_fst`

English:
theorem sigma_subset_preimage_fst
  given: (s : Set ι) (t : forall i, Set (α i))
  statement: s.sigma t subseteq Sigma.fst ⁻¹' s
  proof: fun _ => And.left

中文:
定理 sigma_subset_preimage_fst
  条件: (s : Set ι) (t : 对任意 i, Set (α i))
  结论: s.sigma t subseteq Sigma.fst ⁻¹' s
  证明: fun _ => And.left

Depends on / 依赖: And.left
-/
theorem sigma_subset_preimage_fst (s : Set ι) (t : forall i, Set (α i)) : s.sigma t subseteq Sigma.fst ⁻¹' s :=
  fun _ => And.left

/--
theorem `fst_image_sigma_subset` / 定理 `fst_image_sigma_subset`

English:
theorem fst_image_sigma_subset
  given: (s : Set ι) (t : forall i, Set (α i))
  statement: Sigma.fst '' s.sigma t subseteq s
  proof: image_subset_iff.2 fun _ => And.left

中文:
定理 fst_image_sigma_subset
  条件: (s : Set ι) (t : 对任意 i, Set (α i))
  结论: Sigma.fst '' s.sigma t subseteq s
  证明: image_subset_iff.2 fun _ => And.left

Depends on / 依赖: And.left, image_subset_iff
-/
theorem fst_image_sigma_subset (s : Set ι) (t : forall i, Set (α i)) : Sigma.fst '' s.sigma t subseteq s :=
  image_subset_iff.2 fun _ => And.left

/--
lemma `image_sigma_eq_iUnion` / 引理 `image_sigma_eq_iUnion`

English:
lemma image_sigma_eq_iUnion
  given: {γ : Type*} (f : (Σ i, α i) -> γ)
  proof: by
  aesop

中文:
引理 image_sigma_eq_iUnion
  条件: {γ : 类型} (f : (Σ i, α i) -> γ)
  证明: by
  aesop
-/
lemma image_sigma_eq_iUnion {γ : Type*} (f : (Σ i, α i) -> γ) :
    f '' (s.sigma t) = ⋃ i in s, (f ∘ Sigma.mk i) '' t i := by
  aesop

/--
theorem `fst_image_sigma` / 定理 `fst_image_sigma`

English:
theorem fst_image_sigma
  given: (s : Set ι) (ht : forall i, (t i).Nonempty)
  statement: Sigma.fst '' s.sigma t = s
  proof: (fst_image_sigma_subset _ _).antisymm fun i hi =>
    let ⟨a, ha⟩ := ht i
    ⟨⟨i, a⟩, ⟨hi, ha⟩, rfl⟩

中文:
定理 fst_image_sigma
  条件: (s : Set ι) (ht : 对任意 i, (t i).Nonempty)
  结论: Sigma.fst '' s.sigma t = s
  证明: (fst_image_sigma_subset _ _).antisymm fun i hi =>
    let ⟨a, ha⟩ := ht i
    ⟨⟨i, a⟩, ⟨hi, ha⟩, rfl⟩

Depends on / 依赖: antisymm, fst_image_sigma_subset
-/
theorem fst_image_sigma (s : Set ι) (ht : forall i, (t i).Nonempty) : Sigma.fst '' s.sigma t = s :=
  (fst_image_sigma_subset _ _).antisymm fun i hi =>
    let ⟨a, ha⟩ := ht i
    ⟨⟨i, a⟩, ⟨hi, ha⟩, rfl⟩

/--
theorem `sigma_sdiff_sigma` / 定理 `sigma_sdiff_sigma`

English:
theorem sigma_sdiff_sigma
  statement: s₁.sigma t₁ \ s₂.sigma t₂ = s₁.sigma (t₁ \ t₂) union (s₁ \ s₂).sigma t₁
  proof: ext fun x => by
    by_cases h₁ : x.1 in s₁ <;> by_cases h₂ : x.2 in t₁ x.1 <;> simp [*, ← imp_iff_or_not]

@[deprecated (since := "2026-06-03")] alias sigma_diff_sigma := sigma_sdiff_sigma

中文:
定理 sigma_sdiff_sigma
  结论: s₁.sigma t₁ \ s₂.sigma t₂ = s₁.sigma (t₁ \ t₂) union (s₁ \ s₂).sigma t₁
  证明: ext fun x => by
    by_cases h₁ : x.1 in s₁ <;> by_cases h₂ : x.2 in t₁ x.1 <;> simp [*, ← imp_iff_or_not]

@[deprecated (since := "2026-06-03")] alias sigma_diff_sigma := sigma_sdiff_sigma

Depends on / 依赖: imp_iff_or_not
-/
theorem sigma_sdiff_sigma : s₁.sigma t₁ \ s₂.sigma t₂ = s₁.sigma (t₁ \ t₂) union (s₁ \ s₂).sigma t₁ :=
  ext fun x => by
    by_cases h₁ : x.1 in s₁ <;> by_cases h₂ : x.2 in t₁ x.1 <;> simp [*, ← imp_iff_or_not]

@[deprecated (since := "2026-06-03")] alias sigma_diff_sigma := sigma_sdiff_sigma

/--
lemma `sigma_eq_biUnion` / 引理 `sigma_eq_biUnion`

English:
lemma sigma_eq_biUnion
  statement: s.sigma t = ⋃ i in s, Sigma.mk i '' t i
  proof: by
  aesop

中文:
引理 sigma_eq_biUnion
  结论: s.sigma t = ⋃ i in s, Sigma.mk i '' t i
  证明: by
  aesop
-/
lemma sigma_eq_biUnion : s.sigma t = ⋃ i in s, Sigma.mk i '' t i := by
  aesop

/--
lemma `uncurry_preimage_sigma_pi` / 引理 `uncurry_preimage_sigma_pi`

English:
lemma uncurry_preimage_sigma_pi
  statement: {β : (i : ι) -> α i -> Type*} (s : Set ι) (t : (i : ι) -> Set (α i))
  proof: by
  ext x
  simp only [mem_preimage, mem_pi, mem_sigma_iff, and_imp]
  exact ⟨fun h i hi j hj => h ⟨i, j⟩ hi hj, fun h p hp1 hp2 => h p.1 hp1 p.2 hp2⟩

中文:
引理 uncurry_preimage_sigma_pi
  结论: {β : (i : ι) -> α i -> 类型} (s : Set ι) (t : (i : ι) -> Set (α i))
  证明: by
  ext x
  simp only [mem_preimage, mem_pi, mem_sigma_iff, and_imp]
  exact ⟨fun h i hi j hj => h ⟨i, j⟩ hi hj, fun h p hp1 hp2 => h p.1 hp1 p.2 hp2⟩

Depends on / 依赖: and_imp, mem_pi, mem_preimage, mem_sigma_iff
-/
lemma uncurry_preimage_sigma_pi {β : (i : ι) -> α i -> Type*} (s : Set ι) (t : (i : ι) -> Set (α i))
    (u : (p : (i : ι) × α i) -> Set (β p.1 p.2)) :
    Sigma.uncurry ⁻¹' (s.sigma t).pi u = s.pi (fun i => (t i).pi fun j => u ⟨i, j⟩) := by
  ext x
  simp only [mem_preimage, mem_pi, mem_sigma_iff, and_imp]
  exact ⟨fun h i hi j hj => h ⟨i, j⟩ hi hj, fun h p hp1 hp2 => h p.1 hp1 p.2 hp2⟩

end Set
