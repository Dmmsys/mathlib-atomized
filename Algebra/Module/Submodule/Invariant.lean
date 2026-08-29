/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Sublattice

/-!
# The lattice of invariant submodules

In this file we defined the type `Module.End.invtSubmodule`, associated to a linear endomorphism of
a module. Its utility stems primarily from those occasions on which we wish to take advantage of the
lattice structure of invariant submodules.

See also `Mathlib/Algebra/Polynomial/Module/AEval.lean`.

-/

@[expose] public section

open Submodule (span)

namespace Module.End

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

/--
Definition of `invtSubmodule` / `invtSubmodule` 的定义

English:
definition invtSubmodule
  signature: : Sublattice (Submodule R M) where
  body: {p : Submodule R M | p <= p.comap f}
  supClosed' p hp q hq := sup_le_iff.mpr
⟨le_trans hp Submodule.comap_mono le_sup_left,
le_trans hq Submodule.comap_mono le_sup_right⟩
  infClosed' p hp q hq := by
    simp only [Set.mem_ofPred_eq, Submodule.comap_inf, le_inf_iff]
    exact ⟨inf_le_of_left_le hp, inf_le_of_right_le hq⟩

中文:
定义 invtSubmodule
  签名: : 子格 (子模 R M) where
  定义体: {p : Submodule R M | p <= p.comap f}
  supClosed' p hp q hq := sup_le_iff.mpr
⟨le_trans hp Submodule.comap_mono le_sup_left,
le_trans hq Submodule.comap_mono le_sup_right⟩
  infClosed' p hp q hq := by
    simp only [Set.mem_ofPred_eq, Submodule.comap_inf, le_inf_iff]
    exact ⟨inf_le_of_left_le hp, inf_le_of_right_le hq⟩

Depends on / 依赖: Submodule, p.comap
-/
def invtSubmodule : Sublattice (Submodule R M) where
  carrier := {p : Submodule R M | p <= p.comap f}
  supClosed' p hp q hq := sup_le_iff.mpr
⟨le_trans hp Submodule.comap_mono le_sup_left,
le_trans hq Submodule.comap_mono le_sup_right⟩
  infClosed' p hp q hq := by
    simp only [Set.mem_ofPred_eq, Submodule.comap_inf, le_inf_iff]
    exact ⟨inf_le_of_left_le hp, inf_le_of_right_le hq⟩

/--
lemma `mem_invtSubmodule` / 引理 `mem_invtSubmodule`

English:
lemma mem_invtSubmodule
  given: {p : Submodule R M}
  proof: Iff.rfl

中文:
引理 mem_invtSubmodule
  条件: {p : 子模 R M}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_invtSubmodule {p : Submodule R M} :
    p in f.invtSubmodule ↔ p <= p.comap f :=
  Iff.rfl

/--
theorem `mem_invtSubmodule_iff_map_le` / 定理 `mem_invtSubmodule_iff_map_le`

English:
theorem mem_invtSubmodule_iff_map_le
  given: {p : Submodule R M}
  proof: Submodule.map_le_iff_le_comap.symm

中文:
定理 mem_invtSubmodule_iff_map_le
  条件: {p : 子模 R M}
  证明: Submodule.map_le_iff_le_comap.symm

Depends on / 依赖: Submodule, Submodule.map_le_iff_le_comap.symm, map_le_iff_le_comap
-/
theorem mem_invtSubmodule_iff_map_le {p : Submodule R M} :
    p in f.invtSubmodule ↔ p.map f <= p := Submodule.map_le_iff_le_comap.symm

/--
theorem `mem_invtSubmodule_iff_mapsTo` / 定理 `mem_invtSubmodule_iff_mapsTo`

English:
theorem mem_invtSubmodule_iff_mapsTo
  given: {p : Submodule R M}
  proof: Iff.rfl

alias ⟨_, _root_.Set.Mapsto.mem_invtSubmodule⟩ := mem_invtSubmodule_iff_mapsTo

中文:
定理 mem_invtSubmodule_iff_mapsTo
  条件: {p : 子模 R M}
  证明: Iff.rfl

alias ⟨_, _root_.Set.Mapsto.mem_invtSubmodule⟩ := mem_invtSubmodule_iff_mapsTo

Depends on / 依赖: Iff.rfl
-/
theorem mem_invtSubmodule_iff_mapsTo {p : Submodule R M} :
    p in f.invtSubmodule ↔ Set.MapsTo f p p := Iff.rfl

alias ⟨_, _root_.Set.Mapsto.mem_invtSubmodule⟩ := mem_invtSubmodule_iff_mapsTo

/--
theorem `mem_invtSubmodule_iff_forall_mem_of_mem` / 定理 `mem_invtSubmodule_iff_forall_mem_of_mem`

English:
theorem mem_invtSubmodule_iff_forall_mem_of_mem
  given: {p : Submodule R M}
  proof: Iff.rfl

中文:
定理 mem_invtSubmodule_iff_对任意_mem_of_mem
  条件: {p : 子模 R M}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_invtSubmodule_iff_forall_mem_of_mem {p : Submodule R M} :
    p in f.invtSubmodule ↔ forall x in p, f x in p :=
  Iff.rfl

/--
lemma `mem_invtSubmodule_symm_iff_le_map` / 引理 `mem_invtSubmodule_symm_iff_le_map`

English:
lemma mem_invtSubmodule_symm_iff_le_map
  given: {f : M ≃ₗ[R] M} {p : Submodule R M}
  proof: (mem_invtSubmodule_iff_map_le _).trans (f.toEquiv.symm.subset_symm_image _ _).symm

中文:
引理 mem_invtSubmodule_symm_iff_le_map
  条件: {f : M ≃ₗ[R] M} {p : 子模 R M}
  证明: (mem_invtSubmodule_iff_map_le _).trans (f.toEquiv.symm.subset_symm_image _ _).symm

Depends on / 依赖: f.toEquiv.symm.subset_symm_image, mem_invtSubmodule_iff_map_le, subset_symm_image, toEquiv
-/
lemma mem_invtSubmodule_symm_iff_le_map {f : M ≃ₗ[R] M} {p : Submodule R M} :
    p in invtSubmodule f.symm ↔ p <= p.map (f : M ->ₗ[R] M) :=
  (mem_invtSubmodule_iff_map_le _).trans (f.toEquiv.symm.subset_symm_image _ _).symm

/--
lemma `invtSubmodule_inf_invtSubmodule_le_invtSubmodule_add` / 引理 `invtSubmodule_inf_invtSubmodule_le_invtSubmodule_add`

English:
lemma invtSubmodule_inf_invtSubmodule_le_invtSubmodule_add
  proof: fun p ⟨hfp, hgp⟩ _ hx => p.add_mem (hfp hx) (hgp hx)

中文:
引理 invtSubmodule_inf_invtSubmodule_le_invtSubmodule_add
  证明: fun p ⟨hfp, hgp⟩ _ hx => p.add_mem (hfp hx) (hgp hx)

Depends on / 依赖: add_mem, p.add_mem
-/
lemma invtSubmodule_inf_invtSubmodule_le_invtSubmodule_add :
    f.invtSubmodule ⊓ g.invtSubmodule <= (f + g).invtSubmodule :=
  fun p ⟨hfp, hgp⟩ _ hx => p.add_mem (hfp hx) (hgp hx)

section CommRing

variable {R S : Type*} [Semiring R] [Semiring S] [Module R M] [Module S M]
  [DistribSMul S R] [SMulCommClass R S M] [IsScalarTower S R M] (f : End R M)

/--
lemma `invtSubmodule_le_invtSubmodule_smul` / 引理 `invtSubmodule_le_invtSubmodule_smul`

English:
lemma invtSubmodule_le_invtSubmodule_smul
  given: (c : S)
  statement: f.invtSubmodule <= (c • f).invtSubmodule
  proof: fun p hfp _ hx => p.smul_of_tower_mem c (hfp hx)

@[simp]

中文:
引理 invtSubmodule_le_invtSubmodule_smul
  条件: (c : S)
  结论: f.invtSubmodule <= (c • f).invtSubmodule
  证明: fun p hfp _ hx => p.smul_of_tower_mem c (hfp hx)

@[simp]

Depends on / 依赖: p.smul_of_tower_mem, smul_of_tower_mem
-/
lemma invtSubmodule_le_invtSubmodule_smul (c : S) : f.invtSubmodule <= (c • f).invtSubmodule :=
  fun p hfp _ hx => p.smul_of_tower_mem c (hfp hx)

@[simp]
/--
lemma `invtSubmodule_smul` / 引理 `invtSubmodule_smul`

English:
lemma invtSubmodule_smul
  given: (c : Sˣ)
  statement: (c • f).invtSubmodule = f.invtSubmodule
  proof: by
  apply le_antisymm ?_ (invtSubmodule_le_invtSubmodule_smul f c.1)
  grw [invtSubmodule_le_invtSubmodule_smul (c.1 • f) c⁻¹.1]
  simp [smul_smul]

中文:
引理 invtSubmodule_smul
  条件: (c : Sˣ)
  结论: (c • f).invtSubmodule = f.invtSubmodule
  证明: by
  apply le_antisymm ?_ (invtSubmodule_le_invtSubmodule_smul f c.1)
  grw [invtSubmodule_le_invtSubmodule_smul (c.1 • f) c⁻¹.1]
  simp [smul_smul]

Depends on / 依赖: invtSubmodule_le_invtSubmodule_smul, le_antisymm, smul_smul
-/
lemma invtSubmodule_smul (c : Sˣ) : (c • f).invtSubmodule = f.invtSubmodule := by
  apply le_antisymm ?_ (invtSubmodule_le_invtSubmodule_smul f c.1)
  grw [invtSubmodule_le_invtSubmodule_smul (c.1 • f) c⁻¹.1]
  simp [smul_smul]

end CommRing

namespace invtSubmodule

variable {f}

/--
lemma `inf_mem` / 引理 `inf_mem`

English:
lemma inf_mem
  given: {p q : Submodule R M} (hp : p in f.invtSubmodule) (hq : q in f.invtSubmodule)
  proof: Sublattice.inf_mem hp hq

中文:
引理 inf_mem
  条件: {p q : 子模 R M} (hp : p in f.invtSubmodule) (hq : q in f.invtSubmodule)
  证明: Sublattice.inf_mem hp hq

Depends on / 依赖: Sublattice, Sublattice.inf_mem, inf_mem
-/
lemma inf_mem {p q : Submodule R M} (hp : p in f.invtSubmodule) (hq : q in f.invtSubmodule) :
    p ⊓ q in f.invtSubmodule :=
  Sublattice.inf_mem hp hq

/--
lemma `sup_mem` / 引理 `sup_mem`

English:
lemma sup_mem
  given: {p q : Submodule R M} (hp : p in f.invtSubmodule) (hq : q in f.invtSubmodule)
  proof: Sublattice.sup_mem hp hq

中文:
引理 sup_mem
  条件: {p q : 子模 R M} (hp : p in f.invtSubmodule) (hq : q in f.invtSubmodule)
  证明: Sublattice.sup_mem hp hq

Depends on / 依赖: Sublattice, Sublattice.sup_mem, sup_mem
-/
lemma sup_mem {p q : Submodule R M} (hp : p in f.invtSubmodule) (hq : q in f.invtSubmodule) :
    p ⊔ q in f.invtSubmodule :=
  Sublattice.sup_mem hp hq

variable (f)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `top_mem` / 引理 `top_mem`

English:
lemma top_mem
  statement: ⊤ in f.invtSubmodule
  proof: by simp [invtSubmodule]

中文:
引理 top_mem
  结论: ⊤ in f.invtSubmodule
  证明: by simp [invtSubmodule]
-/
protected lemma top_mem : ⊤ in f.invtSubmodule := by simp [invtSubmodule]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `bot_mem` / 引理 `bot_mem`

English:
lemma bot_mem
  statement: ⊥ in f.invtSubmodule
  proof: by simp [invtSubmodule]

中文:
引理 bot_mem
  结论: ⊥ in f.invtSubmodule
  证明: by simp [invtSubmodule]
-/
protected lemma bot_mem : ⊥ in f.invtSubmodule := by simp [invtSubmodule]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedOrder (f.invtSubmodule)
  body: ⟨⊤, invtSubmodule.top_mem f⟩
  bot := ⟨⊥, invtSubmodule.bot_mem f⟩
  le_top := fun ⟨p, hp⟩ => by simp
  bot_le := fun ⟨p, hp⟩ => by simp

@[simp]

中文:
实例 :
  签名: 有界序 (f.invtSubmodule)
  定义体: ⟨⊤, invtSubmodule.top_mem f⟩
  bot := ⟨⊥, invtSubmodule.bot_mem f⟩
  le_top := fun ⟨p, hp⟩ => by simp
  bot_le := fun ⟨p, hp⟩ => by simp

@[simp]

Depends on / 依赖: invtSubmodule, invtSubmodule.top_mem, top_mem
-/
instance : BoundedOrder (f.invtSubmodule) where
  top := ⟨⊤, invtSubmodule.top_mem f⟩
  bot := ⟨⊥, invtSubmodule.bot_mem f⟩
  le_top := fun ⟨p, hp⟩ => by simp
  bot_le := fun ⟨p, hp⟩ => by simp

@[simp]
/--
lemma `zero` / 引理 `zero`

English:
lemma zero
  proof: eq_top_iff.mpr fun x => by simp [invtSubmodule]

@[simp]

中文:
引理 zero
  证明: eq_top_iff.mpr fun x => by simp [invtSubmodule]

@[simp]
-/
protected lemma zero :
    (0 : End R M).invtSubmodule = ⊤ :=
  eq_top_iff.mpr fun x => by simp [invtSubmodule]

@[simp]
/--
lemma `id` / 引理 `id`

English:
lemma id
  proof: eq_top_iff.mpr fun x => by simp [invtSubmodule]

@[simp]

中文:
引理 id
  证明: eq_top_iff.mpr fun x => by simp [invtSubmodule]

@[simp]
-/
protected lemma id :
    invtSubmodule (LinearMap.id : End R M) = ⊤ :=
  eq_top_iff.mpr fun x => by simp [invtSubmodule]

@[simp]
/--
lemma `one` / 引理 `one`

English:
lemma one
  proof: invtSubmodule.id

中文:
引理 one
  证明: invtSubmodule.id
-/
protected lemma one :
    invtSubmodule (1 : End R M) = ⊤ :=
  invtSubmodule.id

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mk_eq_bot_iff` / 引理 `mk_eq_bot_iff`

English:
lemma mk_eq_bot_iff
  given: {p : Submodule R M} (hp : p in f.invtSubmodule)
  proof: Subtype.mk_eq_bot_iff (by simp [invtSubmodule]) _

中文:
引理 mk_eq_bot_iff
  条件: {p : 子模 R M} (hp : p in f.invtSubmodule)
  证明: Subtype.mk_eq_bot_iff (by simp [invtSubmodule]) _
-/
protected lemma mk_eq_bot_iff {p : Submodule R M} (hp : p in f.invtSubmodule) :
    (⟨p, hp⟩ : f.invtSubmodule) = ⊥ ↔ p = ⊥ :=
  Subtype.mk_eq_bot_iff (by simp [invtSubmodule]) _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mk_eq_top_iff` / 引理 `mk_eq_top_iff`

English:
lemma mk_eq_top_iff
  given: {p : Submodule R M} (hp : p in f.invtSubmodule)
  proof: Subtype.mk_eq_top_iff (by simp [invtSubmodule]) _

@[simp]

中文:
引理 mk_eq_top_iff
  条件: {p : 子模 R M} (hp : p in f.invtSubmodule)
  证明: Subtype.mk_eq_top_iff (by simp [invtSubmodule]) _

@[simp]
-/
protected lemma mk_eq_top_iff {p : Submodule R M} (hp : p in f.invtSubmodule) :
    (⟨p, hp⟩ : f.invtSubmodule) = ⊤ ↔ p = ⊤ :=
  Subtype.mk_eq_top_iff (by simp [invtSubmodule]) _

@[simp]
/--
lemma `disjoint_mk_iff` / 引理 `disjoint_mk_iff`

English:
lemma disjoint_mk_iff
  statement: {p q : Submodule R M}
  proof: by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [Sublattice.mk_inf_mk]; rw [Subtype.mk_eq_bot_iff (⊥ : f.invtSubmodule).property]

中文:
引理 disjoint_mk_iff
  结论: {p q : 子模 R M}
  证明: by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [Sublattice.mk_inf_mk]; rw [Subtype.mk_eq_bot_iff (⊥ : f.invtSubmodule).property]
-/
protected lemma disjoint_mk_iff {p q : Submodule R M}
    (hp : p in f.invtSubmodule) (hq : q in f.invtSubmodule) :
    Disjoint (α := f.invtSubmodule) ⟨p, hp⟩ ⟨q, hq⟩ ↔ Disjoint p q := by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [Sublattice.mk_inf_mk]; rw [Subtype.mk_eq_bot_iff (⊥ : f.invtSubmodule).property]

/--
lemma `disjoint_iff` / 引理 `disjoint_iff`

English:
lemma disjoint_iff
  given: {p q : f.invtSubmodule}
  proof: by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp

@[simp]

中文:
引理 disjoint_iff
  条件: {p q : f.invtSubmodule}
  证明: by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp

@[simp]
-/
protected lemma disjoint_iff {p q : f.invtSubmodule} :
    Disjoint p q ↔ Disjoint (p : Submodule R M) (q : Submodule R M) := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp

@[simp]
/--
lemma `codisjoint_mk_iff` / 引理 `codisjoint_mk_iff`

English:
lemma codisjoint_mk_iff
  statement: {p q : Submodule R M}
  proof: by
  rw [codisjoint_iff]; rw [codisjoint_iff]; rw [Sublattice.mk_sup_mk]; rw [Subtype.mk_eq_top_iff (⊤ : f.invtSubmodule).property]

中文:
引理 codisjoint_mk_iff
  结论: {p q : 子模 R M}
  证明: by
  rw [codisjoint_iff]; rw [codisjoint_iff]; rw [Sublattice.mk_sup_mk]; rw [Subtype.mk_eq_top_iff (⊤ : f.invtSubmodule).property]
-/
protected lemma codisjoint_mk_iff {p q : Submodule R M}
    (hp : p in f.invtSubmodule) (hq : q in f.invtSubmodule) :
    Codisjoint (α := f.invtSubmodule) ⟨p, hp⟩ ⟨q, hq⟩ ↔ Codisjoint p q := by
  rw [codisjoint_iff]; rw [codisjoint_iff]; rw [Sublattice.mk_sup_mk]; rw [Subtype.mk_eq_top_iff (⊤ : f.invtSubmodule).property]

/--
lemma `codisjoint_iff` / 引理 `codisjoint_iff`

English:
lemma codisjoint_iff
  given: {p q : f.invtSubmodule}
  proof: by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp

@[simp]

中文:
引理 codisjoint_iff
  条件: {p q : f.invtSubmodule}
  证明: by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp

@[simp]
-/
protected lemma codisjoint_iff {p q : f.invtSubmodule} :
    Codisjoint p q ↔ Codisjoint (p : Submodule R M) (q : Submodule R M) := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp

@[simp]
/--
lemma `isCompl_mk_iff` / 引理 `isCompl_mk_iff`

English:
lemma isCompl_mk_iff
  statement: {p q : Submodule R M}
  proof: by
  simp [isCompl_iff]

中文:
引理 isCompl_mk_iff
  结论: {p q : 子模 R M}
  证明: by
  simp [isCompl_iff]
-/
protected lemma isCompl_mk_iff {p q : Submodule R M}
    (hp : p in f.invtSubmodule) (hq : q in f.invtSubmodule) :
    IsCompl (α := f.invtSubmodule) ⟨p, hp⟩ ⟨q, hq⟩ ↔ IsCompl p q := by
  simp [isCompl_iff]

/--
lemma `isCompl_iff` / 引理 `isCompl_iff`

English:
lemma isCompl_iff
  given: {p q : f.invtSubmodule}
  proof: by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp

中文:
引理 isCompl_iff
  条件: {p q : f.invtSubmodule}
  证明: by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp
-/
protected lemma isCompl_iff {p q : f.invtSubmodule} :
    IsCompl p q ↔ IsCompl (p : Submodule R M) (q : Submodule R M) := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_subtype_mem_of_mem_invtSubmodule` / 引理 `map_subtype_mem_of_mem_invtSubmodule`

English:
lemma map_subtype_mem_of_mem_invtSubmodule
  statement: {p : Submodule R M} (hp : p in f.invtSubmodule)
  proof: by
  rintro - ⟨⟨x, hx⟩, hx', rfl⟩
  specialize hq hx'
  rw [Submodule.mem_comap]; rw [LinearMap.restrict_apply] at hq
  simpa [hq] using hp hx

中文:
引理 map_subtype_mem_of_mem_invtSubmodule
  结论: {p : 子模 R M} (hp : p in f.invtSubmodule)
  证明: by
  rintro - ⟨⟨x, hx⟩, hx', rfl⟩
  specialize hq hx'
  rw [Submodule.mem_comap]; rw [LinearMap.restrict_apply] at hq
  simpa [hq] using hp hx

Depends on / 依赖: LinearMap, LinearMap.restrict_apply, Submodule, Submodule.mem_comap, mem_comap, restrict_apply, specialize
-/
lemma map_subtype_mem_of_mem_invtSubmodule {p : Submodule R M} (hp : p in f.invtSubmodule)
    {q : Submodule R p} (hq : q in invtSubmodule (LinearMap.restrict f hp)) :
    Submodule.map p.subtype q in f.invtSubmodule := by
  rintro - ⟨⟨x, hx⟩, hx', rfl⟩
  specialize hq hx'
  rw [Submodule.mem_comap]; rw [LinearMap.restrict_apply] at hq
  simpa [hq] using hp hx

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  statement: {p : Submodule R M} {g : End R M}
  proof: fun _ hx => hf (hg hx)

中文:
引理 comp
  结论: {p : 子模 R M} {g : End R M}
  证明: fun _ hx => hf (hg hx)
-/
protected lemma comp {p : Submodule R M} {g : End R M}
    (hf : p in f.invtSubmodule) (hg : p in g.invtSubmodule) :
    p in invtSubmodule (f ∘ₗ g) :=
  fun _ hx => hf (hg hx)

/--
lemma `_root_.LinearEquiv.map_mem_invtSubmodule_conj_iff` / 引理 `_root_.LinearEquiv.map_mem_invtSubmodule_conj_iff`

English:
lemma _root_.LinearEquiv.map_mem_invtSubmodule_conj_iff
  statement: {R M N : Type*} [CommSemiring R]
  proof: by
  have : e.symm.toLinearMap ∘ₗ ((e ∘ₗ f) ∘ₗ e.symm.toLinearMap) ∘ₗ e = f := by ext; simp
  rw [LinearEquiv.conj_apply]; rw [mem_invtSubmodule]; rw [mem_invtSubmodule]; rw [Submodule.map_le_iff_le_comap]; rw [Submodule.map_equiv_eq_comap_symm]; rw [← Submodule.comap_comp]; rw [← Submodule.comap_comp]; rw [this]

中文:
引理 _root_.线性等价.map_mem_invtSubmodule_conj_iff
  结论: {R M N : 类型} [交换半环 R]
  证明: by
  have : e.symm.toLinearMap ∘ₗ ((e ∘ₗ f) ∘ₗ e.symm.toLinearMap) ∘ₗ e = f := by ext; simp
  rw [LinearEquiv.conj_apply]; rw [mem_invtSubmodule]; rw [mem_invtSubmodule]; rw [Submodule.map_le_iff_le_comap]; rw [Submodule.map_equiv_eq_comap_symm]; rw [← Submodule.comap_comp]; rw [← Submodule.comap_comp]; rw [this]
-/
@[simp] lemma _root_.LinearEquiv.map_mem_invtSubmodule_conj_iff {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] {f : End R M}
    {e : M ≃ₗ[R] N} {p : Submodule R M} :
    p.map (e : M ->ₗ[R] N) in (e.conj f).invtSubmodule ↔ p in f.invtSubmodule := by
  have : e.symm.toLinearMap ∘ₗ ((e ∘ₗ f) ∘ₗ e.symm.toLinearMap) ∘ₗ e = f := by ext; simp
  rw [LinearEquiv.conj_apply]; rw [mem_invtSubmodule]; rw [mem_invtSubmodule]; rw [Submodule.map_le_iff_le_comap]; rw [Submodule.map_equiv_eq_comap_symm]; rw [← Submodule.comap_comp]; rw [← Submodule.comap_comp]; rw [this]

/--
lemma `_root_.LinearEquiv.map_mem_invtSubmodule_iff` / 引理 `_root_.LinearEquiv.map_mem_invtSubmodule_iff`

English:
lemma _root_.LinearEquiv.map_mem_invtSubmodule_iff
  statement: {R M N : Type*} [CommSemiring R]
  proof: by
  simp [← e.map_mem_invtSubmodule_conj_iff]

中文:
引理 _root_.线性等价.map_mem_invtSubmodule_iff
  结论: {R M N : 类型} [交换半环 R]
  证明: by
  simp [← e.map_mem_invtSubmodule_conj_iff]

Depends on / 依赖: e.map_mem_invtSubmodule_conj_iff, map_mem_invtSubmodule_conj_iff
-/
lemma _root_.LinearEquiv.map_mem_invtSubmodule_iff {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] {f : End R N}
    {e : M ≃ₗ[R] N} {p : Submodule R M} :
    p.map (e : M ->ₗ[R] N) in f.invtSubmodule ↔ p in (e.symm.conj f).invtSubmodule := by
  simp [← e.map_mem_invtSubmodule_conj_iff]

end invtSubmodule

variable (R) in
/--
lemma `span_orbit_mem_invtSubmodule` / 引理 `span_orbit_mem_invtSubmodule`

English:
lemma span_orbit_mem_invtSubmodule
  statement: {G : Type*}
  proof: by
  rw [mem_invtSubmodule]; rw [Submodule.span_le]; rw [Submodule.comap_coe]
  intro y hy
  simp only [Set.mem_preimage, DistribSMul.toLinearMap_apply, SetLike.mem_coe]
exact Submodule.subset_span MulAction.mem_orbit_of_mem_orbit g hy

中文:
引理 span_orbit_mem_invtSubmodule
  结论: {G : 类型}
  证明: by
  rw [mem_invtSubmodule]; rw [Submodule.span_le]; rw [Submodule.comap_coe]
  intro y hy
  simp only [Set.mem_preimage, DistribSMul.toLinearMap_apply, SetLike.mem_coe]
exact Submodule.subset_span MulAction.mem_orbit_of_mem_orbit g hy

Depends on / 依赖: DistribSMul, DistribSMul.toLinearMap_apply, MulAction, MulAction.mem_orbit_of_mem_orbit, Set.mem_preimage, SetLike, SetLike.mem_coe, Submodule, Submodule.comap_coe, Submodule.span_le, Submodule.subset_span, comap_coe, mem_coe, mem_invtSubmodule, mem_orbit_of_mem_orbit, mem_preimage, span_le, subset_span, toLinearMap_apply
-/
lemma span_orbit_mem_invtSubmodule {G : Type*}
    [Monoid G] [DistribMulAction G M] [SMulCommClass G R M] (x : M) (g : G) :
    span R (MulAction.orbit G x) in invtSubmodule (DistribSMul.toLinearMap R M g) := by
  rw [mem_invtSubmodule]; rw [Submodule.span_le]; rw [Submodule.comap_coe]
  intro y hy
  simp only [Set.mem_preimage, DistribSMul.toLinearMap_apply, SetLike.mem_coe]
exact Submodule.subset_span MulAction.mem_orbit_of_mem_orbit g hy

end Module.End
