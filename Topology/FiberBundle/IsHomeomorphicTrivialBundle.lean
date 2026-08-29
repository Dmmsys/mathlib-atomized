/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Constructions.SumProd

/-!
# Maps equivariantly-homeomorphic to projection in a product

This file contains the definition `IsHomeomorphicTrivialFiberBundle F p`, a Prop saying that a
map `p : Z → B` between topological spaces is a "trivial fiber bundle" in the sense that there
exists a homeomorphism `h : Z ≃ₜ B × F` such that `proj x = (h x).1`. This is an abstraction which
is occasionally convenient in showing that a map is open, a quotient map, etc.

This material was formerly linked to the main definition of fiber bundles, but after a series of
refactors, there is no longer a direct connection.
-/

@[expose] public section

open Topology

variable {B : Type*} (F : Type*) {Z : Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace Z]

/--
Definition of `IsHomeomorphicTrivialFiberBundle` / `IsHomeomorphicTrivialFiberBundle` 的定义

English:
definition IsHomeomorphicTrivialFiberBundle
  signature: (proj : Z -> B)
  body: exists e : Z ≃ₜ B × F, forall x, (e x).1 = proj x

中文:
定义 IsHomeomorphicTrivialFiberBundle
  签名: (proj : Z -> B)
  定义体: exists e : Z ≃ₜ B × F, forall x, (e x).1 = proj x
-/
def IsHomeomorphicTrivialFiberBundle (proj : Z -> B) : Prop :=
  exists e : Z ≃ₜ B × F, forall x, (e x).1 = proj x

namespace IsHomeomorphicTrivialFiberBundle

variable {F} {proj : Z -> B}

/--
theorem `proj_eq` / 定理 `proj_eq`

English:
theorem proj_eq
  given: (h : IsHomeomorphicTrivialFiberBundle F proj)
  proof: ⟨h.choose, (funext h.choose_spec).symm⟩

中文:
定理 proj_eq
  条件: (h : IsHomeomorphicTrivialFiberBundle F proj)
  证明: ⟨h.choose, (funext h.choose_spec).symm⟩
-/
protected theorem proj_eq (h : IsHomeomorphicTrivialFiberBundle F proj) :
    exists e : Z ≃ₜ B × F, proj = Prod.fst ∘ e :=
  ⟨h.choose, (funext h.choose_spec).symm⟩

/--
theorem `surjective_proj` / 定理 `surjective_proj`

English:
theorem surjective_proj
  given: [Nonempty F] (h : IsHomeomorphicTrivialFiberBundle F proj)
  proof: by
  obtain ⟨e, rfl⟩ := h.proj_eq
  exact Prod.fst_surjective.comp e.surjective

中文:
定理 surjective_proj
  条件: [Nonempty F] (h : IsHomeomorphicTrivialFiberBundle F proj)
  证明: by
  obtain ⟨e, rfl⟩ := h.proj_eq
  exact Prod.fst_surjective.comp e.surjective
-/
protected theorem surjective_proj [Nonempty F] (h : IsHomeomorphicTrivialFiberBundle F proj) :
    Function.Surjective proj := by
  obtain ⟨e, rfl⟩ := h.proj_eq
  exact Prod.fst_surjective.comp e.surjective

/--
theorem `continuous_proj` / 定理 `continuous_proj`

English:
theorem continuous_proj
  given: (h : IsHomeomorphicTrivialFiberBundle F proj)
  proof: by
  obtain ⟨e, rfl⟩ := h.proj_eq; exact continuous_fst.comp e.continuous

中文:
定理 continuous_proj
  条件: (h : IsHomeomorphicTrivialFiberBundle F proj)
  证明: by
  obtain ⟨e, rfl⟩ := h.proj_eq; exact continuous_fst.comp e.continuous
-/
protected theorem continuous_proj (h : IsHomeomorphicTrivialFiberBundle F proj) :
    Continuous proj := by
  obtain ⟨e, rfl⟩ := h.proj_eq; exact continuous_fst.comp e.continuous

/--
theorem `isOpenMap_proj` / 定理 `isOpenMap_proj`

English:
theorem isOpenMap_proj
  given: (h : IsHomeomorphicTrivialFiberBundle F proj)
  proof: by
  obtain ⟨e, rfl⟩ := h.proj_eq; exact isOpenMap_fst.comp e.isOpenMap

中文:
定理 isOpenMap_proj
  条件: (h : IsHomeomorphicTrivialFiberBundle F proj)
  证明: by
  obtain ⟨e, rfl⟩ := h.proj_eq; exact isOpenMap_fst.comp e.isOpenMap
-/
protected theorem isOpenMap_proj (h : IsHomeomorphicTrivialFiberBundle F proj) :
    IsOpenMap proj := by
  obtain ⟨e, rfl⟩ := h.proj_eq; exact isOpenMap_fst.comp e.isOpenMap

/--
theorem `isQuotientMap_proj` / 定理 `isQuotientMap_proj`

English:
theorem isQuotientMap_proj
  given: [Nonempty F] (h : IsHomeomorphicTrivialFiberBundle F proj)
  proof: h.isOpenMap_proj.isQuotientMap h.continuous_proj h.surjective_proj

中文:
定理 isQuotientMap_proj
  条件: [Nonempty F] (h : IsHomeomorphicTrivialFiberBundle F proj)
  证明: h.isOpenMap_proj.isQuotientMap h.continuous_proj h.surjective_proj
-/
protected theorem isQuotientMap_proj [Nonempty F] (h : IsHomeomorphicTrivialFiberBundle F proj) :
    IsQuotientMap proj :=
  h.isOpenMap_proj.isQuotientMap h.continuous_proj h.surjective_proj

end IsHomeomorphicTrivialFiberBundle

/--
theorem `isHomeomorphicTrivialFiberBundle_fst` / 定理 `isHomeomorphicTrivialFiberBundle_fst`

English:
theorem isHomeomorphicTrivialFiberBundle_fst
  proof: ⟨Homeomorph.refl _, fun _x => rfl⟩

中文:
定理 isHomeomorphicTrivialFiberBundle_fst
  证明: ⟨Homeomorph.refl _, fun _x => rfl⟩

Depends on / 依赖: Homeomorph, Homeomorph.refl
-/
theorem isHomeomorphicTrivialFiberBundle_fst :
    IsHomeomorphicTrivialFiberBundle F (Prod.fst : B × F -> B) :=
  ⟨Homeomorph.refl _, fun _x => rfl⟩

/--
theorem `isHomeomorphicTrivialFiberBundle_snd` / 定理 `isHomeomorphicTrivialFiberBundle_snd`

English:
theorem isHomeomorphicTrivialFiberBundle_snd
  proof: ⟨Homeomorph.prodComm _ _, fun _x => rfl⟩

中文:
定理 isHomeomorphicTrivialFiberBundle_snd
  证明: ⟨Homeomorph.prodComm _ _, fun _x => rfl⟩

Depends on / 依赖: Homeomorph, Homeomorph.prodComm, prodComm
-/
theorem isHomeomorphicTrivialFiberBundle_snd :
    IsHomeomorphicTrivialFiberBundle F (Prod.snd : F × B -> B) :=
  ⟨Homeomorph.prodComm _ _, fun _x => rfl⟩
