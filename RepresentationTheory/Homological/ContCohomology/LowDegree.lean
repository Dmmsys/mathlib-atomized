/-
Copyright (c) 2026 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill, Andrew Yang, Edison Xie
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
## Low degree continuous cohomology

In this file we show that the zeroth continuous cohomology is isomorphic to the
invariants of the representation.
-/

@[expose] public section

namespace ContinuousCohomology

open CategoryTheory Functor TopRep ContRepresentation

variable {k G : Type*} [Ring k] [Group G] [TopologicalSpace k]
  [TopologicalSpace G] [IsTopologicalGroup G]

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

variable (X : TopRep k G)

/--
lemma `cocycles₀IsoAux` / 引理 `cocycles₀IsoAux`

English:
lemma cocycles₀IsoAux
  statement: (σ : (homogeneousCochains X).X 0)
  proof: by
  simp only [Nat.reduceAdd, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Subtype.ext_iff, homogeneousCochains.d_apply _] at hσ
  simp only [mem_invariants]
  intro g
  rw [d_succ]; rw [hom_sub]; rw [hom_ofHom]; rw [ContIntertwiningMap.sub_apply]; rw [d_zero]; rw [ZeroMemClass.coe_zero]; rw

中文:
引理 cocycles₀IsoAux
  结论: (σ : (homogeneousCochains X).X 0)
  证明: by
  simp only [Nat.reduceAdd, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Subtype.ext_iff, homogeneousCochains.d_apply _] at hσ
  simp only [mem_invariants]
  intro g
  rw [d_succ]; rw [hom_sub]; rw [hom_ofHom]; rw [ContIntertwiningMap.sub_apply]; rw [d_zero]; rw [ZeroMemClass.coe_zero]; rw

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ofHom, ContIntertwiningMap, ContIntertwiningMap.sub_apply, ContinuousLinearMap, ContinuousLinearMap.coe_coe, ContinuousMap, ContinuousMap.c, ContinuousMap.const_apply, DFunLike, DFunLike.ext_iff, LinearMap, LinearMap.mem_ker, Nat.reduceAdd, Subtype, Subtype.ext_iff, ZeroMemClass, ZeroMemClass.coe_zero, coe_coe, coe_zero
-/
lemma cocycles₀IsoAux (σ : (homogeneousCochains X).X 0)
    (hσ : σ in ((homogeneousCochains X).d 0 1).hom.ker) : σ.1 1 in X.ρ.invariants := by
  simp only [Nat.reduceAdd, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Subtype.ext_iff, homogeneousCochains.d_apply _] at hσ
  simp only [mem_invariants]
  intro g
  rw [d_succ]; rw [hom_sub]; rw [hom_ofHom]; rw [ContIntertwiningMap.sub_apply]; rw [d_zero]; rw [ZeroMemClass.coe_zero]; rw [sub_eq_zero] at hσ
  replace hσ := DFunLike.ext_iff.1 (DFunLike.ext_iff.1 hσ 1) g⁻¹
  simp only [Nat.reduceAdd, coind₁ι_toFun, ContinuousMap.const_apply, ConcreteCategory.hom_ofHom,
    coind₁Map_toFun, ContinuousMap.comp_apply, ContinuousMap.coe_mk] at hσ
  simpa [hσ] using DFunLike.ext_iff.1 (σ.2 g) 1

/--
lemma `mem_const_resol₀` / 引理 `mem_const_resol₀`

English:
lemma mem_const_resol₀
  given: (x : X) (hx : x in X.ρ.invariants)
  proof: .1 fun _ => ContinuousMap.ext fun _ => hx _ ContRepresentation.mem_invariants _

中文:
引理 mem_const_resol₀
  条件: (x : X) (hx : x in X.ρ.invariants)
  证明: .1 fun _ => ContinuousMap.ext fun _ => hx _ ContRepresentation.mem_invariants _

Depends on / 依赖: ContRepresentation, ContRepresentation.mem_invariants, ContinuousMap, ContinuousMap.ext, mem_invariants
-/
lemma mem_const_resol₀ (x : X) (hx : x in X.ρ.invariants) :
    ContinuousMap.const G x in ((resolution' X).X 0).ρ.invariants :=
.1 fun _ => ContinuousMap.ext fun _ => hx _ ContRepresentation.mem_invariants _

/--
lemma `cocycles₀IsoAux'` / 引理 `cocycles₀IsoAux'`

English:
lemma cocycles₀IsoAux'
  given: (x : X) (h : ContinuousMap.const G x in ((resolution' X).X 0).ρ.invariants)
  proof: by
  rw [LinearMap.mem_ker]; rw [Subtype.ext_iff]; rw [ContinuousLinearMap.coe_coe]; rw [homogeneousCochains.d_apply]
  simp [d_succ, hom_sub, ContIntertwiningMap.sub_apply, d_zero]

中文:
引理 cocycles₀IsoAux'
  条件: (x : X) (h : ContinuousMap.const G x in ((resolution' X).X 0).ρ.invariants)
  证明: by
  rw [LinearMap.mem_ker]; rw [Subtype.ext_iff]; rw [ContinuousLinearMap.coe_coe]; rw [homogeneousCochains.d_apply]
  simp [d_succ, hom_sub, ContIntertwiningMap.sub_apply, d_zero]

Depends on / 依赖: ContIntertwiningMap, ContIntertwiningMap.sub_apply, ContinuousLinearMap, ContinuousLinearMap.coe_coe, LinearMap, LinearMap.mem_ker, Subtype, Subtype.ext_iff, coe_coe, d_apply, d_succ, d_zero, ext_iff, hom_sub, homogeneousCochains, homogeneousCochains.d_apply, mem_ker, sub_apply
-/
lemma cocycles₀IsoAux' (x : X) (h : ContinuousMap.const G x in ((resolution' X).X 0).ρ.invariants) :
    ⟨ContinuousMap.const G x, h⟩ in ((homogeneousCochains X).d 0 1).hom.ker := by
  rw [LinearMap.mem_ker]; rw [Subtype.ext_iff]; rw [ContinuousLinearMap.coe_coe]; rw [homogeneousCochains.d_apply]
  simp [d_succ, hom_sub, ContIntertwiningMap.sub_apply, d_zero]

/--
Definition of `cocycles₀Iso` / `cocycles₀Iso` 的定义

English:
abbreviation cocycles₀Iso
  signature: : cocycles X 0 ≅
  body: Limits.KernelFork.mapIsoOfIsLimit ((homogeneousCochains X).cyclesIsKernel 0 1 (by simp))
    (TopModuleCat.isLimitKer _) (Iso.refl _)

中文:
缩写 cocycles₀Iso
  签名: : cocycles X 0 ≅
  定义体: Limits.KernelFork.mapIsoOfIsLimit ((homogeneousCochains X).cyclesIsKernel 0 1 (by simp))
    (TopModuleCat.isLimitKer _) (Iso.refl _)

Depends on / 依赖: Iso.refl, KernelFork, Limits, Limits.KernelFork.mapIsoOfIsLimit, TopModuleCat, TopModuleCat.isLimitKer, cyclesIsKernel, homogeneousCochains, isLimitKer, mapIsoOfIsLimit
-/
noncomputable abbrev cocycles₀Iso : cocycles X 0 ≅
    TopModuleCat.of k ((homogeneousCochains X).d 0 1).hom.ker :=
  Limits.KernelFork.mapIsoOfIsLimit ((homogeneousCochains X).cyclesIsKernel 0 1 (by simp))
    (TopModuleCat.isLimitKer _) (Iso.refl _)

/--
Definition of `d₀kerIso` / `d₀kerIso` 的定义

English:
definition d₀kerIso
  signature: : ((homogeneousCochains X).d 0 1).hom.ker ≃L[k] X.ρ.invariants where
  body: fun ⟨σ, hσ⟩ => ⟨σ.val 1, cocycles₀IsoAux X σ hσ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := fun ⟨x, hx⟩ => ⟨⟨ContinuousMap.const G x, mem_const_resol₀ X x hx⟩,
    cocycles₀IsoAux' X x (mem_const_resol₀ X x hx)⟩
  left_inv := fun ⟨⟨(x : C(G, X)), hx'⟩, hx⟩ => by
    ext g
    rw [Linea

中文:
定义 d₀kerIso
  签名: : ((homogeneousCochains X).d 0 1).hom.ker ≃L[k] X.ρ.invariants where
  定义体: fun ⟨σ, hσ⟩ => ⟨σ.val 1, cocycles₀IsoAux X σ hσ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := fun ⟨x, hx⟩ => ⟨⟨ContinuousMap.const G x, mem_const_resol₀ X x hx⟩,
    cocycles₀IsoAux' X x (mem_const_resol₀ X x hx)⟩
  left_inv := fun ⟨⟨(x : C(G, X)), hx'⟩, hx⟩ => by
    ext g
    rw [Linea
-/
def d₀kerIso : ((homogeneousCochains X).d 0 1).hom.ker ≃L[k] X.ρ.invariants where
  toFun := fun ⟨σ, hσ⟩ => ⟨σ.val 1, cocycles₀IsoAux X σ hσ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := fun ⟨x, hx⟩ => ⟨⟨ContinuousMap.const G x, mem_const_resol₀ X x hx⟩,
    cocycles₀IsoAux' X x (mem_const_resol₀ X x hx)⟩
  left_inv := fun ⟨⟨(x : C(G, X)), hx'⟩, hx⟩ => by
    ext g
    rw [LinearMap.mem_ker]; rw [Subtype.ext_iff]; rw [ContinuousLinearMap.coe_coe]; rw [homogeneousCochains.d_apply] at hx
    simp only [Nat.reduceAdd, d_succ, d_zero, ConcreteCategory.hom_ofHom, hom_sub,
      ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun, ZeroMemClass.coe_zero,
      sub_eq_zero, ContinuousMap.const_apply] at hx ⊢
    simpa using DFunLike.ext_iff.1 (DFunLike.ext_iff.1 hx g) 1
  right_inv _ := rfl
continuous_toFun := continuous_induced_rng.2 (continuous_eval_const 1).comp
    (continuous_subtype_val.comp continuous_subtype_val)
continuous_invFun := continuous_induced_rng.2 continuous_induced_rng.2
    ContinuousMap.continuous_const'.comp continuous_subtype_val

/--
Definition of `zeroIso` / `zeroIso` 的定义

English:
definition zeroIso
  signature: (A : TopRep k G)
  body: (homogeneousCochains A).isoHomologyπ₀.symm ≪≫ cocycles₀Iso A ≪≫
    TopModuleCat.ofIso (d₀kerIso A)

中文:
定义 zeroIso
  签名: (A : TopRep k G)
  定义体: (homogeneousCochains A).isoHomologyπ₀.symm ≪≫ cocycles₀Iso A ≪≫
    TopModuleCat.ofIso (d₀kerIso A)

Depends on / 依赖: TopModuleCat, TopModuleCat.ofIso, homogeneousCochains
-/
noncomputable def zeroIso (A : TopRep k G) :
    continuousCohomology 0 A ≅ TopModuleCat.of k A.ρ.invariants :=
  (homogeneousCochains A).isoHomologyπ₀.symm ≪≫ cocycles₀Iso A ≪≫
    TopModuleCat.ofIso (d₀kerIso A)

end ContinuousCohomology
