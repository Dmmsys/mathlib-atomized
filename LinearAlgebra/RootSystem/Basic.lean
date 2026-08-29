/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury, Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Defs
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# Root data and root systems

This file contains basic results for root systems and root data.

## Main definitions / results:

* `RootPairing.ext`: In characteristic zero if there is no torsion, the correspondence between
  roots and coroots is unique.
* `RootSystem.ext`: In characteristic zero if there is no torsion, a root system is determined
  entirely by its roots.
* `RootPairing.mk'`: In characteristic zero if there is no torsion, to check that two finite
  families of roots and coroots form a root pairing, it is sufficient to check that they are
  stable under reflections.
* `RootSystem.mk'`: In characteristic zero if there is no torsion, to check that a finite family of
  roots form a root system, we do not need to check that the coroots are stable under reflections
  since this follows from the corresponding property for the roots.

-/

@[expose] public section

open Set Function
open Module hiding reflection
open Submodule (span)
open AddSubgroup (zmultiples)

noncomputable section

variable {ι R M N : Type*}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

section reflectionPerm

variable (p : M ->ₗ[R] N ->ₗ[R] R) (root : ι ↪ M) (coroot : ι ↪ N) (i j : ι)
  (h : forall i, MapsTo (preReflection (root i) (p.flip (coroot i)))
    (range root) (range root))
include h

set_option backward.privateInPublic true in
/--
theorem `exist_eq_reflection_of_mapsTo` / 定理 `exist_eq_reflection_of_mapsTo`

English:
theorem exist_eq_reflection_of_mapsTo
  proof: h i (mem_range_self j)

中文:
定理 exist_eq_reflection_of_mapsTo
  证明: h i (mem_range_self j)
-/
private theorem exist_eq_reflection_of_mapsTo :
    exists k, root k = (preReflection (root i) (p.flip (coroot i))) (root j) :=
  h i (mem_range_self j)

variable (hp : forall i, p (root i) (coroot i) = 2)
include hp

set_option backward.privateInPublic true in
/--
theorem `choose_choose_eq_of_mapsTo` / 定理 `choose_choose_eq_of_mapsTo`

English:
theorem choose_choose_eq_of_mapsTo
  proof: by
  refine root.injective ?_
  rw [(exist_eq_reflection_of_mapsTo p root coroot i _ h).choose_spec]; rw [(exist_eq_reflection_of_mapsTo p root coroot i j h).choose_spec]
  apply involutive_preReflection (x := root i) (hp i)

中文:
定理 choose_choose_eq_of_mapsTo
  证明: by
  refine root.injective ?_
  rw [(exist_eq_reflection_of_mapsTo p root coroot i _ h).choose_spec]; rw [(exist_eq_reflection_of_mapsTo p root coroot i j h).choose_spec]
  apply involutive_preReflection (x := root i) (hp i)
-/
private theorem choose_choose_eq_of_mapsTo :
    (exist_eq_reflection_of_mapsTo p root coroot i
      (exist_eq_reflection_of_mapsTo p root coroot i j h).choose h).choose = j := by
  refine root.injective ?_
  rw [(exist_eq_reflection_of_mapsTo p root coroot i _ h).choose_spec]; rw [(exist_eq_reflection_of_mapsTo p root coroot i j h).choose_spec]
  apply involutive_preReflection (x := root i) (hp i)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The bijection on the indexing set induced by reflection. -/
@[simps]
/--
Definition of `equiv_of_mapsTo` / `equiv_of_mapsTo` 的定义

English:
definition equiv_of_mapsTo
  signature: :
  body: (exist_eq_reflection_of_mapsTo p root coroot i j h).choose
  invFun j := (exist_eq_reflection_of_mapsTo p root coroot i j h).choose
  left_inv j := choose_choose_eq_of_mapsTo p root coroot i j h hp
  right_inv j := choose_choose_eq_of_mapsTo p root coroot i j h hp

中文:
定义 equiv_of_mapsTo
  签名: :
  定义体: (exist_eq_reflection_of_mapsTo p root coroot i j h).choose
  invFun j := (exist_eq_reflection_of_mapsTo p root coroot i j h).choose
  left_inv j := choose_choose_eq_of_mapsTo p root coroot i j h hp
  right_inv j := choose_choose_eq_of_mapsTo p root coroot i j h hp
-/
protected def equiv_of_mapsTo :
    ι ≃ ι where
  toFun j := (exist_eq_reflection_of_mapsTo p root coroot i j h).choose
  invFun j := (exist_eq_reflection_of_mapsTo p root coroot i j h).choose
  left_inv j := choose_choose_eq_of_mapsTo p root coroot i j h hp
  right_inv j := choose_choose_eq_of_mapsTo p root coroot i j h hp

end reflectionPerm

variable (P : RootPairing ι R M N) [Finite ι]

/--
lemma `injOn_dualMap_subtype_span_root_coroot` / 引理 `injOn_dualMap_subtype_span_root_coroot`

English:
lemma injOn_dualMap_subtype_span_root_coroot
  given: [IsAddTorsionFree M]
  proof: by
  have := injOn_dualMap_subtype_span_range_range (finite_range P.root)
    (c := P.toLinearMap.flip ∘ P.coroot) P.root_coroot_two P.mapsTo_reflection_root
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
exact P.flip.toPerfPair.injective this (mem_range_self i) (mem_range_self j) hij

中文:
引理 injOn_dualMap_subtype_span_root_coroot
  条件: [是加法无挠 M]
  证明: by
  have := injOn_dualMap_subtype_span_range_range (finite_range P.root)
    (c := P.toLinearMap.flip ∘ P.coroot) P.root_coroot_two P.mapsTo_reflection_root
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
exact P.flip.toPerfPair.injective this (mem_range_self i) (mem_range_self j) hij

Depends on / 依赖: P.coroot, P.flip.toPerfPair.injective, P.mapsTo_reflection_root, P.root, P.root_coroot_two, P.toLinearMap.flip, coroot, finite_range, injOn_dualMap_subtype_span_range_range, injective, mapsTo_reflection_root, mem_range_self, root_coroot_two, toLinearMap, toPerfPair
-/
lemma injOn_dualMap_subtype_span_root_coroot [IsAddTorsionFree M] :
    InjOn ((span R (range P.root)).subtype.dualMap ∘ₗ P.toLinearMap.flip) (range P.coroot) := by
  have := injOn_dualMap_subtype_span_range_range (finite_range P.root)
    (c := P.toLinearMap.flip ∘ P.coroot) P.root_coroot_two P.mapsTo_reflection_root
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
exact P.flip.toPerfPair.injective this (mem_range_self i) (mem_range_self j) hij

/-- In characteristic zero if there is no torsion, the correspondence between roots and coroots is
unique.

Formally, the point is that the hypothesis `hc` depends only on the range of the coroot mappings. -/
@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: [CharZero R] [IsDomain R] [IsTorsionFree R M]
  proof: by
  have hp (hc' : P₁.coroot = P₂.coroot) : P₁.reflectionPerm = P₂.reflectionPerm := by
    ext i j
    refine P₁.root.injective ?_
    conv_rhs => rw [hr]
    simp only [root_reflectionPerm, reflection_apply, coroot']
    simp only [hr, he, hc']
  suffices P₁.coroot = P₂.coroot by
    obtain ⟨p₁⟩ := P₁; obtain ⟨p₂⟩ := P₂
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was: `grind` -/
    simp_all
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  ext i
  apply P₁.injOn_dualMap_subtype_span_root_coroot (mem_range_self i) (hc ▸ mem_range_self i)
  simp only [LinearMap.coe_comp, comp_apply]
  apply Dual.eq_of_preReflection_mapsTo' (finite_range P₁.root)
  · exact Submodule.subset_span (mem_range_self i)
  · exact P₁.coroot_root_two i
  · exact P₁.mapsTo_reflection_root i
  · exact hr ▸ he ▸ P₂.coroot_root_two i
  · exact hr ▸ he ▸ P₂.mapsTo_reflection_root i

中文:
引理 ext
  结论: [特征零 R] [是整环 R] [是无挠 R M]
  证明: by
  have hp (hc' : P₁.coroot = P₂.coroot) : P₁.reflectionPerm = P₂.reflectionPerm := by
    ext i j
    refine P₁.root.injective ?_
    conv_rhs => rw [hr]
    simp only [root_reflectionPerm, reflection_apply, coroot']
    simp only [hr, he, hc']
  suffices P₁.coroot = P₂.coroot by
    obtain ⟨p₁⟩ := P₁; obtain ⟨p₂⟩ := P₂
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was: `grind` -/
    simp_all
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  ext i
  apply P₁.injOn_dualMap_subtype_span_root_coroot (mem_range_self i) (hc ▸ mem_range_self i)
  simp only [LinearMap.coe_comp, comp_apply]
  apply Dual.eq_of_preReflection_mapsTo' (finite_range P₁.root)
  · exact Submodule.subset_span (mem_range_self i)
  · exact P₁.coroot_root_two i
  · exact P₁.mapsTo_reflection_root i
  · exact hr ▸ he ▸ P₂.coroot_root_two i
  · exact hr ▸ he ▸ P₂.mapsTo_reflection_root i
-/
protected lemma ext [CharZero R] [IsDomain R] [IsTorsionFree R M]
    {P₁ P₂ : RootPairing ι R M N}
    (he : P₁.toLinearMap = P₂.toLinearMap)
    (hr : P₁.root = P₂.root)
    (hc : range P₁.coroot = range P₂.coroot) :
    P₁ = P₂ := by
  have hp (hc' : P₁.coroot = P₂.coroot) : P₁.reflectionPerm = P₂.reflectionPerm := by
    ext i j
    refine P₁.root.injective ?_
    conv_rhs => rw [hr]
    simp only [root_reflectionPerm, reflection_apply, coroot']
    simp only [hr, he, hc']
  suffices P₁.coroot = P₂.coroot by
    obtain ⟨p₁⟩ := P₁; obtain ⟨p₂⟩ := P₂
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was: `grind` -/
    simp_all
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  ext i
  apply P₁.injOn_dualMap_subtype_span_root_coroot (mem_range_self i) (hc ▸ mem_range_self i)
  simp only [LinearMap.coe_comp, comp_apply]
  apply Dual.eq_of_preReflection_mapsTo' (finite_range P₁.root)
  · exact Submodule.subset_span (mem_range_self i)
  · exact P₁.coroot_root_two i
  · exact P₁.mapsTo_reflection_root i
  · exact hr ▸ he ▸ P₂.coroot_root_two i
  · exact hr ▸ he ▸ P₂.mapsTo_reflection_root i

/--
lemma `coroot_eq_coreflection_of_root_eq'` / 引理 `coroot_eq_coreflection_of_root_eq'`

English:
lemma coroot_eq_coreflection_of_root_eq'
  statement: [CharZero R] [IsDomain R] [IsTorsionFree R M]
  proof: by
  set α := root i
  set β := root j
  set α' := coroot i
  set β' := coroot j
  set sα := preReflection α (p.flip α')
  set sβ := preReflection β (p.flip β')
  let sα' := preReflection α' (p α)
  have hij : preReflection (sα β) (p.flip (sα' β')) = sα ∘ₗ sβ ∘ₗ sα := by
    ext
    have hpi : (p.flip (coroot i)) (root i) = 2 := by simp [hp i]
    simp [α, β, α', β', sα, sβ, sα', ← preReflection_preReflection β (p.flip β') hpi,
      preReflection_apply]
  obtain ⟨l, hl⟩ := hc i (mem_range_self j)
  rw [← hl]
  have hkl : (p.flip (coroot l)) (root k) = 2 := by
    simp only [hl, preReflection_apply, map_sub, map_smul, hk, LinearMap.flip_apply,
      LinearMap.sub_apply, hp j, LinearMap.smul_apply, smul_eq_mul, hp i, mul_two,
      sub_add_cancel_right, mul_neg, sub_neg_eq_add, sα, α, α', β]
    rw [mul_comm (p (root i) (coroot j))]
    abel
  suffices p.flip (coroot k) = p.flip (coroot l) from p.flip.toPerfPair.injective this
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  have := injOn_dualMap_subtype_span_range_range (finite_range root)
    (c := p.flip ∘ coroot) hp hr
  apply this (mem_range_self k) (mem_range_self l)
  refine Dual.eq_of_preReflection_mapsTo' (finite_range root)
    (Submodule.subset_span <| mem_range_self k) (hp k) (hr k) hkl ?_
  rw [comp_apply]; rw [hl]; rw [hk]; rw [hij]
exact (hr i).comp (hr j).comp (hr i)

中文:
引理 coroot_eq_coreflection_of_root_eq'
  结论: [特征零 R] [是整环 R] [是无挠 R M]
  证明: by
  set α := root i
  set β := root j
  set α' := coroot i
  set β' := coroot j
  set sα := preReflection α (p.flip α')
  set sβ := preReflection β (p.flip β')
  let sα' := preReflection α' (p α)
  have hij : preReflection (sα β) (p.flip (sα' β')) = sα ∘ₗ sβ ∘ₗ sα := by
    ext
    have hpi : (p.flip (coroot i)) (root i) = 2 := by simp [hp i]
    simp [α, β, α', β', sα, sβ, sα', ← preReflection_preReflection β (p.flip β') hpi,
      preReflection_apply]
  obtain ⟨l, hl⟩ := hc i (mem_range_self j)
  rw [← hl]
  have hkl : (p.flip (coroot l)) (root k) = 2 := by
    simp only [hl, preReflection_apply, map_sub, map_smul, hk, LinearMap.flip_apply,
      LinearMap.sub_apply, hp j, LinearMap.smul_apply, smul_eq_mul, hp i, mul_two,
      sub_add_cancel_right, mul_neg, sub_neg_eq_add, sα, α, α', β]
    rw [mul_comm (p (root i) (coroot j))]
    abel
  suffices p.flip (coroot k) = p.flip (coroot l) from p.flip.toPerfPair.injective this
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  have := injOn_dualMap_subtype_span_range_range (finite_range root)
    (c := p.flip ∘ coroot) hp hr
  apply this (mem_range_self k) (mem_range_self l)
  refine Dual.eq_of_preReflection_mapsTo' (finite_range root)
    (Submodule.subset_span <| mem_range_self k) (hp k) (hr k) hkl ?_
  rw [comp_apply]; rw [hl]; rw [hk]; rw [hij]
exact (hr i).comp (hr j).comp (hr i)
-/
private lemma coroot_eq_coreflection_of_root_eq' [CharZero R] [IsDomain R] [IsTorsionFree R M]
    (p : M ->ₗ[R] N ->ₗ[R] R) [p.IsPerfPair]
    (root : ι ↪ M)
    (coroot : ι ↪ N)
    (hp : forall i, p (root i) (coroot i) = 2)
    (hr : forall i, MapsTo (preReflection (root i) (p.flip (coroot i))) (range root) (range root))
    (hc : forall i, MapsTo (preReflection (coroot i) (p (root i))) (range coroot) (range coroot))
    {i j k : ι} (hk : root k = preReflection (root i) (p.flip (coroot i)) (root j)) :
    coroot k = preReflection (coroot i) (p (root i)) (coroot j) := by
  set α := root i
  set β := root j
  set α' := coroot i
  set β' := coroot j
  set sα := preReflection α (p.flip α')
  set sβ := preReflection β (p.flip β')
  let sα' := preReflection α' (p α)
  have hij : preReflection (sα β) (p.flip (sα' β')) = sα ∘ₗ sβ ∘ₗ sα := by
    ext
    have hpi : (p.flip (coroot i)) (root i) = 2 := by simp [hp i]
    simp [α, β, α', β', sα, sβ, sα', ← preReflection_preReflection β (p.flip β') hpi,
      preReflection_apply]
  obtain ⟨l, hl⟩ := hc i (mem_range_self j)
  rw [← hl]
  have hkl : (p.flip (coroot l)) (root k) = 2 := by
    simp only [hl, preReflection_apply, map_sub, map_smul, hk, LinearMap.flip_apply,
      LinearMap.sub_apply, hp j, LinearMap.smul_apply, smul_eq_mul, hp i, mul_two,
      sub_add_cancel_right, mul_neg, sub_neg_eq_add, sα, α, α', β]
    rw [mul_comm (p (root i) (coroot j))]
    abel
  suffices p.flip (coroot k) = p.flip (coroot l) from p.flip.toPerfPair.injective this
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  have := injOn_dualMap_subtype_span_range_range (finite_range root)
    (c := p.flip ∘ coroot) hp hr
  apply this (mem_range_self k) (mem_range_self l)
  refine Dual.eq_of_preReflection_mapsTo' (finite_range root)
    (Submodule.subset_span <| mem_range_self k) (hp k) (hr k) hkl ?_
  rw [comp_apply]; rw [hl]; rw [hk]; rw [hij]
exact (hr i).comp (hr j).comp (hr i)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: [CharZero R] [IsDomain R] [IsTorsionFree R M]
  body: p
  root := root
  coroot := coroot
  root_coroot_two := hp
  reflectionPerm i := RootPairing.equiv_of_mapsTo p root coroot i hr hp
  reflectionPerm_root i j := by
    simp [(exist_eq_reflection_of_mapsTo p root coroot i j hr).choose_spec, preReflection_apply]
  reflectionPerm_coroot i j := by
    refine (coroot_eq_coreflection_of_root_eq' p root coroot hp hr hc ?_).symm
    rw [equiv_of_mapsTo_apply]; rw [(exist_eq_reflection_of_mapsTo p root coroot i j hr).choose_spec]

中文:
定义 mk'
  签名: [特征零 R] [是整环 R] [是无挠 R M]
  定义体: p
  root := root
  coroot := coroot
  root_coroot_two := hp
  reflectionPerm i := RootPairing.equiv_of_mapsTo p root coroot i hr hp
  reflectionPerm_root i j := by
    simp [(exist_eq_reflection_of_mapsTo p root coroot i j hr).choose_spec, preReflection_apply]
  reflectionPerm_coroot i j := by
    refine (coroot_eq_coreflection_of_root_eq' p root coroot hp hr hc ?_).symm
    rw [equiv_of_mapsTo_apply]; rw [(exist_eq_reflection_of_mapsTo p root coroot i j hr).choose_spec]
-/
def mk' [CharZero R] [IsDomain R] [IsTorsionFree R M]
    (p : M ->ₗ[R] N ->ₗ[R] R) [p.IsPerfPair]
    (root : ι ↪ M)
    (coroot : ι ↪ N)
    (hp : forall i, p (root i) (coroot i) = 2)
    (hr : forall i, MapsTo (preReflection (root i) (p.flip (coroot i))) (range root) (range root))
    (hc : forall i, MapsTo (preReflection (coroot i) (p (root i))) (range coroot) (range coroot)) :
    RootPairing ι R M N where
  toLinearMap := p
  root := root
  coroot := coroot
  root_coroot_two := hp
  reflectionPerm i := RootPairing.equiv_of_mapsTo p root coroot i hr hp
  reflectionPerm_root i j := by
    simp [(exist_eq_reflection_of_mapsTo p root coroot i j hr).choose_spec, preReflection_apply]
  reflectionPerm_coroot i j := by
    refine (coroot_eq_coreflection_of_root_eq' p root coroot hp hr hc ?_).symm
    rw [equiv_of_mapsTo_apply]; rw [(exist_eq_reflection_of_mapsTo p root coroot i j hr).choose_spec]

variable [P.IsRootSystem]

/--
lemma `IsRootSystem.ext` / 引理 `IsRootSystem.ext`

English:
lemma IsRootSystem.ext
  statement: [CharZero R] [IsDomain R] [IsTorsionFree R M]
  proof: by
  suffices forall (P₁ P₂ : RootPairing ι R M N) [P₁.IsRootSystem] [P₂.IsRootSystem],
      P₁.toLinearMap = P₂.toLinearMap -> P₁.root = P₂.root -> range P₁.coroot subseteq range P₂.coroot by
    have h₁ := this P₁ P₂ he hr
    have h₂ := this P₂ P₁ he.symm hr.symm
    exact RootPairing.ext he hr (le_antisymm h₁ h₂)
  clear! P₁ P₂
  rintro P₁ P₂ hP₁ hP₂ he hr - ⟨i, rfl⟩
  use i
  apply P₁.flip.toPerfPair.injective
  apply Dual.eq_of_preReflection_mapsTo (finite_range P₁.root) IsRootSystem.span_root_eq_top
  · exact hr ▸ he ▸ P₂.coroot_root_two i
  · change MapsTo (preReflection _ (P₁.toLinearMap.flip.toPerfPair _)) _ _
    simp_rw [hr, he]
    exact P₂.mapsTo_reflection_root i
  · exact P₁.coroot_root_two i
  · exact P₁.mapsTo_reflection_root i

中文:
引理 是RootSystem.ext
  结论: [特征零 R] [是整环 R] [是无挠 R M]
  证明: by
  suffices forall (P₁ P₂ : RootPairing ι R M N) [P₁.IsRootSystem] [P₂.IsRootSystem],
      P₁.toLinearMap = P₂.toLinearMap -> P₁.root = P₂.root -> range P₁.coroot subseteq range P₂.coroot by
    have h₁ := this P₁ P₂ he hr
    have h₂ := this P₂ P₁ he.symm hr.symm
    exact RootPairing.ext he hr (le_antisymm h₁ h₂)
  clear! P₁ P₂
  rintro P₁ P₂ hP₁ hP₂ he hr - ⟨i, rfl⟩
  use i
  apply P₁.flip.toPerfPair.injective
  apply Dual.eq_of_preReflection_mapsTo (finite_range P₁.root) IsRootSystem.span_root_eq_top
  · exact hr ▸ he ▸ P₂.coroot_root_two i
  · change MapsTo (preReflection _ (P₁.toLinearMap.flip.toPerfPair _)) _ _
    simp_rw [hr, he]
    exact P₂.mapsTo_reflection_root i
  · exact P₁.coroot_root_two i
  · exact P₁.mapsTo_reflection_root i
-/
protected lemma IsRootSystem.ext [CharZero R] [IsDomain R] [IsTorsionFree R M]
    {P₁ P₂ : RootPairing ι R M N} [P₁.IsRootSystem] [P₂.IsRootSystem]
    (he : P₁.toLinearMap = P₂.toLinearMap)
    (hr : P₁.root = P₂.root) :
    P₁ = P₂ := by
  suffices forall (P₁ P₂ : RootPairing ι R M N) [P₁.IsRootSystem] [P₂.IsRootSystem],
      P₁.toLinearMap = P₂.toLinearMap -> P₁.root = P₂.root -> range P₁.coroot subseteq range P₂.coroot by
    have h₁ := this P₁ P₂ he hr
    have h₂ := this P₂ P₁ he.symm hr.symm
    exact RootPairing.ext he hr (le_antisymm h₁ h₂)
  clear! P₁ P₂
  rintro P₁ P₂ hP₁ hP₂ he hr - ⟨i, rfl⟩
  use i
  apply P₁.flip.toPerfPair.injective
  apply Dual.eq_of_preReflection_mapsTo (finite_range P₁.root) IsRootSystem.span_root_eq_top
  · exact hr ▸ he ▸ P₂.coroot_root_two i
  · change MapsTo (preReflection _ (P₁.toLinearMap.flip.toPerfPair _)) _ _
    simp_rw [hr, he]
    exact P₂.mapsTo_reflection_root i
  · exact P₁.coroot_root_two i
  · exact P₁.mapsTo_reflection_root i

/--
lemma `coroot_eq_coreflection_of_root_eq_of_span_eq_top` / 引理 `coroot_eq_coreflection_of_root_eq_of_span_eq_top`

English:
lemma coroot_eq_coreflection_of_root_eq_of_span_eq_top
  statement: [CharZero R] [IsDomain R]
  proof: by
  set α := root i
  set β := root j
  set α' := coroot i
  set β' := coroot j
  set sα := preReflection α (p.flip α')
  set sβ := preReflection β (p.flip β')
  let sα' := preReflection α' (p α)
  have hij : preReflection (sα β) (p.flip (sα' β')) = sα ∘ₗ sβ ∘ₗ sα := by
    ext
    have hpi : (p.flip (coroot i)) (root i) = 2 := by simp [hp i]
    simp [α, β, α', β', sα, sβ, sα', ← preReflection_preReflection β (p.flip β') hpi,
      preReflection_apply] -- v4.7.0-rc1 issues
  apply p.flip.toPerfPair.injective
  apply Dual.eq_of_preReflection_mapsTo (finite_range root) hsp (hp k) (hs k)
  · simp [map_sub, α, β, α', β', sα, hk, preReflection_apply, hp i, hp j,
      mul_comm (p α β')]
    ring -- v4.7.0-rc1 issues
  · rw [hk, LinearMap.toLinearMap_toPerfPair, hij]
exact (hs i).comp (hs j).comp (hs i)

中文:
引理 coroot_eq_coreflection_of_root_eq_of_span_eq_top
  结论: [特征零 R] [是整环 R]
  证明: by
  set α := root i
  set β := root j
  set α' := coroot i
  set β' := coroot j
  set sα := preReflection α (p.flip α')
  set sβ := preReflection β (p.flip β')
  let sα' := preReflection α' (p α)
  have hij : preReflection (sα β) (p.flip (sα' β')) = sα ∘ₗ sβ ∘ₗ sα := by
    ext
    have hpi : (p.flip (coroot i)) (root i) = 2 := by simp [hp i]
    simp [α, β, α', β', sα, sβ, sα', ← preReflection_preReflection β (p.flip β') hpi,
      preReflection_apply] -- v4.7.0-rc1 issues
  apply p.flip.toPerfPair.injective
  apply Dual.eq_of_preReflection_mapsTo (finite_range root) hsp (hp k) (hs k)
  · simp [map_sub, α, β, α', β', sα, hk, preReflection_apply, hp i, hp j,
      mul_comm (p α β')]
    ring -- v4.7.0-rc1 issues
  · rw [hk, LinearMap.toLinearMap_toPerfPair, hij]
exact (hs i).comp (hs j).comp (hs i)
-/
private lemma coroot_eq_coreflection_of_root_eq_of_span_eq_top [CharZero R] [IsDomain R]
    [IsTorsionFree R M] (p : M ->ₗ[R] N ->ₗ[R] R) [p.IsPerfPair]
    (root : ι ↪ M)
    (coroot : ι ↪ N)
    (hp : forall i, p (root i) (coroot i) = 2)
    (hs : forall i, MapsTo (preReflection (root i) (p.flip (coroot i))) (range root) (range root))
    (hsp : span R (range root) = ⊤)
    {i j k : ι} (hk : root k = preReflection (root i) (p.flip (coroot i)) (root j)) :
    coroot k = preReflection (coroot i) (p (root i)) (coroot j) := by
  set α := root i
  set β := root j
  set α' := coroot i
  set β' := coroot j
  set sα := preReflection α (p.flip α')
  set sβ := preReflection β (p.flip β')
  let sα' := preReflection α' (p α)
  have hij : preReflection (sα β) (p.flip (sα' β')) = sα ∘ₗ sβ ∘ₗ sα := by
    ext
    have hpi : (p.flip (coroot i)) (root i) = 2 := by simp [hp i]
    simp [α, β, α', β', sα, sβ, sα', ← preReflection_preReflection β (p.flip β') hpi,
      preReflection_apply] -- v4.7.0-rc1 issues
  apply p.flip.toPerfPair.injective
  apply Dual.eq_of_preReflection_mapsTo (finite_range root) hsp (hp k) (hs k)
  · simp [map_sub, α, β, α', β', sα, hk, preReflection_apply, hp i, hp j,
      mul_comm (p α β')]
    ring -- v4.7.0-rc1 issues
  · rw [hk, LinearMap.toLinearMap_toPerfPair, hij]
exact (hs i).comp (hs j).comp (hs i)

section

variable {k : Type*} [Field k] [CharZero k] [Module k M] [Module k N]
  (p : M ->ₗ[k] N ->ₗ[k] k) [p.IsPerfPair]
  (root : ι ↪ M)
  (coroot : ι ↪ N)
  (hp : forall i, p (root i) (coroot i) = 2)
  (hs : forall i, MapsTo (preReflection (root i) (p.flip (coroot i))) (range root) (range root))
  (hsp : span k (range root) = ⊤)

/--
Definition of `mk''` / `mk''` 的定义

English:
definition mk''
  signature: :
  body: .mk' p root coroot hp hs by
    rintro i - ⟨j, rfl⟩
    use RootPairing.equiv_of_mapsTo p root coroot i hs hp j
    refine (coroot_eq_coreflection_of_root_eq_of_span_eq_top p root coroot hp hs hsp ?_)
    rw [equiv_of_mapsTo_apply]; rw [(exist_eq_reflection_of_mapsTo p root coroot i j hs).choose_spec]

中文:
定义 mk''
  签名: :
  定义体: .mk' p root coroot hp hs by
    rintro i - ⟨j, rfl⟩
    use RootPairing.equiv_of_mapsTo p root coroot i hs hp j
    refine (coroot_eq_coreflection_of_root_eq_of_span_eq_top p root coroot hp hs hsp ?_)
    rw [equiv_of_mapsTo_apply]; rw [(exist_eq_reflection_of_mapsTo p root coroot i j hs).choose_spec]

Depends on / 依赖: RootPairing, RootPairing.equiv_of_mapsTo, choose_spec, coroot, coroot_eq_coreflection_of_root_eq_of_span_eq_top, equiv_of_mapsTo, equiv_of_mapsTo_apply, exist_eq_reflection_of_mapsTo
-/
def mk'' :
    RootPairing ι k M N :=
.mk' p root coroot hp hs by
    rintro i - ⟨j, rfl⟩
    use RootPairing.equiv_of_mapsTo p root coroot i hs hp j
    refine (coroot_eq_coreflection_of_root_eq_of_span_eq_top p root coroot hp hs hsp ?_)
    rw [equiv_of_mapsTo_apply]; rw [(exist_eq_reflection_of_mapsTo p root coroot i j hs).choose_spec]

variable {p root coroot hp hs hsp} in
/--
lemma `isRootSystem_mk''` / 引理 `isRootSystem_mk''`

English:
lemma isRootSystem_mk''
  given: (h_int : forall i j, exists z : Int, z = p (root i) (coroot j))
  proof: hsp
  span_coroot_eq_top :=
    have _i : (mk'' p root coroot hp hs hsp).IsCrystallographic := ⟨h_int⟩
    have _i : Fintype ι := Fintype.ofFinite ι
    (rootSpan_eq_top_iff _).mp hsp

中文:
引理 isRootSystem_mk''
  条件: (h_int : 对任意 i j, 存在 z : 整数, z = p (root i) (coroot j))
  证明: hsp
  span_coroot_eq_top :=
    have _i : (mk'' p root coroot hp hs hsp).IsCrystallographic := ⟨h_int⟩
    have _i : Fintype ι := Fintype.ofFinite ι
    (rootSpan_eq_top_iff _).mp hsp
-/
lemma isRootSystem_mk'' (h_int : forall i j, exists z : Int, z = p (root i) (coroot j)) :
    (mk'' p root coroot hp hs hsp).IsRootSystem where
  span_root_eq_top := hsp
  span_coroot_eq_top :=
    have _i : (mk'' p root coroot hp hs hsp).IsCrystallographic := ⟨h_int⟩
    have _i : Fintype ι := Fintype.ofFinite ι
    (rootSpan_eq_top_iff _).mp hsp

end

end RootPairing
