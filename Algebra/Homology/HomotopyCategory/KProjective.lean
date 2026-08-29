/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.CochainComplexOpposite

/-!
# K-projective cochain complexes

We define the notion of K-projective cochain complex in an abelian category,
and show that bounded above complexes of projective objects are K-projective.

## TODO (@joelriou)
* Provide an API for computing `Ext`-groups using a projective resolution

## References
* [N. Spaltenstein, *Resolutions of unbounded complexes*][spaltenstein1998]

-/

@[expose] public section

open CategoryTheory Limits Preadditive Opposite

namespace CochainComplex

open HomComplex

variable {C : Type*} [Category* C] [Abelian C]

-- TODO (@joelriou): show that this definition is equivalent to the
-- original definition by Spaltenstein saying that whenever `L`
-- is acyclic, then `HomComplex K L` is acyclic. (The condition below
-- is equivalent to the acyclicity of `HomComplex K L` in degree
-- `0`, and the general case follows by shifting `L`.)
/--
Definition of `IsKProjective` / `IsKProjective` 的定义

English:
class IsKProjective
  parameters: (K : CochainComplex C Int)
  axioms and operations (1):
    - nonempty_homotopy_zero({L : CochainComplex C Int} (f : K ⟶ L)) : L.Acyclic -> Nonempty (Homotopy f 0)

中文:
类 是KProjective
  参数: (K : 上链复形 C 整数)
  公理与运算 (1 个):
    - nonempty_homotopy_zero({L : 上链复形 C 整数} (f : K ⟶ L)) : L.非循环 -> 非空 (同伦 f 0)

Depends on / 依赖: IsKProjective, IsKProjective.nonempty_homotopy_zero, nonempty_homotopy_zero
-/
class IsKProjective (K : CochainComplex C Int) : Prop where
  nonempty_homotopy_zero {L : CochainComplex C Int} (f : K ⟶ L) :
    L.Acyclic -> Nonempty (Homotopy f 0)

/-- A choice of homotopy to zero for a morphism from a
K-projective cochain complex to an acyclic cochain complex. -/
noncomputable irreducible_def IsKProjective.homotopyZero
    {K L : CochainComplex C Int} (f : K ⟶ L)
    (hL : L.Acyclic) [K.IsKProjective] :
    Homotopy f 0 :=
  (IsKProjective.nonempty_homotopy_zero f hL).some

/--
lemma `_root_.HomotopyEquiv.isKProjective` / 引理 `_root_.HomotopyEquiv.isKProjective`

English:
lemma _root_.HomotopyEquiv.isKProjective
  statement: {K₁ K₂ : CochainComplex C Int}
  proof: ⟨Homotopy.trans (Homotopy.trans (.ofEq (by simp))
      ((e.homotopyInvHomId.symm.compRight f).trans (.ofEq (by simp))))
        (((IsKProjective.homotopyZero (e.hom ≫ f) hL).compLeft e.inv).trans (.ofEq (by simp)))⟩

中文:
引理 _root_.同伦等价.isKProjective
  结论: {K₁ K₂ : 上链复形 C 整数}
  证明: ⟨Homotopy.trans (Homotopy.trans (.ofEq (by simp))
      ((e.homotopyInvHomId.symm.compRight f).trans (.ofEq (by simp))))
        (((IsKProjective.homotopyZero (e.hom ≫ f) hL).compLeft e.inv).trans (.ofEq (by simp)))⟩

Depends on / 依赖: Homotopy, Homotopy.trans, IsKProjective, IsKProjective.homotopyZero, compLeft, compRight, e.hom, e.homotopyInvHomId.symm.compRight, e.inv, homotopyInvHomId, homotopyZero
-/
lemma _root_.HomotopyEquiv.isKProjective {K₁ K₂ : CochainComplex C Int}
    (e : HomotopyEquiv K₁ K₂)
    [K₁.IsKProjective] : K₂.IsKProjective where
  nonempty_homotopy_zero {L} f hL :=
    ⟨Homotopy.trans (Homotopy.trans (.ofEq (by simp))
      ((e.homotopyInvHomId.symm.compRight f).trans (.ofEq (by simp))))
        (((IsKProjective.homotopyZero (e.hom ≫ f) hL).compLeft e.inv).trans (.ofEq (by simp)))⟩

/--
lemma `isKProjective_of_iso` / 引理 `isKProjective_of_iso`

English:
lemma isKProjective_of_iso
  statement: {K₁ K₂ : CochainComplex C Int} (e : K₁ ≅ K₂)
  proof: (HomotopyEquiv.ofIso e).isKProjective

中文:
引理 isKProjective_of_iso
  结论: {K₁ K₂ : 上链复形 C 整数} (e : K₁ ≅ K₂)
  证明: (HomotopyEquiv.ofIso e).isKProjective

Depends on / 依赖: HomotopyEquiv, HomotopyEquiv.ofIso, isKProjective
-/
lemma isKProjective_of_iso {K₁ K₂ : CochainComplex C Int} (e : K₁ ≅ K₂)
    [K₁.IsKProjective] :
    K₂.IsKProjective :=
  (HomotopyEquiv.ofIso e).isKProjective

/--
lemma `isKProjective_iff_of_iso` / 引理 `isKProjective_iff_of_iso`

English:
lemma isKProjective_iff_of_iso
  given: {K₁ K₂ : CochainComplex C Int} (e : K₁ ≅ K₂)
  proof: ⟨fun _ => isKProjective_of_iso e, fun _ => isKProjective_of_iso e.symm⟩

中文:
引理 isKProjective_iff_of_iso
  条件: {K₁ K₂ : 上链复形 C 整数} (e : K₁ ≅ K₂)
  证明: ⟨fun _ => isKProjective_of_iso e, fun _ => isKProjective_of_iso e.symm⟩

Depends on / 依赖: e.symm, isKProjective_of_iso
-/
lemma isKProjective_iff_of_iso {K₁ K₂ : CochainComplex C Int} (e : K₁ ≅ K₂) :
    K₁.IsKProjective ↔ K₂.IsKProjective :=
  ⟨fun _ => isKProjective_of_iso e, fun _ => isKProjective_of_iso e.symm⟩

/--
lemma `isKProjective_iff_leftOrthogonal` / 引理 `isKProjective_iff_leftOrthogonal`

English:
lemma isKProjective_iff_leftOrthogonal
  given: (K : CochainComplex C Int)
  proof: by
  refine ⟨fun _ L f hL => ?_,
      fun hK => ⟨fun {L} f hL => ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAc

中文:
引理 isKProjective_iff_leftOrthogonal
  条件: (K : 上链复形 C 整数)
  证明: by
  refine ⟨fun _ L f hL => ?_,
      fun hK => ⟨fun {L} f hL => ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAc

Depends on / 依赖: Functor, Functor.map_zero, Homoto, HomotopyCategory, HomotopyCategory.eq_of_homotopy, HomotopyCategory.homotopyOfEq, HomotopyCategory.quotient, HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic, HomotopyCategory.quotient_obj_surjective, IsKProjective, IsKProjective.homotopyZero, eq_of_homotopy, homotopyOfEq, homotopyZero, map_surjective, map_zero, quotient, quotient_obj_mem_subcategoryAcyclic_iff_acyclic, quotient_obj_surjective
-/
lemma isKProjective_iff_leftOrthogonal (K : CochainComplex C Int) :
    K.IsKProjective ↔
      (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal
        ((HomotopyCategory.quotient _ _).obj K) := by
  refine ⟨fun _ L f hL => ?_,
      fun hK => ⟨fun {L} f hL => ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
    rw [HomotopyCategory.eq_of_homotopy f 0 (IsKProjective.homotopyZero f hL)]; rw [Functor.map_zero]
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
    rw [hK ((HomotopyCategory.quotient _ _).map f) hL]; rw [Functor.map_zero]

/--
lemma `IsKProjective.leftOrthogonal` / 引理 `IsKProjective.leftOrthogonal`

English:
lemma IsKProjective.leftOrthogonal
  given: (K : CochainComplex C Int) [K.IsKProjective]
  proof: by
  rwa [← isKProjective_iff_leftOrthogonal]

中文:
引理 是KProjective.leftOrthogonal
  条件: (K : 上链复形 C 整数) [K.是KProjective]
  证明: by
  rwa [← isKProjective_iff_leftOrthogonal]

Depends on / 依赖: isKProjective_iff_leftOrthogonal
-/
lemma IsKProjective.leftOrthogonal (K : CochainComplex C Int) [K.IsKProjective] :
    (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal
        ((HomotopyCategory.quotient _ _).obj K) := by
  rwa [← isKProjective_iff_leftOrthogonal]

instance (K : CochainComplex C Int) [hK : K.IsKProjective] (n : Int) :
    (K⟦n⟧).IsKProjective := by
  rw [isKProjective_iff_leftOrthogonal] at hK ⊢
  exact ObjectProperty.prop_of_iso _
    (((HomotopyCategory.quotient C (.up Int)).commShiftIso n).symm.app K)
    ((HomotopyCategory.subcategoryAcyclic C).leftOrthogonal.le_shift n _ hK)

/--
lemma `isKProjective_shift_iff` / 引理 `isKProjective_shift_iff`

English:
lemma isKProjective_shift_iff
  given: (K : CochainComplex C Int) (n : Int)
  proof: ⟨fun _ => isKProjective_of_iso (show K⟦n⟧⟦-n⟧ ≅ K from (shiftEquiv _ n).unitIso.symm.app K),
    fun _ => inferInstance⟩

中文:
引理 isKProjective_shift_iff
  条件: (K : 上链复形 C 整数) (n : 整数)
  证明: ⟨fun _ => isKProjective_of_iso (show K⟦n⟧⟦-n⟧ ≅ K from (shiftEquiv _ n).unitIso.symm.app K),
    fun _ => inferInstance⟩

Depends on / 依赖: isKProjective_of_iso, shiftEquiv, unitIso, unitIso.symm.app
-/
lemma isKProjective_shift_iff (K : CochainComplex C Int) (n : Int) :
    (K⟦n⟧).IsKProjective ↔ K.IsKProjective :=
  ⟨fun _ => isKProjective_of_iso (show K⟦n⟧⟦-n⟧ ≅ K from (shiftEquiv _ n).unitIso.symm.app K),
    fun _ => inferInstance⟩

/--
lemma `isKProjective_of_op` / 引理 `isKProjective_of_op`

English:
lemma isKProjective_of_op
  statement: {K : CochainComplex C Int}
  proof: ⟨homotopyUnop ((IsKInjective.homotopyZero
      ((opEquivalence C).functor.map f.op) (acyclic_op hL)).trans
        (.ofEq (by simp)))⟩

中文:
引理 isKProjective_of_op
  结论: {K : 上链复形 C 整数}
  证明: ⟨homotopyUnop ((IsKInjective.homotopyZero
      ((opEquivalence C).functor.map f.op) (acyclic_op hL)).trans
        (.ofEq (by simp)))⟩

Depends on / 依赖: IsKInjective, IsKInjective.homotopyZero, acyclic_op, f.op, functor, functor.map, homotopyUnop, homotopyZero, opEquivalence
-/
lemma isKProjective_of_op {K : CochainComplex C Int}
    (hK : IsKInjective ((opEquivalence C).functor.obj (op K))) :
    K.IsKProjective where
  nonempty_homotopy_zero {L} f hL :=
    ⟨homotopyUnop ((IsKInjective.homotopyZero
      ((opEquivalence C).functor.map f.op) (acyclic_op hL)).trans
        (.ofEq (by simp)))⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] opEquivalence ChainComplex.cochainComplexEquivalence in
open Cochain.InductionUp in
/--
lemma `isKProjective_of_projective` / 引理 `isKProjective_of_projective`

English:
lemma isKProjective_of_projective
  statement: (K : CochainComplex C Int) (d : Int)
  proof: by
  let L := ((opEquivalence C).functor.obj (op K))
  have (n : Int) : Injective (L.X n) := by
    dsimp [L]
    infer_instance
  have : L.IsStrictlyGE (-d) := by
    rw [isStrictlyGE_iff]
    intro i hi
    exact (K.isZero_of_isStrictlyLE d _ (by dsimp; lia)).op
  exact isKProjective_of_op (isKInj

中文:
引理 isKProjective_of_projective
  结论: (K : 上链复形 C 整数) (d : 整数)
  证明: by
  let L := ((opEquivalence C).functor.obj (op K))
  have (n : Int) : Injective (L.X n) := by
    dsimp [L]
    infer_instance
  have : L.IsStrictlyGE (-d) := by
    rw [isStrictlyGE_iff]
    intro i hi
    exact (K.isZero_of_isStrictlyLE d _ (by dsimp; lia)).op
  exact isKProjective_of_op (isKInj

Depends on / 依赖: Injective, IsStrictlyGE, K.isZero_of_isStrictlyLE, L.IsStrictlyGE, functor, functor.obj, infer_instance, isKInjective_of_injective, isKProjective_of_op, isStrictlyGE_iff, isZero_of_isStrictlyLE, opEquivalence
-/
lemma isKProjective_of_projective (K : CochainComplex C Int) (d : Int)
    [K.IsStrictlyLE d] [forall (n : Int), Projective (K.X n)] :
    K.IsKProjective := by
  let L := ((opEquivalence C).functor.obj (op K))
  have (n : Int) : Injective (L.X n) := by
    dsimp [L]
    infer_instance
  have : L.IsStrictlyGE (-d) := by
    rw [isStrictlyGE_iff]
    intro i hi
    exact (K.isZero_of_isStrictlyLE d _ (by dsimp; lia)).op
  exact isKProjective_of_op (isKInjective_of_injective L (-d))

instance (K : ChainComplex C Nat) [forall n, Projective (K.X n)] :
    CochainComplex.IsKProjective (K.extend ComplexShape.embeddingDownNat) :=
  CochainComplex.isKProjective_of_projective _ 0

end CochainComplex
