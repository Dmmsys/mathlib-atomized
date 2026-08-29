/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Topology.Sheaves.Forget
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# The sheaf condition in terms of unique gluings

We provide an alternative formulation of the sheaf condition in terms of unique gluings.

We work with sheaves valued in a concrete category `C` admitting all limits, whose forgetful
functor `C ⥤ Type` preserves limits and reflects isomorphisms. The usual categories of algebraic
structures, such as `MonCat`, `AddCommGrpCat`, `RingCat`, `CommRingCat` etc. are all examples of
this kind of category.

A presheaf `F : Presheaf C X` satisfies the sheaf condition if and only if, for every
compatible family of sections `sf : Π i : ι, F.obj (op (U i))`, there exists a unique gluing
`s : F.obj (op (iSup U))`.

Here, the family `sf` is called compatible, if for all `i j : ι`, the restrictions of `sf i`
and `sf j` to `U i ⊓ U j` agree. A section `s : F.obj (op (iSup U))` is a gluing for the
family `sf`, if `s` restricts to `sf i` on `U i` for all `i : ι`

We show that the sheaf condition in terms of unique gluings is equivalent to the definition
in terms of pairwise intersections. Our approach is as follows: First, we show them to be equivalent
for `Type`-valued presheaves. Then we use that composing a presheaf with a limit-preserving and
isomorphism-reflecting functor leaves the sheaf condition invariant, as shown in
`Mathlib/Topology/Sheaves/Forget.lean`.

-/

@[expose] public section

noncomputable section

open TopCat TopCat.Presheaf CategoryTheory CategoryTheory.Limits
  TopologicalSpace TopologicalSpace.Opens Opposite

universe x

variable {C : Type*} [Category* C] {FC : C -> C -> Type*} {CC : C -> Type*}
variable [forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

namespace TopCat

namespace Presheaf

section

variable {X : TopCat.{x}} (F : Presheaf C X) {ι : Type*} (U : ι -> Opens X)

/--
Definition of `IsCompatible` / `IsCompatible` 的定义

English:
definition IsCompatible
  signature: (sf : forall i : ι, ToType (F.obj (op (U i))))
  body: forall i j : ι, F.map (infLELeft (U i) (U j)).op (sf i) = F.map (infLERight (U i) (U j)).op (sf j)

中文:
定义 IsCompatible
  签名: (sf : 对任意 i : ι, ToType (F.obj (op (U i))))
  定义体: forall i j : ι, F.map (infLELeft (U i) (U j)).op (sf i) = F.map (infLERight (U i) (U j)).op (sf j)

Depends on / 依赖: F.map, infLELeft, infLERight
-/
def IsCompatible (sf : forall i : ι, ToType (F.obj (op (U i)))) : Prop :=
  forall i j : ι, F.map (infLELeft (U i) (U j)).op (sf i) = F.map (infLERight (U i) (U j)).op (sf j)

/--
Definition of `IsGluing` / `IsGluing` 的定义

English:
definition IsGluing
  signature: (sf : forall i : ι, ToType (F.obj (op (U i)))) (s : ToType (F.obj (op (iSup U))))
  body: forall i : ι, F.map (Opens.leSupr U i).op s = sf i

中文:
定义 IsGluing
  签名: (sf : 对任意 i : ι, ToType (F.obj (op (U i)))) (s : ToType (F.obj (op (iSup U))))
  定义体: forall i : ι, F.map (Opens.leSupr U i).op s = sf i

Depends on / 依赖: F.map, Opens.leSupr, leSupr
-/
def IsGluing (sf : forall i : ι, ToType (F.obj (op (U i)))) (s : ToType (F.obj (op (iSup U)))) : Prop :=
  forall i : ι, F.map (Opens.leSupr U i).op s = sf i

/--
Definition of `IsSheafUniqueGluing` / `IsSheafUniqueGluing` 的定义

English:
definition IsSheafUniqueGluing
  signature: : Prop
  body: forall ⦃ι : Type x⦄ (U : ι -> Opens X) (sf : forall i : ι, ToType (F.obj (op (U i)))),
    IsCompatible F U sf -> exists! s : ToType (F.obj (op (iSup U))), IsGluing F U sf s

中文:
定义 IsSheafUniqueGluing
  签名: : 命题
  定义体: forall ⦃ι : Type x⦄ (U : ι -> Opens X) (sf : forall i : ι, ToType (F.obj (op (U i)))),
    IsCompatible F U sf -> exists! s : ToType (F.obj (op (iSup U))), IsGluing F U sf s

Depends on / 依赖: F.obj, IsCompatible, IsGluing, ToType
-/
def IsSheafUniqueGluing : Prop :=
  forall ⦃ι : Type x⦄ (U : ι -> Opens X) (sf : forall i : ι, ToType (F.obj (op (U i)))),
    IsCompatible F U sf -> exists! s : ToType (F.obj (op (iSup U))), IsGluing F U sf s

end

section TypeValued

variable {X : TopCat.{x}} {F : Presheaf Type* X} {ι : Type*} {U : ι -> Opens X}

/--
Definition of `objPairwiseOfFamily` / `objPairwiseOfFamily` 的定义

English:
definition objPairwiseOfFamily
  signature: (sf : forall i, F.obj (op (U i)))

中文:
定义 objPairwiseOfFamily
  签名: (sf : 对任意 i, F.obj (op (U i)))
-/
def objPairwiseOfFamily (sf : forall i, F.obj (op (U i))) :
    forall i, ((Pairwise.diagram U).op ⋙ F).obj i
  | ⟨Pairwise.single i⟩ => sf i
  | ⟨Pairwise.pair i j⟩ => F.map (infLELeft (U i) (U j)).op (sf i)

/--
Definition of `IsCompatible.sectionPairwise` / `IsCompatible.sectionPairwise` 的定义

English:
definition IsCompatible.sectionPairwise
  signature: {sf} (h : IsCompatible F U sf)
  body: by
  refine ⟨objPairwiseOfFamily sf, ?_⟩
  let G := (Pairwise.diagram U).op ⋙ F
  rintro (i | ⟨i, j⟩) (i' | ⟨i', j'⟩) (_ | _ | _ | _)
  · exact ConcreteCategory.congr_hom (G.map_id <| op <| Pairwise.single i) _
  · rfl
  · exact (h i' i).symm
  · exact ConcreteCategory.congr_hom (G.map_id <| op <| Pairwise.pair i j) _

中文:
定义 IsCompatible.sectionPairwise
  签名: {sf} (h : IsCompatible F U sf)
  定义体: by
  refine ⟨objPairwiseOfFamily sf, ?_⟩
  let G := (Pairwise.diagram U).op ⋙ F
  rintro (i | ⟨i, j⟩) (i' | ⟨i', j'⟩) (_ | _ | _ | _)
  · exact ConcreteCategory.congr_hom (G.map_id <| op <| Pairwise.single i) _
  · rfl
  · exact (h i' i).symm
  · exact ConcreteCategory.congr_hom (G.map_id <| op <| Pairwise.pair i j) _

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, G.map_id, Pairwise, Pairwise.diagram, Pairwise.pair, Pairwise.single, congr_hom, diagram, map_id, objPairwiseOfFamily, single
-/
def IsCompatible.sectionPairwise {sf} (h : IsCompatible F U sf) :
    ((Pairwise.diagram U).op ⋙ F).sections := by
  refine ⟨objPairwiseOfFamily sf, ?_⟩
  let G := (Pairwise.diagram U).op ⋙ F
  rintro (i | ⟨i, j⟩) (i' | ⟨i', j'⟩) (_ | _ | _ | _)
  · exact ConcreteCategory.congr_hom (G.map_id <| op <| Pairwise.single i) _
  · rfl
  · exact (h i' i).symm
  · exact ConcreteCategory.congr_hom (G.map_id <| op <| Pairwise.pair i j) _

/--
theorem `isGluing_iff_pairwise` / 定理 `isGluing_iff_pairwise`

English:
theorem isGluing_iff_pairwise
  given: {sf s}
  statement: IsGluing F U sf s ↔
  proof: by
  refine ⟨fun h => ?_, fun h i => h (op <| Pairwise.single i)⟩
  rintro (i | ⟨i, j⟩)
  · exact h i
  · rw [← (F.mapCone (Pairwise.cocone U).op).w (op <| Pairwise.Hom.left i j)]
    exact congr_arg _ (h i)

中文:
定理 isGluing_iff_pairwise
  条件: {sf s}
  结论: IsGluing F U sf s ↔
  证明: by
  refine ⟨fun h => ?_, fun h i => h (op <| Pairwise.single i)⟩
  rintro (i | ⟨i, j⟩)
  · exact h i
  · rw [← (F.mapCone (Pairwise.cocone U).op).w (op <| Pairwise.Hom.left i j)]
    exact congr_arg _ (h i)

Depends on / 依赖: F.mapCone, Pairwise, Pairwise.Hom.left, Pairwise.cocone, Pairwise.single, cocone, congr_arg, mapCone, single
-/
theorem isGluing_iff_pairwise {sf s} : IsGluing F U sf s ↔
    forall i, (F.mapCone (Pairwise.cocone U).op).π.app i s = objPairwiseOfFamily sf i := by
  refine ⟨fun h => ?_, fun h i => h (op <| Pairwise.single i)⟩
  rintro (i | ⟨i, j⟩)
  · exact h i
  · rw [← (F.mapCone (Pairwise.cocone U).op).w (op <| Pairwise.Hom.left i j)]
    exact congr_arg _ (h i)

/--
theorem `IsSheaf.isSheafUniqueGluing_types` / 定理 `IsSheaf.isSheafUniqueGluing_types`

English:
theorem IsSheaf.isSheafUniqueGluing_types
  statement: (h : F.IsSheaf) (sf : forall i : ι, F.obj (op (U i)))
  proof: by
  simp_rw [isGluing_iff_pairwise]
  exact (Types.isLimit_iff _).mp (h.isSheafPairwiseIntersections U) _ cpt.sectionPairwise.prop

中文:
定理 是层.isSheafUniqueGluing_types
  结论: (h : F.是层) (sf : 对任意 i : ι, F.obj (op (U i)))
  证明: by
  simp_rw [isGluing_iff_pairwise]
  exact (Types.isLimit_iff _).mp (h.isSheafPairwiseIntersections U) _ cpt.sectionPairwise.prop

Depends on / 依赖: Types.isLimit_iff, cpt.sectionPairwise.prop, h.isSheafPairwiseIntersections, isGluing_iff_pairwise, isLimit_iff, isSheafPairwiseIntersections, sectionPairwise, simp_rw
-/
theorem IsSheaf.isSheafUniqueGluing_types (h : F.IsSheaf) (sf : forall i : ι, F.obj (op (U i)))
    (cpt : IsCompatible F U sf) : exists! s : F.obj (op (iSup U)), IsGluing F U sf s := by
  simp_rw [isGluing_iff_pairwise]
  exact (Types.isLimit_iff _).mp (h.isSheafPairwiseIntersections U) _ cpt.sectionPairwise.prop

variable (F)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isSheaf_iff_isSheafUniqueGluing_types` / 定理 `isSheaf_iff_isSheafUniqueGluing_types`

English:
theorem isSheaf_iff_isSheafUniqueGluing_types
  statement: F.IsSheaf ↔ F.IsSheafUniqueGluing
  proof: by
  simp_rw [isSheaf_iff_isSheafPairwiseIntersections, IsSheafPairwiseIntersections,
    Types.isLimit_iff, IsSheafUniqueGluing, isGluing_iff_pairwise]
  refine forall₂_congr fun ι U => ⟨fun h sf cpt => ?_, fun h s hs => ?_⟩
  · exact h _ cpt.sectionPairwise.prop
  · specialize h (fun i => s <| op <| Pairwise.single i) fun i j =>
      (hs <| op <| Pairwise.Hom.left i j).trans (hs <| op <| Pairwise.Hom.right i j).symm
    convert! h; ext (i | ⟨i, j⟩)
    · rfl
    · exact (hs <| op <| Pairwise.Hom.left i j).symm

中文:
定理 isSheaf_iff_isSheafUniqueGluing_types
  结论: F.是层 ↔ F.IsSheafUniqueGluing
  证明: by
  simp_rw [isSheaf_iff_isSheafPairwiseIntersections, IsSheafPairwiseIntersections,
    Types.isLimit_iff, IsSheafUniqueGluing, isGluing_iff_pairwise]
  refine forall₂_congr fun ι U => ⟨fun h sf cpt => ?_, fun h s hs => ?_⟩
  · exact h _ cpt.sectionPairwise.prop
  · specialize h (fun i => s <| op <| Pairwise.single i) fun i j =>
      (hs <| op <| Pairwise.Hom.left i j).trans (hs <| op <| Pairwise.Hom.right i j).symm
    convert! h; ext (i | ⟨i, j⟩)
    · rfl
    · exact (hs <| op <| Pairwise.Hom.left i j).symm

Depends on / 依赖: IsSheafPairwiseIntersections, IsSheafUniqueGluing, Pairwise, Pairwise.Hom.left, Pairwise.Hom.right, Pairwise.single, Types.isLimit_iff, convert, cpt.sectionPairwise.prop, isGluing_iff_pairwise, isLimit_iff, isSheaf_iff_isSheafPairwiseIntersections, sectionPairwise, simp_rw, single, specialize
-/
theorem isSheaf_iff_isSheafUniqueGluing_types : F.IsSheaf ↔ F.IsSheafUniqueGluing := by
  simp_rw [isSheaf_iff_isSheafPairwiseIntersections, IsSheafPairwiseIntersections,
    Types.isLimit_iff, IsSheafUniqueGluing, isGluing_iff_pairwise]
  refine forall₂_congr fun ι U => ⟨fun h sf cpt => ?_, fun h s hs => ?_⟩
  · exact h _ cpt.sectionPairwise.prop
  · specialize h (fun i => s <| op <| Pairwise.single i) fun i j =>
      (hs <| op <| Pairwise.Hom.left i j).trans (hs <| op <| Pairwise.Hom.right i j).symm
    convert! h; ext (i | ⟨i, j⟩)
    · rfl
    · exact (hs <| op <| Pairwise.Hom.left i j).symm

/--
theorem `isSheaf_of_isSheafUniqueGluing_types` / 定理 `isSheaf_of_isSheafUniqueGluing_types`

English:
theorem isSheaf_of_isSheafUniqueGluing_types
  given: (Fsh : F.IsSheafUniqueGluing)
  statement: F.IsSheaf
  proof: (isSheaf_iff_isSheafUniqueGluing_types F).mpr Fsh

中文:
定理 isSheaf_of_isSheafUniqueGluing_types
  条件: (Fsh : F.IsSheafUniqueGluing)
  结论: F.是层
  证明: (isSheaf_iff_isSheafUniqueGluing_types F).mpr Fsh

Depends on / 依赖: isSheaf_iff_isSheafUniqueGluing_types
-/
theorem isSheaf_of_isSheafUniqueGluing_types (Fsh : F.IsSheafUniqueGluing) : F.IsSheaf :=
  (isSheaf_iff_isSheafUniqueGluing_types F).mpr Fsh

end TypeValued

section

variable [HasLimitsOfSize.{x, x} C] [(forget C).ReflectsIsomorphisms]
  [PreservesLimitsOfSize.{x, x} (forget C)]
variable {X : TopCat.{x}} {F : Presheaf C X}

/--
theorem `IsSheaf.isSheafUniqueGluing` / 定理 `IsSheaf.isSheafUniqueGluing`

English:
theorem IsSheaf.isSheafUniqueGluing
  statement: (h : F.IsSheaf) {ι : Type*} (U : ι -> Opens X)
  proof: ((isSheaf_iff_isSheaf_comp' (forget C) F).mp h).isSheafUniqueGluing_types sf cpt

中文:
定理 是层.isSheafUniqueGluing
  结论: (h : F.是层) {ι : 类型} (U : ι -> Opens X)
  证明: ((isSheaf_iff_isSheaf_comp' (forget C) F).mp h).isSheafUniqueGluing_types sf cpt

Depends on / 依赖: forget, isSheafUniqueGluing_types, isSheaf_iff_isSheaf_comp
-/
theorem IsSheaf.isSheafUniqueGluing (h : F.IsSheaf) {ι : Type*} (U : ι -> Opens X)
    (sf : forall i : ι, ToType (F.obj (op (U i))))
    (cpt : IsCompatible F U sf) : exists! s : ToType (F.obj (op (iSup U))), IsGluing F U sf s :=
  ((isSheaf_iff_isSheaf_comp' (forget C) F).mp h).isSheafUniqueGluing_types sf cpt

variable (F)

/--
theorem `isSheaf_iff_isSheafUniqueGluing` / 定理 `isSheaf_iff_isSheafUniqueGluing`

English:
theorem isSheaf_iff_isSheafUniqueGluing
  statement: F.IsSheaf ↔ F.IsSheafUniqueGluing
  proof: Iff.trans (isSheaf_iff_isSheaf_comp' (forget C) F)
    (isSheaf_iff_isSheafUniqueGluing_types (F ⋙ forget C))

中文:
定理 isSheaf_iff_isSheafUniqueGluing
  结论: F.是层 ↔ F.IsSheafUniqueGluing
  证明: Iff.trans (isSheaf_iff_isSheaf_comp' (forget C) F)
    (isSheaf_iff_isSheafUniqueGluing_types (F ⋙ forget C))

Depends on / 依赖: Iff.trans, forget, isSheaf_iff_isSheafUniqueGluing_types, isSheaf_iff_isSheaf_comp
-/
theorem isSheaf_iff_isSheafUniqueGluing : F.IsSheaf ↔ F.IsSheafUniqueGluing :=
  Iff.trans (isSheaf_iff_isSheaf_comp' (forget C) F)
    (isSheaf_iff_isSheafUniqueGluing_types (F ⋙ forget C))

end

end Presheaf

namespace Sheaf

open Presheaf CategoryTheory

section

variable [HasLimitsOfSize.{x, x} C] [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [PreservesLimitsOfSize.{x, x} (CategoryTheory.forget C)]
variable {X : TopCat.{x}} (F : Sheaf C X) {ι : Type*} (U : ι -> Opens X)

/--
theorem `existsUnique_gluing` / 定理 `existsUnique_gluing`

English:
theorem existsUnique_gluing
  statement: (sf : forall i : ι, ToType (F.1.obj (op (U i))))
  proof: IsSheaf.isSheafUniqueGluing F.property U sf h

中文:
定理 存在Unique_gluing
  结论: (sf : 对任意 i : ι, ToType (F.1.obj (op (U i))))
  证明: IsSheaf.isSheafUniqueGluing F.property U sf h

Depends on / 依赖: F.property, IsSheaf, IsSheaf.isSheafUniqueGluing, isSheafUniqueGluing, property
-/
theorem existsUnique_gluing (sf : forall i : ι, ToType (F.1.obj (op (U i))))
    (h : IsCompatible F.1 U sf) :
    exists! s : ToType (F.1.obj (op (iSup U))), IsGluing F.1 U sf s :=
  IsSheaf.isSheafUniqueGluing F.property U sf h

/--
theorem `existsUnique_gluing'` / 定理 `existsUnique_gluing'`

English:
theorem existsUnique_gluing'
  statement: (V : Opens X) (iUV : forall i : ι, U i ⟶ V) (hcover : V <= iSup U)
  proof: by
  have V_eq_supr_U : V = iSup U := le_antisymm hcover (iSup_le fun i => (iUV i).le)
  obtain ⟨gl, gl_spec, gl_uniq⟩ := F.existsUnique_gluing U sf h
  refine ⟨F.1.map (eqToHom V_eq_supr_U).op gl, ?_, ?_⟩
  · intro i
    rw [← ConcreteCategory.comp_apply]; rw [← F.1.map_comp]
    exact gl_spec i
  · intro gl' gl'_spec
    convert! congr_arg _ (gl_uniq (F.1.map (eqToHom V_eq_supr_U.symm).op gl') fun i => _) <;>
      rw [← ConcreteCategory.comp_apply]; rw [← F.1.map_comp]
    · simp
    · exact gl'_spec i

@[ext]

中文:
定理 存在Unique_gluing'
  结论: (V : Opens X) (iUV : 对任意 i : ι, U i ⟶ V) (hcover : V <= iSup U)
  证明: by
  have V_eq_supr_U : V = iSup U := le_antisymm hcover (iSup_le fun i => (iUV i).le)
  obtain ⟨gl, gl_spec, gl_uniq⟩ := F.existsUnique_gluing U sf h
  refine ⟨F.1.map (eqToHom V_eq_supr_U).op gl, ?_, ?_⟩
  · intro i
    rw [← ConcreteCategory.comp_apply]; rw [← F.1.map_comp]
    exact gl_spec i
  · intro gl' gl'_spec
    convert! congr_arg _ (gl_uniq (F.1.map (eqToHom V_eq_supr_U.symm).op gl') fun i => _) <;>
      rw [← ConcreteCategory.comp_apply]; rw [← F.1.map_comp]
    · simp
    · exact gl'_spec i

@[ext]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, F.existsUnique_gluing, V_eq_supr_U, V_eq_supr_U.symm, _spec, comp_apply, congr_arg, convert, eqToHom, existsUnique_gluing, gl_spec, gl_uniq, hcover, iSup_le, le_antisymm, map_comp
-/
theorem existsUnique_gluing' (V : Opens X) (iUV : forall i : ι, U i ⟶ V) (hcover : V <= iSup U)
    (sf : forall i : ι, ToType (F.1.obj (op (U i)))) (h : IsCompatible F.1 U sf) :
    exists! s : ToType (F.1.obj (op V)), forall i : ι, F.1.map (iUV i).op s = sf i := by
  have V_eq_supr_U : V = iSup U := le_antisymm hcover (iSup_le fun i => (iUV i).le)
  obtain ⟨gl, gl_spec, gl_uniq⟩ := F.existsUnique_gluing U sf h
  refine ⟨F.1.map (eqToHom V_eq_supr_U).op gl, ?_, ?_⟩
  · intro i
    rw [← ConcreteCategory.comp_apply]; rw [← F.1.map_comp]
    exact gl_spec i
  · intro gl' gl'_spec
    convert! congr_arg _ (gl_uniq (F.1.map (eqToHom V_eq_supr_U.symm).op gl') fun i => _) <;>
      rw [← ConcreteCategory.comp_apply]; rw [← F.1.map_comp]
    · simp
    · exact gl'_spec i

@[ext]
/--
theorem `eq_of_locally_eq` / 定理 `eq_of_locally_eq`

English:
theorem eq_of_locally_eq
  statement: (s t : ToType (F.1.obj (op (iSup U))))
  proof: by
  let sf : forall i : ι, ToType (F.1.obj (op (U i))) := fun i => F.1.map (Opens.leSupr U i).op s
  have sf_compatible : IsCompatible _ U sf := by
    intro i j
    simp_rw [sf, ← ConcreteCategory.comp_apply, ← F.1.map_comp]
    rfl
  obtain ⟨gl, -, gl_uniq⟩ := F.existsUnique_gluing U sf sf_compatible
  trans gl
  · apply gl_uniq
    intro i
    rfl
  · symm
    apply gl_uniq
    intro i
    rw [← h]

中文:
定理 eq_of_locally_eq
  结论: (s t : ToType (F.1.obj (op (iSup U))))
  证明: by
  let sf : forall i : ι, ToType (F.1.obj (op (U i))) := fun i => F.1.map (Opens.leSupr U i).op s
  have sf_compatible : IsCompatible _ U sf := by
    intro i j
    simp_rw [sf, ← ConcreteCategory.comp_apply, ← F.1.map_comp]
    rfl
  obtain ⟨gl, -, gl_uniq⟩ := F.existsUnique_gluing U sf sf_compatible
  trans gl
  · apply gl_uniq
    intro i
    rfl
  · symm
    apply gl_uniq
    intro i
    rw [← h]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, F.existsUnique_gluing, IsCompatible, Opens.leSupr, ToType, comp_apply, existsUnique_gluing, gl_uniq, leSupr, map_comp, sf_compatible, simp_rw
-/
theorem eq_of_locally_eq (s t : ToType (F.1.obj (op (iSup U))))
    (h : forall i, F.1.map (Opens.leSupr U i).op s = F.1.map (Opens.leSupr U i).op t) : s = t := by
  let sf : forall i : ι, ToType (F.1.obj (op (U i))) := fun i => F.1.map (Opens.leSupr U i).op s
  have sf_compatible : IsCompatible _ U sf := by
    intro i j
    simp_rw [sf, ← ConcreteCategory.comp_apply, ← F.1.map_comp]
    rfl
  obtain ⟨gl, -, gl_uniq⟩ := F.existsUnique_gluing U sf sf_compatible
  trans gl
  · apply gl_uniq
    intro i
    rfl
  · symm
    apply gl_uniq
    intro i
    rw [← h]

/--
theorem `eq_of_locally_eq'` / 定理 `eq_of_locally_eq'`

English:
theorem eq_of_locally_eq'
  statement: (V : Opens X) (iUV : forall i : ι, U i ⟶ V) (hcover : V <= iSup U)
  proof: by
  have V_eq_supr_U : V = iSup U := le_antisymm hcover (iSup_le fun i => (iUV i).le)
  suffices F.1.map (eqToHom V_eq_supr_U.symm).op s = F.1.map (eqToHom V_eq_supr_U.symm).op t by
    convert! congr_arg (F.1.map (eqToHom V_eq_supr_U).op) this <;>
    rw [← ConcreteCategory.comp_apply]; rw [← F.1.map_comp]; rw [eqToHom_op]; rw [eqToHom_op]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [F.1.map_id]; rw [ConcreteCategory.id_apply]
  apply eq_of_locally_eq
  intro i
  rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [← F.1.map_comp]
  exact h i

中文:
定理 eq_of_locally_eq'
  结论: (V : Opens X) (iUV : 对任意 i : ι, U i ⟶ V) (hcover : V <= iSup U)
  证明: by
  have V_eq_supr_U : V = iSup U := le_antisymm hcover (iSup_le fun i => (iUV i).le)
  suffices F.1.map (eqToHom V_eq_supr_U.symm).op s = F.1.map (eqToHom V_eq_supr_U.symm).op t by
    convert! congr_arg (F.1.map (eqToHom V_eq_supr_U).op) this <;>
    rw [← ConcreteCategory.comp_apply]; rw [← F.1.map_comp]; rw [eqToHom_op]; rw [eqToHom_op]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [F.1.map_id]; rw [ConcreteCategory.id_apply]
  apply eq_of_locally_eq
  intro i
  rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [← F.1.map_comp]
  exact h i

Depends on / 依赖: Concret, ConcreteCategory, ConcreteCategory.comp_apply, ConcreteCategory.id_apply, V_eq_supr_U, V_eq_supr_U.symm, comp_apply, congr_arg, convert, eqToHom, eqToHom_op, eqToHom_refl, eqToHom_trans, eq_of_locally_eq, hcover, iSup_le, id_apply, le_antisymm, map_comp, map_id
-/
theorem eq_of_locally_eq' (V : Opens X) (iUV : forall i : ι, U i ⟶ V) (hcover : V <= iSup U)
    (s t : ToType (F.1.obj (op V))) (h : forall i, F.1.map (iUV i).op s = F.1.map (iUV i).op t) :
    s = t := by
  have V_eq_supr_U : V = iSup U := le_antisymm hcover (iSup_le fun i => (iUV i).le)
  suffices F.1.map (eqToHom V_eq_supr_U.symm).op s = F.1.map (eqToHom V_eq_supr_U.symm).op t by
    convert! congr_arg (F.1.map (eqToHom V_eq_supr_U).op) this <;>
    rw [← ConcreteCategory.comp_apply]; rw [← F.1.map_comp]; rw [eqToHom_op]; rw [eqToHom_op]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [F.1.map_id]; rw [ConcreteCategory.id_apply]
  apply eq_of_locally_eq
  intro i
  rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [← F.1.map_comp]
  exact h i

/--
theorem `eq_of_locally_eq₂` / 定理 `eq_of_locally_eq₂`

English:
theorem eq_of_locally_eq₂
  statement: {U₁ U₂ V : Opens X} (i₁ : U₁ ⟶ V) (i₂ : U₂ ⟶ V) (hcover : V <= U₁ ⊔ U₂)
  proof: by
  fapply F.eq_of_locally_eq' fun t : Bool => if t then U₁ else U₂
  · exact fun i => if h : i then eqToHom (if_pos h) ≫ i₁ else eqToHom (if_neg h) ≫ i₂
  · refine le_trans hcover ?_
    rw [sup_le_iff]
    constructor
    · exact le_iSup (fun t : Bool => if t then U₁ else U₂) true
    · exact le_iSup (fun t : Bool => if t then U₁ else U₂) false
  · rintro ⟨_ | _⟩
    any_goals exact h₁
    any_goals exact h₂

中文:
定理 eq_of_locally_eq₂
  结论: {U₁ U₂ V : Opens X} (i₁ : U₁ ⟶ V) (i₂ : U₂ ⟶ V) (hcover : V <= U₁ ⊔ U₂)
  证明: by
  fapply F.eq_of_locally_eq' fun t : Bool => if t then U₁ else U₂
  · exact fun i => if h : i then eqToHom (if_pos h) ≫ i₁ else eqToHom (if_neg h) ≫ i₂
  · refine le_trans hcover ?_
    rw [sup_le_iff]
    constructor
    · exact le_iSup (fun t : Bool => if t then U₁ else U₂) true
    · exact le_iSup (fun t : Bool => if t then U₁ else U₂) false
  · rintro ⟨_ | _⟩
    any_goals exact h₁
    any_goals exact h₂

Depends on / 依赖: F.eq_of_locally_eq, any_goals, eqToHom, eq_of_locally_eq, fapply, hcover, if_neg, if_pos, le_iSup, le_trans, sup_le_iff
-/
theorem eq_of_locally_eq₂ {U₁ U₂ V : Opens X} (i₁ : U₁ ⟶ V) (i₂ : U₂ ⟶ V) (hcover : V <= U₁ ⊔ U₂)
    (s t : ToType (F.1.obj (op V))) (h₁ : F.1.map i₁.op s = F.1.map i₁.op t)
    (h₂ : F.1.map i₂.op s = F.1.map i₂.op t) : s = t := by
  fapply F.eq_of_locally_eq' fun t : Bool => if t then U₁ else U₂
  · exact fun i => if h : i then eqToHom (if_pos h) ≫ i₁ else eqToHom (if_neg h) ≫ i₂
  · refine le_trans hcover ?_
    rw [sup_le_iff]
    constructor
    · exact le_iSup (fun t : Bool => if t then U₁ else U₂) true
    · exact le_iSup (fun t : Bool => if t then U₁ else U₂) false
  · rintro ⟨_ | _⟩
    any_goals exact h₁
    any_goals exact h₂

variable {F} {U} in
/--
theorem `eq_app_of_locally_eq` / 定理 `eq_app_of_locally_eq`

English:
theorem eq_app_of_locally_eq
  statement: {V : Opens X} {G : Sheaf C X} {f : F ⟶ G}
  proof: by
  refine eq_of_locally_eq G U _ _ (fun _ => ?_)
  rw [← NatTrans.naturality_apply]; rw [h]; rw [ht]; rw [← ConcreteCategory.comp_apply]; rw [← Functor.map_comp]
  rfl

中文:
定理 eq_app_of_locally_eq
  结论: {V : Opens X} {G : 层 C X} {f : F ⟶ G}
  证明: by
  refine eq_of_locally_eq G U _ _ (fun _ => ?_)
  rw [← NatTrans.naturality_apply]; rw [h]; rw [ht]; rw [← ConcreteCategory.comp_apply]; rw [← Functor.map_comp]
  rfl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, Functor, Functor.map_comp, NatTrans, NatTrans.naturality_apply, comp_apply, eq_of_locally_eq, map_comp, naturality_apply
-/
theorem eq_app_of_locally_eq {V : Opens X} {G : Sheaf C X} {f : F ⟶ G}
    {s : ToType (F.1.obj (op (iSup U)))} {t : ToType (G.1.obj (op V))}
    {sf : forall i : ι, ToType (F.1.obj (op (U i)))} (h : IsGluing F.1 U sf s) (hV : forall i : ι, U i <= V)
    (ht : forall i : ι, f.1.app (op (U i)) (sf i) = G.1.map (homOfLE (hV i)).op t) :
    f.hom.app (op (iSup U)) s = G.obj.map (homOfLE (by aesop_cat)).op t := by
  refine eq_of_locally_eq G U _ _ (fun _ => ?_)
  rw [← NatTrans.naturality_apply]; rw [h]; rw [ht]; rw [← ConcreteCategory.comp_apply]; rw [← Functor.map_comp]
  rfl

end

end Sheaf

end TopCat
