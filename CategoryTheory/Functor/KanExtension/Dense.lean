/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAt
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Generator.StrongGenerator

/-!
# Dense functors

A functor `F : C ⥤ D` is dense (`F.IsDense`) if `𝟭 D` is a pointwise
left Kan extension of `F` along itself, i.e. any `Y : D` is the
colimit of all `F.obj X` for all morphisms `F.obj X ⟶ Y` (which
is the condition `F.DenseAt Y`).
When `F` is full, we show that this
is equivalent to saying that the restricted Yoneda functor
`D ⥤ Cᵒᵖ ⥤ Type _` is fully faithful (see the lemma
`Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda`).

We also show that the range of a dense functor is a strong
generator (see `Functor.isStrongGenerator_of_isDense`).

## References

* https://ncatlab.org/nlab/show/dense+subcategory

-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite Presheaf ConcreteCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {C' : Type u₃} [Category.{v₃} C']

namespace Functor

/--
Definition of `IsDense` / `IsDense` 的定义

English:
class IsDense
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - isDenseAt((F) (Y : D)) : F.isDenseAt Y

中文:
类 是稠密
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - isDenseAt((F) (Y : D)) : F.isDenseAt Y
-/
class IsDense (F : C ⥤ D) : Prop where
  isDenseAt (F) (Y : D) : F.isDenseAt Y

/--
Definition of `denseAt` / `denseAt` 的定义

English:
definition denseAt
  signature: (F : C ⥤ D) [F.IsDense] (Y : D)
  body: (IsDense.isDenseAt F Y).some

中文:
定义 denseAt
  签名: (F : C ⥤ D) [F.是稠密] (Y : D)
  定义体: (IsDense.isDenseAt F Y).some

Depends on / 依赖: IsDense, IsDense.isDenseAt, isDenseAt
-/
noncomputable def denseAt (F : C ⥤ D) [F.IsDense] (Y : D) : F.DenseAt Y :=
  (IsDense.isDenseAt F Y).some

/--
lemma `isDense_iff_nonempty_isPointwiseLeftKanExtension` / 引理 `isDense_iff_nonempty_isPointwiseLeftKanExtension`

English:
lemma isDense_iff_nonempty_isPointwiseLeftKanExtension
  given: (F : C ⥤ D)
  proof: ⟨fun _ => ⟨fun _ => F.denseAt _⟩, fun ⟨h⟩ => ⟨fun _ => ⟨h _⟩⟩⟩

中文:
引理 isDense_iff_nonempty_isPointwiseLeftKanExtension
  条件: (F : C ⥤ D)
  证明: ⟨fun _ => ⟨fun _ => F.denseAt _⟩, fun ⟨h⟩ => ⟨fun _ => ⟨h _⟩⟩⟩

Depends on / 依赖: F.denseAt, denseAt
-/
lemma isDense_iff_nonempty_isPointwiseLeftKanExtension (F : C ⥤ D) :
    F.IsDense ↔
      Nonempty ((LeftExtension.mk _ (rightUnitor F).inv).IsPointwiseLeftKanExtension) :=
  ⟨fun _ => ⟨fun _ => F.denseAt _⟩, fun ⟨h⟩ => ⟨fun _ => ⟨h _⟩⟩⟩

instance (F : C ⥤ D) [F.IsDense] : Functor.IsLeftKanExtension (𝟭 D) (Functor.rightUnitor F).inv :=
  ((Functor.isDense_iff_nonempty_isPointwiseLeftKanExtension F).mp ‹_›).some.isLeftKanExtension

instance (F : C ⥤ D) [F.IsDense] : F.HasPointwiseLeftKanExtension F :=
  fun X => (Functor.IsDense.isDenseAt F X).some.hasPointwiseLeftKanExtensionAt

/--
lemma `IsDense.of_iso` / 引理 `IsDense.of_iso`

English:
lemma IsDense.of_iso
  given: {F G : C ⥤ D} (e : F ≅ G) [F.IsDense]
  proof: by
    rw [← Functor.congr_isDenseAt e]
    exact ⟨F.denseAt Y⟩

中文:
引理 是稠密.of_iso
  条件: {F G : C ⥤ D} (e : F ≅ G) [F.是稠密]
  证明: by
    rw [← Functor.congr_isDenseAt e]
    exact ⟨F.denseAt Y⟩

Depends on / 依赖: F.denseAt, Functor, Functor.congr_isDenseAt, congr_isDenseAt, denseAt
-/
lemma IsDense.of_iso {F G : C ⥤ D} (e : F ≅ G) [F.IsDense] :
    G.IsDense where
  isDenseAt Y := by
    rw [← Functor.congr_isDenseAt e]
    exact ⟨F.denseAt Y⟩

/--
lemma `IsDense.iff_of_iso` / 引理 `IsDense.iff_of_iso`

English:
lemma IsDense.iff_of_iso
  given: {F G : C ⥤ D} (e : F ≅ G)
  proof: ⟨fun _ => of_iso e, fun _ => of_iso e.symm⟩

中文:
引理 是稠密.iff_of_iso
  条件: {F G : C ⥤ D} (e : F ≅ G)
  证明: ⟨fun _ => of_iso e, fun _ => of_iso e.symm⟩

Depends on / 依赖: e.symm, of_iso
-/
lemma IsDense.iff_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.IsDense ↔ G.IsDense :=
  ⟨fun _ => of_iso e, fun _ => of_iso e.symm⟩

variable (F : C ⥤ D)

instance (G : C' ⥤ C) [F.IsDense] [G.IsEquivalence] :
    (G ⋙ F).IsDense where
  isDenseAt Y := ⟨(F.denseAt Y).precompOfFinal G⟩

/--
lemma `IsDense.comp_left_iff_of_isEquivalence` / 引理 `IsDense.comp_left_iff_of_isEquivalence`

English:
lemma IsDense.comp_left_iff_of_isEquivalence
  given: (G : C' ⥤ C) [G.IsEquivalence]
  proof: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  let e : G.inv ⋙ G ⋙ F ≅ F := (associator _ _ _).symm ≪≫
    isoWhiskerRight (G.asEquivalence.counitIso) _ ≪≫ F.leftUnitor
  exact of_iso e

中文:
引理 是稠密.comp_left_iff_of_isEquivalence
  条件: (G : C' ⥤ C) [G.是等价]
  证明: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  let e : G.inv ⋙ G ⋙ F ≅ F := (associator _ _ _).symm ≪≫
    isoWhiskerRight (G.asEquivalence.counitIso) _ ≪≫ F.leftUnitor
  exact of_iso e

Depends on / 依赖: F.leftUnitor, G.asEquivalence.counitIso, G.inv, asEquivalence, associator, counitIso, isoWhiskerRight, leftUnitor, of_iso
-/
lemma IsDense.comp_left_iff_of_isEquivalence (G : C' ⥤ C) [G.IsEquivalence] :
    (G ⋙ F).IsDense ↔ F.IsDense := by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  let e : G.inv ⋙ G ⋙ F ≅ F := (associator _ _ _).symm ≪≫
    isoWhiskerRight (G.asEquivalence.counitIso) _ ≪≫ F.leftUnitor
  exact of_iso e

instance (G : D ⥤ C') [F.IsDense] [G.IsEquivalence] :
    (F ⋙ G).IsDense where
  isDenseAt Y :=
    ⟨ letI e : Y ≅ G.obj (G.inv.obj Y) := G.asEquivalence.counitIso.symm.app Y
      DenseAt.ofIso (F.denseAt (G.inv.obj Y) |>.postcompEquivalence G) e.symm ⟩

/--
lemma `IsDense.comp_right_iff_of_isEquivalence` / 引理 `IsDense.comp_right_iff_of_isEquivalence`

English:
lemma IsDense.comp_right_iff_of_isEquivalence
  given: (G : D ⥤ C') [G.IsEquivalence]
  proof: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  let e : (F ⋙ G) ⋙ G.inv ≅ F := associator .. ≪≫
    isoWhiskerLeft _ G.asEquivalence.unitIso.symm ≪≫ F.rightUnitor
  exact of_iso e

中文:
引理 是稠密.comp_right_iff_of_isEquivalence
  条件: (G : D ⥤ C') [G.是等价]
  证明: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  let e : (F ⋙ G) ⋙ G.inv ≅ F := associator .. ≪≫
    isoWhiskerLeft _ G.asEquivalence.unitIso.symm ≪≫ F.rightUnitor
  exact of_iso e

Depends on / 依赖: F.rightUnitor, G.asEquivalence.unitIso.symm, G.inv, asEquivalence, associator, isoWhiskerLeft, of_iso, rightUnitor, unitIso
-/
lemma IsDense.comp_right_iff_of_isEquivalence (G : D ⥤ C') [G.IsEquivalence] :
    (F ⋙ G).IsDense ↔ F.IsDense := by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  let e : (F ⋙ G) ⋙ G.inv ≅ F := associator .. ≪≫
    isoWhiskerLeft _ G.asEquivalence.unitIso.symm ≪≫ F.rightUnitor
  exact of_iso e

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.IsDense]
  signature: : (restrictedULiftYoneda.{w} F).Faithful where
  body: (F.denseAt _).hom_ext' (fun X p => by
      simpa using! ULift.up_injective (ConcreteCategory.congr_hom (CC := fun X => X)
        (NatTrans.congr_app h (op X)) (ULift.up p)))

中文:
实例 [F.是稠密]
  签名: : (restrictedULiftYoneda.{w} F).忠实 where
  定义体: (F.denseAt _).hom_ext' (fun X p => by
      simpa using! ULift.up_injective (ConcreteCategory.congr_hom (CC := fun X => X)
        (NatTrans.congr_app h (op X)) (ULift.up p)))

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, F.denseAt, NatTrans, NatTrans.congr_app, ULift.up, ULift.up_injective, congr_app, congr_hom, denseAt, hom_ext, up_injective
-/
instance [F.IsDense] : (restrictedULiftYoneda.{w} F).Faithful where
  map_injective h :=
    (F.denseAt _).hom_ext' (fun X p => by
      simpa using! ULift.up_injective (ConcreteCategory.congr_hom (CC := fun X => X)
        (NatTrans.congr_app h (op X)) (ULift.up p)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.IsDense]
  signature: : (restrictedULiftYoneda.{w} F).Full where
  body: by
    let c : Cocone (CostructuredArrow.proj F Y ⋙ F) :=
      { pt := Z
        ι :=
          { app g := ((f.app (op g.left)) (ULift.up g.hom)).down
            naturality g₁ g₂ φ := by
              simpa [uliftFunctor, uliftYoneda,
                restrictedULiftYoneda, ← ULift.down_inj] using


中文:
实例 [F.是稠密]
  签名: : (restrictedULiftYoneda.{w} F).满 where
  定义体: by
    let c : Cocone (CostructuredArrow.proj F Y ⋙ F) :=
      { pt := Z
        ι :=
          { app g := ((f.app (op g.left)) (ULift.up g.hom)).down
            naturality g₁ g₂ φ := by
              simpa [uliftFunctor, uliftYoneda,
                restrictedULiftYoneda, ← ULift.down_inj] using


Depends on / 依赖: Cocone, CostructuredArrow, CostructuredArrow.proj, F.denseAt, ULift.down_inj, ULift.down_injective, ULift.up, denseAt, down_inj, down_injective, f.app, f.naturality_apply, g.hom, g.left, left.op, naturality, naturality_apply, restrictedULiftYoneda, uliftFunctor, uliftYoneda
-/
instance [F.IsDense] : (restrictedULiftYoneda.{w} F).Full where
  map_surjective {Y Z} f := by
    let c : Cocone (CostructuredArrow.proj F Y ⋙ F) :=
      { pt := Z
        ι :=
          { app g := ((f.app (op g.left)) (ULift.up g.hom)).down
            naturality g₁ g₂ φ := by
              simpa [uliftFunctor, uliftYoneda,
                restrictedULiftYoneda, ← ULift.down_inj] using
                ((f.naturality_apply φ.left.op) (ULift.up g₂.hom)).symm } }
    refine ⟨(F.denseAt Y).desc c, ?_⟩
    ext ⟨X⟩ ⟨x⟩
    have := (F.denseAt Y).fac c (.mk x)
    dsimp [c] at this
    simpa using ULift.down_injective this

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {F} in
/--
lemma `IsDense.of_fullyFaithful_restrictedULiftYoneda` / 引理 `IsDense.of_fullyFaithful_restrictedULiftYoneda`

English:
lemma IsDense.of_fullyFaithful_restrictedULiftYoneda
  statement: [F.Full]
  proof: by
    let φ (s : Cocone (CostructuredArrow.proj F Y ⋙ F)) :
        (restrictedULiftYoneda.{w} F).obj Y ⟶ (restrictedULiftYoneda F).obj s.pt :=
      { app := fun ⟨X⟩ => ↾fun ⟨x⟩ => ULift.up (s.ι.app (.mk x))
        naturality := by
          rintro ⟨X₁⟩ ⟨X₂⟩ ⟨f⟩
          ext ⟨x⟩
          let α 

中文:
引理 是稠密.of_fullyFaithful_restrictedULiftYoneda
  结论: [F.满]
  证明: by
    let φ (s : Cocone (CostructuredArrow.proj F Y ⋙ F)) :
        (restrictedULiftYoneda.{w} F).obj Y ⟶ (restrictedULiftYoneda F).obj s.pt :=
      { app := fun ⟨X⟩ => ↾fun ⟨x⟩ => ULift.up (s.ι.app (.mk x))
        naturality := by
          rintro ⟨X₁⟩ ⟨X₂⟩ ⟨f⟩
          ext ⟨x⟩
          let α 

Depends on / 依赖: Cocone, CostructuredArrow, CostructuredArrow.homMk, CostructuredArrow.mk, CostructuredArrow.proj, F.map, ULift.down_injective, ULift.up, down_injective, j.hom, naturality, restrictedULiftYoneda, s.pt
-/
lemma IsDense.of_fullyFaithful_restrictedULiftYoneda [F.Full]
    (h : (restrictedULiftYoneda.{w} F).FullyFaithful) :
    F.IsDense where
  isDenseAt Y := by
    let φ (s : Cocone (CostructuredArrow.proj F Y ⋙ F)) :
        (restrictedULiftYoneda.{w} F).obj Y ⟶ (restrictedULiftYoneda F).obj s.pt :=
      { app := fun ⟨X⟩ => ↾fun ⟨x⟩ => ULift.up (s.ι.app (.mk x))
        naturality := by
          rintro ⟨X₁⟩ ⟨X₂⟩ ⟨f⟩
          ext ⟨x⟩
          let α : CostructuredArrow.mk (F.map f ≫ x) ⟶ CostructuredArrow.mk x :=
            CostructuredArrow.homMk f
          exact ULift.down_injective (s.w α).symm }
    have hφ (s) (j) : (restrictedULiftYoneda F).map j.hom ≫ φ s =
        (restrictedULiftYoneda F).map (s.ι.app j) := by
      ext ⟨X⟩ ⟨x⟩
      let α : .mk (x ≫ j.hom) ⟶ j := CostructuredArrow.homMk (F.preimage x)
      have := s.w α
      dsimp [uliftYoneda, φ, α] at this ⊢
      apply ULift.down_injective
      simpa using this.symm
    exact
      ⟨{desc s := (h.preimage (φ s))
        fac s j := h.map_injective (by simp [hφ])
        uniq s m hm := h.map_injective (by
          ext ⟨_⟩ ⟨_⟩
          simp [φ, ← hm]) }⟩

/--
lemma `isDense_iff_fullyFaithful_restrictedULiftYoneda` / 引理 `isDense_iff_fullyFaithful_restrictedULiftYoneda`

English:
lemma isDense_iff_fullyFaithful_restrictedULiftYoneda
  given: [F.Full]
  proof: ⟨fun _ => ⟨FullyFaithful.ofFullyFaithful _⟩,
    fun ⟨h⟩ => IsDense.of_fullyFaithful_restrictedULiftYoneda h⟩

中文:
引理 isDense_iff_fullyFaithful_restrictedULiftYoneda
  条件: [F.满]
  证明: ⟨fun _ => ⟨FullyFaithful.ofFullyFaithful _⟩,
    fun ⟨h⟩ => IsDense.of_fullyFaithful_restrictedULiftYoneda h⟩

Depends on / 依赖: FullyFaithful, FullyFaithful.ofFullyFaithful, IsDense, IsDense.of_fullyFaithful_restrictedULiftYoneda, ofFullyFaithful, of_fullyFaithful_restrictedULiftYoneda
-/
lemma isDense_iff_fullyFaithful_restrictedULiftYoneda [F.Full] :
    F.IsDense ↔ Nonempty (restrictedULiftYoneda.{w} F).FullyFaithful :=
  ⟨fun _ => ⟨FullyFaithful.ofFullyFaithful _⟩,
    fun ⟨h⟩ => IsDense.of_fullyFaithful_restrictedULiftYoneda h⟩

open ObjectProperty in
/--
lemma `isStrongGenerator_of_isDense` / 引理 `isStrongGenerator_of_isDense`

English:
lemma isStrongGenerator_of_isDense
  given: [F.IsDense]
  proof: (IsStrongGenerator.mk_of_exists_colimitsOfShape.{max u₁ u₂ v₁ v₂,
      max u₁ v₁ v₂} (fun Y => ⟨_, _, ⟨{
    ι := _
    diag := _
    isColimit := (IsColimit.whiskerEquivalence (F.denseAt Y)
      ((ShrinkHoms.equivalence _).symm.trans ((Shrink.equivalence _)).symm))
    prop_diag_obj := by simp }⟩

中文:
引理 isStrongGenerator_of_isDense
  条件: [F.是稠密]
  证明: (IsStrongGenerator.mk_of_exists_colimitsOfShape.{max u₁ u₂ v₁ v₂,
      max u₁ v₁ v₂} (fun Y => ⟨_, _, ⟨{
    ι := _
    diag := _
    isColimit := (IsColimit.whiskerEquivalence (F.denseAt Y)
      ((ShrinkHoms.equivalence _).symm.trans ((Shrink.equivalence _)).symm))
    prop_diag_obj := by simp }⟩

Depends on / 依赖: F.denseAt, IsColimit, IsColimit.whiskerEquivalence, IsStrongGenerator, IsStrongGenerator.mk_of_exists_colimitsOfShape, Shrink, Shrink.equivalence, ShrinkHoms, ShrinkHoms.equivalence, denseAt, equivalence, isColimit, mk_of_exists_colimitsOfShape, prop_diag_obj, symm.trans, whiskerEquivalence
-/
lemma isStrongGenerator_of_isDense [F.IsDense] :
    IsStrongGenerator (.ofObj F.obj) :=
  (IsStrongGenerator.mk_of_exists_colimitsOfShape.{max u₁ u₂ v₁ v₂,
      max u₁ v₁ v₂} (fun Y => ⟨_, _, ⟨{
    ι := _
    diag := _
    isColimit := (IsColimit.whiskerEquivalence (F.denseAt Y)
      ((ShrinkHoms.equivalence _).symm.trans ((Shrink.equivalence _)).symm))
    prop_diag_obj := by simp }⟩⟩))

/--
Definition of `IsDense.leftKanExtensionIso` / `IsDense.leftKanExtensionIso` 的定义

English:
definition IsDense.leftKanExtensionIso
  signature: (F : C ⥤ D) [F.IsDense]
  body: Functor.leftKanExtensionUnique _ (F.leftKanExtensionUnit F) _ F.rightUnitor.inv

@[reassoc (attr := simp)]

中文:
定义 是稠密.leftKanExtensionIso
  签名: (F : C ⥤ D) [F.是稠密]
  定义体: Functor.leftKanExtensionUnique _ (F.leftKanExtensionUnit F) _ F.rightUnitor.inv

@[reassoc (attr := simp)]

Depends on / 依赖: F.leftKanExtensionUnit, F.rightUnitor.inv, Functor, Functor.leftKanExtensionUnique, leftKanExtensionUnique, leftKanExtensionUnit, rightUnitor
-/
noncomputable def IsDense.leftKanExtensionIso (F : C ⥤ D) [F.IsDense] :
    F.leftKanExtension F ≅ 𝟭 D :=
  Functor.leftKanExtensionUnique _ (F.leftKanExtensionUnit F) _ F.rightUnitor.inv

@[reassoc (attr := simp)]
/--
lemma `IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom` / 引理 `IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom`

English:
lemma IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom
  given: (F : C ⥤ D) [F.IsDense]
  proof: by
  simp [Functor.IsDense.leftKanExtensionIso]

@[reassoc (attr := simp)]

中文:
引理 是稠密.leftKanExtensionUnit_leftKanExtensionIso_hom
  条件: (F : C ⥤ D) [F.是稠密]
  证明: by
  simp [Functor.IsDense.leftKanExtensionIso]

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.IsDense.leftKanExtensionIso, IsDense, leftKanExtensionIso
-/
lemma IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom (F : C ⥤ D) [F.IsDense] :
    F.leftKanExtensionUnit F ≫ F.whiskerLeft (Functor.IsDense.leftKanExtensionIso F).hom =
      F.rightUnitor.inv := by
  simp [Functor.IsDense.leftKanExtensionIso]

@[reassoc (attr := simp)]
/--
lemma `IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom_app` / 引理 `IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom_app`

English:
lemma IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom_app
  given: [F.IsDense] (X : C)
  proof: congr($(Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom _).app _)

中文:
引理 是稠密.leftKanExtensionUnit_leftKanExtensionIso_hom_app
  条件: [F.是稠密] (X : C)
  证明: congr($(Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom _).app _)

Depends on / 依赖: Functor, Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom, IsDense, leftKanExtensionUnit_leftKanExtensionIso_hom
-/
lemma IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom_app [F.IsDense] (X : C) :
    (F.leftKanExtensionUnit F).app X ≫ (Functor.IsDense.leftKanExtensionIso F).hom.app (F.obj X) =
      F.rightUnitor.inv.app _ :=
  congr($(Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom _).app _)

end Functor

/--
Definition of `denseAtYoneda` / `denseAtYoneda` 的定义

English:
definition denseAtYoneda
  signature: (X : Cᵒᵖ ⥤ Type v₁)
  body: Presheaf.isColimitTautologicalCocone X

中文:
定义 denseAtYoneda
  签名: (X : Cᵒᵖ ⥤ 类型v₁)
  定义体: Presheaf.isColimitTautologicalCocone X

Depends on / 依赖: Presheaf, Presheaf.isColimitTautologicalCocone, isColimitTautologicalCocone
-/
def denseAtYoneda (X : Cᵒᵖ ⥤ Type v₁) : yoneda.DenseAt X :=
  Presheaf.isColimitTautologicalCocone X

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (yoneda (C := C)).IsDense
  body: ⟨denseAtYoneda X⟩

中文:
实例 :
  签名: (yoneda (C := C)).是稠密
  定义体: ⟨denseAtYoneda X⟩

Depends on / 依赖: IsDense
-/
instance : (yoneda (C := C)).IsDense where
  isDenseAt X := ⟨denseAtYoneda X⟩

/--
Definition of `denseAtUliftYoneda` / `denseAtUliftYoneda` 的定义

English:
definition denseAtUliftYoneda
  signature: (X : Cᵒᵖ ⥤ Type max w v₁)
  body: Presheaf.isColimitTautologicalCocone' X

中文:
定义 denseAtUliftYoneda
  签名: (X : Cᵒᵖ ⥤ 类型 最大值 w v₁)
  定义体: Presheaf.isColimitTautologicalCocone' X

Depends on / 依赖: Presheaf, Presheaf.isColimitTautologicalCocone, isColimitTautologicalCocone
-/
def denseAtUliftYoneda (X : Cᵒᵖ ⥤ Type max w v₁) : uliftYoneda.DenseAt X :=
  Presheaf.isColimitTautologicalCocone' X

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (uliftYoneda.{w} (C := C)).IsDense
  body: ⟨denseAtUliftYoneda X⟩

中文:
实例 :
  签名: (uliftYoneda.{w} (C := C)).是稠密
  定义体: ⟨denseAtUliftYoneda X⟩

Depends on / 依赖: IsDense
-/
instance : (uliftYoneda.{w} (C := C)).IsDense where
  isDenseAt X := ⟨denseAtUliftYoneda X⟩

end CategoryTheory
