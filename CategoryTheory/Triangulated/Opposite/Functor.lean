/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Adjunction.Opposites

/-!
# Opposites of functors between pretriangulated categories,

If `F : C ⥤ D` is a functor between pretriangulated categories, we prove that
`F` is a triangulated functor if and only if `F.op` is a triangulated functor.
In order to do this, we first show that a `CommShift` structure on `F` naturally
gives one on `F.op` (for the shifts on `Cᵒᵖ` and `Dᵒᵖ` defined in
`CategoryTheory.Triangulated.Opposite.Basic`), and we then prove
that `F.mapTriangle.op` and `F.op.mapTriangle` correspond to each other via the
equivalences `(Triangle C)ᵒᵖ ≌ Triangle Cᵒᵖ` and `(Triangle D)ᵒᵖ ≌ Triangle Dᵒᵖ`
given by `CategoryTheory.Pretriangulated.triangleOpEquivalence`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [HasShift C Int] [HasShift D Int] (F : C ⥤ D)
  [F.CommShift Int]

open Category Limits Pretriangulated Opposite

namespace Pretriangulated.Opposite

/-- If `F` commutes with shifts, so does `F.op`, for the shifts chosen on `Cᵒᵖ` in
`CategoryTheory.Triangulated.Opposite.Basic`.
-/
noncomputable scoped instance commShiftFunctorOpInt : F.op.CommShift Int :=
  inferInstanceAs ((PullbackShift.functor
    (AddMonoidHom.mk' (fun (n : Int) => -n) (by intros; lia))
      (OppositeShift.functor Int F)).CommShift Int)

variable {F}

noncomputable scoped instance commShift_natTrans_op_int {G : C ⥤ D} [G.CommShift Int] (τ : F ⟶ G)
    [NatTrans.CommShift τ Int] : NatTrans.CommShift (NatTrans.op τ) Int :=
  inferInstanceAs (NatTrans.CommShift (PullbackShift.natTrans
    (AddMonoidHom.mk' (fun (n : Int) => -n) (by intros; lia))
      (OppositeShift.natTrans Int τ)) Int)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable scoped instance commShift_adjunction_op_int {G : D ⥤ C} [G.CommShift Int] (adj : F ⊣ G)
    [Adjunction.CommShift adj Int] : Adjunction.CommShift adj.op Int := by
  have eq : adj.op = PullbackShift.adjunction
    (AddMonoidHom.mk' (fun (n : Int) => -n) (by intros; lia))
      (OppositeShift.adjunction Int adj) := by
    ext
    dsimp [PullbackShift.adjunction, NatTrans.PullbackShift.natIsoId,
      NatTrans.PullbackShift.natIsoComp, PullbackShift.functor, PullbackShift.natTrans,
      OppositeShift.adjunction, OppositeShift.natTrans, NatTrans.OppositeShift.natIsoId,
      NatTrans.OppositeShift.natIsoComp, OppositeShift.functor]
    simp only [Category.comp_id, Category.id_comp]
  rw [eq]
  exact inferInstanceAs (Adjunction.CommShift (PullbackShift.adjunction
    (AddMonoidHom.mk' (fun (n : Int) => -n) (by intros; lia))
      (OppositeShift.adjunction Int adj)) Int)

end Pretriangulated.Opposite

namespace Functor

set_option backward.isDefEq.respectTransparency false in -- Needed in map_opShiftFunctorEquivalence_counitIso_hom_app_unop
@[reassoc]
/--
lemma `op_commShiftIso_hom_app` / 引理 `op_commShiftIso_hom_app`

English:
lemma op_commShiftIso_hom_app
  given: (X : Cᵒᵖ) (n m : Int) (h : n + m = 0)
  proof: by
  obtain rfl : m = -n := by lia
  rfl

中文:
引理 op_commShiftIso_hom_app
  条件: (X : Cᵒᵖ) (n m : 整数) (h : n + m = 0)
  证明: by
  obtain rfl : m = -n := by lia
  rfl
-/
lemma op_commShiftIso_hom_app (X : Cᵒᵖ) (n m : Int) (h : n + m = 0) :
    (F.op.commShiftIso n).hom.app X =
      (F.map ((shiftFunctorOpIso C n m h).hom.app X).unop).op ≫
        ((F.commShiftIso m).inv.app X.unop).op ≫
        (shiftFunctorOpIso D n m h).inv.app (op (F.obj X.unop)) := by
  obtain rfl : m = -n := by lia
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `op_commShiftIso_inv_app` / 引理 `op_commShiftIso_inv_app`

English:
lemma op_commShiftIso_inv_app
  given: (X : Cᵒᵖ) (n m : Int) (h : n + m = 0)
  proof: by
  rw [← cancel_epi ((F.op.commShiftIso n).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [op_commShiftIso_hom_app _ X n m h]; rw [assoc]; rw [assoc]
  simp [← op_comp, ← F.map_comp]

#adaptation_note

中文:
引理 op_commShiftIso_inv_app
  条件: (X : Cᵒᵖ) (n m : 整数) (h : n + m = 0)
  证明: by
  rw [← cancel_epi ((F.op.commShiftIso n).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [op_commShiftIso_hom_app _ X n m h]; rw [assoc]; rw [assoc]
  simp [← op_comp, ← F.map_comp]

#adaptation_note

Depends on / 依赖: F.map_comp, F.op.commShiftIso, Iso.hom_inv_id_app, cancel_epi, commShiftIso, hom.app, hom_inv_id_app, map_comp, op_commShiftIso_hom_app, op_comp
-/
lemma op_commShiftIso_inv_app (X : Cᵒᵖ) (n m : Int) (h : n + m = 0) :
    (F.op.commShiftIso n).inv.app X =
      (shiftFunctorOpIso D n m h).hom.app (op (F.obj X.unop)) ≫
        ((F.commShiftIso m).hom.app X.unop).op ≫
          (F.map ((shiftFunctorOpIso C n m h).inv.app X).unop).op := by
  rw [← cancel_epi ((F.op.commShiftIso n).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [op_commShiftIso_hom_app _ X n m h]; rw [assoc]; rw [assoc]
  simp [← op_comp, ← F.map_comp]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `shift_map_op` / 引理 `shift_map_op`

English:
lemma shift_map_op
  given: {X Y : C} (f : X ⟶ Y) (n : Int)
  proof: (NatIso.naturality_1 (F.op.commShiftIso n) f.op).symm

中文:
引理 shift_map_op
  条件: {X Y : C} (f : X ⟶ Y) (n : 整数)
  证明: (NatIso.naturality_1 (F.op.commShiftIso n) f.op).symm

Depends on / 依赖: F.op.commShiftIso, NatIso, NatIso.naturality_1, commShiftIso, f.op, naturality_1
-/
lemma shift_map_op {X Y : C} (f : X ⟶ Y) (n : Int) :
    (F.map f).op⟦n⟧' = (F.op.commShiftIso n).inv.app _ ≫
      (F.map (f.op⟦n⟧').unop).op ≫ (F.op.commShiftIso n).hom.app _ :=
  (NatIso.naturality_1 (F.op.commShiftIso n) f.op).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `map_shift_unop` / 引理 `map_shift_unop`

English:
lemma map_shift_unop
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : Int)
  proof: by
  simp [shift_map_op]

中文:
引理 map_shift_unop
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : 整数)
  证明: by
  simp [shift_map_op]

Depends on / 依赖: shift_map_op
-/
lemma map_shift_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : Int) :
    F.map ((f⟦n⟧').unop) = ((F.op.commShiftIso n).inv.app Y).unop ≫
      ((F.map f.unop).op⟦n⟧').unop ≫ ((F.op.commShiftIso n).hom.app X).unop := by
  simp [shift_map_op]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `map_opShiftFunctorEquivalence_unitIso_hom_app_unop` / 引理 `map_opShiftFunctorEquivalence_unitIso_hom_app_unop`

English:
lemma map_opShiftFunctorEquivalence_unitIso_hom_app_unop
  given: (X : Cᵒᵖ) (n : Int)
  proof: by
  dsimp [opShiftFunctorEquivalence]
  simp only [map_comp, unop_comp, Quiver.Hom.unop_op, assoc,
    map_shiftFunctorCompIsoId_hom_app, commShiftIso_hom_naturality_assoc,
    op_commShiftIso_inv_app _ _ _ _ (add_neg_cancel n)]
  congr 3
  rw [← Functor.map_comp_assoc]; rw [← unop_comp]; rw [Iso.i

中文:
引理 map_opShiftFunctorEquivalence_unitIso_hom_app_unop
  条件: (X : Cᵒᵖ) (n : 整数)
  证明: by
  dsimp [opShiftFunctorEquivalence]
  simp only [map_comp, unop_comp, Quiver.Hom.unop_op, assoc,
    map_shiftFunctorCompIsoId_hom_app, commShiftIso_hom_naturality_assoc,
    op_commShiftIso_inv_app _ _ _ _ (add_neg_cancel n)]
  congr 3
  rw [← Functor.map_comp_assoc]; rw [← unop_comp]; rw [Iso.i

Depends on / 依赖: Functor, Functor.map_comp_assoc, Iso.inv_hom_id_app, Quiver, Quiver.Hom.unop_op, add_neg_cancel, commShiftIso_hom_naturality_assoc, id_comp, inv_hom_id_app, map_comp, map_comp_assoc, map_id, map_shiftFunctorCompIsoId_hom_app, opShiftFunctorEquivalence, op_commShiftIso_inv_app, unop_comp, unop_op
-/
lemma map_opShiftFunctorEquivalence_unitIso_hom_app_unop (X : Cᵒᵖ) (n : Int) :
    F.map ((opShiftFunctorEquivalence C n).unitIso.hom.app X).unop =
      (F.commShiftIso n).hom.app _ ≫
        (((F.op).commShiftIso n).inv.app X).unop⟦n⟧' ≫
        ((opShiftFunctorEquivalence D n).unitIso.hom.app (op _)).unop := by
  dsimp [opShiftFunctorEquivalence]
  simp only [map_comp, unop_comp, Quiver.Hom.unop_op, assoc,
    map_shiftFunctorCompIsoId_hom_app, commShiftIso_hom_naturality_assoc,
    op_commShiftIso_inv_app _ _ _ _ (add_neg_cancel n)]
  congr 3
  rw [← Functor.map_comp_assoc]; rw [← unop_comp]; rw [Iso.inv_hom_id_app]
  dsimp
  rw [map_id]; rw [id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `map_opShiftFunctorEquivalence_unitIso_inv_app_unop` / 引理 `map_opShiftFunctorEquivalence_unitIso_inv_app_unop`

English:
lemma map_opShiftFunctorEquivalence_unitIso_inv_app_unop
  given: (X : Cᵒᵖ) (n : Int)
  proof: by
  rw [← cancel_mono (F.map ((opShiftFunctorEquivalence C n).unitIso.hom.app X).unop)]; rw [← F.map_comp]; rw [← unop_comp]; rw [Iso.hom_inv_id_app]; rw [map_opShiftFunctorEquivalence_unitIso_hom_app_unop]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [← Functor.map_comp_assoc]; rw [←

中文:
引理 map_opShiftFunctorEquivalence_unitIso_inv_app_unop
  条件: (X : Cᵒᵖ) (n : 整数)
  证明: by
  rw [← cancel_mono (F.map ((opShiftFunctorEquivalence C n).unitIso.hom.app X).unop)]; rw [← F.map_comp]; rw [← unop_comp]; rw [Iso.hom_inv_id_app]; rw [map_opShiftFunctorEquivalence_unitIso_hom_app_unop]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [← Functor.map_comp_assoc]; rw [←

Depends on / 依赖: F.map, F.map_comp, Functor, Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc, cancel_mono, hom_inv_id_app, inv_hom_id_app_assoc, map_comp, map_comp_assoc, map_opShiftFunctorEquivalence_unitIso_hom_app_unop, opShiftFunctorEquivalence, unitIso, unitIso.hom.app, unop_comp
-/
lemma map_opShiftFunctorEquivalence_unitIso_inv_app_unop (X : Cᵒᵖ) (n : Int) :
    F.map ((opShiftFunctorEquivalence C n).unitIso.inv.app X).unop =
      ((opShiftFunctorEquivalence D n).unitIso.inv.app (op (F.obj X.unop))).unop ≫
        (((F.op).commShiftIso n).hom.app X).unop⟦n⟧' ≫
        ((F.commShiftIso n).inv.app _) := by
  rw [← cancel_mono (F.map ((opShiftFunctorEquivalence C n).unitIso.hom.app X).unop)]; rw [← F.map_comp]; rw [← unop_comp]; rw [Iso.hom_inv_id_app]; rw [map_opShiftFunctorEquivalence_unitIso_hom_app_unop]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [← Functor.map_comp_assoc]; rw [← unop_comp]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `map_opShiftFunctorEquivalence_counitIso_hom_app_unop` / 引理 `map_opShiftFunctorEquivalence_counitIso_hom_app_unop`

English:
lemma map_opShiftFunctorEquivalence_counitIso_hom_app_unop
  given: (X : Cᵒᵖ) (n : Int)
  proof: by
  apply Quiver.Hom.op_inj
  dsimp [opShiftFunctorEquivalence]
  rw [assoc]; rw [F.op_commShiftIso_hom_app_assoc _ _ _ (add_neg_cancel n)]; rw [map_comp]; rw [map_shiftFunctorCompIsoId_inv_app_assoc]; rw [op_comp]; rw [op_comp_assoc]; rw [op_comp_assoc]; rw [NatTrans.naturality_assoc]; rw [op_map]

中文:
引理 map_opShiftFunctorEquivalence_counitIso_hom_app_unop
  条件: (X : Cᵒᵖ) (n : 整数)
  证明: by
  apply Quiver.Hom.op_inj
  dsimp [opShiftFunctorEquivalence]
  rw [assoc]; rw [F.op_commShiftIso_hom_app_assoc _ _ _ (add_neg_cancel n)]; rw [map_comp]; rw [map_shiftFunctorCompIsoId_inv_app_assoc]; rw [op_comp]; rw [op_comp_assoc]; rw [op_comp_assoc]; rw [NatTrans.naturality_assoc]; rw [op_map]

Depends on / 依赖: F.op_commShiftIso_hom_app_assoc, Iso.inv_hom_id_app_assoc, NatTrans, NatTrans.naturality_assoc, Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_op, add_neg_cancel, inv_hom_id_app_assoc, map_comp, map_shiftFunctorCompIsoId_inv_app_assoc, naturality_assoc, opShiftFunctorEquivalence, op_commShiftIso_hom_app_assoc, op_comp, op_comp_assoc, op_inj, op_map, unop_op
-/
lemma map_opShiftFunctorEquivalence_counitIso_hom_app_unop (X : Cᵒᵖ) (n : Int) :
    F.map ((opShiftFunctorEquivalence C n).counitIso.hom.app X).unop =
      ((opShiftFunctorEquivalence D n).counitIso.hom.app (op (F.obj X.unop))).unop ≫
        (((F.commShiftIso n).inv.app X.unop).op⟦n⟧').unop ≫
          ((F.op.commShiftIso n).hom.app (op (X.unop⟦n⟧))).unop := by
  apply Quiver.Hom.op_inj
  dsimp [opShiftFunctorEquivalence]
  rw [assoc]; rw [F.op_commShiftIso_hom_app_assoc _ _ _ (add_neg_cancel n)]; rw [map_comp]; rw [map_shiftFunctorCompIsoId_inv_app_assoc]; rw [op_comp]; rw [op_comp_assoc]; rw [op_comp_assoc]; rw [NatTrans.naturality_assoc]; rw [op_map]; rw [Iso.inv_hom_id_app_assoc]; rw [Quiver.Hom.unop_op]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `map_opShiftFunctorEquivalence_counitIso_inv_app_unop` / 引理 `map_opShiftFunctorEquivalence_counitIso_inv_app_unop`

English:
lemma map_opShiftFunctorEquivalence_counitIso_inv_app_unop
  given: (X : Cᵒᵖ) (n : Int)
  proof: by
  rw [← cancel_epi (F.map ((opShiftFunctorEquivalence C n).counitIso.hom.app X).unop)]; rw [← F.map_comp]; rw [← unop_comp]; rw [Iso.inv_hom_id_app]; rw [map_opShiftFunctorEquivalence_counitIso_hom_app_unop]
  dsimp
  simp only [map_id, assoc, ← Functor.map_comp_assoc,
    ← unop_comp, Iso.inv_ho

中文:
引理 map_opShiftFunctorEquivalence_counitIso_inv_app_unop
  条件: (X : Cᵒᵖ) (n : 整数)
  证明: by
  rw [← cancel_epi (F.map ((opShiftFunctorEquivalence C n).counitIso.hom.app X).unop)]; rw [← F.map_comp]; rw [← unop_comp]; rw [Iso.inv_hom_id_app]; rw [map_opShiftFunctorEquivalence_counitIso_hom_app_unop]
  dsimp
  simp only [map_id, assoc, ← Functor.map_comp_assoc,
    ← unop_comp, Iso.inv_ho

Depends on / 依赖: F.map, F.map_comp, Functor, Functor.map_comp_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, cancel_epi, counitIso, counitIso.hom.app, inv_hom_id_app, inv_hom_id_app_assoc, map_comp, map_comp_assoc, map_id, map_opShiftFunctorEquivalence_counitIso_hom_app_unop, opShiftFunctorEquivalence, op_comp, unop_comp
-/
lemma map_opShiftFunctorEquivalence_counitIso_inv_app_unop (X : Cᵒᵖ) (n : Int) :
    F.map ((opShiftFunctorEquivalence C n).counitIso.inv.app X).unop =
      ((F.op.commShiftIso n).inv.app (op (X.unop⟦n⟧))).unop ≫
        (((F.commShiftIso n).hom.app X.unop).op⟦n⟧').unop ≫
          ((opShiftFunctorEquivalence D n).counitIso.inv.app (op (F.obj X.unop))).unop := by
  rw [← cancel_epi (F.map ((opShiftFunctorEquivalence C n).counitIso.hom.app X).unop)]; rw [← F.map_comp]; rw [← unop_comp]; rw [Iso.inv_hom_id_app]; rw [map_opShiftFunctorEquivalence_counitIso_hom_app_unop]
  dsimp
  simp only [map_id, assoc, ← Functor.map_comp_assoc,
    ← unop_comp, Iso.inv_hom_id_app_assoc, ← op_comp,
    Iso.inv_hom_id_app]
  simp

end Functor

variable [HasZeroObject C] [Preadditive C] [forall (n : Int), (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasZeroObject D] [Preadditive D]
  [forall (n : Int), (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
If `F : C ⥤ D` commutes with shifts, this expresses the compatibility of `F.mapTriangle`
with the equivalences `Pretriangulated.triangleOpEquivalence` on `C` and `D`.
-/
@[simps!]
/--
Definition of `mapTriangleOpCompTriangleOpEquivalenceFunctorApp` / `mapTriangleOpCompTriangleOpEquivalenceFunctorApp` 的定义

English:
definition mapTriangleOpCompTriangleOpEquivalenceFunctorApp
  signature: (T : Triangle C)
  body: Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [shift_map_op, map_opShiftFunctorEquivalence_counitIso_inv_app_unop])

中文:
定义 mapTriangleOpCompTriangleOpEquivalenceFunctorApp
  签名: (T : Triangle C)
  定义体: Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [shift_map_op, map_opShiftFunctorEquivalence_counitIso_inv_app_unop])

Depends on / 依赖: Iso.refl, Triangle, Triangle.isoMk, map_opShiftFunctorEquivalence_counitIso_inv_app_unop, shift_map_op
-/
noncomputable def mapTriangleOpCompTriangleOpEquivalenceFunctorApp (T : Triangle C) :
    (triangleOpEquivalence D).functor.obj (op (F.mapTriangle.obj T)) ≅
      F.op.mapTriangle.obj ((triangleOpEquivalence C).functor.obj (op T)) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [shift_map_op, map_opShiftFunctorEquivalence_counitIso_inv_app_unop])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mapTriangleOpCompTriangleOpEquivalenceFunctor` / `mapTriangleOpCompTriangleOpEquivalenceFunctor` 的定义

English:
definition mapTriangleOpCompTriangleOpEquivalenceFunctor
  signature: :
  body: NatIso.ofComponents
    (fun T => F.mapTriangleOpCompTriangleOpEquivalenceFunctorApp T.unop)
    (by intros; ext <;> dsimp <;> simp only [id_comp, comp_id])

中文:
定义 mapTriangleOpCompTriangleOpEquivalenceFunctor
  签名: :
  定义体: NatIso.ofComponents
    (fun T => F.mapTriangleOpCompTriangleOpEquivalenceFunctorApp T.unop)
    (by intros; ext <;> dsimp <;> simp only [id_comp, comp_id])

Depends on / 依赖: F.mapTriangleOpCompTriangleOpEquivalenceFunctorApp, NatIso, NatIso.ofComponents, T.unop, comp_id, id_comp, intros, mapTriangleOpCompTriangleOpEquivalenceFunctorApp, ofComponents
-/
noncomputable def mapTriangleOpCompTriangleOpEquivalenceFunctor :
    F.mapTriangle.op ⋙ (triangleOpEquivalence D).functor ≅
      (triangleOpEquivalence C).functor ⋙ F.op.mapTriangle :=
  NatIso.ofComponents
    (fun T => F.mapTriangleOpCompTriangleOpEquivalenceFunctorApp T.unop)
    (by intros; ext <;> dsimp <;> simp only [id_comp, comp_id])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: ⟨F.mapTriangleOpCompTriangleOpEquivalenceFunctor⟩

中文:
实例 :
  定义体: ⟨F.mapTriangleOpCompTriangleOpEquivalenceFunctor⟩

Depends on / 依赖: F.mapTriangleOpCompTriangleOpEquivalenceFunctor, mapTriangleOpCompTriangleOpEquivalenceFunctor
-/
noncomputable instance :
    CatCommSq (F.mapTriangle.op) (triangleOpEquivalence C).functor
      (triangleOpEquivalence D).functor F.op.mapTriangle :=
  ⟨F.mapTriangleOpCompTriangleOpEquivalenceFunctor⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: CatCommSq.vInv (F.mapTriangle.op) (triangleOpEquivalence C)
      (triangleOpEquivalence D) F.op.mapTriangle inferInstance

中文:
实例 :
  定义体: CatCommSq.vInv (F.mapTriangle.op) (triangleOpEquivalence C)
      (triangleOpEquivalence D) F.op.mapTriangle inferInstance

Depends on / 依赖: CatCommSq, CatCommSq.vInv, F.mapTriangle.op, F.op.mapTriangle, mapTriangle, triangleOpEquivalence
-/
noncomputable instance :
    CatCommSq (F.op.mapTriangle) (triangleOpEquivalence C).inverse
      (triangleOpEquivalence D).inverse F.mapTriangle.op :=
  CatCommSq.vInv (F.mapTriangle.op) (triangleOpEquivalence C)
      (triangleOpEquivalence D) F.op.mapTriangle inferInstance

/--
Definition of `opMapTriangleCompTriangleOpEquivalenceInverse` / `opMapTriangleCompTriangleOpEquivalenceInverse` 的定义

English:
definition opMapTriangleCompTriangleOpEquivalenceInverse
  signature: :
  body: CatCommSq.iso (F.op.mapTriangle) (triangleOpEquivalence C).inverse
      (triangleOpEquivalence D).inverse F.mapTriangle.op

中文:
定义 opMapTriangleCompTriangleOpEquivalenceInverse
  签名: :
  定义体: CatCommSq.iso (F.op.mapTriangle) (triangleOpEquivalence C).inverse
      (triangleOpEquivalence D).inverse F.mapTriangle.op

Depends on / 依赖: CatCommSq, CatCommSq.iso, F.mapTriangle.op, F.op.mapTriangle, inverse, mapTriangle, triangleOpEquivalence
-/
noncomputable def opMapTriangleCompTriangleOpEquivalenceInverse :
    F.op.mapTriangle ⋙ (triangleOpEquivalence D).inverse ≅
      (triangleOpEquivalence C).inverse ⋙ F.mapTriangle.op :=
  CatCommSq.iso (F.op.mapTriangle) (triangleOpEquivalence C).inverse
      (triangleOpEquivalence D).inverse F.mapTriangle.op

end Functor

namespace Pretriangulated.Opposite

open CategoryTheory.Functor in
/-- If `F` is triangulated, so is `F.op`.
-/
scoped instance functor_isTriangulated_op [F.IsTriangulated] : F.op.IsTriangulated where
  map_distinguished T dT := by
    rw [mem_distTriang_op_iff]
    exact Pretriangulated.isomorphic_distinguished _
      ((F.map_distinguished _ (unop_distinguished _ dT))) _
      (((opMapTriangleCompTriangleOpEquivalenceInverse F).symm.app T).unop)

end Pretriangulated.Opposite

namespace Functor

/--
lemma `isTriangulated_of_op` / 引理 `isTriangulated_of_op`

English:
lemma isTriangulated_of_op
  given: [F.op.IsTriangulated]
  statement: F.IsTriangulated where
  proof: by
    have := distinguished_iff_of_iso ((triangleOpEquivalence D).unitIso.app
      (Opposite.op (F.mapTriangle.obj T))).unop
    rw [Functor.id_obj]; rw [Opposite.unop_op (F.mapTriangle.obj T)] at this
    rw [← this]; rw [Functor.comp_obj]; rw [← mem_distTriang_op_iff]; rw [← Functor.op_obj]; rw 

中文:
引理 isTriangulated_of_op
  条件: [F.op.IsTriangulated]
  结论: F.IsTriangulated where
  证明: by
    have := distinguished_iff_of_iso ((triangleOpEquivalence D).unitIso.app
      (Opposite.op (F.mapTriangle.obj T))).unop
    rw [Functor.id_obj]; rw [Opposite.unop_op (F.mapTriangle.obj T)] at this
    rw [← this]; rw [Functor.comp_obj]; rw [← mem_distTriang_op_iff]; rw [← Functor.op_obj]; rw 

Depends on / 依赖: F.mapTriangle.obj, F.op.map_distinguished, Functor, Functor.comp_obj, Functor.id_obj, Functor.op_obj, Opposite, Opposite.op, Opposite.unop_op, comp_obj, distinguished_iff_of_iso, id_obj, mapTriangle, mapTriangleOpCompTriangleOpEquivalenceFunctor, map_distinguished, mem_distTriang_op_iff, op_distinguished, op_obj, triangleOpEquivalence, unitIso
-/
lemma isTriangulated_of_op [F.op.IsTriangulated] : F.IsTriangulated where
  map_distinguished T dT := by
    have := distinguished_iff_of_iso ((triangleOpEquivalence D).unitIso.app
      (Opposite.op (F.mapTriangle.obj T))).unop
    rw [Functor.id_obj]; rw [Opposite.unop_op (F.mapTriangle.obj T)] at this
    rw [← this]; rw [Functor.comp_obj]; rw [← mem_distTriang_op_iff]; rw [← Functor.op_obj]; rw [← Functor.comp_obj]; rw [distinguished_iff_of_iso ((mapTriangleOpCompTriangleOpEquivalenceFunctor F).app
      (Opposite.op T))]
    exact F.op.map_distinguished _ (op_distinguished _ dT)

open Pretriangulated.Opposite in
/--
lemma `op_isTriangulated_iff` / 引理 `op_isTriangulated_iff`

English:
lemma op_isTriangulated_iff
  statement: F.op.IsTriangulated ↔ F.IsTriangulated
  proof: ⟨fun _ => F.isTriangulated_of_op, fun _ => inferInstance⟩

中文:
引理 op_isTriangulated_iff
  结论: F.op.IsTriangulated ↔ F.IsTriangulated
  证明: ⟨fun _ => F.isTriangulated_of_op, fun _ => inferInstance⟩

Depends on / 依赖: F.isTriangulated_of_op, isTriangulated_of_op
-/
lemma op_isTriangulated_iff : F.op.IsTriangulated ↔ F.IsTriangulated :=
  ⟨fun _ => F.isTriangulated_of_op, fun _ => inferInstance⟩

end Functor

end CategoryTheory
