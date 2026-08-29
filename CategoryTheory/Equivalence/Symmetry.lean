/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Functoriality of the symmetry of equivalences

Using the calculus of mates in `Mathlib.CategoryTheory.Adjunction.Mates`, we prove that passing
to the symmetric equivalence defines an equivalence between `C ≌ D` and `(D ≌ C)ᵒᵖ`,
and provides the definition of the functor that takes an equivalence to its inverse.

## Main definitions
- `Equivalence.symmEquiv C D`: the equivalence `(C ≌ D) ≌ (D ≌ C)ᵒᵖ` obtained by
  taking `Equivalence.symm` on objects, and `conjugateEquiv` on maps.
- `Equivalence.inverseFunctor C D`: The functor `(C ≌ D) ⥤ (D ⥤ C)ᵒᵖ` sending an equivalence
  `e` to the functor `e.inverse`.
- `congrLeftFunctor C D E`: the functor (C ≌ D) ⥤ ((C ⥤ E) ≌ (D ⥤ E))ᵒᵖ that applies
  `Equivalence.congrLeft` on objects, and whiskers left by `conjugateEquiv` on maps.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

namespace Equivalence

variable (C : Type*) [Category* C] (D : Type*) [Category* D]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The forward functor of the equivalence `(C ≌ D) ≌ (D ≌ C)ᵒᵖ`. -/
@[simps]
/--
Definition of `symmEquivFunctor` / `symmEquivFunctor` 的定义

English:
definition symmEquivFunctor
  signature: : (C ≌ D) ⥤ (D ≌ C)ᵒᵖ where
  body: Opposite.op e.symm
  map {e f} α := (mkHom <| conjugateEquiv f.toAdjunction e.toAdjunction <| asNatTrans α).op
  map_comp _ _ := Quiver.Hom.unop_inj (by cat_disch)

中文:
定义 symmEquivFunctor
  签名: : (C ≌ D) ⥤ (D ≌ C)ᵒᵖ where
  定义体: Opposite.op e.symm
  map {e f} α := (mkHom <| conjugateEquiv f.toAdjunction e.toAdjunction <| asNatTrans α).op
  map_comp _ _ := Quiver.Hom.unop_inj (by cat_disch)

Depends on / 依赖: Opposite, Opposite.op, e.symm
-/
def symmEquivFunctor : (C ≌ D) ⥤ (D ≌ C)ᵒᵖ where
  obj e := Opposite.op e.symm
  map {e f} α := (mkHom <| conjugateEquiv f.toAdjunction e.toAdjunction <| asNatTrans α).op
  map_comp _ _ := Quiver.Hom.unop_inj (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor of the equivalence `(C ≌ D) ≌ (D ≌ C)ᵒᵖ`. -/
@[simps!]
/--
Definition of `symmEquivInverse` / `symmEquivInverse` 的定义

English:
definition symmEquivInverse
  signature: : (D ≌ C)ᵒᵖ ⥤ (C ≌ D)
  body: Functor.leftOp
    { obj e := Opposite.op e.symm
map {e f} α := Quiver.Hom.op mkHom
.invFun asNatTrans α conjugateEquiv e.symm.toAdjunction f.symm.toAdjunction
      map_comp _ _ := Quiver.Hom.unop_inj (by cat_disch) }

中文:
定义 symmEquivInverse
  签名: : (D ≌ C)ᵒᵖ ⥤ (C ≌ D)
  定义体: Functor.leftOp
    { obj e := Opposite.op e.symm
map {e f} α := Quiver.Hom.op mkHom
.invFun asNatTrans α conjugateEquiv e.symm.toAdjunction f.symm.toAdjunction
      map_comp _ _ := Quiver.Hom.unop_inj (by cat_disch) }

Depends on / 依赖: Functor, Functor.leftOp, Opposite, Opposite.op, Quiver, Quiver.Hom.op, Quiver.Hom.unop_inj, asNatTrans, cat_disch, conjugateEquiv, e.symm, e.symm.toAdjunction, f.symm.toAdjunction, invFun, leftOp, map_comp, toAdjunction, unop_inj
-/
def symmEquivInverse : (D ≌ C)ᵒᵖ ⥤ (C ≌ D) :=
  Functor.leftOp
    { obj e := Opposite.op e.symm
map {e f} α := Quiver.Hom.op mkHom
.invFun asNatTrans α conjugateEquiv e.symm.toAdjunction f.symm.toAdjunction
      map_comp _ _ := Quiver.Hom.unop_inj (by cat_disch) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Taking the symmetric of an equivalence induces an equivalence of categories
`(C ≌ D) ≌ (D ≌ C)ᵒᵖ`. -/
@[simps]
/--
Definition of `symmEquiv` / `symmEquiv` 的定义

English:
definition symmEquiv
  signature: : (C ≌ D) ≌ (D ≌ C)ᵒᵖ where
  body: symmEquivFunctor _ _
  inverse := symmEquivInverse _ _
  counitIso :=
NatIso.ofComponents (fun e => Iso.op <| Iso.refl _) fun _ =>
      (by simp [symm, symmEquivInverse])
  unitIso :=
NatIso.ofComponents (fun e => Iso.refl _) fun _ => by
      ext c
      simp [symm, symmEquivInverse]
  functor_uni

中文:
定义 symmEquiv
  签名: : (C ≌ D) ≌ (D ≌ C)ᵒᵖ where
  定义体: symmEquivFunctor _ _
  inverse := symmEquivInverse _ _
  counitIso :=
NatIso.ofComponents (fun e => Iso.op <| Iso.refl _) fun _ =>
      (by simp [symm, symmEquivInverse])
  unitIso :=
NatIso.ofComponents (fun e => Iso.refl _) fun _ => by
      ext c
      simp [symm, symmEquivInverse]
  functor_uni

Depends on / 依赖: symmEquivFunctor
-/
def symmEquiv : (C ≌ D) ≌ (D ≌ C)ᵒᵖ where
  functor := symmEquivFunctor _ _
  inverse := symmEquivInverse _ _
  counitIso :=
NatIso.ofComponents (fun e => Iso.op <| Iso.refl _) fun _ =>
      (by simp [symm, symmEquivInverse])
  unitIso :=
NatIso.ofComponents (fun e => Iso.refl _) fun _ => by
      ext c
      simp [symm, symmEquivInverse]
  functor_unitIso_comp X := by
    simp [symm, symmEquivInverse]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The `inverse` functor that sends a functor to its inverse. -/
@[simps!]
/--
Definition of `inverseFunctor` / `inverseFunctor` 的定义

English:
definition inverseFunctor
  signature: : (C ≌ D) ⥤ (D ⥤ C)ᵒᵖ
  body: (symmEquiv C D).functor ⋙ (Functor.op <| functorFunctor D C)

中文:
定义 inverseFunctor
  签名: : (C ≌ D) ⥤ (D ⥤ C)ᵒᵖ
  定义体: (symmEquiv C D).functor ⋙ (Functor.op <| functorFunctor D C)

Depends on / 依赖: Functor, Functor.op, functor, functorFunctor, symmEquiv
-/
def inverseFunctor : (C ≌ D) ⥤ (D ⥤ C)ᵒᵖ :=
  (symmEquiv C D).functor ⋙ (Functor.op <| functorFunctor D C)

variable {C D}

set_option backward.isDefEq.respectTransparency.types false in
/-- The `inverse` functor sends an equivalence to its inverse. -/
@[simps!]
/--
Definition of `inverseFunctorObjIso` / `inverseFunctorObjIso` 的定义

English:
definition inverseFunctorObjIso
  signature: (e : C ≌ D)
  body: Iso.refl _

中文:
定义 inverseFunctorObjIso
  签名: (e : C ≌ D)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def inverseFunctorObjIso (e : C ≌ D) :
    (inverseFunctor C D).obj e ≅ Opposite.op e.inverse := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `inverseFunctorMapIso_symm_eq_isoInverseOfIsoFunctor` / 引理 `inverseFunctorMapIso_symm_eq_isoInverseOfIsoFunctor`

English:
lemma inverseFunctorMapIso_symm_eq_isoInverseOfIsoFunctor
  given: {e f : C ≌ D} (α : e ≅ f)
  proof: by
  cat_disch

中文:
引理 inverseFunctorMapIso_symm_eq_isoInverseOfIsoFunctor
  条件: {e f : C ≌ D} (α : e ≅ f)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma inverseFunctorMapIso_symm_eq_isoInverseOfIsoFunctor {e f : C ≌ D} (α : e ≅ f) :
    Iso.unop ((inverseFunctor C D).mapIso α.symm) =
    Iso.isoInverseOfIsoFunctor ((functorFunctor _ _).mapIso α) := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-- An "unopped" version of the equivalence `inverseFunctorObj'`. -/
@[simps!]
/--
Definition of `inverseFunctorObj'` / `inverseFunctorObj'` 的定义

English:
definition inverseFunctorObj'
  signature: (e : C ≌ D)
  body: Iso.refl _

中文:
定义 inverseFunctorObj'
  签名: (e : C ≌ D)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl, getBinaryBiproductData
-/
def inverseFunctorObj' (e : C ≌ D) :
    Opposite.unop ((inverseFunctor C D).obj e) ≅ e.inverse :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
variable (C D) in
/-- Promoting `Equivalence.congrLeft` to a functor. -/
@[simps!]
/--
Definition of `congrLeftFunctor` / `congrLeftFunctor` 的定义

English:
definition congrLeftFunctor
  signature: (E : Type*) [Category* E]
  body: Functor.rightOp
    { obj f := f.unop.congrLeft
map {e f} α := mkHom (whiskeringLeft _ _ _).map
conjugateEquiv e.unop.toAdjunction f.unop.toAdjunction asNatTrans
          Quiver.Hom.unop α
      map_comp _ _ := by
        ext
        simp [← map_comp] }

中文:
定义 congrLeftFunctor
  签名: (E : 类型) [范畴* E]
  定义体: Functor.rightOp
    { obj f := f.unop.congrLeft
map {e f} α := mkHom (whiskeringLeft _ _ _).map
conjugateEquiv e.unop.toAdjunction f.unop.toAdjunction asNatTrans
          Quiver.Hom.unop α
      map_comp _ _ := by
        ext
        simp [← map_comp] }

Depends on / 依赖: Functor, Functor.rightOp, Quiver, Quiver.Hom.unop, asNatTrans, congrLeft, conjugateEquiv, e.unop.toAdjunction, f.unop.congrLeft, f.unop.toAdjunction, map_comp, rightOp, toAdjunction, whiskeringLeft
-/
def congrLeftFunctor (E : Type*) [Category* E] : (C ≌ D) ⥤ ((C ⥤ E) ≌ (D ⥤ E))ᵒᵖ :=
  Functor.rightOp
    { obj f := f.unop.congrLeft
map {e f} α := mkHom (whiskeringLeft _ _ _).map
conjugateEquiv e.unop.toAdjunction f.unop.toAdjunction asNatTrans
          Quiver.Hom.unop α
      map_comp _ _ := by
        ext
        simp [← map_comp] }

end Equivalence

end CategoryTheory
