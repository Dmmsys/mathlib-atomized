/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Read, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Opposites

/-!
# Opposite adjunctions

This file contains constructions to relate adjunctions of functors to adjunctions of their
opposites.

## Tags
adjunction, opposite, uniqueness
-/

@[expose] public section


open CategoryTheory

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category theory universes].
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Adjunction

attribute [local simp] homEquiv_unit homEquiv_counit

/-- If `G` is adjoint to `F` then `F.unop` is adjoint to `G.unop`. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {F : Cᵒᵖ ⥤ Dᵒᵖ} {G : Dᵒᵖ ⥤ Cᵒᵖ} (h : G ⊣ F)
  body: NatTrans.unop h.counit
  counit := NatTrans.unop h.unit
  left_triangle_components _ := Quiver.Hom.op_inj (h.right_triangle_components _)
  right_triangle_components _ := Quiver.Hom.op_inj (h.left_triangle_components _)

中文:
定义 unop
  签名: {F : Cᵒᵖ ⥤ Dᵒᵖ} {G : Dᵒᵖ ⥤ Cᵒᵖ} (h : G ⊣ F)
  定义体: NatTrans.unop h.counit
  counit := NatTrans.unop h.unit
  left_triangle_components _ := Quiver.Hom.op_inj (h.right_triangle_components _)
  right_triangle_components _ := Quiver.Hom.op_inj (h.left_triangle_components _)

Depends on / 依赖: NatTrans, NatTrans.unop, counit, h.counit
-/
def unop {F : Cᵒᵖ ⥤ Dᵒᵖ} {G : Dᵒᵖ ⥤ Cᵒᵖ} (h : G ⊣ F) : F.unop ⊣ G.unop where
  unit := NatTrans.unop h.counit
  counit := NatTrans.unop h.unit
  left_triangle_components _ := Quiver.Hom.op_inj (h.right_triangle_components _)
  right_triangle_components _ := Quiver.Hom.op_inj (h.left_triangle_components _)

set_option backward.defeqAttrib.useBackward true in
/-- If `G` is adjoint to `F` then `F.op` is adjoint to `G.op`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: {F : C ⥤ D} {G : D ⥤ C} (h : G ⊣ F)
  body: NatTrans.op h.counit
  counit := NatTrans.op h.unit
  left_triangle_components _ := Quiver.Hom.unop_inj (by simp)
  right_triangle_components _ := Quiver.Hom.unop_inj (by simp)

中文:
定义 op
  签名: {F : C ⥤ D} {G : D ⥤ C} (h : G ⊣ F)
  定义体: NatTrans.op h.counit
  counit := NatTrans.op h.unit
  left_triangle_components _ := Quiver.Hom.unop_inj (by simp)
  right_triangle_components _ := Quiver.Hom.unop_inj (by simp)

Depends on / 依赖: NatTrans, NatTrans.op, counit, h.counit
-/
def op {F : C ⥤ D} {G : D ⥤ C} (h : G ⊣ F) : F.op ⊣ G.op where
  unit := NatTrans.op h.counit
  counit := NatTrans.op h.unit
  left_triangle_components _ := Quiver.Hom.unop_inj (by simp)
  right_triangle_components _ := Quiver.Hom.unop_inj (by simp)

/-- If `F` is adjoint to `G.leftOp` then `G` is adjoint to `F.leftOp`. -/
@[simps]
/--
Definition of `leftOp` / `leftOp` 的定义

English:
definition leftOp
  signature: {F : C ⥤ Dᵒᵖ} {G : D ⥤ Cᵒᵖ} (a : F ⊣ G.leftOp)
  body: NatTrans.unop a.counit
  counit := NatTrans.op a.unit
  left_triangle_components X := congr($(a.right_triangle_components (.op X)).op)
  right_triangle_components X := congr($(a.left_triangle_components X.unop).unop)

中文:
定义 leftOp
  签名: {F : C ⥤ Dᵒᵖ} {G : D ⥤ Cᵒᵖ} (a : F ⊣ G.leftOp)
  定义体: NatTrans.unop a.counit
  counit := NatTrans.op a.unit
  left_triangle_components X := congr($(a.right_triangle_components (.op X)).op)
  right_triangle_components X := congr($(a.left_triangle_components X.unop).unop)

Depends on / 依赖: NatTrans, NatTrans.unop, a.counit, counit
-/
def leftOp {F : C ⥤ Dᵒᵖ} {G : D ⥤ Cᵒᵖ} (a : F ⊣ G.leftOp) : G ⊣ F.leftOp where
  unit := NatTrans.unop a.counit
  counit := NatTrans.op a.unit
  left_triangle_components X := congr($(a.right_triangle_components (.op X)).op)
  right_triangle_components X := congr($(a.left_triangle_components X.unop).unop)

/-- If `F.rightOp` is adjoint to `G` then `G.rightOp` is adjoint to `F`. -/
@[simps]
/--
Definition of `rightOp` / `rightOp` 的定义

English:
definition rightOp
  signature: {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C} (a : F.rightOp ⊣ G)
  body: NatTrans.unop a.counit
  counit := NatTrans.op a.unit
  left_triangle_components X := congr($(a.right_triangle_components (.op X)).op)
  right_triangle_components X := congr($(a.left_triangle_components X.unop).unop)

中文:
定义 rightOp
  签名: {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C} (a : F.rightOp ⊣ G)
  定义体: NatTrans.unop a.counit
  counit := NatTrans.op a.unit
  left_triangle_components X := congr($(a.right_triangle_components (.op X)).op)
  right_triangle_components X := congr($(a.left_triangle_components X.unop).unop)

Depends on / 依赖: NatTrans, NatTrans.unop, a.counit, counit
-/
def rightOp {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C} (a : F.rightOp ⊣ G) : G.rightOp ⊣ F where
  unit := NatTrans.unop a.counit
  counit := NatTrans.op a.unit
  left_triangle_components X := congr($(a.right_triangle_components (.op X)).op)
  right_triangle_components X := congr($(a.left_triangle_components X.unop).unop)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `leftOp_eq` / 引理 `leftOp_eq`

English:
lemma leftOp_eq
  given: {F : C ⥤ Dᵒᵖ} {G : D ⥤ Cᵒᵖ} (a : F ⊣ G.leftOp)
  proof: by
  ext X; simp [Equivalence.unit]

中文:
引理 leftOp_eq
  条件: {F : C ⥤ Dᵒᵖ} {G : D ⥤ Cᵒᵖ} (a : F ⊣ G.leftOp)
  证明: by
  ext X; simp [Equivalence.unit]

Depends on / 依赖: Equivalence, Equivalence.unit
-/
lemma leftOp_eq {F : C ⥤ Dᵒᵖ} {G : D ⥤ Cᵒᵖ} (a : F ⊣ G.leftOp) :
    a.leftOp = (opOpEquivalence D).symm.toAdjunction.comp a.op := by
  ext X; simp [Equivalence.unit]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `rightOp_eq` / 引理 `rightOp_eq`

English:
lemma rightOp_eq
  given: {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C} (a : F.rightOp ⊣ G)
  proof: by
  ext X; simp [Equivalence.unit]

中文:
引理 rightOp_eq
  条件: {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C} (a : F.rightOp ⊣ G)
  证明: by
  ext X; simp [Equivalence.unit]

Depends on / 依赖: Equivalence, Equivalence.unit
-/
lemma rightOp_eq {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C} (a : F.rightOp ⊣ G) :
    a.rightOp = (opOpEquivalence D).symm.toAdjunction.comp a.op := by
  ext X; simp [Equivalence.unit]

set_option backward.defeqAttrib.useBackward true in
/-- If `F` and `F'` are both adjoint to `G`, there is a natural isomorphism
`F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda`.
We use this in combination with `fullyFaithfulCancelRight` to show left adjoints are unique.
-/
@[deprecated "No replacement" (since := "2026-04-11")]
/--
Definition of `leftAdjointsCoyonedaEquiv` / `leftAdjointsCoyonedaEquiv` 的定义

English:
definition leftAdjointsCoyonedaEquiv
  signature: {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  body: NatIso.ofComponents fun X =>
    NatIso.ofComponents fun Y =>
      ((adj1.homEquiv X.unop Y).trans (adj2.homEquiv X.unop Y).symm).toIso

中文:
定义 leftAdjointsCoyonedaEquiv
  签名: {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  定义体: NatIso.ofComponents fun X =>
    NatIso.ofComponents fun Y =>
      ((adj1.homEquiv X.unop Y).trans (adj2.homEquiv X.unop Y).symm).toIso

Depends on / 依赖: NatIso, NatIso.ofComponents, X.unop, adj1.homEquiv, adj2.homEquiv, homEquiv, ofComponents
-/
def leftAdjointsCoyonedaEquiv {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda :=
  NatIso.ofComponents fun X =>
    NatIso.ofComponents fun Y =>
      ((adj1.homEquiv X.unop Y).trans (adj2.homEquiv X.unop Y).symm).toIso

/-- Deprecated: prefer `(Adjunction.conjugateIsoEquiv adj1 adj2).symm`. -/
@[deprecated "Use `(Adjunction.conjugateIsoEquiv adj1 adj2).symm` \
  (requires `import Mathlib.CategoryTheory.Adjunction.Mates`)." (since := "2026-01-31")]
/--
Definition of `natIsoOfRightAdjointNatIso` / `natIsoOfRightAdjointNatIso` 的定义

English:
definition natIsoOfRightAdjointNatIso
  signature: {F F' : C ⥤ D} {G G' : D ⥤ C}
  body: NatIso.removeOp ((Coyoneda.fullyFaithful.whiskeringRight _).isoEquiv.symm
    (leftAdjointsCoyonedaEquiv adj2 (adj1.ofNatIsoRight r)))

中文:
定义 natIsoOfRightAdjointNatIso
  签名: {F F' : C ⥤ D} {G G' : D ⥤ C}
  定义体: NatIso.removeOp ((Coyoneda.fullyFaithful.whiskeringRight _).isoEquiv.symm
    (leftAdjointsCoyonedaEquiv adj2 (adj1.ofNatIsoRight r)))

Depends on / 依赖: Coyoneda, Coyoneda.fullyFaithful.whiskeringRight, NatIso, NatIso.removeOp, adj1.ofNatIsoRight, fullyFaithful, isoEquiv, isoEquiv.symm, leftAdjointsCoyonedaEquiv, ofNatIsoRight, removeOp, whiskeringRight
-/
def natIsoOfRightAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (r : G ≅ G') : F ≅ F' :=
  NatIso.removeOp ((Coyoneda.fullyFaithful.whiskeringRight _).isoEquiv.symm
    (leftAdjointsCoyonedaEquiv adj2 (adj1.ofNatIsoRight r)))

/-- Deprecated: prefer `Adjunction.conjugateIsoEquiv adj1 adj2`. -/
@[deprecated "Use `Adjunction.conjugateIsoEquiv adj1 adj2` \
  (requires `import Mathlib.CategoryTheory.Adjunction.Mates`)." (since := "2026-01-31")]
/--
Definition of `natIsoOfLeftAdjointNatIso` / `natIsoOfLeftAdjointNatIso` 的定义

English:
definition natIsoOfLeftAdjointNatIso
  signature: {F F' : C ⥤ D} {G G' : D ⥤ C}
  body: NatIso.removeOp (natIsoOfRightAdjointNatIso (op adj2) (op adj1) (NatIso.op l))

中文:
定义 natIsoOfLeftAdjointNatIso
  签名: {F F' : C ⥤ D} {G G' : D ⥤ C}
  定义体: NatIso.removeOp (natIsoOfRightAdjointNatIso (op adj2) (op adj1) (NatIso.op l))

Depends on / 依赖: NatIso, NatIso.op, NatIso.removeOp, natIsoOfRightAdjointNatIso, removeOp
-/
def natIsoOfLeftAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (l : F ≅ F') : G ≅ G' :=
  NatIso.removeOp (natIsoOfRightAdjointNatIso (op adj2) (op adj1) (NatIso.op l))

end Adjunction

namespace Functor

/--
Instance `IsLeftAdjoint.op` / 实例 `IsLeftAdjoint.op`

English:
instance IsLeftAdjoint.op
  signature: {F : C ⥤ D} [F.IsLeftAdjoint]
  body: ⟨F.rightAdjoint.op, ⟨.op .ofIsLeftAdjoint _⟩⟩

中文:
实例 IsLeftAdjoint.op
  签名: {F : C ⥤ D} [F.IsLeftAdjoint]
  定义体: ⟨F.rightAdjoint.op, ⟨.op .ofIsLeftAdjoint _⟩⟩

Depends on / 依赖: F.rightAdjoint.op, ofIsLeftAdjoint, rightAdjoint
-/
instance IsLeftAdjoint.op {F : C ⥤ D} [F.IsLeftAdjoint] : F.op.IsRightAdjoint :=
⟨F.rightAdjoint.op, ⟨.op .ofIsLeftAdjoint _⟩⟩

/--
Instance `IsRightAdjoint.op` / 实例 `IsRightAdjoint.op`

English:
instance IsRightAdjoint.op
  signature: {F : C ⥤ D} [F.IsRightAdjoint]
  body: ⟨F.leftAdjoint.op, ⟨.op .ofIsRightAdjoint _⟩⟩

中文:
实例 IsRightAdjoint.op
  签名: {F : C ⥤ D} [F.IsRightAdjoint]
  定义体: ⟨F.leftAdjoint.op, ⟨.op .ofIsRightAdjoint _⟩⟩

Depends on / 依赖: F.leftAdjoint.op, leftAdjoint, ofIsRightAdjoint
-/
instance IsRightAdjoint.op {F : C ⥤ D} [F.IsRightAdjoint] : F.op.IsLeftAdjoint :=
⟨F.leftAdjoint.op, ⟨.op .ofIsRightAdjoint _⟩⟩

/--
Instance `IsLeftAdjoint.leftOp` / 实例 `IsLeftAdjoint.leftOp`

English:
instance IsLeftAdjoint.leftOp
  signature: {F : C ⥤ Dᵒᵖ} [F.IsLeftAdjoint]
  body: ⟨F.rightAdjoint.rightOp, ⟨.leftOp .ofIsLeftAdjoint _⟩⟩

中文:
实例 IsLeftAdjoint.leftOp
  签名: {F : C ⥤ Dᵒᵖ} [F.IsLeftAdjoint]
  定义体: ⟨F.rightAdjoint.rightOp, ⟨.leftOp .ofIsLeftAdjoint _⟩⟩

Depends on / 依赖: F.rightAdjoint.rightOp, inhabit, leftOp, ofIsLeftAdjoint, rightAdjoint, rightOp
-/
instance IsLeftAdjoint.leftOp {F : C ⥤ Dᵒᵖ} [F.IsLeftAdjoint] : F.leftOp.IsRightAdjoint :=
⟨F.rightAdjoint.rightOp, ⟨.leftOp .ofIsLeftAdjoint _⟩⟩

-- TODO: Do we need to introduce `Adjunction.leftUnop`?
/--
Instance `IsRightAdjoint.leftOp` / 实例 `IsRightAdjoint.leftOp`

English:
instance IsRightAdjoint.leftOp
  signature: {F : C ⥤ Dᵒᵖ} [F.IsRightAdjoint]
  body: inferInstanceAs (F.op ⋙ (opOpEquivalence D).functor).IsLeftAdjoint

中文:
实例 IsRightAdjoint.leftOp
  签名: {F : C ⥤ Dᵒᵖ} [F.IsRightAdjoint]
  定义体: inferInstanceAs (F.op ⋙ (opOpEquivalence D).functor).IsLeftAdjoint

Depends on / 依赖: F.op, IsLeftAdjoint, functor, opOpEquivalence
-/
instance IsRightAdjoint.leftOp {F : C ⥤ Dᵒᵖ} [F.IsRightAdjoint] : F.leftOp.IsLeftAdjoint :=
  inferInstanceAs (F.op ⋙ (opOpEquivalence D).functor).IsLeftAdjoint

-- TODO: Do we need to introduce `Adjunction.rightUnop`?
/--
Instance `IsLeftAdjoint.rightOp` / 实例 `IsLeftAdjoint.rightOp`

English:
instance IsLeftAdjoint.rightOp
  signature: {F : Cᵒᵖ ⥤ D} [F.IsLeftAdjoint]
  body: inferInstanceAs ((opOpEquivalence C).inverse ⋙ F.op).IsRightAdjoint

中文:
实例 IsLeftAdjoint.rightOp
  签名: {F : Cᵒᵖ ⥤ D} [F.IsLeftAdjoint]
  定义体: inferInstanceAs ((opOpEquivalence C).inverse ⋙ F.op).IsRightAdjoint

Depends on / 依赖: F.op, IsRightAdjoint, inverse, opOpEquivalence
-/
instance IsLeftAdjoint.rightOp {F : Cᵒᵖ ⥤ D} [F.IsLeftAdjoint] : F.rightOp.IsRightAdjoint :=
  inferInstanceAs ((opOpEquivalence C).inverse ⋙ F.op).IsRightAdjoint

/--
Instance `IsRightAdjoint.rightOp` / 实例 `IsRightAdjoint.rightOp`

English:
instance IsRightAdjoint.rightOp
  signature: {F : Cᵒᵖ ⥤ D} [F.IsRightAdjoint]
  body: ⟨F.leftAdjoint.leftOp, ⟨.rightOp .ofIsRightAdjoint _⟩⟩

中文:
实例 IsRightAdjoint.rightOp
  签名: {F : Cᵒᵖ ⥤ D} [F.IsRightAdjoint]
  定义体: ⟨F.leftAdjoint.leftOp, ⟨.rightOp .ofIsRightAdjoint _⟩⟩

Depends on / 依赖: F.leftAdjoint.leftOp, leftAdjoint, leftOp, ofIsRightAdjoint, rightOp
-/
instance IsRightAdjoint.rightOp {F : Cᵒᵖ ⥤ D} [F.IsRightAdjoint] : F.rightOp.IsLeftAdjoint :=
⟨F.leftAdjoint.leftOp, ⟨.rightOp .ofIsRightAdjoint _⟩⟩

end Functor
end CategoryTheory
