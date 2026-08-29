/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Data.Setoid.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# (Co)limits of functors out of `SingleObj M`

We characterise (co)limits of shape `SingleObj M`. Currently only in the category of types.

## Main results

* `SingleObj.Types.limitEquivFixedPoints`: The limit of `J : SingleObj G ⥤ Type u` is the fixed
  points of `J.obj (SingleObj.star G)` under the induced action.

* `SingleObj.Types.colimitEquivQuotient`: The colimit of `J : SingleObj G ⥤ Type u` is the
  quotient of `J.obj (SingleObj.star G)` by the induced action.

-/

@[expose] public section

assert_not_exists MonoidWithZero

universe u v

namespace CategoryTheory

namespace Limits

namespace SingleObj

variable {M G : Type v} [Monoid M] [Group G]

/-- The induced `G`-action on the target of `J : SingleObj G ⥤ Type u`. -/
instance (J : SingleObj M ⥤ Type u) : MulAction M (J.obj (SingleObj.star M)) where
  smul g x := J.map g x
  one_smul x := by
    change J.map (𝟙 _) x = x
    simp
  mul_smul g h x := by
    change J.map (g * h) x = (J.map h ≫ J.map g) x
    rw [← SingleObj.comp_as_mul]
    · simp
      rfl

section Limits

variable (J : SingleObj M ⥤ Type u)

/-- The equivalence between sections of `J : SingleObj M ⥤ Type u` and fixed points of the
induced action on `J.obj (SingleObj.star M)`. -/
@[simps]
/--
Definition of `Types.sections.equivFixedPoints` / `Types.sections.equivFixedPoints` 的定义

English:
definition Types.sections.equivFixedPoints
  signature: :
  body: ⟨s.val _, s.property⟩
  invFun p := ⟨fun _ => p.val, p.property⟩

中文:
定义 Types.sections.equivFixedPoints
  签名: :
  定义体: ⟨s.val _, s.property⟩
  invFun p := ⟨fun _ => p.val, p.property⟩

Depends on / 依赖: property, s.property, s.val
-/
def Types.sections.equivFixedPoints :
    J.sections ≃ MulAction.fixedPoints M (J.obj (SingleObj.star M)) where
  toFun s := ⟨s.val _, s.property⟩
  invFun p := ⟨fun _ => p.val, p.property⟩

/-- The limit of `J : SingleObj M ⥤ Type u` is equivalent to the fixed points of the
induced action on `J.obj (SingleObj.star M)`. -/
@[simps!]
/--
Definition of `Types.limitEquivFixedPoints` / `Types.limitEquivFixedPoints` 的定义

English:
definition Types.limitEquivFixedPoints
  signature: :
  body: (Types.limitEquivSections J).trans (Types.sections.equivFixedPoints J)

中文:
定义 Types.limitEquivFixedPoints
  签名: :
  定义体: (Types.limitEquivSections J).trans (Types.sections.equivFixedPoints J)

Depends on / 依赖: Types.limitEquivSections, Types.sections.equivFixedPoints, equivFixedPoints, limitEquivSections, sections
-/
noncomputable def Types.limitEquivFixedPoints :
    limit J ≃ MulAction.fixedPoints M (J.obj (SingleObj.star M)) :=
  (Types.limitEquivSections J).trans (Types.sections.equivFixedPoints J)

end Limits

section Colimits

variable {G : Type v} [Group G] (J : SingleObj G ⥤ Type u)

/--
lemma `colimitTypeRel_iff_orbitRel` / 引理 `colimitTypeRel_iff_orbitRel`

English:
lemma colimitTypeRel_iff_orbitRel
  given: (x y : J.obj (SingleObj.star G))
  proof: by
  conv => rhs; rw [Setoid.comm']
  change (exists g : G, y = g • x) ↔ (exists g : G, g • x = y)
  grind

中文:
引理 colimitTypeRel_iff_orbitRel
  条件: (x y : J.obj (SingleObj.star G))
  证明: by
  conv => rhs; rw [Setoid.comm']
  change (exists g : G, y = g • x) ↔ (exists g : G, g • x = y)
  grind

Depends on / 依赖: Setoid, Setoid.comm
-/
lemma colimitTypeRel_iff_orbitRel (x y : J.obj (SingleObj.star G)) :
    J.ColimitTypeRel ⟨SingleObj.star G, x⟩ ⟨SingleObj.star G, y⟩ ↔
      MulAction.orbitRel G (J.obj (SingleObj.star G)) x y := by
  conv => rhs; rw [Setoid.comm']
  change (exists g : G, y = g • x) ↔ (exists g : G, g • x = y)
  grind

/-- The explicit quotient construction of the colimit of `J : SingleObj G ⥤ Type u` is
equivalent to the quotient of `J.obj (SingleObj.star G)` by the induced action. -/
@[simps]
/--
Definition of `colimitTypeRelEquivOrbitRelQuotient` / `colimitTypeRelEquivOrbitRelQuotient` 的定义

English:
definition colimitTypeRelEquivOrbitRelQuotient
  signature: :
  body: Quot.lift (fun p => ⟦p.2⟧) fun a b h => Quotient.sound
    (colimitTypeRel_iff_orbitRel J a.2 b.2).mp h
invFun := Quot.lift (fun x => Quot.mk _ ⟨SingleObj.star G, x⟩) fun a b h =>
Quot.sound (colimitTypeRel_iff_orbitRel J a b).mpr h
  left_inv := fun x => Quot.inductionOn x (fun _ => rfl)
  right_inv := fun x => Quot.inductionOn x (fun _ => rfl)

#adaptation_note

中文:
定义 colimitTypeRelEquivOrbitRelQuotient
  签名: :
  定义体: Quot.lift (fun p => ⟦p.2⟧) fun a b h => Quotient.sound
    (colimitTypeRel_iff_orbitRel J a.2 b.2).mp h
invFun := Quot.lift (fun x => Quot.mk _ ⟨SingleObj.star G, x⟩) fun a b h =>
Quot.sound (colimitTypeRel_iff_orbitRel J a b).mpr h
  left_inv := fun x => Quot.inductionOn x (fun _ => rfl)
  right_inv := fun x => Quot.inductionOn x (fun _ => rfl)

#adaptation_note

Depends on / 依赖: Quot.lift, Quotient, Quotient.sound
-/
def colimitTypeRelEquivOrbitRelQuotient :
    J.ColimitType ≃ MulAction.orbitRel.Quotient G (J.obj (SingleObj.star G)) where
toFun := Quot.lift (fun p => ⟦p.2⟧) fun a b h => Quotient.sound
    (colimitTypeRel_iff_orbitRel J a.2 b.2).mp h
invFun := Quot.lift (fun x => Quot.mk _ ⟨SingleObj.star G, x⟩) fun a b h =>
Quot.sound (colimitTypeRel_iff_orbitRel J a b).mpr h
  left_inv := fun x => Quot.inductionOn x (fun _ => rfl)
  right_inv := fun x => Quot.inductionOn x (fun _ => rfl)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The colimit of `J : SingleObj G ⥤ Type u` is equivalent to the quotient of
`J.obj (SingleObj.star G)` by the induced action. -/
@[simps!]
/--
Definition of `Types.colimitEquivQuotient` / `Types.colimitEquivQuotient` 的定义

English:
definition Types.colimitEquivQuotient
  signature: :
  body: (Types.colimitEquivColimitType J).trans (colimitTypeRelEquivOrbitRelQuotient J)

中文:
定义 Types.colimitEquivQuotient
  签名: :
  定义体: (Types.colimitEquivColimitType J).trans (colimitTypeRelEquivOrbitRelQuotient J)

Depends on / 依赖: Types.colimitEquivColimitType, colimitEquivColimitType, colimitTypeRelEquivOrbitRelQuotient
-/
noncomputable def Types.colimitEquivQuotient :
    colimit J ≃ MulAction.orbitRel.Quotient G (J.obj (SingleObj.star G)) :=
  (Types.colimitEquivColimitType J).trans (colimitTypeRelEquivOrbitRelQuotient J)

end Colimits

end SingleObj

end Limits

end CategoryTheory
