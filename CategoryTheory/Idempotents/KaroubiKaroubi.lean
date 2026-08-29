/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotence of the Karoubi envelope

In this file, we construct the equivalence of categories
`KaroubiKaroubi.equivalence C : Karoubi C ≌ Karoubi (Karoubi C)` for any category `C`.

-/

@[expose] public section


open CategoryTheory.Category

open CategoryTheory.Idempotents.Karoubi

namespace CategoryTheory

namespace Idempotents

namespace KaroubiKaroubi

variable (C : Type*) [Category* C]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `idem_f` / 引理 `idem_f`

English:
lemma idem_f
  given: (P : Karoubi (Karoubi C))
  statement: P.p.f ≫ P.p.f = P.p.f
  proof: by
  simpa only [hom_ext_iff, comp_f] using P.idem

中文:
引理 idem_f
  条件: (P : Karoubi (Karoubi C))
  结论: P.p.f ≫ P.p.f = P.p.f
  证明: by
  simpa only [hom_ext_iff, comp_f] using P.idem

Depends on / 依赖: P.idem, comp_f, hom_ext_iff
-/
lemma idem_f (P : Karoubi (Karoubi C)) : P.p.f ≫ P.p.f = P.p.f := by
  simpa only [hom_ext_iff, comp_f] using P.idem

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `p_comm_f` / 引理 `p_comm_f`

English:
lemma p_comm_f
  given: {P Q : Karoubi (Karoubi C)} (f : P ⟶ Q)
  statement: P.p.f ≫ f.f.f = f.f.f ≫ Q.p.f
  proof: by
  simpa only [hom_ext_iff, comp_f] using p_comm f

中文:
引理 p_comm_f
  条件: {P Q : Karoubi (Karoubi C)} (f : P ⟶ Q)
  结论: P.p.f ≫ f.f.f = f.f.f ≫ Q.p.f
  证明: by
  simpa only [hom_ext_iff, comp_f] using p_comm f

Depends on / 依赖: comp_f, hom_ext_iff, p_comm
-/
lemma p_comm_f {P Q : Karoubi (Karoubi C)} (f : P ⟶ Q) : P.p.f ≫ f.f.f = f.f.f ≫ Q.p.f := by
  simpa only [hom_ext_iff, comp_f] using p_comm f

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical functor `Karoubi (Karoubi C) ⥤ Karoubi C` -/
@[simps]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : Karoubi (Karoubi C) ⥤ Karoubi C where
  body: ⟨P.X.X, P.p.f, by simpa only [hom_ext_iff] using! P.idem⟩
  map f := ⟨f.f.f, by simpa only [hom_ext_iff] using! f.comm⟩

中文:
定义 inverse
  签名: : Karoubi (Karoubi C) ⥤ Karoubi C where
  定义体: ⟨P.X.X, P.p.f, by simpa only [hom_ext_iff] using! P.idem⟩
  map f := ⟨f.f.f, by simpa only [hom_ext_iff] using! f.comm⟩

Depends on / 依赖: P.X.X, P.idem, P.p.f, hom_ext_iff
-/
def inverse : Karoubi (Karoubi C) ⥤ Karoubi C where
  obj P := ⟨P.X.X, P.p.f, by simpa only [hom_ext_iff] using! P.idem⟩
  map f := ⟨f.f.f, by simpa only [hom_ext_iff] using! f.comm⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: C] : Functor.Additive (inverse C) where

中文:
实例 [预加性
  签名: C] : 函子.加性 (inverse C) where
-/
instance [Preadditive C] : Functor.Additive (inverse C) where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit isomorphism of the equivalence -/
@[simps!]
/--
Definition of `unitIso` / `unitIso` 的定义

English:
definition unitIso
  signature: : 𝟭 (Karoubi C) ≅ toKaroubi (Karoubi C) ⋙ inverse C
  body: eqToIso (Functor.ext (by cat_disch) (by simp))

中文:
定义 unitIso
  签名: : 𝟭 (Karoubi C) ≅ toKaroubi (Karoubi C) ⋙ inverse C
  定义体: eqToIso (Functor.ext (by cat_disch) (by simp))

Depends on / 依赖: Functor, Functor.ext, cat_disch, eqToIso
-/
def unitIso : 𝟭 (Karoubi C) ≅ toKaroubi (Karoubi C) ⋙ inverse C :=
  eqToIso (Functor.ext (by cat_disch) (by simp))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] p_comm_f in
/-- The counit isomorphism of the equivalence -/
@[simps]
/--
Definition of `counitIso` / `counitIso` 的定义

English:
definition counitIso
  signature: : inverse C ⋙ toKaroubi (Karoubi C) ≅ 𝟭 (Karoubi (Karoubi C)) where
  body: { app := fun P => { f := { f := P.p.1 } } }
  inv := { app := fun P => { f := { f := P.p.1 } } }

中文:
定义 counitIso
  签名: : inverse C ⋙ toKaroubi (Karoubi C) ≅ 𝟭 (Karoubi (Karoubi C)) where
  定义体: { app := fun P => { f := { f := P.p.1 } } }
  inv := { app := fun P => { f := { f := P.p.1 } } }
-/
def counitIso : inverse C ⋙ toKaroubi (Karoubi C) ≅ 𝟭 (Karoubi (Karoubi C)) where
  hom := { app := fun P => { f := { f := P.p.1 } } }
  inv := { app := fun P => { f := { f := P.p.1 } } }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `Karoubi C ≌ Karoubi (Karoubi C)` -/
@[simps]
/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: : Karoubi C ≌ Karoubi (Karoubi C) where
  body: toKaroubi (Karoubi C)
  inverse := KaroubiKaroubi.inverse C
  unitIso := KaroubiKaroubi.unitIso C
  counitIso := KaroubiKaroubi.counitIso C

中文:
定义 equivalence
  签名: : Karoubi C ≌ Karoubi (Karoubi C) where
  定义体: toKaroubi (Karoubi C)
  inverse := KaroubiKaroubi.inverse C
  unitIso := KaroubiKaroubi.unitIso C
  counitIso := KaroubiKaroubi.counitIso C

Depends on / 依赖: Karoubi, toKaroubi
-/
def equivalence : Karoubi C ≌ Karoubi (Karoubi C) where
  functor := toKaroubi (Karoubi C)
  inverse := KaroubiKaroubi.inverse C
  unitIso := KaroubiKaroubi.unitIso C
  counitIso := KaroubiKaroubi.counitIso C

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `equivalence.additive_functor` / 实例 `equivalence.additive_functor`

English:
instance equivalence.additive_functor
  signature: [Preadditive C]

中文:
实例 equivalence.additive_functor
  签名: [预加性 C]
-/
instance equivalence.additive_functor [Preadditive C] :
    Functor.Additive (equivalence C).functor where

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `equivalence.additive_inverse` / 实例 `equivalence.additive_inverse`

English:
instance equivalence.additive_inverse
  signature: [Preadditive C]

中文:
实例 equivalence.additive_inverse
  签名: [预加性 C]
-/
instance equivalence.additive_inverse [Preadditive C] :
    Functor.Additive (equivalence C).inverse where

end KaroubiKaroubi

end Idempotents

end CategoryTheory
