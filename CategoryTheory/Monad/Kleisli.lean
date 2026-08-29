/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monad.Basic

/-! # Kleisli category on a (co)monad

This file defines the Kleisli category on a monad `(T, η_ T, μ_ T)` as well as the co-Kleisli
category on a comonad `(U, ε_ U, δ_ U)`. It also defines the Kleisli adjunction which gives rise to
the monad `(T, η_ T, μ_ T)` as well as the co-Kleisli adjunction which gives rise to the comonad
`(U, ε_ U, δ_ U)`.

## References
* [Riehl, *Category theory in context*, Definition 5.2.9][riehl2017]
-/

@[expose] public section


namespace CategoryTheory

universe v u

-- morphism levels before object levels. See note [category theory universes].
variable {C : Type u} [Category.{v} C]

/--
Definition of `Kleisli` / `Kleisli` 的定义

English:
structure Kleisli
  parameters: (T : Monad C)
  (no additional axioms)

中文:
结构 Kleisli
  参数: (T : Monad C)
  (无附加公理)
-/
structure Kleisli (T : Monad C) where mk (T) ::
  /-- The underlying object of the base category. -/
  of : C

namespace Kleisli

variable {T : Monad C}

/--
lemma `mk_of` / 引理 `mk_of`

English:
lemma mk_of
  given: (c : Kleisli T)
  statement: Kleisli.mk T c.of = c
  proof: rfl

中文:
引理 mk_of
  条件: (c : Kleisli T)
  结论: Kleisli.mk T c.of = c
  证明: rfl
-/
@[simp] lemma mk_of (c : Kleisli T) : Kleisli.mk T c.of = c := rfl
/--
lemma `of_mk` / 引理 `of_mk`

English:
lemma of_mk
  given: (c : C)
  statement: (Kleisli.mk T c).of = c
  proof: rfl

中文:
引理 of_mk
  条件: (c : C)
  结论: (Kleisli.mk T c).of = c
  证明: rfl
-/
lemma of_mk (c : C) : (Kleisli.mk T c).of = c := rfl

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (c c' : Kleisli T)
  axioms and operations (1):
    - of : c.of ⟶ T.obj c'.of

中文:
结构 Hom
  参数: (c c' : Kleisli T)
  公理与运算 (1 个):
    - of : c.of ⟶ T.obj c'.of
-/
structure Hom (c c' : Kleisli T) where
  /-- The morphism in C underlying the morphism in the Kleisli category. -/
  of : c.of ⟶ T.obj c'.of

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: C] (T
  body: ⟨.mk T default⟩

中文:
实例 [Inhabited
  签名: C] (T
  定义体: ⟨.mk T default⟩
-/
instance [Inhabited C] (T : Monad C) : Inhabited (Kleisli T) := ⟨.mk T default⟩

variable (T)

attribute [local ext] Hom in
/-- The Kleisli category on a monad `T`.
cf Definition 5.2.9 in [Riehl][riehl2017]. -/
@[simps!]
/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category (Kleisli T) where
  body: Hom X Y
id X := .mk T.η.app X.of
comp {_} {_} {Z} f g := .mk f.of ≫ T.map g.of ≫ T.μ.app Z.of
  id_comp {X} {Y} f := by
    ext
    dsimp
    rw [← T.η.naturality_assoc f.of]; rw [T.left_unit]
    apply Category.comp_id
  assoc f g h := by
    simp [Monad.assoc, T.mu_naturality_assoc]

中文:
实例 category
  签名: : Category (Kleisli T) where
  定义体: Hom X Y
id X := .mk T.η.app X.of
comp {_} {_} {Z} f g := .mk f.of ≫ T.map g.of ≫ T.μ.app Z.of
  id_comp {X} {Y} f := by
    ext
    dsimp
    rw [← T.η.naturality_assoc f.of]; rw [T.left_unit]
    apply Category.comp_id
  assoc f g h := by
    simp [Monad.assoc, T.mu_naturality_assoc]
-/
instance category : Category (Kleisli T) where
  Hom X Y := Hom X Y
id X := .mk T.η.app X.of
comp {_} {_} {Z} f g := .mk f.of ≫ T.map g.of ≫ T.μ.app Z.of
  id_comp {X} {Y} f := by
    ext
    dsimp
    rw [← T.η.naturality_assoc f.of]; rw [T.left_unit]
    apply Category.comp_id
  assoc f g h := by
    simp [Monad.assoc, T.mu_naturality_assoc]

variable {T} in
attribute [local ext] Hom in
@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {x y : Kleisli T} {f g : x ⟶ y} (h : f.of = g.of)
  statement: f = g
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: {x y : Kleisli T} {f g : x ⟶ y} (h : f.of = g.of)
  结论: f = g
  证明: Hom.ext h

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {x y : Kleisli T} {f g : x ⟶ y} (h : f.of = g.of) : f = g :=
  Hom.ext h

namespace Adjunction

/-- The left adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps]
/--
Definition of `toKleisli` / `toKleisli` 的定义

English:
definition toKleisli
  signature: : C ⥤ Kleisli T where
  body: .mk T X
map {X} {Y} f := .mk f ≫ T.η.app Y
  map_comp {X} {Y} {Z} f g := by
    unfold_projs
    simp [← T.η.naturality g]

中文:
定义 toKleisli
  签名: : C ⥤ Kleisli T where
  定义体: .mk T X
map {X} {Y} f := .mk f ≫ T.η.app Y
  map_comp {X} {Y} {Z} f g := by
    unfold_projs
    simp [← T.η.naturality g]
-/
def toKleisli : C ⥤ Kleisli T where
  obj X := .mk T X
map {X} {Y} f := .mk f ≫ T.η.app Y
  map_comp {X} {Y} {Z} f g := by
    unfold_projs
    simp [← T.η.naturality g]

/-- The right adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps]
/--
Definition of `fromKleisli` / `fromKleisli` 的定义

English:
definition fromKleisli
  signature: : Kleisli T ⥤ C where
  body: T.obj X.of
  map {_} {Y} f := T.map f.of ≫ T.μ.app Y.of
  map_id _ := T.right_unit _
  map_comp {X} {Y} {Z} f g := by
    simp [← T.μ.naturality_assoc g.of, T.assoc]

中文:
定义 fromKleisli
  签名: : Kleisli T ⥤ C where
  定义体: T.obj X.of
  map {_} {Y} f := T.map f.of ≫ T.μ.app Y.of
  map_id _ := T.right_unit _
  map_comp {X} {Y} {Z} f g := by
    simp [← T.μ.naturality_assoc g.of, T.assoc]

Depends on / 依赖: T.obj, X.of
-/
def fromKleisli : Kleisli T ⥤ C where
  obj X := T.obj X.of
  map {_} {Y} f := T.map f.of ≫ T.μ.app Y.of
  map_id _ := T.right_unit _
  map_comp {X} {Y} {Z} f g := by
    simp [← T.μ.naturality_assoc g.of, T.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : toKleisli T ⊣ fromKleisli T
  body: Adjunction.mkOfHomEquiv
    { homEquiv X Y := { toFun f := f.of, invFun f := .mk f }
      homEquiv_naturality_left_symm := fun {X} {Y} {Z} f g => by
        ext
        simp [← T.η.naturality_assoc g] }

中文:
定义 adj
  签名: : toKleisli T ⊣ fromKleisli T
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv X Y := { toFun f := f.of, invFun f := .mk f }
      homEquiv_naturality_left_symm := fun {X} {Y} {Z} f g => by
        ext
        simp [← T.η.naturality_assoc g] }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, f.of, homEquiv, homEquiv_naturality_left_symm, invFun, mkOfHomEquiv, naturality_assoc
-/
def adj : toKleisli T ⊣ fromKleisli T :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y := { toFun f := f.of, invFun f := .mk f }
      homEquiv_naturality_left_symm := fun {X} {Y} {Z} f g => by
        ext
        simp [← T.η.naturality_assoc g] }

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `toKleisliCompFromKleisliIsoSelf` / `toKleisliCompFromKleisliIsoSelf` 的定义

English:
definition toKleisliCompFromKleisliIsoSelf
  signature: : toKleisli T ⋙ fromKleisli T ≅ T
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 toKleisliCompFromKleisliIsoSelf
  签名: : toKleisli T ⋙ fromKleisli T ≅ T
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def toKleisliCompFromKleisliIsoSelf : toKleisli T ⋙ fromKleisli T ≅ T :=
  NatIso.ofComponents fun _ => Iso.refl _

end Adjunction

end Kleisli

/--
Definition of `Cokleisli` / `Cokleisli` 的定义

English:
structure Cokleisli
  parameters: (U : Comonad C)
  (no additional axioms)

中文:
结构 Cokleisli
  参数: (U : Comonad C)
  (无附加公理)
-/
structure Cokleisli (U : Comonad C) where mk (U) ::
  /-- The underlying object of the base category. -/
  of : C

namespace Cokleisli

variable (U : Comonad C)

/--
lemma `mk_of` / 引理 `mk_of`

English:
lemma mk_of
  given: (c : Cokleisli U)
  statement: Cokleisli.mk U c.of = c
  proof: rfl

中文:
引理 mk_of
  条件: (c : Cokleisli U)
  结论: Cokleisli.mk U c.of = c
  证明: rfl
-/
@[simp] lemma mk_of (c : Cokleisli U) : Cokleisli.mk U c.of = c := rfl
/--
lemma `of_mk` / 引理 `of_mk`

English:
lemma of_mk
  given: (c : C)
  statement: (Cokleisli.mk U c).of = c
  proof: rfl

中文:
引理 of_mk
  条件: (c : C)
  结论: (Cokleisli.mk U c).of = c
  证明: rfl
-/
lemma of_mk (c : C) : (Cokleisli.mk U c).of = c := rfl

variable {U} in
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (c c' : Cokleisli U)
  axioms and operations (1):
    - of : U.obj c.of ⟶ c'.of

中文:
结构 Hom
  参数: (c c' : Cokleisli U)
  公理与运算 (1 个):
    - of : U.obj c.of ⟶ c'.of
-/
structure Hom (c c' : Cokleisli U) where
  /-- The morphism in C underlying the morphism in the Kleisli category. -/
  of : U.obj c.of ⟶ c'.of

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: C] (U
  body: ⟨.mk U default⟩

中文:
实例 [Inhabited
  签名: C] (U
  定义体: ⟨.mk U default⟩
-/
instance [Inhabited C] (U : Comonad C) : Inhabited (Cokleisli U) := ⟨.mk U default⟩

/-- The co-Kleisli category on a comonad `U`. -/
@[simps!]
/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category (Cokleisli U) where
  body: Hom X Y
id X := .mk U.ε.app X.of
comp f g := .mk U.δ.app _ ≫ (U : C ⥤ C).map f.of ≫ g.of

中文:
实例 category
  签名: : Category (Cokleisli U) where
  定义体: Hom X Y
id X := .mk U.ε.app X.of
comp f g := .mk U.δ.app _ ≫ (U : C ⥤ C).map f.of ≫ g.of
-/
instance category : Category (Cokleisli U) where
  Hom X Y := Hom X Y
id X := .mk U.ε.app X.of
comp f g := .mk U.δ.app _ ≫ (U : C ⥤ C).map f.of ≫ g.of

variable {T} in
attribute [local ext] Hom in
@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {x y : Cokleisli U} {f g : x ⟶ y} (h : f.of = g.of)
  statement: f = g
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: {x y : Cokleisli U} {f g : x ⟶ y} (h : f.of = g.of)
  结论: f = g
  证明: Hom.ext h

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {x y : Cokleisli U} {f g : x ⟶ y} (h : f.of = g.of) : f = g :=
  Hom.ext h

namespace Adjunction

/-- The right adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps]
/--
Definition of `toCokleisli` / `toCokleisli` 的定义

English:
definition toCokleisli
  signature: : C ⥤ Cokleisli U where
  body: .mk U X
  map {X} {_} f := .mk (U.ε.app X ≫ f)

中文:
定义 toCokleisli
  签名: : C ⥤ Cokleisli U where
  定义体: .mk U X
  map {X} {_} f := .mk (U.ε.app X ≫ f)
-/
def toCokleisli : C ⥤ Cokleisli U where
  obj X := .mk U X
  map {X} {_} f := .mk (U.ε.app X ≫ f)

/-- The left adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps]
/--
Definition of `fromCokleisli` / `fromCokleisli` 的定义

English:
definition fromCokleisli
  signature: : Cokleisli U ⥤ C where
  body: U.obj X.of
  map {X} {_} f := U.δ.app X.of ≫ U.map f.of
  map_id _ := U.right_counit _

中文:
定义 fromCokleisli
  签名: : Cokleisli U ⥤ C where
  定义体: U.obj X.of
  map {X} {_} f := U.δ.app X.of ≫ U.map f.of
  map_id _ := U.right_counit _

Depends on / 依赖: U.obj, X.of
-/
def fromCokleisli : Cokleisli U ⥤ C where
  obj X := U.obj X.of
  map {X} {_} f := U.δ.app X.of ≫ U.map f.of
  map_id _ := U.right_counit _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : fromCokleisli U ⊣ toCokleisli U
  body: Adjunction.mkOfHomEquiv
    { homEquiv X Y := { toFun f := .mk f, invFun f := f.of }
      homEquiv_naturality_right := fun {X} {Y} {_} f g => by cat_disch }

中文:
定义 adj
  签名: : fromCokleisli U ⊣ toCokleisli U
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv X Y := { toFun f := .mk f, invFun f := f.of }
      homEquiv_naturality_right := fun {X} {Y} {_} f g => by cat_disch }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, cat_disch, f.of, homEquiv, homEquiv_naturality_right, invFun, mkOfHomEquiv
-/
def adj : fromCokleisli U ⊣ toCokleisli U :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y := { toFun f := .mk f, invFun f := f.of }
      homEquiv_naturality_right := fun {X} {Y} {_} f g => by cat_disch }

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `toCokleisliCompFromCokleisliIsoSelf` / `toCokleisliCompFromCokleisliIsoSelf` 的定义

English:
definition toCokleisliCompFromCokleisliIsoSelf
  signature: : toCokleisli U ⋙ fromCokleisli U ≅ U
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 toCokleisliCompFromCokleisliIsoSelf
  签名: : toCokleisli U ⋙ fromCokleisli U ≅ U
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def toCokleisliCompFromCokleisliIsoSelf : toCokleisli U ⋙ fromCokleisli U ≅ U :=
  NatIso.ofComponents fun _ => Iso.refl _

end Adjunction

end Cokleisli

end CategoryTheory
