/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Biproducts and binary biproducts

We introduce the notion of (finite) biproducts.
Binary biproducts are defined in `CategoryTheory.Limits.Shapes.BinaryBiproducts`.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

For results about biproducts in preadditive categories see
`CategoryTheory.Preadditive.Biproducts`.

For biproducts indexed by a `Fintype J`, a `bicone` consists of a cone point `X`
and morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.

## Notation
As `⊕` is already taken for the sum of types, we introduce the notation `X ⊞ Y` for
a binary biproduct. We introduce `⨁ f` for the indexed biproduct.

## Implementation notes

Prior to https://github.com/leanprover-community/mathlib3/pull/14046,
`HasFiniteBiproducts` required a `DecidableEq` instance on the indexing type.
As this had no pay-off (everything about limits is non-constructive in mathlib),
and occasional cost
(constructing decidability instances appropriate for constructions involving the indexing type),
we made everything classical.
-/

@[expose] public section

noncomputable section

universe w w' v u

open CategoryTheory Functor

namespace CategoryTheory.Limits

variable {J : Type w}
universe uC' uC uD' uD
variable {C : Type uC} [Category.{uC'} C] [HasZeroMorphisms C]
variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

open scoped Classical in
/--
Definition of `Bicone` / `Bicone` 的定义

English:
structure Bicone
  parameters: (F : J -> C)
  axioms and operations (4):
    - pt : C
    - π : forall j, pt ⟶ F j
    - ι : forall j, F j ⟶ pt
    - ι_π : forall j j', ι j ≫ π j' = if h : j = j' then eqToHom (congrArg F h) else 0  [default: by aesop]

中文:
结构 Bicone
  参数: (F : J -> C)
  公理与运算 (4 个):
    - pt : C
    - π : 对任意 j, pt ⟶ F j
    - ι : 对任意 j, F j ⟶ pt
    - ι_π : 对任意 j j', ι j ≫ π j' = if h : j = j' then eqToHom (congrArg F h) else 0  [默认: by aesop]
-/
structure Bicone (F : J -> C) where
  pt : C
  π : forall j, pt ⟶ F j
  ι : forall j, F j ⟶ pt
  ι_π : forall j j', ι j ≫ π j' =
    if h : j = j' then eqToHom (congrArg F h) else 0 := by aesop

attribute [inherit_doc Bicone] Bicone.pt Bicone.π Bicone.ι Bicone.ι_π

@[reassoc (attr := simp)]
/--
theorem `bicone_ι_π_self` / 定理 `bicone_ι_π_self`

English:
theorem bicone_ι_π_self
  given: {F : J -> C} (B : Bicone F) (j : J)
  statement: B.ι j ≫ B.π j = 𝟙 (F j)
  proof: by
  simpa using B.ι_π j j

@[reassoc (attr := simp)]

中文:
定理 bicone_ι_π_self
  条件: {F : J -> C} (B : Bicone F) (j : J)
  结论: B.ι j ≫ B.π j = 𝟙 (F j)
  证明: by
  simpa using B.ι_π j j

@[reassoc (attr := simp)]
-/
theorem bicone_ι_π_self {F : J -> C} (B : Bicone F) (j : J) : B.ι j ≫ B.π j = 𝟙 (F j) := by
  simpa using B.ι_π j j

@[reassoc (attr := simp)]
/--
theorem `bicone_ι_π_ne` / 定理 `bicone_ι_π_ne`

English:
theorem bicone_ι_π_ne
  given: {F : J -> C} (B : Bicone F) {j j' : J} (h : j != j')
  statement: B.ι j ≫ B.π j' = 0
  proof: by
  simpa [h] using B.ι_π j j'

中文:
定理 bicone_ι_π_ne
  条件: {F : J -> C} (B : Bicone F) {j j' : J} (h : j != j')
  结论: B.ι j ≫ B.π j' = 0
  证明: by
  simpa [h] using B.ι_π j j'
-/
theorem bicone_ι_π_ne {F : J -> C} (B : Bicone F) {j j' : J} (h : j != j') : B.ι j ≫ B.π j' = 0 := by
  simpa [h] using B.ι_π j j'

variable {F : J -> C}

/--
Definition of `BiconeMorphism` / `BiconeMorphism` 的定义

English:
structure BiconeMorphism
  parameters: {F : J -> C} (A B : Bicone F)
  axioms and operations (3):
    - hom : A.pt ⟶ B.pt
    - wπ : forall j : J, hom ≫ B.π j = A.π j  [default: by cat_disch]
    - wι : forall j : J, A.ι j ≫ hom = B.ι j  [default: by cat_disch]

中文:
结构 BiconeMorphism
  参数: {F : J -> C} (A B : Bicone F)
  公理与运算 (3 个):
    - hom : A.pt ⟶ B.pt
    - wπ : 对任意 j : J, hom ≫ B.π j = A.π j  [默认: by cat_disch]
    - wι : 对任意 j : J, A.ι j ≫ hom = B.ι j  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure BiconeMorphism {F : J -> C} (A B : Bicone F) where
  /-- A morphism between the two vertex objects of the bicones -/
  hom : A.pt ⟶ B.pt
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wπ : forall j : J, hom ≫ B.π j = A.π j := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wι : forall j : J, A.ι j ≫ hom = B.ι j := by cat_disch

attribute [reassoc (attr := simp)] BiconeMorphism.wι BiconeMorphism.wπ

/-- The category of bicones on a given diagram. -/
@[simps]
/--
Instance `Bicone.category` / 实例 `Bicone.category`

English:
instance Bicone.category
  signature: : Category (Bicone F) where
  body: BiconeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

中文:
实例 Bicone.category
  签名: : Category (Bicone F) where
  定义体: BiconeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

Depends on / 依赖: BiconeMorphism
-/
instance Bicone.category : Category (Bicone F) where
  Hom A B := BiconeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

/-! We do not want `simps` automatically generate the lemma for simplifying the `Hom` field of
a category. So we need to write the `ext` lemma in terms of the categorical morphism, rather than
the underlying structure. -/
@[ext]
/--
theorem `BiconeMorphism.ext` / 定理 `BiconeMorphism.ext`

English:
theorem BiconeMorphism.ext
  given: {c c' : Bicone F} (f g : c ⟶ c') (w : f.hom = g.hom)
  statement: f = g
  proof: by
  cases f
  cases g
  congr

中文:
定理 BiconeMorphism.ext
  条件: {c c' : Bicone F} (f g : c ⟶ c') (w : f.hom = g.hom)
  结论: f = g
  证明: by
  cases f
  cases g
  congr
-/
theorem BiconeMorphism.ext {c c' : Bicone F} (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

namespace Bicones

/-- To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps. -/
@[aesop apply safe (rule_sets := [CategoryTheory]), simps]
/--
Definition of `ext` / `ext` 的定义

English:
definition ext
  signature: {c c' : Bicone F} (φ : c.pt ≅ c'.pt)
  body: { hom := φ.hom }
  inv :=
    { hom := φ.inv
      wι := fun j => φ.comp_inv_eq.mpr (wι j).symm
      wπ := fun j => φ.inv_comp_eq.mpr (wπ j).symm }

中文:
定义 ext
  签名: {c c' : Bicone F} (φ : c.pt ≅ c'.pt)
  定义体: { hom := φ.hom }
  inv :=
    { hom := φ.inv
      wι := fun j => φ.comp_inv_eq.mpr (wι j).symm
      wπ := fun j => φ.inv_comp_eq.mpr (wπ j).symm }

Depends on / 依赖: cat_disch, comp_inv_eq, comp_inv_eq.mpr, inv_comp_eq, inv_comp_eq.mpr
-/
def ext {c c' : Bicone F} (φ : c.pt ≅ c'.pt)
    (wι : forall j, c.ι j ≫ φ.hom = c'.ι j := by cat_disch)
    (wπ : forall j, φ.hom ≫ c'.π j = c.π j := by cat_disch) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      wι := fun j => φ.comp_inv_eq.mpr (wι j).symm
      wπ := fun j => φ.inv_comp_eq.mpr (wπ j).symm }

variable (F) in
/-- A functor `G : C ⥤ D` sends bicones over `F` to bicones over `G.obj ∘ F` functorially. -/
@[simps]
/--
Definition of `functoriality` / `functoriality` 的定义

English:
definition functoriality
  signature: (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]
  body: { pt := G.obj A.pt
      π := fun j => G.map (A.π j)
      ι := fun j => G.map (A.ι j)
ι_π := fun i j => (Functor.map_comp _ _ _).symm.trans by
        rw [A.ι_π]
        cat_disch }
  map f :=
    { hom := G.map f.hom
      wπ := fun j => by simp [-BiconeMorphism.wπ, ← f.wπ j]
      wι := fun j => 

中文:
定义 functoriality
  签名: (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]
  定义体: { pt := G.obj A.pt
      π := fun j => G.map (A.π j)
      ι := fun j => G.map (A.ι j)
ι_π := fun i j => (Functor.map_comp _ _ _).symm.trans by
        rw [A.ι_π]
        cat_disch }
  map f :=
    { hom := G.map f.hom
      wπ := fun j => by simp [-BiconeMorphism.wπ, ← f.wπ j]
      wι := fun j => 

Depends on / 依赖: A.pt, BiconeMorphism, BiconeMorphism.w, Functor, Functor.map_comp, G.map, G.obj, cat_disch, f.hom, map_comp, symm.trans
-/
def functoriality (G : C ⥤ D) [Functor.PreservesZeroMorphisms G] :
    Bicone F ⥤ Bicone (G.obj ∘ F) where
  obj A :=
    { pt := G.obj A.pt
      π := fun j => G.map (A.π j)
      ι := fun j => G.map (A.ι j)
ι_π := fun i j => (Functor.map_comp _ _ _).symm.trans by
        rw [A.ι_π]
        cat_disch }
  map f :=
    { hom := G.map f.hom
      wπ := fun j => by simp [-BiconeMorphism.wπ, ← f.wπ j]
      wι := fun j => by simp [-BiconeMorphism.wι, ← f.wι j] }

variable (G : C ⥤ D)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `functoriality_full` / 实例 `functoriality_full`

English:
instance functoriality_full
  signature: [G.PreservesZeroMorphisms] [G.Full] [G.Faithful]
  body: ⟨{ hom := G.preimage t.hom
      wι := fun j => G.map_injective (by simpa using! t.wι j)
      wπ := fun j => G.map_injective (by simpa using! t.wπ j) }, by cat_disch⟩

中文:
实例 functoriality_full
  签名: [G.PreservesZeroMorphisms] [G.Full] [G.Faithful]
  定义体: ⟨{ hom := G.preimage t.hom
      wι := fun j => G.map_injective (by simpa using! t.wι j)
      wπ := fun j => G.map_injective (by simpa using! t.wπ j) }, by cat_disch⟩

Depends on / 依赖: G.map_injective, G.preimage, cat_disch, map_injective, preimage, t.hom
-/
instance functoriality_full [G.PreservesZeroMorphisms] [G.Full] [G.Faithful] :
    (functoriality F G).Full where
  map_surjective t :=
   ⟨{ hom := G.preimage t.hom
      wι := fun j => G.map_injective (by simpa using! t.wι j)
      wπ := fun j => G.map_injective (by simpa using! t.wπ j) }, by cat_disch⟩

/--
Instance `functoriality_faithful` / 实例 `functoriality_faithful`

English:
instance functoriality_faithful
  signature: [G.PreservesZeroMorphisms] [G.Faithful]
  body: BiconeMorphism.ext f g G.map_injective congr_arg BiconeMorphism.hom h

中文:
实例 functoriality_faithful
  签名: [G.PreservesZeroMorphisms] [G.Faithful]
  定义体: BiconeMorphism.ext f g G.map_injective congr_arg BiconeMorphism.hom h

Depends on / 依赖: BiconeMorphism, BiconeMorphism.ext, BiconeMorphism.hom, G.map_injective, congr_arg, map_injective
-/
instance functoriality_faithful [G.PreservesZeroMorphisms] [G.Faithful] :
    (functoriality F G).Faithful where
  map_injective {_X} {_Y} f g h :=
BiconeMorphism.ext f g G.map_injective congr_arg BiconeMorphism.hom h

end Bicones

namespace Bicone

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases
-- Porting note: would it be okay to use this more generally?
attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Eq

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `toConeFunctor` / `toConeFunctor` 的定义

English:
definition toConeFunctor
  signature: : Bicone F ⥤ Cone (Discrete.functor F) where
  body: { pt := B.pt, π := { app := fun j => B.π j.as } }
  map {_ _} F := { hom := F.hom, w := fun _ => F.wπ _ }

中文:
定义 toConeFunctor
  签名: : Bicone F ⥤ Cone (Discrete.functor F) where
  定义体: { pt := B.pt, π := { app := fun j => B.π j.as } }
  map {_ _} F := { hom := F.hom, w := fun _ => F.wπ _ }

Depends on / 依赖: B.pt, j.as
-/
def toConeFunctor : Bicone F ⥤ Cone (Discrete.functor F) where
  obj B := { pt := B.pt, π := { app := fun j => B.π j.as } }
  map {_ _} F := { hom := F.hom, w := fun _ => F.wπ _ }

/--
Definition of `toCone` / `toCone` 的定义

English:
abbreviation toCone
  signature: (B : Bicone F)
  body: toConeFunctor.obj B

中文:
缩写 toCone
  签名: (B : Bicone F)
  定义体: toConeFunctor.obj B

Depends on / 依赖: toConeFunctor, toConeFunctor.obj
-/
abbrev toCone (B : Bicone F) : Cone (Discrete.functor F) := toConeFunctor.obj B

-- TODO Consider changing this API to `toFan (B : Bicone F) : Fan F`.

/--
theorem `toCone_pt` / 定理 `toCone_pt`

English:
theorem toCone_pt
  given: (B : Bicone F)
  statement: B.toCone.pt = B.pt
  proof: rfl

中文:
定理 toCone_pt
  条件: (B : Bicone F)
  结论: B.toCone.pt = B.pt
  证明: rfl
-/
@[simp] theorem toCone_pt (B : Bicone F) : B.toCone.pt = B.pt := rfl

/--
theorem `toCone_π_app` / 定理 `toCone_π_app`

English:
theorem toCone_π_app
  given: (B : Bicone F) (j : Discrete J)
  statement: B.toCone.π.app j = B.π j.as
  proof: rfl

中文:
定理 toCone_π_app
  条件: (B : Bicone F) (j : Discrete J)
  结论: B.toCone.π.app j = B.π j.as
  证明: rfl
-/
@[simp] theorem toCone_π_app (B : Bicone F) (j : Discrete J) : B.toCone.π.app j = B.π j.as := rfl

/--
theorem `toCone_π_app_mk` / 定理 `toCone_π_app_mk`

English:
theorem toCone_π_app_mk
  given: (B : Bicone F) (j : J)
  statement: B.toCone.π.app ⟨j⟩ = B.π j
  proof: rfl

中文:
定理 toCone_π_app_mk
  条件: (B : Bicone F) (j : J)
  结论: B.toCone.π.app ⟨j⟩ = B.π j
  证明: rfl
-/
theorem toCone_π_app_mk (B : Bicone F) (j : J) : B.toCone.π.app ⟨j⟩ = B.π j := rfl

/--
theorem `toCone_proj` / 定理 `toCone_proj`

English:
theorem toCone_proj
  given: (B : Bicone F) (j : J)
  statement: Fan.proj B.toCone j = B.π j
  proof: rfl

中文:
定理 toCone_proj
  条件: (B : Bicone F) (j : J)
  结论: Fan.proj B.toCone j = B.π j
  证明: rfl
-/
@[simp] theorem toCone_proj (B : Bicone F) (j : J) : Fan.proj B.toCone j = B.π j := rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `toCoconeFunctor` / `toCoconeFunctor` 的定义

English:
definition toCoconeFunctor
  signature: : Bicone F ⥤ Cocone (Discrete.functor F) where
  body: { pt := B.pt, ι := { app := fun j => B.ι j.as } }
  map {_ _} F := { hom := F.hom, w := fun _ => F.wι _ }

中文:
定义 toCoconeFunctor
  签名: : Bicone F ⥤ Cocone (Discrete.functor F) where
  定义体: { pt := B.pt, ι := { app := fun j => B.ι j.as } }
  map {_ _} F := { hom := F.hom, w := fun _ => F.wι _ }

Depends on / 依赖: B.pt, j.as
-/
def toCoconeFunctor : Bicone F ⥤ Cocone (Discrete.functor F) where
  obj B := { pt := B.pt, ι := { app := fun j => B.ι j.as } }
  map {_ _} F := { hom := F.hom, w := fun _ => F.wι _ }

/--
Definition of `toCocone` / `toCocone` 的定义

English:
abbreviation toCocone
  signature: (B : Bicone F)
  body: toCoconeFunctor.obj B

中文:
缩写 toCocone
  签名: (B : Bicone F)
  定义体: toCoconeFunctor.obj B

Depends on / 依赖: toCoconeFunctor, toCoconeFunctor.obj
-/
abbrev toCocone (B : Bicone F) : Cocone (Discrete.functor F) := toCoconeFunctor.obj B

/--
theorem `toCocone_pt` / 定理 `toCocone_pt`

English:
theorem toCocone_pt
  given: (B : Bicone F)
  statement: B.toCocone.pt = B.pt
  proof: rfl

@[simp]

中文:
定理 toCocone_pt
  条件: (B : Bicone F)
  结论: B.toCocone.pt = B.pt
  证明: rfl

@[simp]
-/
@[simp] theorem toCocone_pt (B : Bicone F) : B.toCocone.pt = B.pt := rfl

@[simp]
/--
theorem `toCocone_ι_app` / 定理 `toCocone_ι_app`

English:
theorem toCocone_ι_app
  given: (B : Bicone F) (j : Discrete J)
  statement: B.toCocone.ι.app j = B.ι j.as
  proof: rfl

中文:
定理 toCocone_ι_app
  条件: (B : Bicone F) (j : Discrete J)
  结论: B.toCocone.ι.app j = B.ι j.as
  证明: rfl
-/
theorem toCocone_ι_app (B : Bicone F) (j : Discrete J) : B.toCocone.ι.app j = B.ι j.as := rfl

/--
theorem `toCocone_inj` / 定理 `toCocone_inj`

English:
theorem toCocone_inj
  given: (B : Bicone F) (j : J)
  statement: Cofan.inj B.toCocone j = B.ι j
  proof: rfl

中文:
定理 toCocone_inj
  条件: (B : Bicone F) (j : J)
  结论: Cofan.inj B.toCocone j = B.ι j
  证明: rfl
-/
@[simp] theorem toCocone_inj (B : Bicone F) (j : J) : Cofan.inj B.toCocone j = B.ι j := rfl

/--
theorem `toCocone_ι_app_mk` / 定理 `toCocone_ι_app_mk`

English:
theorem toCocone_ι_app_mk
  given: (B : Bicone F) (j : J)
  statement: B.toCocone.ι.app ⟨j⟩ = B.ι j
  proof: rfl

中文:
定理 toCocone_ι_app_mk
  条件: (B : Bicone F) (j : J)
  结论: B.toCocone.ι.app ⟨j⟩ = B.ι j
  证明: rfl
-/
theorem toCocone_ι_app_mk (B : Bicone F) (j : J) : B.toCocone.ι.app ⟨j⟩ = B.ι j := rfl

/--
Definition of `retract` / `retract` 的定义

English:
definition retract
  signature: (B : Bicone F) (j : J)
  body: B.ι j
  r := B.π j

中文:
定义 retract
  签名: (B : Bicone F) (j : J)
  定义体: B.ι j
  r := B.π j
-/
def retract (B : Bicone F) (j : J) : Retract (F j) B.pt where
  i := B.ι j
  r := B.π j

instance (B : Bicone F) (j : J) : IsSplitMono (B.ι j) := (B.retract j).instIsSplitMonoI

instance (B : Bicone F) (j : J) : IsSplitEpi (B.π j) := (B.retract j).instIsSplitEpiR

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- We can turn any limit cone over a discrete collection of objects into a bicone. -/
@[simps]
/--
Definition of `ofLimitCone` / `ofLimitCone` 的定义

English:
definition ofLimitCone
  signature: {f : J -> C} {t : Cone (Discrete.functor f)} (ht : IsLimit t)
  body: t.pt
  π j := t.π.app ⟨j⟩
  ι j := ht.lift (Fan.mk _ fun j' => if h : j = j' then eqToHom (congr_arg f h) else 0)
  ι_π j j' := by simp

中文:
定义 ofLimitCone
  签名: {f : J -> C} {t : Cone (Discrete.functor f)} (ht : IsLimit t)
  定义体: t.pt
  π j := t.π.app ⟨j⟩
  ι j := ht.lift (Fan.mk _ fun j' => if h : j = j' then eqToHom (congr_arg f h) else 0)
  ι_π j j' := by simp

Depends on / 依赖: t.pt
-/
def ofLimitCone {f : J -> C} {t : Cone (Discrete.functor f)} (ht : IsLimit t) : Bicone f where
  pt := t.pt
  π j := t.π.app ⟨j⟩
  ι j := ht.lift (Fan.mk _ fun j' => if h : j = j' then eqToHom (congr_arg f h) else 0)
  ι_π j j' := by simp

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
theorem `ι_of_isLimit` / 定理 `ι_of_isLimit`

English:
theorem ι_of_isLimit
  given: {f : J -> C} {t : Bicone f} (ht : IsLimit t.toCone) (j : J)
  proof: ht.hom_ext fun j' => by
    rw [ht.fac]
    simp [t.ι_π]

中文:
定理 ι_of_isLimit
  条件: {f : J -> C} {t : Bicone f} (ht : IsLimit t.toCone) (j : J)
  证明: ht.hom_ext fun j' => by
    rw [ht.fac]
    simp [t.ι_π]

Depends on / 依赖: hom_ext, ht.fac, ht.hom_ext
-/
theorem ι_of_isLimit {f : J -> C} {t : Bicone f} (ht : IsLimit t.toCone) (j : J) :
    t.ι j = ht.lift (Fan.mk _ fun j' => if h : j = j' then eqToHom (congr_arg f h) else 0) :=
  ht.hom_ext fun j' => by
    rw [ht.fac]
    simp [t.ι_π]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- We can turn any colimit cocone over a discrete collection of objects into a bicone. -/
@[simps]
/--
Definition of `ofColimitCocone` / `ofColimitCocone` 的定义

English:
definition ofColimitCocone
  signature: {f : J -> C} {t : Cocone (Discrete.functor f)} (ht : IsColimit t)
  body: t.pt
  π j := ht.desc (Cofan.mk _ fun j' => if h : j' = j then eqToHom (congr_arg f h) else 0)
  ι j := t.ι.app ⟨j⟩
  ι_π j j' := by simp

中文:
定义 ofColimitCocone
  签名: {f : J -> C} {t : Cocone (Discrete.functor f)} (ht : IsColimit t)
  定义体: t.pt
  π j := ht.desc (Cofan.mk _ fun j' => if h : j' = j then eqToHom (congr_arg f h) else 0)
  ι j := t.ι.app ⟨j⟩
  ι_π j j' := by simp

Depends on / 依赖: t.pt
-/
def ofColimitCocone {f : J -> C} {t : Cocone (Discrete.functor f)} (ht : IsColimit t) :
    Bicone f where
  pt := t.pt
  π j := ht.desc (Cofan.mk _ fun j' => if h : j' = j then eqToHom (congr_arg f h) else 0)
  ι j := t.ι.app ⟨j⟩
  ι_π j j' := by simp

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
theorem `π_of_isColimit` / 定理 `π_of_isColimit`

English:
theorem π_of_isColimit
  given: {f : J -> C} {t : Bicone f} (ht : IsColimit t.toCocone) (j : J)
  proof: ht.hom_ext fun j' => by
    rw [ht.fac]
    simp [t.ι_π]

中文:
定理 π_of_isColimit
  条件: {f : J -> C} {t : Bicone f} (ht : IsColimit t.toCocone) (j : J)
  证明: ht.hom_ext fun j' => by
    rw [ht.fac]
    simp [t.ι_π]

Depends on / 依赖: hom_ext, ht.fac, ht.hom_ext
-/
theorem π_of_isColimit {f : J -> C} {t : Bicone f} (ht : IsColimit t.toCocone) (j : J) :
    t.π j = ht.desc (Cofan.mk _ fun j' => if h : j' = j then eqToHom (congr_arg f h) else 0) :=
  ht.hom_ext fun j' => by
    rw [ht.fac]
    simp [t.ι_π]

/--
Definition of `IsBilimit` / `IsBilimit` 的定义

English:
structure IsBilimit
  parameters: {F : J -> C} (B : Bicone F)
  axioms and operations (2):
    - isLimit : IsLimit B.toCone
    - isColimit : IsColimit B.toCocone

中文:
结构 IsBilimit
  参数: {F : J -> C} (B : Bicone F)
  公理与运算 (2 个):
    - isLimit : IsLimit B.toCone
    - isColimit : IsColimit B.toCocone
-/
structure IsBilimit {F : J -> C} (B : Bicone F) where
  isLimit : IsLimit B.toCone
  isColimit : IsColimit B.toCocone

attribute [inherit_doc IsBilimit] IsBilimit.isLimit IsBilimit.isColimit

attribute [simp] IsBilimit.mk.injEq

attribute [local ext] Bicone.IsBilimit

/--
Instance `subsingleton_isBilimit` / 实例 `subsingleton_isBilimit`

English:
instance subsingleton_isBilimit
  signature: {f : J -> C} {c : Bicone f}
  body: ⟨fun _ _ => Bicone.IsBilimit.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

中文:
实例 subsingleton_isBilimit
  签名: {f : J -> C} {c : Bicone f}
  定义体: ⟨fun _ _ => Bicone.IsBilimit.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

Depends on / 依赖: Bicone, Bicone.IsBilimit.ext, IsBilimit, Subsingleton, Subsingleton.elim
-/
instance subsingleton_isBilimit {f : J -> C} {c : Bicone f} : Subsingleton c.IsBilimit :=
  ⟨fun _ _ => Bicone.IsBilimit.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

section Whisker

variable {K : Type w'}

set_option backward.isDefEq.respectTransparency false in
/-- Whisker a bicone with an equivalence between the indexing types. -/
@[simps]
/--
Definition of `whisker` / `whisker` 的定义

English:
definition whisker
  signature: {f : J -> C} (c : Bicone f) (g : K ≃ J)
  body: c.pt
  π k := c.π (g k)
  ι k := c.ι (g k)
  ι_π k k' := by
    simp only [c.ι_π]
    split_ifs with h h' h' <;> simp [Equiv.apply_eq_iff_eq g] at h h' <;> tauto

中文:
定义 whisker
  签名: {f : J -> C} (c : Bicone f) (g : K ≃ J)
  定义体: c.pt
  π k := c.π (g k)
  ι k := c.ι (g k)
  ι_π k k' := by
    simp only [c.ι_π]
    split_ifs with h h' h' <;> simp [Equiv.apply_eq_iff_eq g] at h h' <;> tauto

Depends on / 依赖: c.pt
-/
def whisker {f : J -> C} (c : Bicone f) (g : K ≃ J) : Bicone (f ∘ g) where
  pt := c.pt
  π k := c.π (g k)
  ι k := c.ι (g k)
  ι_π k k' := by
    simp only [c.ι_π]
    split_ifs with h h' h' <;> simp [Equiv.apply_eq_iff_eq g] at h h' <;> tauto

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `whiskerToCone` / `whiskerToCone` 的定义

English:
definition whiskerToCone
  signature: {f : J -> C} (c : Bicone f) (g : K ≃ J)
  body: Cone.ext (Iso.refl _) (by simp)

中文:
定义 whiskerToCone
  签名: {f : J -> C} (c : Bicone f) (g : K ≃ J)
  定义体: Cone.ext (Iso.refl _) (by simp)

Depends on / 依赖: Cone.ext, Iso.refl
-/
def whiskerToCone {f : J -> C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).toCone ≅
      (Cone.postcompose (Discrete.functorComp f g).inv).obj
        (c.toCone.whisker (Discrete.functor (Discrete.mk ∘ g))) :=
  Cone.ext (Iso.refl _) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `whiskerToCocone` / `whiskerToCocone` 的定义

English:
definition whiskerToCocone
  signature: {f : J -> C} (c : Bicone f) (g : K ≃ J)
  body: Cocone.ext (Iso.refl _) (by simp)

中文:
定义 whiskerToCocone
  签名: {f : J -> C} (c : Bicone f) (g : K ≃ J)
  定义体: Cocone.ext (Iso.refl _) (by simp)

Depends on / 依赖: Cocone, Cocone.ext, Iso.refl
-/
def whiskerToCocone {f : J -> C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).toCocone ≅
      (Cocone.precompose (Discrete.functorComp f g).hom).obj
        (c.toCocone.whisker (Discrete.functor (Discrete.mk ∘ g))) :=
  Cocone.ext (Iso.refl _) (by simp)

/--
Definition of `whiskerIsBilimitIff` / `whiskerIsBilimitIff` 的定义

English:
definition whiskerIsBilimitIff
  signature: {f : J -> C} (c : Bicone f) (g : K ≃ J)
  body: by
  refine equivOfSubsingletonOfSubsingleton (fun hc => ⟨?_, ?_⟩) fun hc => ⟨?_, ?_⟩
  · let := IsLimit.ofIsoLimit hc.isLimit (Bicone.whiskerToCone c g)
    let := (IsLimit.postcomposeHomEquiv (Discrete.functorComp f g).symm _) this
    exact IsLimit.ofWhiskerEquivalence (Discrete.equivalence g) th

中文:
定义 whiskerIsBilimitIff
  签名: {f : J -> C} (c : Bicone f) (g : K ≃ J)
  定义体: by
  refine equivOfSubsingletonOfSubsingleton (fun hc => ⟨?_, ?_⟩) fun hc => ⟨?_, ?_⟩
  · let := IsLimit.ofIsoLimit hc.isLimit (Bicone.whiskerToCone c g)
    let := (IsLimit.postcomposeHomEquiv (Discrete.functorComp f g).symm _) this
    exact IsLimit.ofWhiskerEquivalence (Discrete.equivalence g) th

Depends on / 依赖: Bicone, Bicone.whiskerToCocone, Bicone.whiskerToCone, Discrete, Discrete.equivalence, Discrete.functorComp, IsColimit, IsColimit.ofIsoColimit, IsColimit.ofWhiskerEquivalence, IsColimit.precomposeHomEquiv, IsLimit, IsLimit.ofIsoLimit, IsLimit.ofWhiskerEquivalence, IsLimit.postcomposeHomEquiv, equivOfSubsingletonOfSubsingleton, equivalence, functorComp, hc.isColimit, hc.isLimit, isColimit
-/
noncomputable def whiskerIsBilimitIff {f : J -> C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).IsBilimit ≃ c.IsBilimit := by
  refine equivOfSubsingletonOfSubsingleton (fun hc => ⟨?_, ?_⟩) fun hc => ⟨?_, ?_⟩
  · let := IsLimit.ofIsoLimit hc.isLimit (Bicone.whiskerToCone c g)
    let := (IsLimit.postcomposeHomEquiv (Discrete.functorComp f g).symm _) this
    exact IsLimit.ofWhiskerEquivalence (Discrete.equivalence g) this
  · let := IsColimit.ofIsoColimit hc.isColimit (Bicone.whiskerToCocone c g)
    let := (IsColimit.precomposeHomEquiv (Discrete.functorComp f g) _) this
    exact IsColimit.ofWhiskerEquivalence (Discrete.equivalence g) this
  · apply IsLimit.ofIsoLimit _ (Bicone.whiskerToCone c g).symm
    apply (IsLimit.postcomposeHomEquiv (Discrete.functorComp f g).symm _).symm _
    exact IsLimit.whiskerEquivalence hc.isLimit (Discrete.equivalence g)
  · apply IsColimit.ofIsoColimit _ (Bicone.whiskerToCocone c g).symm
    apply (IsColimit.precomposeHomEquiv (Discrete.functorComp f g) _).symm _
    exact IsColimit.whiskerEquivalence hc.isColimit (Discrete.equivalence g)

end Whisker

end Bicone

/--
Definition of `LimitBicone` / `LimitBicone` 的定义

English:
structure LimitBicone
  parameters: (F : J -> C)
  axioms and operations (2):
    - bicone : Bicone F
    - isBilimit : bicone.IsBilimit

中文:
结构 LimitBicone
  参数: (F : J -> C)
  公理与运算 (2 个):
    - bicone : Bicone F
    - isBilimit : bicone.IsBilimit
-/
structure LimitBicone (F : J -> C) where
  bicone : Bicone F
  isBilimit : bicone.IsBilimit

attribute [inherit_doc LimitBicone] LimitBicone.bicone LimitBicone.isBilimit

/--
Definition of `HasBiproduct` / `HasBiproduct` 的定义

English:
class HasBiproduct
  parameters: (F : J -> C)
  (no additional axioms)

中文:
类 HasBiproduct
  参数: (F : J -> C)
  (无附加公理)
-/
class HasBiproduct (F : J -> C) : Prop where mk' ::
  exists_biproduct : Nonempty (LimitBicone F)

attribute [inherit_doc HasBiproduct] HasBiproduct.exists_biproduct

/--
theorem `HasBiproduct.mk` / 定理 `HasBiproduct.mk`

English:
theorem HasBiproduct.mk
  given: {F : J -> C} (d : LimitBicone F)
  statement: HasBiproduct F
  proof: ⟨Nonempty.intro d⟩

中文:
定理 HasBiproduct.mk
  条件: {F : J -> C} (d : LimitBicone F)
  结论: HasBiproduct F
  证明: ⟨Nonempty.intro d⟩

Depends on / 依赖: Nonempty, Nonempty.intro
-/
theorem HasBiproduct.mk {F : J -> C} (d : LimitBicone F) : HasBiproduct F :=
  ⟨Nonempty.intro d⟩

/--
Definition of `getBiproductData` / `getBiproductData` 的定义

English:
definition getBiproductData
  signature: (F : J -> C) [HasBiproduct F]
  body: Classical.choice HasBiproduct.exists_biproduct

中文:
定义 getBiproductData
  签名: (F : J -> C) [HasBiproduct F]
  定义体: Classical.choice HasBiproduct.exists_biproduct

Depends on / 依赖: Classical, Classical.choice, HasBiproduct, HasBiproduct.exists_biproduct, choice, exists_biproduct
-/
def getBiproductData (F : J -> C) [HasBiproduct F] : LimitBicone F :=
  Classical.choice HasBiproduct.exists_biproduct

/--
Definition of `biproduct.bicone` / `biproduct.bicone` 的定义

English:
definition biproduct.bicone
  signature: (F : J -> C) [HasBiproduct F]
  body: (getBiproductData F).bicone

中文:
定义 biproduct.bicone
  签名: (F : J -> C) [HasBiproduct F]
  定义体: (getBiproductData F).bicone

Depends on / 依赖: bicone, getBiproductData
-/
def biproduct.bicone (F : J -> C) [HasBiproduct F] : Bicone F :=
  (getBiproductData F).bicone

/--
Definition of `biproduct.isBilimit` / `biproduct.isBilimit` 的定义

English:
definition biproduct.isBilimit
  signature: (F : J -> C) [HasBiproduct F]
  body: (getBiproductData F).isBilimit

中文:
定义 biproduct.isBilimit
  签名: (F : J -> C) [HasBiproduct F]
  定义体: (getBiproductData F).isBilimit

Depends on / 依赖: getBiproductData, isBilimit
-/
def biproduct.isBilimit (F : J -> C) [HasBiproduct F] : (biproduct.bicone F).IsBilimit :=
  (getBiproductData F).isBilimit

/--
Definition of `biproduct.isLimit` / `biproduct.isLimit` 的定义

English:
definition biproduct.isLimit
  signature: (F : J -> C) [HasBiproduct F]
  body: (getBiproductData F).isBilimit.isLimit

中文:
定义 biproduct.isLimit
  签名: (F : J -> C) [HasBiproduct F]
  定义体: (getBiproductData F).isBilimit.isLimit

Depends on / 依赖: getBiproductData, isBilimit, isBilimit.isLimit, isLimit
-/
def biproduct.isLimit (F : J -> C) [HasBiproduct F] : IsLimit (biproduct.bicone F).toCone :=
  (getBiproductData F).isBilimit.isLimit

/--
Definition of `biproduct.isColimit` / `biproduct.isColimit` 的定义

English:
definition biproduct.isColimit
  signature: (F : J -> C) [HasBiproduct F]
  body: (getBiproductData F).isBilimit.isColimit

中文:
定义 biproduct.isColimit
  签名: (F : J -> C) [HasBiproduct F]
  定义体: (getBiproductData F).isBilimit.isColimit

Depends on / 依赖: getBiproductData, isBilimit, isBilimit.isColimit, isColimit
-/
def biproduct.isColimit (F : J -> C) [HasBiproduct F] : IsColimit (biproduct.bicone F).toCocone :=
  (getBiproductData F).isBilimit.isColimit

instance (priority := 100) hasProduct_of_hasBiproduct [HasBiproduct F] : HasProduct F :=
  HasLimit.mk
    { cone := (biproduct.bicone F).toCone
      isLimit := biproduct.isLimit F }

instance (priority := 100) hasCoproduct_of_hasBiproduct [HasBiproduct F] : HasCoproduct F :=
  HasColimit.mk
    { cocone := (biproduct.bicone F).toCocone
      isColimit := biproduct.isColimit F }

variable (J C)

/--
Definition of `HasBiproductsOfShape` / `HasBiproductsOfShape` 的定义

English:
class HasBiproductsOfShape
  parameters: : Prop where
  axioms and operations (1):
    - has_biproduct : forall F : J -> C, HasBiproduct F

中文:
类 HasBiproductsOfShape
  参数: : 命题 where
  公理与运算 (1 个):
    - has_biproduct : 对任意 F : J -> C, HasBiproduct F
-/
class HasBiproductsOfShape : Prop where
  has_biproduct : forall F : J -> C, HasBiproduct F

attribute [instance 100] HasBiproductsOfShape.has_biproduct

/--
Definition of `HasFiniteBiproducts` / `HasFiniteBiproducts` 的定义

English:
class HasFiniteBiproducts
  parameters: : Prop where
  axioms and operations (1):
    - out : forall n, HasBiproductsOfShape (Fin n) C

中文:
类 HasFiniteBiproducts
  参数: : 命题 where
  公理与运算 (1 个):
    - out : 对任意 n, HasBiproductsOfShape (Fin n) C
-/
class HasFiniteBiproducts : Prop where
  out : forall n, HasBiproductsOfShape (Fin n) C

attribute [inherit_doc HasFiniteBiproducts] HasFiniteBiproducts.out

variable {J}

/--
theorem `hasBiproductsOfShape_of_equiv` / 定理 `hasBiproductsOfShape_of_equiv`

English:
theorem hasBiproductsOfShape_of_equiv
  given: {K : Type w'} [HasBiproductsOfShape K C] (e : J ≃ K)
  proof: ⟨fun F =>
    let ⟨⟨h⟩⟩ := HasBiproductsOfShape.has_biproduct (F ∘ e.symm)
    let ⟨c, hc⟩ := h
HasBiproduct.mk by
      simpa only [Function.comp_def, e.symm_apply_apply] using
        LimitBicone.mk (c.whisker e) ((c.whiskerIsBilimitIff _).2 hc)⟩

中文:
定理 hasBiproductsOfShape_of_equiv
  条件: {K : Type w'} [HasBiproductsOfShape K C] (e : J ≃ K)
  证明: ⟨fun F =>
    let ⟨⟨h⟩⟩ := HasBiproductsOfShape.has_biproduct (F ∘ e.symm)
    let ⟨c, hc⟩ := h
HasBiproduct.mk by
      simpa only [Function.comp_def, e.symm_apply_apply] using
        LimitBicone.mk (c.whisker e) ((c.whiskerIsBilimitIff _).2 hc)⟩

Depends on / 依赖: Function, Function.comp_def, HasBiproduct, HasBiproduct.mk, HasBiproductsOfShape, HasBiproductsOfShape.has_biproduct, LimitBicone, LimitBicone.mk, c.whisker, c.whiskerIsBilimitIff, comp_def, e.symm, e.symm_apply_apply, has_biproduct, symm_apply_apply, whisker, whiskerIsBilimitIff
-/
theorem hasBiproductsOfShape_of_equiv {K : Type w'} [HasBiproductsOfShape K C] (e : J ≃ K) :
    HasBiproductsOfShape J C :=
  ⟨fun F =>
    let ⟨⟨h⟩⟩ := HasBiproductsOfShape.has_biproduct (F ∘ e.symm)
    let ⟨c, hc⟩ := h
HasBiproduct.mk by
      simpa only [Function.comp_def, e.symm_apply_apply] using
        LimitBicone.mk (c.whisker e) ((c.whiskerIsBilimitIff _).2 hc)⟩

instance (priority := 100) hasBiproductsOfShape_finite [HasFiniteBiproducts C] [Finite J] :
    HasBiproductsOfShape J C := by
  rcases Finite.exists_equiv_fin J with ⟨n, ⟨e⟩⟩
  have : HasBiproductsOfShape (Fin n) C := HasFiniteBiproducts.out n
  exact hasBiproductsOfShape_of_equiv C e

instance (priority := 100) hasFiniteProducts_of_hasFiniteBiproducts [HasFiniteBiproducts C] :
    HasFiniteProducts C where
  out _ := ⟨fun _ => hasLimit_of_iso Discrete.natIsoFunctor.symm⟩

instance (priority := 100) hasFiniteCoproducts_of_hasFiniteBiproducts [HasFiniteBiproducts C] :
    HasFiniteCoproducts C where
  out _ := ⟨fun _ => hasColimit_of_iso Discrete.natIsoFunctor⟩

instance (priority := 100) hasProductsOfShape_of_hasBiproductsOfShape [HasBiproductsOfShape J C] :
    HasProductsOfShape J C where
  has_limit _ := hasLimit_of_iso Discrete.natIsoFunctor.symm

instance (priority := 100) hasCoproductsOfShape_of_hasBiproductsOfShape [HasBiproductsOfShape J C] :
    HasCoproductsOfShape J C where
  has_colimit _ := hasColimit_of_iso Discrete.natIsoFunctor

variable {C}

/--
Definition of `biproductIso` / `biproductIso` 的定义

English:
definition biproductIso
  signature: (F : J -> C) [HasBiproduct F]
  body: (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (biproduct.isLimit F)).trans
    IsColimit.coconePointUniqueUpToIso (biproduct.isColimit F) (colimit.isColimit _)

中文:
定义 biproductIso
  签名: (F : J -> C) [HasBiproduct F]
  定义体: (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (biproduct.isLimit F)).trans
    IsColimit.coconePointUniqueUpToIso (biproduct.isColimit F) (colimit.isColimit _)

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, IsLimit, IsLimit.conePointUniqueUpToIso, biproduct, biproduct.isColimit, biproduct.isLimit, coconePointUniqueUpToIso, colimit, colimit.isColimit, conePointUniqueUpToIso, isColimit, isLimit, limit.isLimit
-/
def biproductIso (F : J -> C) [HasBiproduct F] : Limits.piObj F ≅ Limits.sigmaObj F :=
(IsLimit.conePointUniqueUpToIso (limit.isLimit _) (biproduct.isLimit F)).trans
    IsColimit.coconePointUniqueUpToIso (biproduct.isColimit F) (colimit.isColimit _)

variable {J : Type w} {K : Type*}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/--
Definition of `biproduct` / `biproduct` 的定义

English:
abbreviation biproduct
  signature: (f : J -> C) [HasBiproduct f]
  body: (biproduct.bicone f).pt

@[inherit_doc biproduct]
notation "⨁ " f:20 => biproduct f

中文:
缩写 biproduct
  签名: (f : J -> C) [HasBiproduct f]
  定义体: (biproduct.bicone f).pt

@[inherit_doc biproduct]
notation "⨁ " f:20 => biproduct f

Depends on / 依赖: bicone, biproduct, biproduct.bicone
-/
abbrev biproduct (f : J -> C) [HasBiproduct f] : C :=
  (biproduct.bicone f).pt

@[inherit_doc biproduct]
notation "⨁ " f:20 => biproduct f

/--
Definition of `biproduct.π` / `biproduct.π` 的定义

English:
abbreviation biproduct.π
  signature: (f : J -> C) [HasBiproduct f] (b : J)
  body: (biproduct.bicone f).π b

@[simp]

中文:
缩写 biproduct.π
  签名: (f : J -> C) [HasBiproduct f] (b : J)
  定义体: (biproduct.bicone f).π b

@[simp]

Depends on / 依赖: bicone, biproduct, biproduct.bicone
-/
abbrev biproduct.π (f : J -> C) [HasBiproduct f] (b : J) : ⨁ f ⟶ f b :=
  (biproduct.bicone f).π b

@[simp]
/--
theorem `biproduct.bicone_π` / 定理 `biproduct.bicone_π`

English:
theorem biproduct.bicone_π
  given: (f : J -> C) [HasBiproduct f] (b : J)
  proof: rfl

中文:
定理 biproduct.bicone_π
  条件: (f : J -> C) [HasBiproduct f] (b : J)
  证明: rfl
-/
theorem biproduct.bicone_π (f : J -> C) [HasBiproduct f] (b : J) :
    (biproduct.bicone f).π b = biproduct.π f b := rfl

/--
Definition of `biproduct.ι` / `biproduct.ι` 的定义

English:
abbreviation biproduct.ι
  signature: (f : J -> C) [HasBiproduct f] (b : J)
  body: (biproduct.bicone f).ι b

@[simp]

中文:
缩写 biproduct.ι
  签名: (f : J -> C) [HasBiproduct f] (b : J)
  定义体: (biproduct.bicone f).ι b

@[simp]

Depends on / 依赖: bicone, biproduct, biproduct.bicone
-/
abbrev biproduct.ι (f : J -> C) [HasBiproduct f] (b : J) : f b ⟶ ⨁ f :=
  (biproduct.bicone f).ι b

@[simp]
/--
theorem `biproduct.bicone_ι` / 定理 `biproduct.bicone_ι`

English:
theorem biproduct.bicone_ι
  given: (f : J -> C) [HasBiproduct f] (b : J)
  proof: rfl

中文:
定理 biproduct.bicone_ι
  条件: (f : J -> C) [HasBiproduct f] (b : J)
  证明: rfl
-/
theorem biproduct.bicone_ι (f : J -> C) [HasBiproduct f] (b : J) :
    (biproduct.bicone f).ι b = biproduct.ι f b := rfl

/-- Note that as this lemma has an `if` in the statement, we include a `DecidableEq` argument.
This means you may not be able to `simp` using this lemma unless you `open scoped Classical`. -/
@[reassoc]
/--
theorem `biproduct.ι_π` / 定理 `biproduct.ι_π`

English:
theorem biproduct.ι_π
  given: [DecidableEq J] (f : J -> C) [HasBiproduct f] (j j' : J)
  proof: by
  convert! (biproduct.bicone f).ι_π j j'

@[reassoc] -- Not `simp` because `simp` can prove this

中文:
定理 biproduct.ι_π
  条件: [DecidableEq J] (f : J -> C) [HasBiproduct f] (j j' : J)
  证明: by
  convert! (biproduct.bicone f).ι_π j j'

@[reassoc] -- Not `simp` because `simp` can prove this

Depends on / 依赖: bicone, biproduct, biproduct.bicone, convert
-/
theorem biproduct.ι_π [DecidableEq J] (f : J -> C) [HasBiproduct f] (j j' : J) :
    biproduct.ι f j ≫ biproduct.π f j' = if h : j = j' then eqToHom (congr_arg f h) else 0 := by
  convert! (biproduct.bicone f).ι_π j j'

@[reassoc] -- Not `simp` because `simp` can prove this
/--
theorem `biproduct.ι_π_self` / 定理 `biproduct.ι_π_self`

English:
theorem biproduct.ι_π_self
  given: (f : J -> C) [HasBiproduct f] (j : J)
  proof: by simp

@[reassoc]

中文:
定理 biproduct.ι_π_self
  条件: (f : J -> C) [HasBiproduct f] (j : J)
  证明: by simp

@[reassoc]
-/
theorem biproduct.ι_π_self (f : J -> C) [HasBiproduct f] (j : J) :
    biproduct.ι f j ≫ biproduct.π f j = 𝟙 _ := by simp

@[reassoc]
/--
theorem `biproduct.ι_π_ne` / 定理 `biproduct.ι_π_ne`

English:
theorem biproduct.ι_π_ne
  given: (f : J -> C) [HasBiproduct f] {j j' : J} (h : j != j')
  proof: by simp [h]

@[reassoc (attr := simp)]

中文:
定理 biproduct.ι_π_ne
  条件: (f : J -> C) [HasBiproduct f] {j j' : J} (h : j != j')
  证明: by simp [h]

@[reassoc (attr := simp)]
-/
theorem biproduct.ι_π_ne (f : J -> C) [HasBiproduct f] {j j' : J} (h : j != j') :
    biproduct.ι f j ≫ biproduct.π f j' = 0 := by simp [h]

@[reassoc (attr := simp)]
/--
theorem `biproduct.eqToHom_comp_ι` / 定理 `biproduct.eqToHom_comp_ι`

English:
theorem biproduct.eqToHom_comp_ι
  given: (f : J -> C) [HasBiproduct f] {j j' : J} (w : j = j')
  proof: by
  cases w
  simp

中文:
定理 biproduct.eqToHom_comp_ι
  条件: (f : J -> C) [HasBiproduct f] {j j' : J} (w : j = j')
  证明: by
  cases w
  simp

Depends on / 依赖: Functor, Functor.comp_map, Functor.map_comp, associator_hom_app, comp_id, comp_map, comp_obj, id_comp, id_whiskerRight, map_comp, tensor, tensorHom_id
-/
theorem biproduct.eqToHom_comp_ι (f : J -> C) [HasBiproduct f] {j j' : J} (w : j = j') :
    eqToHom (by simp [w]) ≫ biproduct.ι f j' = biproduct.ι f j := by
  cases w
  simp

-- TODO?: simp can prove this using `eqToHom_naturality`
-- but `eqToHom_naturality` applies less easily than this lemma
@[reassoc]
/--
theorem `biproduct.π_comp_eqToHom` / 定理 `biproduct.π_comp_eqToHom`

English:
theorem biproduct.π_comp_eqToHom
  given: (f : J -> C) [HasBiproduct f] {j j' : J} (w : j = j')
  proof: by
  simp [*]

中文:
定理 biproduct.π_comp_eqToHom
  条件: (f : J -> C) [HasBiproduct f] {j j' : J} (w : j = j')
  证明: by
  simp [*]

Depends on / 依赖: IsMonoidal, IsMonoidal.tensor, IsMonoidal.unit, _app_fst, _app_snd, prodMonoidal_tensorHom, prod_comp_fst, prod_comp_snd, tensor
-/
theorem biproduct.π_comp_eqToHom (f : J -> C) [HasBiproduct f] {j j' : J} (w : j = j') :
    biproduct.π f j ≫ eqToHom (by simp [w]) = biproduct.π f j' := by
  simp [*]

/--
Definition of `biproduct.lift` / `biproduct.lift` 的定义

English:
abbreviation biproduct.lift
  signature: {f : J -> C} [HasBiproduct f] {P : C} (p : forall b, P ⟶ f b)
  body: (biproduct.isLimit f).lift (Fan.mk P p)

中文:
缩写 biproduct.lift
  签名: {f : J -> C} [HasBiproduct f] {P : C} (p : 对任意 b, P ⟶ f b)
  定义体: (biproduct.isLimit f).lift (Fan.mk P p)

Depends on / 依赖: Fan.mk, biproduct, biproduct.isLimit, isLimit
-/
abbrev biproduct.lift {f : J -> C} [HasBiproduct f] {P : C} (p : forall b, P ⟶ f b) : P ⟶ ⨁ f :=
  (biproduct.isLimit f).lift (Fan.mk P p)

/--
Definition of `biproduct.desc` / `biproduct.desc` 的定义

English:
abbreviation biproduct.desc
  signature: {f : J -> C} [HasBiproduct f] {P : C} (p : forall b, f b ⟶ P)
  body: (biproduct.isColimit f).desc (Cofan.mk P p)

@[reassoc (attr := simp)]

中文:
缩写 biproduct.desc
  签名: {f : J -> C} [HasBiproduct f] {P : C} (p : 对任意 b, f b ⟶ P)
  定义体: (biproduct.isColimit f).desc (Cofan.mk P p)

@[reassoc (attr := simp)]

Depends on / 依赖: Cofan.mk, biproduct, biproduct.isColimit, isColimit
-/
abbrev biproduct.desc {f : J -> C} [HasBiproduct f] {P : C} (p : forall b, f b ⟶ P) : ⨁ f ⟶ P :=
  (biproduct.isColimit f).desc (Cofan.mk P p)

@[reassoc (attr := simp)]
/--
theorem `biproduct.lift_π` / 定理 `biproduct.lift_π`

English:
theorem biproduct.lift_π
  given: {f : J -> C} [HasBiproduct f] {P : C} (p : forall b, P ⟶ f b) (j : J)
  proof: (biproduct.isLimit f).fac _ ⟨j⟩

@[reassoc (attr := simp)]

中文:
定理 biproduct.lift_π
  条件: {f : J -> C} [HasBiproduct f] {P : C} (p : 对任意 b, P ⟶ f b) (j : J)
  证明: (biproduct.isLimit f).fac _ ⟨j⟩

@[reassoc (attr := simp)]

Depends on / 依赖: biproduct, biproduct.isLimit, isLimit
-/
theorem biproduct.lift_π {f : J -> C} [HasBiproduct f] {P : C} (p : forall b, P ⟶ f b) (j : J) :
    biproduct.lift p ≫ biproduct.π f j = p j := (biproduct.isLimit f).fac _ ⟨j⟩

@[reassoc (attr := simp)]
/--
theorem `biproduct.ι_desc` / 定理 `biproduct.ι_desc`

English:
theorem biproduct.ι_desc
  given: {f : J -> C} [HasBiproduct f] {P : C} (p : forall b, f b ⟶ P) (j : J)
  proof: (biproduct.isColimit f).fac _ ⟨j⟩

中文:
定理 biproduct.ι_desc
  条件: {f : J -> C} [HasBiproduct f] {P : C} (p : 对任意 b, f b ⟶ P) (j : J)
  证明: (biproduct.isColimit f).fac _ ⟨j⟩

Depends on / 依赖: biproduct, biproduct.isColimit, isColimit
-/
theorem biproduct.ι_desc {f : J -> C} [HasBiproduct f] {P : C} (p : forall b, f b ⟶ P) (j : J) :
    biproduct.ι f j ≫ biproduct.desc p = p j := (biproduct.isColimit f).fac _ ⟨j⟩

/--
Definition of `biproduct.map` / `biproduct.map` 的定义

English:
abbreviation biproduct.map
  signature: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall b, f b ⟶ g b)
  body: IsLimit.map (biproduct.bicone f).toCone (biproduct.isLimit g)
    (Discrete.natTrans (fun j => p j.as))

中文:
缩写 biproduct.map
  签名: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : 对任意 b, f b ⟶ g b)
  定义体: IsLimit.map (biproduct.bicone f).toCone (biproduct.isLimit g)
    (Discrete.natTrans (fun j => p j.as))

Depends on / 依赖: Discrete, Discrete.natTrans, IsLimit, IsLimit.map, bicone, biproduct, biproduct.bicone, biproduct.isLimit, isLimit, j.as, natTrans, toCone
-/
abbrev biproduct.map {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall b, f b ⟶ g b) :
    ⨁ f ⟶ ⨁ g :=
  IsLimit.map (biproduct.bicone f).toCone (biproduct.isLimit g)
    (Discrete.natTrans (fun j => p j.as))

/--
Definition of `biproduct.map'` / `biproduct.map'` 的定义

English:
abbreviation biproduct.map'
  signature: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall b, f b ⟶ g b)
  body: IsColimit.map (biproduct.isColimit f) (biproduct.bicone g).toCocone
    (Discrete.natTrans fun j => p j.as)

中文:
缩写 biproduct.map'
  签名: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : 对任意 b, f b ⟶ g b)
  定义体: IsColimit.map (biproduct.isColimit f) (biproduct.bicone g).toCocone
    (Discrete.natTrans fun j => p j.as)

Depends on / 依赖: Discrete, Discrete.natTrans, IsColimit, IsColimit.map, bicone, biproduct, biproduct.bicone, biproduct.isColimit, isColimit, j.as, natTrans, toCocone
-/
abbrev biproduct.map' {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall b, f b ⟶ g b) :
    ⨁ f ⟶ ⨁ g :=
  IsColimit.map (biproduct.isColimit f) (biproduct.bicone g).toCocone
    (Discrete.natTrans fun j => p j.as)

-- We put this at slightly higher priority than `biproduct.hom_ext'`,
-- to get the matrix indices in the "right" order.
@[ext 1001]
/--
theorem `biproduct.hom_ext` / 定理 `biproduct.hom_ext`

English:
theorem biproduct.hom_ext
  statement: {f : J -> C} [HasBiproduct f] {Z : C} (g h : Z ⟶ ⨁ f)
  proof: (biproduct.isLimit f).hom_ext fun j => w j.as

@[ext]

中文:
定理 biproduct.hom_ext
  结论: {f : J -> C} [HasBiproduct f] {Z : C} (g h : Z ⟶ ⨁ f)
  证明: (biproduct.isLimit f).hom_ext fun j => w j.as

@[ext]

Depends on / 依赖: biproduct, biproduct.isLimit, hom_ext, isLimit, j.as
-/
theorem biproduct.hom_ext {f : J -> C} [HasBiproduct f] {Z : C} (g h : Z ⟶ ⨁ f)
    (w : forall j, g ≫ biproduct.π f j = h ≫ biproduct.π f j) : g = h :=
  (biproduct.isLimit f).hom_ext fun j => w j.as

@[ext]
/--
theorem `biproduct.hom_ext'` / 定理 `biproduct.hom_ext'`

English:
theorem biproduct.hom_ext'
  statement: {f : J -> C} [HasBiproduct f] {Z : C} (g h : ⨁ f ⟶ Z)
  proof: (biproduct.isColimit f).hom_ext fun j => w j.as

中文:
定理 biproduct.hom_ext'
  结论: {f : J -> C} [HasBiproduct f] {Z : C} (g h : ⨁ f ⟶ Z)
  证明: (biproduct.isColimit f).hom_ext fun j => w j.as

Depends on / 依赖: biproduct, biproduct.isColimit, hom_ext, isColimit, j.as
-/
theorem biproduct.hom_ext' {f : J -> C} [HasBiproduct f] {Z : C} (g h : ⨁ f ⟶ Z)
    (w : forall j, biproduct.ι f j ≫ g = biproduct.ι f j ≫ h) : g = h :=
  (biproduct.isColimit f).hom_ext fun j => w j.as

/--
Definition of `biproduct.isoProduct` / `biproduct.isoProduct` 的定义

English:
definition biproduct.isoProduct
  signature: (f : J -> C) [HasBiproduct f]
  body: IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (limit.isLimit _)

中文:
定义 biproduct.isoProduct
  签名: (f : J -> C) [HasBiproduct f]
  定义体: IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (limit.isLimit _)

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, biproduct, biproduct.isLimit, conePointUniqueUpToIso, isLimit, limit.isLimit
-/
def biproduct.isoProduct (f : J -> C) [HasBiproduct f] : ⨁ f ≅ ∏ᶜ f :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `biproduct.isoProduct_hom` / 定理 `biproduct.isoProduct_hom`

English:
theorem biproduct.isoProduct_hom
  given: {f : J -> C} [HasBiproduct f]
  proof: limit.hom_ext fun j => by simp [biproduct.isoProduct]

中文:
定理 biproduct.isoProduct_hom
  条件: {f : J -> C} [HasBiproduct f]
  证明: limit.hom_ext fun j => by simp [biproduct.isoProduct]

Depends on / 依赖: biproduct, biproduct.isoProduct, hom_ext, isoProduct, limit.hom_ext
-/
theorem biproduct.isoProduct_hom {f : J -> C} [HasBiproduct f] :
    (biproduct.isoProduct f).hom = Pi.lift (biproduct.π f) :=
  limit.hom_ext fun j => by simp [biproduct.isoProduct]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `biproduct.isoProduct_inv` / 定理 `biproduct.isoProduct_inv`

English:
theorem biproduct.isoProduct_inv
  given: {f : J -> C} [HasBiproduct f]
  proof: biproduct.hom_ext _ _ fun j => by simp [Iso.inv_comp_eq]

中文:
定理 biproduct.isoProduct_inv
  条件: {f : J -> C} [HasBiproduct f]
  证明: biproduct.hom_ext _ _ fun j => by simp [Iso.inv_comp_eq]

Depends on / 依赖: Iso.inv_comp_eq, biproduct, biproduct.hom_ext, hom_ext, inv_comp_eq
-/
theorem biproduct.isoProduct_inv {f : J -> C} [HasBiproduct f] :
    (biproduct.isoProduct f).inv = biproduct.lift (Pi.π f) :=
  biproduct.hom_ext _ _ fun j => by simp [Iso.inv_comp_eq]

/--
Definition of `biproduct.isoCoproduct` / `biproduct.isoCoproduct` 的定义

English:
definition biproduct.isoCoproduct
  signature: (f : J -> C) [HasBiproduct f]
  body: IsColimit.coconePointUniqueUpToIso (biproduct.isColimit f) (colimit.isColimit _)

中文:
定义 biproduct.isoCoproduct
  签名: (f : J -> C) [HasBiproduct f]
  定义体: IsColimit.coconePointUniqueUpToIso (biproduct.isColimit f) (colimit.isColimit _)

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, biproduct, biproduct.isColimit, coconePointUniqueUpToIso, colimit, colimit.isColimit, isColimit
-/
def biproduct.isoCoproduct (f : J -> C) [HasBiproduct f] : ⨁ f ≅ ∐ f :=
  IsColimit.coconePointUniqueUpToIso (biproduct.isColimit f) (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `biproduct.isoCoproduct_inv` / 定理 `biproduct.isoCoproduct_inv`

English:
theorem biproduct.isoCoproduct_inv
  given: {f : J -> C} [HasBiproduct f]
  proof: colimit.hom_ext fun j => by simp [biproduct.isoCoproduct]

中文:
定理 biproduct.isoCoproduct_inv
  条件: {f : J -> C} [HasBiproduct f]
  证明: colimit.hom_ext fun j => by simp [biproduct.isoCoproduct]

Depends on / 依赖: biproduct, biproduct.isoCoproduct, colimit, colimit.hom_ext, hom_ext, isoCoproduct
-/
theorem biproduct.isoCoproduct_inv {f : J -> C} [HasBiproduct f] :
    (biproduct.isoCoproduct f).inv = Sigma.desc (biproduct.ι f) :=
  colimit.hom_ext fun j => by simp [biproduct.isoCoproduct]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `biproduct.isoCoproduct_hom` / 定理 `biproduct.isoCoproduct_hom`

English:
theorem biproduct.isoCoproduct_hom
  given: {f : J -> C} [HasBiproduct f]
  proof: biproduct.hom_ext' _ _ fun j => by simp [← Iso.eq_comp_inv]

中文:
定理 biproduct.isoCoproduct_hom
  条件: {f : J -> C} [HasBiproduct f]
  证明: biproduct.hom_ext' _ _ fun j => by simp [← Iso.eq_comp_inv]

Depends on / 依赖: Iso.eq_comp_inv, biproduct, biproduct.hom_ext, eq_comp_inv, hom_ext
-/
theorem biproduct.isoCoproduct_hom {f : J -> C} [HasBiproduct f] :
    (biproduct.isoCoproduct f).hom = biproduct.desc (Sigma.ι f) :=
  biproduct.hom_ext' _ _ fun j => by simp [← Iso.eq_comp_inv]

set_option backward.isDefEq.respectTransparency false in
/-- If a category has biproducts of a shape `J`, its `colim` and `lim` functor on diagrams over `J`
are isomorphic. -/
@[simps!]
/--
Definition of `HasBiproductsOfShape.colimIsoLim` / `HasBiproductsOfShape.colimIsoLim` 的定义

English:
definition HasBiproductsOfShape.colimIsoLim
  signature: [HasBiproductsOfShape J C]
  body: NatIso.ofComponents (fun F => (Sigma.isoColimit F).symm ≪≫
      (biproduct.isoCoproduct _).symm ≪≫ biproduct.isoProduct _ ≪≫ Pi.isoLimit F)
    fun η => colimit.hom_ext fun ⟨i⟩ => limit.hom_ext fun ⟨j⟩ => by
      classical
      by_cases h : i = j <;>
       simp_all [Sigma.isoColimit, Pi.isoLimit

中文:
定义 HasBiproductsOfShape.colimIsoLim
  签名: [HasBiproductsOfShape J C]
  定义体: NatIso.ofComponents (fun F => (Sigma.isoColimit F).symm ≪≫
      (biproduct.isoCoproduct _).symm ≪≫ biproduct.isoProduct _ ≪≫ Pi.isoLimit F)
    fun η => colimit.hom_ext fun ⟨i⟩ => limit.hom_ext fun ⟨j⟩ => by
      classical
      by_cases h : i = j <;>
       simp_all [Sigma.isoColimit, Pi.isoLimit

Depends on / 依赖: Discrete
-/
def HasBiproductsOfShape.colimIsoLim [HasBiproductsOfShape J C] :
    colim (J := Discrete J) (C := C) ≅ lim :=
  NatIso.ofComponents (fun F => (Sigma.isoColimit F).symm ≪≫
      (biproduct.isoCoproduct _).symm ≪≫ biproduct.isoProduct _ ≪≫ Pi.isoLimit F)
    fun η => colimit.hom_ext fun ⟨i⟩ => limit.hom_ext fun ⟨j⟩ => by
      classical
      by_cases h : i = j <;>
       simp_all [Sigma.isoColimit, Pi.isoLimit, biproduct.ι_π, biproduct.ι_π_assoc]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `biproduct.map_eq_map'` / 定理 `biproduct.map_eq_map'`

English:
theorem biproduct.map_eq_map'
  given: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall b, f b ⟶ g b)
  proof: by
  classical
  ext
  simp only [Discrete.natTrans_app, Limits.IsColimit.ι_map_assoc, Limits.IsLimit.map_π,
    ← Bicone.toCone_π_app_mk, ← Bicone.toCocone_ι_app_mk]
  dsimp
  rw [biproduct.ι_π_assoc]; rw [biproduct.ι_π]
  split_ifs with h
  · subst h; simp
  · simp

@[reassoc (attr := simp)]

中文:
定理 biproduct.map_eq_map'
  条件: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : 对任意 b, f b ⟶ g b)
  证明: by
  classical
  ext
  simp only [Discrete.natTrans_app, Limits.IsColimit.ι_map_assoc, Limits.IsLimit.map_π,
    ← Bicone.toCone_π_app_mk, ← Bicone.toCocone_ι_app_mk]
  dsimp
  rw [biproduct.ι_π_assoc]; rw [biproduct.ι_π]
  split_ifs with h
  · subst h; simp
  · simp

@[reassoc (attr := simp)]

Depends on / 依赖: Bicone, Bicone.toCocone_, Bicone.toCone_, Discrete, Discrete.natTrans_app, IsColimit, IsLimit, Limits, Limits.IsColimit, Limits.IsLimit.map_, biproduct, classical, natTrans_app, split_ifs
-/
theorem biproduct.map_eq_map' {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall b, f b ⟶ g b) :
    biproduct.map p = biproduct.map' p := by
  classical
  ext
  simp only [Discrete.natTrans_app, Limits.IsColimit.ι_map_assoc, Limits.IsLimit.map_π,
    ← Bicone.toCone_π_app_mk, ← Bicone.toCocone_ι_app_mk]
  dsimp
  rw [biproduct.ι_π_assoc]; rw [biproduct.ι_π]
  split_ifs with h
  · subst h; simp
  · simp

@[reassoc (attr := simp)]
/--
theorem `biproduct.map_π` / 定理 `biproduct.map_π`

English:
theorem biproduct.map_π
  statement: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall j, f j ⟶ g j)
  proof: Limits.IsLimit.map_π _ _ _ (Discrete.mk j)

@[reassoc (attr := simp)]

中文:
定理 biproduct.map_π
  结论: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : 对任意 j, f j ⟶ g j)
  证明: Limits.IsLimit.map_π _ _ _ (Discrete.mk j)

@[reassoc (attr := simp)]

Depends on / 依赖: Discrete, Discrete.mk, IsLimit, Limits, Limits.IsLimit.map_
-/
theorem biproduct.map_π {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall j, f j ⟶ g j)
    (j : J) : biproduct.map p ≫ biproduct.π g j = biproduct.π f j ≫ p j :=
  Limits.IsLimit.map_π _ _ _ (Discrete.mk j)

@[reassoc (attr := simp)]
/--
theorem `biproduct.ι_map` / 定理 `biproduct.ι_map`

English:
theorem biproduct.ι_map
  statement: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall j, f j ⟶ g j)
  proof: by
  rw [biproduct.map_eq_map']
  apply
    Limits.IsColimit.ι_map (biproduct.isColimit f) (biproduct.bicone g).toCocone
    (Discrete.natTrans fun j => p j.as) (Discrete.mk j)

@[reassoc (attr := simp)]

中文:
定理 biproduct.ι_map
  结论: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : 对任意 j, f j ⟶ g j)
  证明: by
  rw [biproduct.map_eq_map']
  apply
    Limits.IsColimit.ι_map (biproduct.isColimit f) (biproduct.bicone g).toCocone
    (Discrete.natTrans fun j => p j.as) (Discrete.mk j)

@[reassoc (attr := simp)]

Depends on / 依赖: Discrete, Discrete.mk, Discrete.natTrans, IsColimit, Limits, Limits.IsColimit, bicone, biproduct, biproduct.bicone, biproduct.isColimit, biproduct.map_eq_map, isColimit, j.as, map_eq_map, natTrans, toCocone
-/
theorem biproduct.ι_map {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall j, f j ⟶ g j)
    (j : J) : biproduct.ι f j ≫ biproduct.map p = p j ≫ biproduct.ι g j := by
  rw [biproduct.map_eq_map']
  apply
    Limits.IsColimit.ι_map (biproduct.isColimit f) (biproduct.bicone g).toCocone
    (Discrete.natTrans fun j => p j.as) (Discrete.mk j)

@[reassoc (attr := simp)]
/--
theorem `biproduct.map_desc` / 定理 `biproduct.map_desc`

English:
theorem biproduct.map_desc
  statement: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall j, f j ⟶ g j)
  proof: by
  ext; simp

@[reassoc (attr := simp)]

中文:
定理 biproduct.map_desc
  结论: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : 对任意 j, f j ⟶ g j)
  证明: by
  ext; simp

@[reassoc (attr := simp)]
-/
theorem biproduct.map_desc {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall j, f j ⟶ g j)
    {P : C} (k : forall j, g j ⟶ P) :
    biproduct.map p ≫ biproduct.desc k = biproduct.desc fun j => p j ≫ k j := by
  ext; simp

@[reassoc (attr := simp)]
/--
theorem `biproduct.lift_map` / 定理 `biproduct.lift_map`

English:
theorem biproduct.lift_map
  statement: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] {P : C}
  proof: by
  ext; simp

中文:
定理 biproduct.lift_map
  结论: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] {P : C}
  证明: by
  ext; simp
-/
theorem biproduct.lift_map {f g : J -> C} [HasBiproduct f] [HasBiproduct g] {P : C}
    (k : forall j, P ⟶ f j) (p : forall j, f j ⟶ g j) :
    biproduct.lift k ≫ biproduct.map p = biproduct.lift fun j => k j ≫ p j := by
  ext; simp

/-- Given a collection of isomorphisms between corresponding summands of a pair of biproducts
indexed by the same type, we obtain an isomorphism between the biproducts. -/
@[simps]
/--
Definition of `biproduct.mapIso` / `biproduct.mapIso` 的定义

English:
definition biproduct.mapIso
  signature: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall b, f b ≅ g b)
  body: biproduct.map fun b => (p b).hom
  inv := biproduct.map fun b => (p b).inv

中文:
定义 biproduct.mapIso
  签名: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : 对任意 b, f b ≅ g b)
  定义体: biproduct.map fun b => (p b).hom
  inv := biproduct.map fun b => (p b).inv

Depends on / 依赖: biproduct, biproduct.map
-/
def biproduct.mapIso {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall b, f b ≅ g b) :
    ⨁ f ≅ ⨁ g where
  hom := biproduct.map fun b => (p b).hom
  inv := biproduct.map fun b => (p b).inv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `biproduct.map_epi` / 实例 `biproduct.map_epi`

English:
instance biproduct.map_epi
  signature: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall j, f j ⟶ g j)
  body: by
  classical
  have : biproduct.map p =
      (biproduct.isoCoproduct _).hom ≫ Sigma.map p ≫ (biproduct.isoCoproduct _).inv := by
    ext
    simp only [map_π, isoCoproduct_hom, isoCoproduct_inv, Category.assoc, ι_desc_assoc, ι_π_assoc]
    split
    · subst_vars
      simp
    · simp_all
  rw [th

中文:
实例 biproduct.map_epi
  签名: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : 对任意 j, f j ⟶ g j)
  定义体: by
  classical
  have : biproduct.map p =
      (biproduct.isoCoproduct _).hom ≫ Sigma.map p ≫ (biproduct.isoCoproduct _).inv := by
    ext
    simp only [map_π, isoCoproduct_hom, isoCoproduct_inv, Category.assoc, ι_desc_assoc, ι_π_assoc]
    split
    · subst_vars
      simp
    · simp_all
  rw [th

Depends on / 依赖: Category, Category.assoc, Sigma.map, biproduct, biproduct.isoCoproduct, biproduct.map, classical, infer_instance, isoCoproduct, isoCoproduct_hom, isoCoproduct_inv
-/
instance biproduct.map_epi {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall j, f j ⟶ g j)
    [forall j, Epi (p j)] : Epi (biproduct.map p) := by
  classical
  have : biproduct.map p =
      (biproduct.isoCoproduct _).hom ≫ Sigma.map p ≫ (biproduct.isoCoproduct _).inv := by
    ext
    simp only [map_π, isoCoproduct_hom, isoCoproduct_inv, Category.assoc, ι_desc_assoc, ι_π_assoc]
    split
    · subst_vars
      simp
    · simp_all
  rw [this]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Pi.map_epi` / 实例 `Pi.map_epi`

English:
instance Pi.map_epi
  signature: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall j, f j ⟶ g j)
  body: by
  rw [show Pi.map p = (biproduct.isoProduct _).inv ≫ biproduct.map p ≫
    (biproduct.isoProduct _).hom by aesop]
  infer_instance

中文:
实例 Pi.map_epi
  签名: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : 对任意 j, f j ⟶ g j)
  定义体: by
  rw [show Pi.map p = (biproduct.isoProduct _).inv ≫ biproduct.map p ≫
    (biproduct.isoProduct _).hom by aesop]
  infer_instance

Depends on / 依赖: Pi.map, biproduct, biproduct.isoProduct, biproduct.map, infer_instance, isoProduct
-/
instance Pi.map_epi {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall j, f j ⟶ g j)
    [forall j, Epi (p j)] : Epi (Pi.map p) := by
  rw [show Pi.map p = (biproduct.isoProduct _).inv ≫ biproduct.map p ≫
    (biproduct.isoProduct _).hom by aesop]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `biproduct.map_mono` / 实例 `biproduct.map_mono`

English:
instance biproduct.map_mono
  signature: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall j, f j ⟶ g j)
  body: by
  rw [show biproduct.map p = (biproduct.isoProduct _).hom ≫ Pi.map p ≫
    (biproduct.isoProduct _).inv by aesop]
  infer_instance

中文:
实例 biproduct.map_mono
  签名: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : 对任意 j, f j ⟶ g j)
  定义体: by
  rw [show biproduct.map p = (biproduct.isoProduct _).hom ≫ Pi.map p ≫
    (biproduct.isoProduct _).inv by aesop]
  infer_instance

Depends on / 依赖: Pi.map, biproduct, biproduct.isoProduct, biproduct.map, infer_instance, isoProduct
-/
instance biproduct.map_mono {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall j, f j ⟶ g j)
    [forall j, Mono (p j)] : Mono (biproduct.map p) := by
  rw [show biproduct.map p = (biproduct.isoProduct _).hom ≫ Pi.map p ≫
    (biproduct.isoProduct _).inv by aesop]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Sigma.map_mono` / 实例 `Sigma.map_mono`

English:
instance Sigma.map_mono
  signature: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall j, f j ⟶ g j)
  body: by
  rw [show Sigma.map p = (biproduct.isoCoproduct _).inv ≫ biproduct.map p ≫
    (biproduct.isoCoproduct _).hom by aesop]
  infer_instance

中文:
实例 Sigma.map_mono
  签名: {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : 对任意 j, f j ⟶ g j)
  定义体: by
  rw [show Sigma.map p = (biproduct.isoCoproduct _).inv ≫ biproduct.map p ≫
    (biproduct.isoCoproduct _).hom by aesop]
  infer_instance

Depends on / 依赖: Sigma.map, biproduct, biproduct.isoCoproduct, biproduct.map, infer_instance, isoCoproduct
-/
instance Sigma.map_mono {f g : J -> C} [HasBiproduct f] [HasBiproduct g] (p : forall j, f j ⟶ g j)
    [forall j, Mono (p j)] : Mono (Sigma.map p) := by
  rw [show Sigma.map p = (biproduct.isoCoproduct _).inv ≫ biproduct.map p ≫
    (biproduct.isoCoproduct _).hom by aesop]
  infer_instance

/-- Two biproducts which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.

Unfortunately there are two natural ways to define each direction of this isomorphism
(because it is true for both products and coproducts separately).
We give the alternative definitions as lemmas below. -/
@[simps]
/--
Definition of `biproduct.whiskerEquiv` / `biproduct.whiskerEquiv` 的定义

English:
definition biproduct.whiskerEquiv
  signature: {f : J -> C} {g : K -> C} (e : J ≃ K) (w : forall j, g (e j) ≅ f j)
  body: biproduct.desc fun j => (w j).inv ≫ biproduct.ι g (e j)
  inv := biproduct.desc fun k => eqToHom (by simp) ≫ (w (e.symm k)).hom ≫ biproduct.ι f _

中文:
定义 biproduct.whiskerEquiv
  签名: {f : J -> C} {g : K -> C} (e : J ≃ K) (w : 对任意 j, g (e j) ≅ f j)
  定义体: biproduct.desc fun j => (w j).inv ≫ biproduct.ι g (e j)
  inv := biproduct.desc fun k => eqToHom (by simp) ≫ (w (e.symm k)).hom ≫ biproduct.ι f _

Depends on / 依赖: biproduct, biproduct.desc
-/
def biproduct.whiskerEquiv {f : J -> C} {g : K -> C} (e : J ≃ K) (w : forall j, g (e j) ≅ f j)
    [HasBiproduct f] [HasBiproduct g] : ⨁ f ≅ ⨁ g where
  hom := biproduct.desc fun j => (w j).inv ≫ biproduct.ι g (e j)
  inv := biproduct.desc fun k => eqToHom (by simp) ≫ (w (e.symm k)).hom ≫ biproduct.ι f _

/--
lemma `biproduct.whiskerEquiv_hom_eq_lift` / 引理 `biproduct.whiskerEquiv_hom_eq_lift`

English:
lemma biproduct.whiskerEquiv_hom_eq_lift
  statement: {f : J -> C} {g : K -> C} (e : J ≃ K)
  proof: by
  simp only [whiskerEquiv_hom]
  ext k j
  by_cases h : k = e j
  · subst h
    simp
  · simp only [ι_desc_assoc, Category.assoc, lift_π]
    rw [biproduct.ι_π_ne]; rw [biproduct.ι_π_ne_assoc]
    · simp
    · rintro rfl
      simp at h
    · exact Ne.symm h

中文:
引理 biproduct.whiskerEquiv_hom_eq_lift
  结论: {f : J -> C} {g : K -> C} (e : J ≃ K)
  证明: by
  simp only [whiskerEquiv_hom]
  ext k j
  by_cases h : k = e j
  · subst h
    simp
  · simp only [ι_desc_assoc, Category.assoc, lift_π]
    rw [biproduct.ι_π_ne]; rw [biproduct.ι_π_ne_assoc]
    · simp
    · rintro rfl
      simp at h
    · exact Ne.symm h

Depends on / 依赖: Category, Category.assoc, Ne.symm, biproduct, whiskerEquiv_hom
-/
lemma biproduct.whiskerEquiv_hom_eq_lift {f : J -> C} {g : K -> C} (e : J ≃ K)
    (w : forall j, g (e j) ≅ f j) [HasBiproduct f] [HasBiproduct g] :
    (biproduct.whiskerEquiv e w).hom =
      biproduct.lift fun k => biproduct.π f (e.symm k) ≫ (w _).inv ≫ eqToHom (by simp) := by
  simp only [whiskerEquiv_hom]
  ext k j
  by_cases h : k = e j
  · subst h
    simp
  · simp only [ι_desc_assoc, Category.assoc, lift_π]
    rw [biproduct.ι_π_ne]; rw [biproduct.ι_π_ne_assoc]
    · simp
    · rintro rfl
      simp at h
    · exact Ne.symm h

/--
lemma `biproduct.whiskerEquiv_inv_eq_lift` / 引理 `biproduct.whiskerEquiv_inv_eq_lift`

English:
lemma biproduct.whiskerEquiv_inv_eq_lift
  statement: {f : J -> C} {g : K -> C} (e : J ≃ K)
  proof: by
  simp only [whiskerEquiv_inv]
  ext j k
  by_cases h : k = e j
  · subst h
    simp only [ι_desc_assoc, ← eqToHom_iso_hom_naturality_assoc w (e.symm_apply_apply j).symm,
      Equiv.symm_apply_apply, eqToHom_comp_ι, Category.assoc, bicone_ι_π_self, Category.comp_id,
      lift_π, bicone_ι_π_self

中文:
引理 biproduct.whiskerEquiv_inv_eq_lift
  结论: {f : J -> C} {g : K -> C} (e : J ≃ K)
  证明: by
  simp only [whiskerEquiv_inv]
  ext j k
  by_cases h : k = e j
  · subst h
    simp only [ι_desc_assoc, ← eqToHom_iso_hom_naturality_assoc w (e.symm_apply_apply j).symm,
      Equiv.symm_apply_apply, eqToHom_comp_ι, Category.assoc, bicone_ι_π_self, Category.comp_id,
      lift_π, bicone_ι_π_self

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Equiv.symm_apply_apply, biproduct, comp_id, e.symm_apply_apply, eqToHom_iso_hom_naturality_assoc, symm_apply_apply, whiskerEquiv_inv
-/
lemma biproduct.whiskerEquiv_inv_eq_lift {f : J -> C} {g : K -> C} (e : J ≃ K)
    (w : forall j, g (e j) ≅ f j) [HasBiproduct f] [HasBiproduct g] :
    (biproduct.whiskerEquiv e w).inv =
      biproduct.lift fun j => biproduct.π g (e j) ≫ (w j).hom := by
  simp only [whiskerEquiv_inv]
  ext j k
  by_cases h : k = e j
  · subst h
    simp only [ι_desc_assoc, ← eqToHom_iso_hom_naturality_assoc w (e.symm_apply_apply j).symm,
      Equiv.symm_apply_apply, eqToHom_comp_ι, Category.assoc, bicone_ι_π_self, Category.comp_id,
      lift_π, bicone_ι_π_self_assoc]
  · simp only [ι_desc_assoc, Category.assoc, lift_π]
    rw [biproduct.ι_π_ne]; rw [biproduct.ι_π_ne_assoc]
    · simp
    · exact h
    · rintro rfl
      simp at h

set_option backward.isDefEq.respectTransparency.types false in
attribute [local simp] Sigma.forall in
instance {ι} (f : ι -> Type*) (g : (i : ι) -> (f i) -> C)
    [forall i, HasBiproduct (g i)] [HasBiproduct fun i => ⨁ g i] :
    HasBiproduct fun p : Σ i, f i => g p.1 p.2 where
  exists_biproduct := Nonempty.intro
    { bicone :=
      { pt := ⨁ fun i => ⨁ g i
        ι := fun X => biproduct.ι (g X.1) X.2 ≫ biproduct.ι (fun i => ⨁ g i) X.1
        π := fun X => biproduct.π (fun i => ⨁ g i) X.1 ≫ biproduct.π (g X.1) X.2
        ι_π := fun ⟨j, x⟩ ⟨j', y⟩ => by
          split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h
            simp
          · simp only [Sigma.mk.inj_iff, not_and] at h
            by_cases w : j = j'
            · cases w
              simp only [heq_eq_eq, forall_true_left] at h
              simp [biproduct.ι_π_ne _ h]
            · simp [biproduct.ι_π_ne_assoc _ w] }
      isBilimit :=
      { isLimit := Fan.IsLimit.mk _
          (fun s => biproduct.lift fun b => biproduct.lift fun c => s.proj ⟨b, c⟩)
        isColimit := Cofan.IsColimit.mk _
          (fun s => biproduct.desc fun b => biproduct.desc fun c => s.inj ⟨b, c⟩) } }

/-- An iterated biproduct is a biproduct over a sigma type. -/
@[simps]
/--
Definition of `biproductBiproductIso` / `biproductBiproductIso` 的定义

English:
definition biproductBiproductIso
  signature: {ι} (f : ι -> Type*) (g : (i : ι) -> (f i) -> C)
  body: biproduct.lift fun ⟨i, x⟩ => biproduct.π _ i ≫ biproduct.π _ x
  inv := biproduct.lift fun i => biproduct.lift fun x => biproduct.π _ (⟨i, x⟩ : Σ i, f i)

中文:
定义 biproductBiproductIso
  签名: {ι} (f : ι -> 类型) (g : (i : ι) -> (f i) -> C)
  定义体: biproduct.lift fun ⟨i, x⟩ => biproduct.π _ i ≫ biproduct.π _ x
  inv := biproduct.lift fun i => biproduct.lift fun x => biproduct.π _ (⟨i, x⟩ : Σ i, f i)

Depends on / 依赖: biproduct, biproduct.lift
-/
def biproductBiproductIso {ι} (f : ι -> Type*) (g : (i : ι) -> (f i) -> C)
    [forall i, HasBiproduct (g i)] [HasBiproduct fun i => ⨁ g i] :
    (⨁ fun i => ⨁ g i) ≅ (⨁ fun p : Σ i, f i => g p.1 p.2) where
  hom := biproduct.lift fun ⟨i, x⟩ => biproduct.π _ i ≫ biproduct.π _ x
  inv := biproduct.lift fun i => biproduct.lift fun x => biproduct.π _ (⟨i, x⟩ : Σ i, f i)

section πKernel

section

variable (f : J -> C) [HasBiproduct f]
variable (p : J -> Prop) [HasBiproduct (Subtype.restrict p f)]

/--
Definition of `biproduct.fromSubtype` / `biproduct.fromSubtype` 的定义

English:
definition biproduct.fromSubtype
  signature: : ⨁ Subtype.restrict p f ⟶ ⨁ f
  body: biproduct.desc fun j => biproduct.ι _ j.val

中文:
定义 biproduct.fromSubtype
  签名: : ⨁ Subtype.restrict p f ⟶ ⨁ f
  定义体: biproduct.desc fun j => biproduct.ι _ j.val

Depends on / 依赖: biproduct, biproduct.desc, j.val
-/
def biproduct.fromSubtype : ⨁ Subtype.restrict p f ⟶ ⨁ f :=
  biproduct.desc fun j => biproduct.ι _ j.val

/--
Definition of `biproduct.toSubtype` / `biproduct.toSubtype` 的定义

English:
definition biproduct.toSubtype
  signature: : ⨁ f ⟶ ⨁ Subtype.restrict p f
  body: biproduct.lift fun _ => biproduct.π _ _

中文:
定义 biproduct.toSubtype
  签名: : ⨁ f ⟶ ⨁ Subtype.restrict p f
  定义体: biproduct.lift fun _ => biproduct.π _ _

Depends on / 依赖: biproduct, biproduct.lift
-/
def biproduct.toSubtype : ⨁ f ⟶ ⨁ Subtype.restrict p f :=
  biproduct.lift fun _ => biproduct.π _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `biproduct.fromSubtype_π` / 定理 `biproduct.fromSubtype_π`

English:
theorem biproduct.fromSubtype_π
  given: [DecidablePred p] (j : J)
  proof: by
  classical
  ext i
  rw [biproduct.fromSubtype]; rw [biproduct.ι_desc_assoc]; rw [biproduct.ι_π]
  by_cases h : p j
  · rw [dif_pos h, biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
  · rw [dif_neg h,

中文:
定理 biproduct.fromSubtype_π
  条件: [DecidablePred p] (j : J)
  证明: by
  classical
  ext i
  rw [biproduct.fromSubtype]; rw [biproduct.ι_desc_assoc]; rw [biproduct.ι_π]
  by_cases h : p j
  · rw [dif_pos h, biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
  · rw [dif_neg h,

Depends on / 依赖: False.elim, Subtype, Subtype.ext, Subtype.val, biproduct, biproduct.fromSubtype, classical, comp_zero, congr_arg, dif_neg, dif_pos, exacts, fromSubtype, split_ifs
-/
theorem biproduct.fromSubtype_π [DecidablePred p] (j : J) :
    biproduct.fromSubtype f p ≫ biproduct.π f j =
      if h : p j then biproduct.π (Subtype.restrict p f) ⟨j, h⟩ else 0 := by
  classical
  ext i
  rw [biproduct.fromSubtype]; rw [biproduct.ι_desc_assoc]; rw [biproduct.ι_π]
  by_cases h : p j
  · rw [dif_pos h, biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
  · rw [dif_neg h, dif_neg (show (i : J) != j from fun h₂ => h (h₂ ▸ i.2)), comp_zero]

/--
theorem `biproduct.fromSubtype_eq_lift` / 定理 `biproduct.fromSubtype_eq_lift`

English:
theorem biproduct.fromSubtype_eq_lift
  given: [DecidablePred p]
  proof: biproduct.hom_ext _ _ (by simp)

中文:
定理 biproduct.fromSubtype_eq_lift
  条件: [DecidablePred p]
  证明: biproduct.hom_ext _ _ (by simp)

Depends on / 依赖: biproduct, biproduct.hom_ext, hom_ext
-/
theorem biproduct.fromSubtype_eq_lift [DecidablePred p] :
    biproduct.fromSubtype f p =
      biproduct.lift fun j => if h : p j then biproduct.π (Subtype.restrict p f) ⟨j, h⟩ else 0 :=
  biproduct.hom_ext _ _ (by simp)

set_option backward.isDefEq.respectTransparency false in
@[reassoc] -- Not `@[simp]` because `simp` can prove this
/--
theorem `biproduct.fromSubtype_π_subtype` / 定理 `biproduct.fromSubtype_π_subtype`

English:
theorem biproduct.fromSubtype_π_subtype
  given: (j : Subtype p)
  proof: by
  classical
  ext
  rw [biproduct.fromSubtype]; rw [biproduct.ι_desc_assoc]; rw [biproduct.ι_π]; rw [biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]

@[reassoc (attr := simp)]

中文:
定理 biproduct.fromSubtype_π_subtype
  条件: (j : Subtype p)
  证明: by
  classical
  ext
  rw [biproduct.fromSubtype]; rw [biproduct.ι_desc_assoc]; rw [biproduct.ι_π]; rw [biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]

@[reassoc (attr := simp)]

Depends on / 依赖: False.elim, Subtype, Subtype.ext, Subtype.val, biproduct, biproduct.fromSubtype, classical, congr_arg, exacts, fromSubtype, split_ifs
-/
theorem biproduct.fromSubtype_π_subtype (j : Subtype p) :
    biproduct.fromSubtype f p ≫ biproduct.π f j = biproduct.π (Subtype.restrict p f) j := by
  classical
  ext
  rw [biproduct.fromSubtype]; rw [biproduct.ι_desc_assoc]; rw [biproduct.ι_π]; rw [biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]

@[reassoc (attr := simp)]
/--
theorem `biproduct.toSubtype_π` / 定理 `biproduct.toSubtype_π`

English:
theorem biproduct.toSubtype_π
  given: (j : Subtype p)
  proof: biproduct.lift_π _ _

中文:
定理 biproduct.toSubtype_π
  条件: (j : Subtype p)
  证明: biproduct.lift_π _ _

Depends on / 依赖: biproduct, biproduct.lift_
-/
theorem biproduct.toSubtype_π (j : Subtype p) :
    biproduct.toSubtype f p ≫ biproduct.π (Subtype.restrict p f) j = biproduct.π f j :=
  biproduct.lift_π _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `biproduct.ι_toSubtype` / 定理 `biproduct.ι_toSubtype`

English:
theorem biproduct.ι_toSubtype
  given: [DecidablePred p] (j : J)
  proof: by
  classical
  ext i
  rw [biproduct.toSubtype]; rw [Category.assoc]; rw [biproduct.lift_π]; rw [biproduct.ι_π]
  by_cases h : p j
  · rw [dif_pos h, biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
  · r

中文:
定理 biproduct.ι_toSubtype
  条件: [DecidablePred p] (j : J)
  证明: by
  classical
  ext i
  rw [biproduct.toSubtype]; rw [Category.assoc]; rw [biproduct.lift_π]; rw [biproduct.ι_π]
  by_cases h : p j
  · rw [dif_pos h, biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
  · r

Depends on / 依赖: Category, Category.assoc, False.elim, Subtype, Subtype.ext, Subtype.val, biproduct, biproduct.lift_, biproduct.toSubtype, classical, congr_arg, dif_neg, dif_pos, exacts, split_ifs, toSubtype, zero_comp
-/
theorem biproduct.ι_toSubtype [DecidablePred p] (j : J) :
    biproduct.ι f j ≫ biproduct.toSubtype f p =
      if h : p j then biproduct.ι (Subtype.restrict p f) ⟨j, h⟩ else 0 := by
  classical
  ext i
  rw [biproduct.toSubtype]; rw [Category.assoc]; rw [biproduct.lift_π]; rw [biproduct.ι_π]
  by_cases h : p j
  · rw [dif_pos h, biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
  · rw [dif_neg h, dif_neg (show j != i from fun h₂ => h (h₂.symm ▸ i.2)), zero_comp]

/--
theorem `biproduct.toSubtype_eq_desc` / 定理 `biproduct.toSubtype_eq_desc`

English:
theorem biproduct.toSubtype_eq_desc
  given: [DecidablePred p]
  proof: biproduct.hom_ext' _ _ (by simp)

中文:
定理 biproduct.toSubtype_eq_desc
  条件: [DecidablePred p]
  证明: biproduct.hom_ext' _ _ (by simp)

Depends on / 依赖: biproduct, biproduct.hom_ext, hom_ext
-/
theorem biproduct.toSubtype_eq_desc [DecidablePred p] :
    biproduct.toSubtype f p =
      biproduct.desc fun j => if h : p j then biproduct.ι (Subtype.restrict p f) ⟨j, h⟩ else 0 :=
  biproduct.hom_ext' _ _ (by simp)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `biproduct.ι_toSubtype_subtype` / 定理 `biproduct.ι_toSubtype_subtype`

English:
theorem biproduct.ι_toSubtype_subtype
  given: (j : Subtype p)
  proof: by
  classical
  ext
  rw [biproduct.toSubtype]; rw [Category.assoc]; rw [biproduct.lift_π]; rw [biproduct.ι_π]; rw [biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]

@[reassoc (attr := simp)]

中文:
定理 biproduct.ι_toSubtype_subtype
  条件: (j : Subtype p)
  证明: by
  classical
  ext
  rw [biproduct.toSubtype]; rw [Category.assoc]; rw [biproduct.lift_π]; rw [biproduct.ι_π]; rw [biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, False.elim, Subtype, Subtype.ext, Subtype.val, biproduct, biproduct.lift_, biproduct.toSubtype, classical, congr_arg, exacts, split_ifs, toSubtype
-/
theorem biproduct.ι_toSubtype_subtype (j : Subtype p) :
    biproduct.ι f j ≫ biproduct.toSubtype f p = biproduct.ι (Subtype.restrict p f) j := by
  classical
  ext
  rw [biproduct.toSubtype]; rw [Category.assoc]; rw [biproduct.lift_π]; rw [biproduct.ι_π]; rw [biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]

@[reassoc (attr := simp)]
/--
theorem `biproduct.ι_fromSubtype` / 定理 `biproduct.ι_fromSubtype`

English:
theorem biproduct.ι_fromSubtype
  given: (j : Subtype p)
  proof: biproduct.ι_desc _ _

中文:
定理 biproduct.ι_fromSubtype
  条件: (j : Subtype p)
  证明: biproduct.ι_desc _ _

Depends on / 依赖: biproduct
-/
theorem biproduct.ι_fromSubtype (j : Subtype p) :
    biproduct.ι (Subtype.restrict p f) j ≫ biproduct.fromSubtype f p = biproduct.ι f j :=
  biproduct.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `biproduct.fromSubtype_toSubtype` / 定理 `biproduct.fromSubtype_toSubtype`

English:
theorem biproduct.fromSubtype_toSubtype
  proof: by
  refine biproduct.hom_ext _ _ fun j => ?_
  rw [Category.assoc]; rw [biproduct.toSubtype_π]; rw [biproduct.fromSubtype_π_subtype]; rw [Category.id_comp]

中文:
定理 biproduct.fromSubtype_toSubtype
  证明: by
  refine biproduct.hom_ext _ _ fun j => ?_
  rw [Category.assoc]; rw [biproduct.toSubtype_π]; rw [biproduct.fromSubtype_π_subtype]; rw [Category.id_comp]

Depends on / 依赖: Category, Category.assoc, Category.id_comp, biproduct, biproduct.fromSubtype_, biproduct.hom_ext, biproduct.toSubtype_, hom_ext, id_comp
-/
theorem biproduct.fromSubtype_toSubtype :
    biproduct.fromSubtype f p ≫ biproduct.toSubtype f p = 𝟙 (⨁ Subtype.restrict p f) := by
  refine biproduct.hom_ext _ _ fun j => ?_
  rw [Category.assoc]; rw [biproduct.toSubtype_π]; rw [biproduct.fromSubtype_π_subtype]; rw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `biproduct.toSubtype_fromSubtype` / 定理 `biproduct.toSubtype_fromSubtype`

English:
theorem biproduct.toSubtype_fromSubtype
  given: [DecidablePred p]
  proof: by
  ext1 i
  by_cases h : p i
  · simp [h]
  · simp [h]

中文:
定理 biproduct.toSubtype_fromSubtype
  条件: [DecidablePred p]
  证明: by
  ext1 i
  by_cases h : p i
  · simp [h]
  · simp [h]
-/
theorem biproduct.toSubtype_fromSubtype [DecidablePred p] :
    biproduct.toSubtype f p ≫ biproduct.fromSubtype f p =
      biproduct.map fun j => if p j then 𝟙 (f j) else 0 := by
  ext1 i
  by_cases h : p i
  · simp [h]
  · simp [h]

end

section

variable (f : J -> C) (i : J) [HasBiproduct f] [HasBiproduct (Subtype.restrict (fun j => j != i) f)]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
Definition of `biproduct.isLimitFromSubtype` / `biproduct.isLimitFromSubtype` 的定义

English:
definition biproduct.isLimitFromSubtype
  signature: :
  body: Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ biproduct.toSubtype _ _, by
      apply biproduct.hom_ext; intro j
      rw [KernelFork.ι_ofι]; rw [Category.assoc]; rw [Category.assoc]; rw [biproduct.toSubtype_fromSubtype_assoc]; rw [biproduct.map_π]
      rcases Classical.em (i = j) with (rfl | h)
      · r

中文:
定义 biproduct.isLimitFromSubtype
  签名: :
  定义体: Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ biproduct.toSubtype _ _, by
      apply biproduct.hom_ext; intro j
      rw [KernelFork.ι_ofι]; rw [Category.assoc]; rw [Category.assoc]; rw [biproduct.toSubtype_fromSubtype_assoc]; rw [biproduct.map_π]
      rcases Classical.em (i = j) with (rfl | h)
      · r

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Classical, Classical.em, Classical.not_not, Fork.IsLimit.mk, IsLimit, KernelFork, KernelFork.condition, Ne.symm, biproduct, biproduct.fromSubtype_toSubty, biproduct.hom_ext, biproduct.map_, biproduct.toSubtype, biproduct.toSubtype_fromSubtype_assoc, comp_id, comp_zero, condition
-/
def biproduct.isLimitFromSubtype :
    IsLimit (KernelFork.ofι (biproduct.fromSubtype f fun j => j != i) (by simp) :
    KernelFork (biproduct.π f i)) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ biproduct.toSubtype _ _, by
      apply biproduct.hom_ext; intro j
      rw [KernelFork.ι_ofι]; rw [Category.assoc]; rw [Category.assoc]; rw [biproduct.toSubtype_fromSubtype_assoc]; rw [biproduct.map_π]
      rcases Classical.em (i = j) with (rfl | h)
      · rw [if_neg (Classical.not_not.2 rfl), comp_zero, comp_zero, KernelFork.condition]
      · rw [if_pos (Ne.symm h), Category.comp_id], by
      intro m hm
      rw [← hm]; rw [KernelFork.ι_ofι]; rw [Category.assoc]; rw [biproduct.fromSubtype_toSubtype]
      exact (Category.comp_id _).symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasKernel (biproduct.π f i)
  body: HasLimit.mk ⟨_, biproduct.isLimitFromSubtype f i⟩

中文:
实例 :
  签名: HasKernel (biproduct.π f i)
  定义体: HasLimit.mk ⟨_, biproduct.isLimitFromSubtype f i⟩

Depends on / 依赖: HasLimit, HasLimit.mk, biproduct, biproduct.isLimitFromSubtype, isLimitFromSubtype
-/
instance : HasKernel (biproduct.π f i) :=
  HasLimit.mk ⟨_, biproduct.isLimitFromSubtype f i⟩

/-- The kernel of `biproduct.π f i` is `⨁ Subtype.restrict {i}ᶜ f`. -/
@[simps!]
/--
Definition of `kernelBiproductπIso` / `kernelBiproductπIso` 的定义

English:
definition kernelBiproductπIso
  signature: : kernel (biproduct.π f i) ≅ ⨁ Subtype.restrict (fun j => j != i) f
  body: limit.isoLimitCone ⟨_, biproduct.isLimitFromSubtype f i⟩

中文:
定义 kernelBiproductπIso
  签名: : kernel (biproduct.π f i) ≅ ⨁ Subtype.restrict (fun j => j != i) f
  定义体: limit.isoLimitCone ⟨_, biproduct.isLimitFromSubtype f i⟩

Depends on / 依赖: biproduct, biproduct.isLimitFromSubtype, isLimitFromSubtype, isoLimitCone, limit.isoLimitCone
-/
def kernelBiproductπIso : kernel (biproduct.π f i) ≅ ⨁ Subtype.restrict (fun j => j != i) f :=
  limit.isoLimitCone ⟨_, biproduct.isLimitFromSubtype f i⟩

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
Definition of `biproduct.isColimitToSubtype` / `biproduct.isColimitToSubtype` 的定义

English:
definition biproduct.isColimitToSubtype
  signature: :
  body: Cofork.IsColimit.mk' _ fun s =>
    ⟨biproduct.fromSubtype _ _ ≫ s.π, by
      apply biproduct.hom_ext'; intro j
      rw [CokernelCofork.π_ofπ]; rw [biproduct.toSubtype_fromSubtype_assoc]; rw [biproduct.ι_map_assoc]
      rcases Classical.em (i = j) with (rfl | h)
      · rw [if_neg (Classical.not_

中文:
定义 biproduct.isColimitToSubtype
  签名: :
  定义体: Cofork.IsColimit.mk' _ fun s =>
    ⟨biproduct.fromSubtype _ _ ≫ s.π, by
      apply biproduct.hom_ext'; intro j
      rw [CokernelCofork.π_ofπ]; rw [biproduct.toSubtype_fromSubtype_assoc]; rw [biproduct.ι_map_assoc]
      rcases Classical.em (i = j) with (rfl | h)
      · rw [if_neg (Classical.not_

Depends on / 依赖: Category, Category.assoc, Category.id_com, Category.id_comp, Classical, Classical.em, Classical.not_not, Cofork, Cofork.IsColimit.mk, CokernelCofork, CokernelCofork.condition, IsColimit, Ne.symm, biproduct, biproduct.fromSubtype, biproduct.fromSubtype_toSubtype, biproduct.hom_ext, biproduct.toSubtype_fromSubtype_assoc, condition, fromSubtype
-/
def biproduct.isColimitToSubtype :
    IsColimit (CokernelCofork.ofπ (biproduct.toSubtype f fun j => j != i) (by simp) :
    CokernelCofork (biproduct.ι f i)) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨biproduct.fromSubtype _ _ ≫ s.π, by
      apply biproduct.hom_ext'; intro j
      rw [CokernelCofork.π_ofπ]; rw [biproduct.toSubtype_fromSubtype_assoc]; rw [biproduct.ι_map_assoc]
      rcases Classical.em (i = j) with (rfl | h)
      · rw [if_neg (Classical.not_not.2 rfl), zero_comp, CokernelCofork.condition]
      · rw [if_pos (Ne.symm h), Category.id_comp], by
      intro m hm
      rw [← hm]; rw [CokernelCofork.π_ofπ]; rw [← Category.assoc]; rw [biproduct.fromSubtype_toSubtype]
      exact (Category.id_comp _).symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCokernel (biproduct.ι f i)
  body: HasColimit.mk ⟨_, biproduct.isColimitToSubtype f i⟩

中文:
实例 :
  签名: HasCokernel (biproduct.ι f i)
  定义体: HasColimit.mk ⟨_, biproduct.isColimitToSubtype f i⟩

Depends on / 依赖: HasColimit, HasColimit.mk, biproduct, biproduct.isColimitToSubtype, isColimitToSubtype
-/
instance : HasCokernel (biproduct.ι f i) :=
  HasColimit.mk ⟨_, biproduct.isColimitToSubtype f i⟩

/-- The cokernel of `biproduct.ι f i` is `⨁ Subtype.restrict {i}ᶜ f`. -/
@[simps!]
/--
Definition of `cokernelBiproductιIso` / `cokernelBiproductιIso` 的定义

English:
definition cokernelBiproductιIso
  signature: : cokernel (biproduct.ι f i) ≅ ⨁ Subtype.restrict (fun j => j != i) f
  body: colimit.isoColimitCocone ⟨_, biproduct.isColimitToSubtype f i⟩

中文:
定义 cokernelBiproductιIso
  签名: : cokernel (biproduct.ι f i) ≅ ⨁ Subtype.restrict (fun j => j != i) f
  定义体: colimit.isoColimitCocone ⟨_, biproduct.isColimitToSubtype f i⟩

Depends on / 依赖: biproduct, biproduct.isColimitToSubtype, colimit, colimit.isoColimitCocone, isColimitToSubtype, isoColimitCocone
-/
def cokernelBiproductιIso : cokernel (biproduct.ι f i) ≅ ⨁ Subtype.restrict (fun j => j != i) f :=
  colimit.isoColimitCocone ⟨_, biproduct.isColimitToSubtype f i⟩

end

section

-- Per https://github.com/leanprover-community/mathlib3/pull/15067, we only allow indexing in `Type 0` here.
variable {K : Type} [Finite K] [HasFiniteBiproducts C] (f : K -> C)

set_option backward.isDefEq.respectTransparency false in
/-- The limit cone exhibiting `⨁ Subtype.restrict pᶜ f` as the kernel of
`biproduct.toSubtype f p` -/
@[simps]
/--
Definition of `kernelForkBiproductToSubtype` / `kernelForkBiproductToSubtype` 的定义

English:
definition kernelForkBiproductToSubtype
  signature: (p : K -> Prop)
  body: KernelFork.ofι (biproduct.fromSubtype f pᶜ)
      (by
        classical
        ext j k
        simp only [Category.assoc, biproduct.ι_fromSubtype_assoc, biproduct.ι_toSubtype_assoc,
          comp_zero, zero_comp]
        rw [dif_neg k.2]
        simp only [zero_comp])
  isLimit :=
    KernelFork.I

中文:
定义 kernelForkBiproductToSubtype
  签名: (p : K -> 命题)
  定义体: KernelFork.ofι (biproduct.fromSubtype f pᶜ)
      (by
        classical
        ext j k
        simp only [Category.assoc, biproduct.ι_fromSubtype_assoc, biproduct.ι_toSubtype_assoc,
          comp_zero, zero_comp]
        rw [dif_neg k.2]
        simp only [zero_comp])
  isLimit :=
    KernelFork.I

Depends on / 依赖: Category, Category.assoc, IsLimit, KernelFork, KernelFork.IsLimit.of, KernelFork.of, Pi.compl_apply, biproduct, biproduct.fromSubtype, biproduct.map_, biproduct.toSubtype, biproduct.toSubtype_fromSubtype, classical, comp_zero, compl_apply, dif_neg, fromSubtype, isLimit, not_not, not_not.mp
-/
def kernelForkBiproductToSubtype (p : K -> Prop) :
    LimitCone (parallelPair (biproduct.toSubtype f p) 0) where
  cone :=
    KernelFork.ofι (biproduct.fromSubtype f pᶜ)
      (by
        classical
        ext j k
        simp only [Category.assoc, biproduct.ι_fromSubtype_assoc, biproduct.ι_toSubtype_assoc,
          comp_zero, zero_comp]
        rw [dif_neg k.2]
        simp only [zero_comp])
  isLimit :=
    KernelFork.IsLimit.ofι _ _ (fun {_} g _ => g ≫ biproduct.toSubtype f pᶜ)
      (by
        classical
        intro W' g' w
        ext j
        simp only [Category.assoc, biproduct.toSubtype_fromSubtype, Pi.compl_apply,
          biproduct.map_π]
        split_ifs with h
        · simp
        · replace w := w =≫ biproduct.π _ ⟨j, not_not.mp h⟩
          simpa using w.symm)
      (by cat_disch)

instance (p : K -> Prop) : HasKernel (biproduct.toSubtype f p) :=
  HasLimit.mk (kernelForkBiproductToSubtype f p)

/-- The kernel of `biproduct.toSubtype f p` is `⨁ Subtype.restrict pᶜ f`. -/
@[simps!]
/--
Definition of `kernelBiproductToSubtypeIso` / `kernelBiproductToSubtypeIso` 的定义

English:
definition kernelBiproductToSubtypeIso
  signature: (p : K -> Prop)
  body: limit.isoLimitCone (kernelForkBiproductToSubtype f p)

中文:
定义 kernelBiproductToSubtypeIso
  签名: (p : K -> 命题)
  定义体: limit.isoLimitCone (kernelForkBiproductToSubtype f p)

Depends on / 依赖: isoLimitCone, kernelForkBiproductToSubtype, limit.isoLimitCone
-/
def kernelBiproductToSubtypeIso (p : K -> Prop) :
    kernel (biproduct.toSubtype f p) ≅ ⨁ Subtype.restrict pᶜ f :=
  limit.isoLimitCone (kernelForkBiproductToSubtype f p)

set_option backward.isDefEq.respectTransparency false in
/-- The colimit cocone exhibiting `⨁ Subtype.restrict pᶜ f` as the cokernel of
`biproduct.fromSubtype f p` -/
@[simps]
/--
Definition of `cokernelCoforkBiproductFromSubtype` / `cokernelCoforkBiproductFromSubtype` 的定义

English:
definition cokernelCoforkBiproductFromSubtype
  signature: (p : K -> Prop)
  body: CokernelCofork.ofπ (biproduct.toSubtype f pᶜ)
      (by
        classical
        ext j k
        simp only [Category.assoc, Pi.compl_apply, biproduct.ι_fromSubtype_assoc,
          biproduct.ι_toSubtype_assoc, comp_zero, zero_comp]
        rw [dif_neg]
        · simp only [zero_comp]
        · exac

中文:
定义 cokernelCoforkBiproductFromSubtype
  签名: (p : K -> 命题)
  定义体: CokernelCofork.ofπ (biproduct.toSubtype f pᶜ)
      (by
        classical
        ext j k
        simp only [Category.assoc, Pi.compl_apply, biproduct.ι_fromSubtype_assoc,
          biproduct.ι_toSubtype_assoc, comp_zero, zero_comp]
        rw [dif_neg]
        · simp only [zero_comp]
        · exac

Depends on / 依赖: Category, Category.assoc, CokernelCofork, CokernelCofork.IsColimit.of, CokernelCofork.of, IsColimit, Pi.compl_apply, biproduct, biproduct.fromSubtype, biproduct.toSubtype, biproduct.toSubtype_fromSubtype_assoc, classical, comp_zero, compl_apply, dif_neg, fromSubtype, isColimit, not_not, not_not.mpr, split_ifs
-/
def cokernelCoforkBiproductFromSubtype (p : K -> Prop) :
    ColimitCocone (parallelPair (biproduct.fromSubtype f p) 0) where
  cocone :=
    CokernelCofork.ofπ (biproduct.toSubtype f pᶜ)
      (by
        classical
        ext j k
        simp only [Category.assoc, Pi.compl_apply, biproduct.ι_fromSubtype_assoc,
          biproduct.ι_toSubtype_assoc, comp_zero, zero_comp]
        rw [dif_neg]
        · simp only [zero_comp]
        · exact not_not.mpr k.2)
  isColimit :=
    CokernelCofork.IsColimit.ofπ _ _ (fun {_} g _ => biproduct.fromSubtype f pᶜ ≫ g)
      (by
        classical
        intro W g' w
        ext j
        simp only [biproduct.toSubtype_fromSubtype_assoc, Pi.compl_apply, biproduct.ι_map_assoc]
        split_ifs with h
        · simp
        · replace w := biproduct.ι _ (⟨j, not_not.mp h⟩ : Subtype p) ≫= w
          simpa using w.symm)
      (by cat_disch)

instance (p : K -> Prop) : HasCokernel (biproduct.fromSubtype f p) :=
  HasColimit.mk (cokernelCoforkBiproductFromSubtype f p)

/-- The cokernel of `biproduct.fromSubtype f p` is `⨁ Subtype.restrict pᶜ f`. -/
@[simps!]
/--
Definition of `cokernelBiproductFromSubtypeIso` / `cokernelBiproductFromSubtypeIso` 的定义

English:
definition cokernelBiproductFromSubtypeIso
  signature: (p : K -> Prop)
  body: colimit.isoColimitCocone (cokernelCoforkBiproductFromSubtype f p)

中文:
定义 cokernelBiproductFromSubtypeIso
  签名: (p : K -> 命题)
  定义体: colimit.isoColimitCocone (cokernelCoforkBiproductFromSubtype f p)

Depends on / 依赖: cokernelCoforkBiproductFromSubtype, colimit, colimit.isoColimitCocone, isoColimitCocone, map_isIso, mopFunctor
-/
def cokernelBiproductFromSubtypeIso (p : K -> Prop) :
    cokernel (biproduct.fromSubtype f p) ≅ ⨁ Subtype.restrict pᶜ f :=
  colimit.isoColimitCocone (cokernelCoforkBiproductFromSubtype f p)

end

end πKernel

section FiniteBiproducts

variable {J : Type} [Finite J] {K : Type} [Finite K] {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C] [HasFiniteBiproducts C] {f : J -> C} {g : K -> C}

/--
Definition of `biproduct.matrix` / `biproduct.matrix` 的定义

English:
definition biproduct.matrix
  signature: (m : forall j k, f j ⟶ g k)
  body: biproduct.desc fun j => biproduct.lift fun k => m j k

@[reassoc (attr := simp)]

中文:
定义 biproduct.matrix
  签名: (m : 对任意 j k, f j ⟶ g k)
  定义体: biproduct.desc fun j => biproduct.lift fun k => m j k

@[reassoc (attr := simp)]

Depends on / 依赖: biproduct, biproduct.desc, biproduct.lift, map_isIso, unmopFunctor
-/
def biproduct.matrix (m : forall j k, f j ⟶ g k) : ⨁ f ⟶ ⨁ g :=
  biproduct.desc fun j => biproduct.lift fun k => m j k

@[reassoc (attr := simp)]
/--
theorem `biproduct.matrix_π` / 定理 `biproduct.matrix_π`

English:
theorem biproduct.matrix_π
  given: (m : forall j k, f j ⟶ g k) (k : K)
  proof: by
  ext
  simp [biproduct.matrix]

@[reassoc (attr := simp)]

中文:
定理 biproduct.matrix_π
  条件: (m : 对任意 j k, f j ⟶ g k) (k : K)
  证明: by
  ext
  simp [biproduct.matrix]

@[reassoc (attr := simp)]

Depends on / 依赖: biproduct, biproduct.matrix, matrix
-/
theorem biproduct.matrix_π (m : forall j k, f j ⟶ g k) (k : K) :
    biproduct.matrix m ≫ biproduct.π g k = biproduct.desc fun j => m j k := by
  ext
  simp [biproduct.matrix]

@[reassoc (attr := simp)]
/--
theorem `biproduct.ι_matrix` / 定理 `biproduct.ι_matrix`

English:
theorem biproduct.ι_matrix
  given: (m : forall j k, f j ⟶ g k) (j : J)
  proof: by
  simp [biproduct.matrix]

中文:
定理 biproduct.ι_matrix
  条件: (m : 对任意 j k, f j ⟶ g k) (j : J)
  证明: by
  simp [biproduct.matrix]

Depends on / 依赖: biproduct, biproduct.matrix, matrix
-/
theorem biproduct.ι_matrix (m : forall j k, f j ⟶ g k) (j : J) :
    biproduct.ι f j ≫ biproduct.matrix m = biproduct.lift fun k => m j k := by
  simp [biproduct.matrix]

/--
Definition of `biproduct.components` / `biproduct.components` 的定义

English:
definition biproduct.components
  signature: (m : ⨁ f ⟶ ⨁ g) (j : J) (k : K)
  body: biproduct.ι f j ≫ m ≫ biproduct.π g k

@[simp]

中文:
定义 biproduct.components
  签名: (m : ⨁ f ⟶ ⨁ g) (j : J) (k : K)
  定义体: biproduct.ι f j ≫ m ≫ biproduct.π g k

@[simp]

Depends on / 依赖: biproduct
-/
def biproduct.components (m : ⨁ f ⟶ ⨁ g) (j : J) (k : K) : f j ⟶ g k :=
  biproduct.ι f j ≫ m ≫ biproduct.π g k

@[simp]
/--
theorem `biproduct.matrix_components` / 定理 `biproduct.matrix_components`

English:
theorem biproduct.matrix_components
  given: (m : forall j k, f j ⟶ g k) (j : J) (k : K)
  proof: by simp [biproduct.components]

@[simp]

中文:
定理 biproduct.matrix_components
  条件: (m : 对任意 j k, f j ⟶ g k) (j : J) (k : K)
  证明: by simp [biproduct.components]

@[simp]

Depends on / 依赖: biproduct, biproduct.components, components
-/
theorem biproduct.matrix_components (m : forall j k, f j ⟶ g k) (j : J) (k : K) :
    biproduct.components (biproduct.matrix m) j k = m j k := by simp [biproduct.components]

@[simp]
/--
theorem `biproduct.components_matrix` / 定理 `biproduct.components_matrix`

English:
theorem biproduct.components_matrix
  given: (m : ⨁ f ⟶ ⨁ g)
  proof: by
  ext
  simp [biproduct.components]

中文:
定理 biproduct.components_matrix
  条件: (m : ⨁ f ⟶ ⨁ g)
  证明: by
  ext
  simp [biproduct.components]

Depends on / 依赖: biproduct, biproduct.components, components
-/
theorem biproduct.components_matrix (m : ⨁ f ⟶ ⨁ g) :
    (biproduct.matrix fun j k => biproduct.components m j k) = m := by
  ext
  simp [biproduct.components]

/-- Morphisms between direct sums are matrices. -/
@[simps]
/--
Definition of `biproduct.matrixEquiv` / `biproduct.matrixEquiv` 的定义

English:
definition biproduct.matrixEquiv
  signature: : (⨁ f ⟶ ⨁ g) ≃ forall j k, f j ⟶ g k where
  body: biproduct.components
  invFun := biproduct.matrix
  left_inv := biproduct.components_matrix
  right_inv m := by
    ext
    apply biproduct.matrix_components

中文:
定义 biproduct.matrixEquiv
  签名: : (⨁ f ⟶ ⨁ g) ≃ 对任意 j k, f j ⟶ g k where
  定义体: biproduct.components
  invFun := biproduct.matrix
  left_inv := biproduct.components_matrix
  right_inv m := by
    ext
    apply biproduct.matrix_components

Depends on / 依赖: biproduct, biproduct.components, components
-/
def biproduct.matrixEquiv : (⨁ f ⟶ ⨁ g) ≃ forall j k, f j ⟶ g k where
  toFun := biproduct.components
  invFun := biproduct.matrix
  left_inv := biproduct.components_matrix
  right_inv m := by
    ext
    apply biproduct.matrix_components

end FiniteBiproducts

variable {J : Type w}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

/--
Instance `biproduct.ι_mono` / 实例 `biproduct.ι_mono`

English:
instance biproduct.ι_mono
  signature: (f : J -> C) [HasBiproduct f] (b : J)
  body: (biproduct.bicone f).instIsSplitMonoι b

中文:
实例 biproduct.ι_mono
  签名: (f : J -> C) [HasBiproduct f] (b : J)
  定义体: (biproduct.bicone f).instIsSplitMonoι b

Depends on / 依赖: bicone, biproduct, biproduct.bicone
-/
instance biproduct.ι_mono (f : J -> C) [HasBiproduct f] (b : J) : IsSplitMono (biproduct.ι f b) :=
  (biproduct.bicone f).instIsSplitMonoι b

/--
Instance `biproduct.π_epi` / 实例 `biproduct.π_epi`

English:
instance biproduct.π_epi
  signature: (f : J -> C) [HasBiproduct f] (b : J)
  body: (biproduct.bicone f).instIsSplitEpiπ b

中文:
实例 biproduct.π_epi
  签名: (f : J -> C) [HasBiproduct f] (b : J)
  定义体: (biproduct.bicone f).instIsSplitEpiπ b

Depends on / 依赖: bicone, biproduct, biproduct.bicone
-/
instance biproduct.π_epi (f : J -> C) [HasBiproduct f] (b : J) : IsSplitEpi (biproduct.π f b) :=
  (biproduct.bicone f).instIsSplitEpiπ b

/--
theorem `biproduct.conePointUniqueUpToIso_hom` / 定理 `biproduct.conePointUniqueUpToIso_hom`

English:
theorem biproduct.conePointUniqueUpToIso_hom
  statement: (f : J -> C) [HasBiproduct f] {b : Bicone f}
  proof: rfl

中文:
定理 biproduct.conePointUniqueUpToIso_hom
  结论: (f : J -> C) [HasBiproduct f] {b : Bicone f}
  证明: rfl
-/
theorem biproduct.conePointUniqueUpToIso_hom (f : J -> C) [HasBiproduct f] {b : Bicone f}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (biproduct.isLimit _)).hom = biproduct.lift b.π :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `biproduct.conePointUniqueUpToIso_inv` / 定理 `biproduct.conePointUniqueUpToIso_inv`

English:
theorem biproduct.conePointUniqueUpToIso_inv
  statement: (f : J -> C) [HasBiproduct f] {b : Bicone f}
  proof: by
  classical
  refine biproduct.hom_ext' _ _ fun j => hb.isLimit.hom_ext fun j' => ?_
  rw [Category.assoc]; rw [IsLimit.conePointUniqueUpToIso_inv_comp]; rw [Bicone.toCone_π_app]; rw [biproduct.bicone_π]; rw [biproduct.ι_desc]; rw [biproduct.ι_π]; rw [b.toCone_π_app]; rw [b.ι_π]

中文:
定理 biproduct.conePointUniqueUpToIso_inv
  结论: (f : J -> C) [HasBiproduct f] {b : Bicone f}
  证明: by
  classical
  refine biproduct.hom_ext' _ _ fun j => hb.isLimit.hom_ext fun j' => ?_
  rw [Category.assoc]; rw [IsLimit.conePointUniqueUpToIso_inv_comp]; rw [Bicone.toCone_π_app]; rw [biproduct.bicone_π]; rw [biproduct.ι_desc]; rw [biproduct.ι_π]; rw [b.toCone_π_app]; rw [b.ι_π]

Depends on / 依赖: Bicone, Bicone.toCone_, Category, Category.assoc, IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, b.toCone_, biproduct, biproduct.bicone_, biproduct.hom_ext, classical, conePointUniqueUpToIso_inv_comp, hb.isLimit.hom_ext, hom_ext, isLimit
-/
theorem biproduct.conePointUniqueUpToIso_inv (f : J -> C) [HasBiproduct f] {b : Bicone f}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (biproduct.isLimit _)).inv = biproduct.desc b.ι := by
  classical
  refine biproduct.hom_ext' _ _ fun j => hb.isLimit.hom_ext fun j' => ?_
  rw [Category.assoc]; rw [IsLimit.conePointUniqueUpToIso_inv_comp]; rw [Bicone.toCone_π_app]; rw [biproduct.bicone_π]; rw [biproduct.ι_desc]; rw [biproduct.ι_π]; rw [b.toCone_π_app]; rw [b.ι_π]

set_option backward.isDefEq.respectTransparency.types false in
/-- Biproducts are unique up to isomorphism. This already follows because bilimits are limits,
but in the case of biproducts we can give an isomorphism with particularly nice definitional
properties, namely that `biproduct.lift b.π` and `biproduct.desc b.ι` are inverses of each
other. -/
@[simps]
/--
Definition of `biproduct.uniqueUpToIso` / `biproduct.uniqueUpToIso` 的定义

English:
definition biproduct.uniqueUpToIso
  signature: (f : J -> C) [HasBiproduct f] {b : Bicone f} (hb : b.IsBilimit)
  body: biproduct.lift b.π
  inv := biproduct.desc b.ι
  hom_inv_id := by
    rw [← biproduct.conePointUniqueUpToIso_hom f hb]; rw [←
      biproduct.conePointUniqueUpToIso_inv f hb]; rw [Iso.hom_inv_id]
  inv_hom_id := by
    rw [← biproduct.conePointUniqueUpToIso_hom f hb]; rw [←
      biproduct.conePoint

中文:
定义 biproduct.uniqueUpToIso
  签名: (f : J -> C) [HasBiproduct f] {b : Bicone f} (hb : b.IsBilimit)
  定义体: biproduct.lift b.π
  inv := biproduct.desc b.ι
  hom_inv_id := by
    rw [← biproduct.conePointUniqueUpToIso_hom f hb]; rw [←
      biproduct.conePointUniqueUpToIso_inv f hb]; rw [Iso.hom_inv_id]
  inv_hom_id := by
    rw [← biproduct.conePointUniqueUpToIso_hom f hb]; rw [←
      biproduct.conePoint

Depends on / 依赖: biproduct, biproduct.lift
-/
def biproduct.uniqueUpToIso (f : J -> C) [HasBiproduct f] {b : Bicone f} (hb : b.IsBilimit) :
    b.pt ≅ ⨁ f where
  hom := biproduct.lift b.π
  inv := biproduct.desc b.ι
  hom_inv_id := by
    rw [← biproduct.conePointUniqueUpToIso_hom f hb]; rw [←
      biproduct.conePointUniqueUpToIso_inv f hb]; rw [Iso.hom_inv_id]
  inv_hom_id := by
    rw [← biproduct.conePointUniqueUpToIso_hom f hb]; rw [←
      biproduct.conePointUniqueUpToIso_inv f hb]; rw [Iso.inv_hom_id]

variable (C)

-- see Note [lower instance priority]
/-- A category with finite biproducts has a zero object. -/
instance (priority := 100) hasZeroObject_of_hasFiniteBiproducts [HasFiniteBiproducts C] :
    HasZeroObject C := by
  refine ⟨⟨biproduct Empty.elim, fun X => ⟨⟨⟨0⟩, ?_⟩⟩, fun X => ⟨⟨⟨0⟩, ?_⟩⟩⟩⟩
  · intro a; apply biproduct.hom_ext'; simp
  · intro a; apply biproduct.hom_ext; simp

section

variable {C}

attribute [local simp] eq_iff_true_of_subsingleton in
/-- The limit bicone for the biproduct over an index type with exactly one term. -/
@[simps]
/--
Definition of `limitBiconeOfUnique` / `limitBiconeOfUnique` 的定义

English:
definition limitBiconeOfUnique
  signature: [Unique J] (f : J -> C)
  body: { pt := f default
      π := fun j => eqToHom (by congr; rw [← Unique.uniq])
      ι := fun j => eqToHom (by congr; rw [← Unique.uniq]) }
  isBilimit :=
    { isLimit := (limitConeOfUnique f).isLimit
      isColimit := (colimitCoconeOfUnique f).isColimit }

中文:
定义 limitBiconeOfUnique
  签名: [Unique J] (f : J -> C)
  定义体: { pt := f default
      π := fun j => eqToHom (by congr; rw [← Unique.uniq])
      ι := fun j => eqToHom (by congr; rw [← Unique.uniq]) }
  isBilimit :=
    { isLimit := (limitConeOfUnique f).isLimit
      isColimit := (colimitCoconeOfUnique f).isColimit }

Depends on / 依赖: Unique, Unique.uniq, colimitCoconeOfUnique, eqToHom, isBilimit, isColimit, isLimit, limitConeOfUnique
-/
def limitBiconeOfUnique [Unique J] (f : J -> C) : LimitBicone f where
  bicone :=
    { pt := f default
      π := fun j => eqToHom (by congr; rw [← Unique.uniq])
      ι := fun j => eqToHom (by congr; rw [← Unique.uniq]) }
  isBilimit :=
    { isLimit := (limitConeOfUnique f).isLimit
      isColimit := (colimitCoconeOfUnique f).isColimit }

instance (priority := 100) hasBiproduct_unique [Subsingleton J] [Nonempty J] (f : J -> C) :
    HasBiproduct f :=
  let ⟨_⟩ := nonempty_unique J; .mk (limitBiconeOfUnique f)

/-- A biproduct over an index type with exactly one term is just the object over that term. -/
@[simps!]
/--
Definition of `biproductUniqueIso` / `biproductUniqueIso` 的定义

English:
definition biproductUniqueIso
  signature: [Unique J] (f : J -> C)
  body: (biproduct.uniqueUpToIso _ (limitBiconeOfUnique f).isBilimit).symm

中文:
定义 biproductUniqueIso
  签名: [Unique J] (f : J -> C)
  定义体: (biproduct.uniqueUpToIso _ (limitBiconeOfUnique f).isBilimit).symm

Depends on / 依赖: biproduct, biproduct.uniqueUpToIso, isBilimit, limitBiconeOfUnique, uniqueUpToIso
-/
def biproductUniqueIso [Unique J] (f : J -> C) : ⨁ f ≅ f default :=
  (biproduct.uniqueUpToIso _ (limitBiconeOfUnique f).isBilimit).symm

end

end CategoryTheory.Limits
