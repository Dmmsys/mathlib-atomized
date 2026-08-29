/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Over and under categories

Over (and under) categories are special cases of comma categories.
* If `L` is the identity functor and `R` is a constant functor, then `Comma L R` is the "slice" or
  "over" category over the object `R` maps to.
* Conversely, if `L` is a constant functor and `R` is the identity functor, then `Comma L R` is the
  "coslice" or "under" category under the object `L` maps to.

## Tags

Comma, Slice, Coslice, Over, Under
-/

@[expose] public section


namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

-- morphism levels before object levels. See note [category theory universes].
variable {T : Type u₁} [Category.{v₁} T]
variable {D : Type u₂} [Category.{v₂} D]

/-- The over category has as objects arrows in `T` with codomain `X` and as morphisms commutative
triangles. -/
@[stacks 001G, implicit_reducible]
/--
Definition of `Over` / `Over` 的定义

English:
definition Over
  signature: (X : T)
  body: CostructuredArrow (𝟭 T) X

中文:
定义 Over
  签名: (X : T)
  定义体: CostructuredArrow (𝟭 T) X

Depends on / 依赖: CostructuredArrow
-/
def Over (X : T) :=
  CostructuredArrow (𝟭 T) X

/--
Definition of `Over.Hom` / `Over.Hom` 的定义

English:
definition Over.Hom
  signature: {X : T} (f g : Over X)
  body: CommaMorphism f g

中文:
定义 Over.态射
  签名: {X : T} (f g : Over X)
  定义体: CommaMorphism f g
-/
protected def Over.Hom {X : T} (f g : Over X) := CommaMorphism f g

instance {X : T} : Category (Over X) where
  Hom := Over.Hom
  __ := (inferInstance : Category (Comma _ _))

-- Satisfying the inhabited linter
/--
Instance `Over.inhabited` / 实例 `Over.inhabited`

English:
instance Over.inhabited
  signature: [Inhabited T]
  body: { left := default
      right := default
      hom := 𝟙 _ }

中文:
实例 Over.inhabited
  签名: [可居 T]
  定义体: { left := default
      right := default
      hom := 𝟙 _ }
-/
instance Over.inhabited [Inhabited T] : Inhabited (Over (default : T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 _ }

namespace Over

variable {X : T}

/--
Definition of `left` / `left` 的定义

English:
abbreviation left
  signature: (f : Over X)
  body: Comma.left f

中文:
缩写 left
  签名: (f : Over X)
  定义体: Comma.left f

Depends on / 依赖: Comma.left
-/
abbrev left (f : Over X) : T := Comma.left f

/--
Definition of `hom` / `hom` 的定义

English:
abbreviation hom
  signature: (f : Over X)
  body: Comma.hom f

中文:
缩写 hom
  签名: (f : Over X)
  定义体: Comma.hom f

Depends on / 依赖: Comma.hom
-/
abbrev hom (f : Over X) : f.left ⟶ X := Comma.hom f

variable {f g : Over X} (φ : f ⟶ g)

/--
Definition of `Hom.left` / `Hom.left` 的定义

English:
abbreviation Hom.left
  signature: : f.left ⟶ g.left
  body: CommaMorphism.left φ

中文:
缩写 态射.left
  签名: : f.left ⟶ g.left
  定义体: CommaMorphism.left φ
-/
abbrev Hom.left : f.left ⟶ g.left := CommaMorphism.left φ

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
theorem `w` / 定理 `w`

English:
theorem w
  statement: φ.left ≫ g.hom = f.hom
  proof: by
  simpa using (CommaMorphism.w φ)

@[reassoc]

中文:
定理 w
  结论: φ.left ≫ g.hom = f.hom
  证明: by
  simpa using (CommaMorphism.w φ)

@[reassoc]

Depends on / 依赖: CommaMorphism, CommaMorphism.w
-/
theorem w : φ.left ≫ g.hom = f.hom := by
  simpa using (CommaMorphism.w φ)

@[reassoc]
/--
lemma `Hom.w` / 引理 `Hom.w`

English:
lemma Hom.w
  statement: φ.left ≫ g.hom = f.hom
  proof: Over.w φ

@[ext]

中文:
引理 态射.w
  结论: φ.left ≫ g.hom = f.hom
  证明: Over.w φ

@[ext]

Depends on / 依赖: Over.w
-/
lemma Hom.w : φ.left ≫ g.hom = f.hom := Over.w φ

@[ext]
/--
theorem `OverMorphism.ext` / 定理 `OverMorphism.ext`

English:
theorem OverMorphism.ext
  given: {X : T} {U V : Over X} {f g : U ⟶ V} (h : f.left = g.left)
  statement: f = g
  proof: by
  let ⟨_,b,_⟩ := f
  let ⟨_,e,_⟩ := g
  congr
  simp only [eq_iff_true_of_subsingleton]

@[simp]

中文:
定理 OverMorphism.ext
  条件: {X : T} {U V : Over X} {f g : U ⟶ V} (h : f.left = g.left)
  结论: f = g
  证明: by
  let ⟨_,b,_⟩ := f
  let ⟨_,e,_⟩ := g
  congr
  simp only [eq_iff_true_of_subsingleton]

@[simp]

Depends on / 依赖: eq_iff_true_of_subsingleton
-/
theorem OverMorphism.ext {X : T} {U V : Over X} {f g : U ⟶ V} (h : f.left = g.left) : f = g := by
  let ⟨_,b,_⟩ := f
  let ⟨_,e,_⟩ := g
  congr
  simp only [eq_iff_true_of_subsingleton]

@[simp]
/--
theorem `over_right` / 定理 `over_right`

English:
theorem over_right
  given: (U : Over X)
  statement: U.right = ⟨⟨⟩⟩
  proof: by simp only

@[simp]

中文:
定理 over_right
  条件: (U : Over X)
  结论: U.right = ⟨⟨⟩⟩
  证明: by simp only

@[simp]

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, colimitCoconeIsColimit, isColimit
-/
theorem over_right (U : Over X) : U.right = ⟨⟨⟩⟩ := by simp only

@[simp]
/--
theorem `id_left` / 定理 `id_left`

English:
theorem id_left
  given: (U : Over X)
  statement: Hom.left (𝟙 U) = 𝟙 U.left
  proof: rfl

@[simp, reassoc]

中文:
定理 id_left
  条件: (U : Over X)
  结论: 态射.left (𝟙 U) = 𝟙 U.left
  证明: rfl

@[simp, reassoc]
-/
theorem id_left (U : Over X) : Hom.left (𝟙 U) = 𝟙 U.left :=
  rfl

@[simp, reassoc]
/--
theorem `comp_left` / 定理 `comp_left`

English:
theorem comp_left
  given: (a b c : Over X) (f : a ⟶ b) (g : b ⟶ c)
  statement: (f ≫ g).left = f.left ≫ g.left
  proof: rfl

中文:
定理 comp_left
  条件: (a b c : Over X) (f : a ⟶ b) (g : b ⟶ c)
  结论: (f ≫ g).left = f.left ≫ g.left
  证明: rfl
-/
theorem comp_left (a b c : Over X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).left = f.left ≫ g.left :=
  rfl

/-- To give an object in the over category, it suffices to give a morphism with codomain `X`. -/
@[simps! left hom, implicit_reducible]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {X Y : T} (f : Y ⟶ X)
  body: CostructuredArrow.mk f

中文:
定义 mk
  签名: {X Y : T} (f : Y ⟶ X)
  定义体: CostructuredArrow.mk f

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk
-/
def mk {X Y : T} (f : Y ⟶ X) : Over X :=
  CostructuredArrow.mk f

/-- We can set up a coercion from arrows with codomain `X` to `over X`. This most likely should not
be a global instance, but it is sometimes useful. -/
@[instance_reducible]
/--
Definition of `coeFromHom` / `coeFromHom` 的定义

English:
definition coeFromHom
  signature: {X Y : T}
  body: mk

中文:
定义 coeFromHom
  签名: {X Y : T}
  定义体: mk
-/
def coeFromHom {X Y : T} : CoeOut (Y ⟶ X) (Over X) where coe := mk

section

attribute [local instance] coeFromHom

@[simp]
/--
theorem `coe_hom` / 定理 `coe_hom`

English:
theorem coe_hom
  given: {X Y : T} (f : Y ⟶ X)
  statement: (f : Over X).hom = f
  proof: rfl

中文:
定理 coe_hom
  条件: {X Y : T} (f : Y ⟶ X)
  结论: (f : Over X).hom = f
  证明: rfl
-/
theorem coe_hom {X Y : T} (f : Y ⟶ X) : (f : Over X).hom = f :=
  rfl

end

/-- To give a morphism in the over category, it suffices to give an arrow fitting in a commutative
triangle. -/
@[simps! left]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {U V : Over X} (f : U.left ⟶ V.left) (w : f ≫ V.hom = U.hom := by cat_disch)
  body: CostructuredArrow.homMk f w

@[simp]

中文:
定义 homMk
  签名: {U V : Over X} (f : U.left ⟶ V.left) (w : f ≫ V.hom = U.hom := by cat_disch)
  定义体: CostructuredArrow.homMk f w

@[simp]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, cat_disch
-/
def homMk {U V : Over X} (f : U.left ⟶ V.left) (w : f ≫ V.hom = U.hom := by cat_disch) : U ⟶ V :=
  CostructuredArrow.homMk f w

@[simp]
/--
lemma `homMk_eta` / 引理 `homMk_eta`

English:
lemma homMk_eta
  given: {U V : Over X} (f : U ⟶ V) (h)
  proof: rfl

中文:
引理 homMk_eta
  条件: {U V : Over X} (f : U ⟶ V) (h)
  证明: rfl
-/
lemma homMk_eta {U V : Over X} (f : U ⟶ V) (h) :
    homMk f.left h = f :=
  rfl

/--
lemma `homMk_comp` / 引理 `homMk_comp`

English:
lemma homMk_comp
  given: {U V W : Over X} (f : U.left ⟶ V.left) (g : V.left ⟶ W.left) (w_f w_g)
  proof: by
  ext
  simp

中文:
引理 homMk_comp
  条件: {U V W : Over X} (f : U.left ⟶ V.left) (g : V.left ⟶ W.left) (w_f w_g)
  证明: by
  ext
  simp
-/
lemma homMk_comp {U V W : Over X} (f : U.left ⟶ V.left) (g : V.left ⟶ W.left) (w_f w_g) :
    homMk (f ≫ g) (by simp_all) = homMk f w_f ≫ homMk g w_g := by
  ext
  simp

/-- Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
@[simps! hom_left inv_left]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {f g : Over X} (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom := by cat_disch)
  body: CostructuredArrow.isoMk hl hw

@[simp]

中文:
定义 isoMk
  签名: {f g : Over X} (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom := by cat_disch)
  定义体: CostructuredArrow.isoMk hl hw

@[simp]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.isoMk, cat_disch
-/
def isoMk {f g : Over X} (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom := by cat_disch) :
    f ≅ g :=
  CostructuredArrow.isoMk hl hw

@[simp]
/--
lemma `eqToHom_left` / 引理 `eqToHom_left`

English:
lemma eqToHom_left
  given: {f g : Over X} (h : f = g)
  proof: by
  subst h
  rfl

@[reassoc (attr := simp)]

中文:
引理 eqToHom_left
  条件: {f g : Over X} (h : f = g)
  证明: by
  subst h
  rfl

@[reassoc (attr := simp)]
-/
lemma eqToHom_left {f g : Over X} (h : f = g) :
    (eqToHom h).left = eqToHom (by rw [h]) := by
  subst h
  rfl

@[reassoc (attr := simp)]
/--
lemma `hom_left_inv_left` / 引理 `hom_left_inv_left`

English:
lemma hom_left_inv_left
  given: {f g : Over X} (e : f ≅ g)
  proof: by
  simp [← Over.comp_left]

@[reassoc (attr := simp)]

中文:
引理 hom_left_inv_left
  条件: {f g : Over X} (e : f ≅ g)
  证明: by
  simp [← Over.comp_left]

@[reassoc (attr := simp)]

Depends on / 依赖: Over.comp_left, comp_left
-/
lemma hom_left_inv_left {f g : Over X} (e : f ≅ g) :
    e.hom.left ≫ e.inv.left = 𝟙 f.left := by
  simp [← Over.comp_left]

@[reassoc (attr := simp)]
/--
lemma `inv_left_hom_left` / 引理 `inv_left_hom_left`

English:
lemma inv_left_hom_left
  given: {f g : Over X} (e : f ≅ g)
  proof: by
  simp [← Over.comp_left]

中文:
引理 inv_left_hom_left
  条件: {f g : Over X} (e : f ≅ g)
  证明: by
  simp [← Over.comp_left]

Depends on / 依赖: Over.comp_left, comp_left
-/
lemma inv_left_hom_left {f g : Over X} (e : f ≅ g) :
    e.inv.left ≫ e.hom.left = 𝟙 g.left := by
  simp [← Over.comp_left]

/--
lemma `forall_iff` / 引理 `forall_iff`

English:
lemma forall_iff
  given: (P : Over X -> Prop)
  proof: by
  aesop

中文:
引理 对任意_iff
  条件: (P : Over X -> 命题)
  证明: by
  aesop
-/
lemma forall_iff (P : Over X -> Prop) :
    (forall Y, P Y) ↔ (forall (Y) (f : Y ⟶ X), P (.mk f)) := by
  aesop

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  given: {S : T} (X : Over S)
  proof: ⟨_, X.hom, rfl⟩

中文:
引理 mk_surjective
  条件: {S : T} (X : Over S)
  证明: ⟨_, X.hom, rfl⟩

Depends on / 依赖: X.hom
-/
lemma mk_surjective {S : T} (X : Over S) :
    exists (Y : T) (f : Y ⟶ S), Over.mk f = X :=
  ⟨_, X.hom, rfl⟩

/--
lemma `homMk_surjective` / 引理 `homMk_surjective`

English:
lemma homMk_surjective
  proof: ⟨f.left, by simp⟩

中文:
引理 homMk_surjective
  证明: ⟨f.left, by simp⟩

Depends on / 依赖: f.left
-/
lemma homMk_surjective
    {S : T} {X Y : Over S} (f : X ⟶ Y) :
    exists (g : X.left ⟶ Y.left) (hg : g ≫ Y.hom = X.hom), f = Over.homMk g :=
  ⟨f.left, by simp⟩

section

variable (X)

/-- The forgetful functor mapping an arrow to its domain. -/
@[stacks 001G]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Over X ⥤ T
  body: Comma.fst _ _

中文:
定义 forget
  签名: : Over X ⥤ T
  定义体: Comma.fst _ _

Depends on / 依赖: Comma.fst
-/
def forget : Over X ⥤ T :=
  Comma.fst _ _

end

@[simp]
/--
theorem `forget_obj` / 定理 `forget_obj`

English:
theorem forget_obj
  given: {U : Over X}
  statement: (forget X).obj U = U.left
  proof: rfl

@[simp]

中文:
定理 forget_obj
  条件: {U : Over X}
  结论: (forget X).obj U = U.left
  证明: rfl

@[simp]
-/
theorem forget_obj {U : Over X} : (forget X).obj U = U.left :=
  rfl

@[simp]
/--
theorem `forget_map` / 定理 `forget_map`

English:
theorem forget_map
  given: {U V : Over X} {f : U ⟶ V}
  statement: (forget X).map f = f.left
  proof: rfl

中文:
定理 forget_map
  条件: {U V : Over X} {f : U ⟶ V}
  结论: (forget X).map f = f.left
  证明: rfl
-/
theorem forget_map {U V : Over X} {f : U ⟶ V} : (forget X).map f = f.left :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- The natural cocone over the forgetful functor `Over X ⥤ T` with cocone point `X`. -/
@[simps]
/--
Definition of `forgetCocone` / `forgetCocone` 的定义

English:
definition forgetCocone
  signature: (X : T)
  body: { pt := X
    ι := { app := Comma.hom } }

中文:
定义 forgetCocone
  签名: (X : T)
  定义体: { pt := X
    ι := { app := Comma.hom } }

Depends on / 依赖: Comma.hom
-/
def forgetCocone (X : T) : Limits.Cocone (forget X) :=
  { pt := X
    ι := { app := Comma.hom } }

/-- A morphism `f : X ⟶ Y` induces a functor `Over X ⥤ Over Y` in the obvious way. -/
@[stacks 001G, implicit_reducible]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {Y : T} (f : X ⟶ Y)
  body: Comma.mapRight _ Discrete.natTrans fun _ => f

中文:
定义 map
  签名: {Y : T} (f : X ⟶ Y)
  定义体: Comma.mapRight _ Discrete.natTrans fun _ => f

Depends on / 依赖: Comma.mapRight, Discrete, Discrete.natTrans, mapRight, natTrans
-/
def map {Y : T} (f : X ⟶ Y) : Over X ⥤ Over Y :=
Comma.mapRight _ Discrete.natTrans fun _ => f

section

variable {Y : T} {f : X ⟶ Y} {U V : Over X} {g : U ⟶ V}

@[simp]
/--
theorem `map_obj_left` / 定理 `map_obj_left`

English:
theorem map_obj_left
  statement: ((map f).obj U).left = U.left
  proof: rfl

@[simp]

中文:
定理 map_obj_left
  结论: ((map f).obj U).left = U.left
  证明: rfl

@[simp]
-/
theorem map_obj_left : ((map f).obj U).left = U.left :=
  rfl

@[simp]
/--
theorem `map_obj_hom` / 定理 `map_obj_hom`

English:
theorem map_obj_hom
  statement: ((map f).obj U).hom = U.hom ≫ f
  proof: rfl

@[simp]

中文:
定理 map_obj_hom
  结论: ((map f).obj U).hom = U.hom ≫ f
  证明: rfl

@[simp]
-/
theorem map_obj_hom : ((map f).obj U).hom = U.hom ≫ f :=
  rfl

@[simp]
/--
theorem `map_map_left` / 定理 `map_map_left`

English:
theorem map_map_left
  statement: ((map f).map g).left = g.left
  proof: rfl

中文:
定理 map_map_left
  结论: ((map f).map g).left = g.left
  证明: rfl
-/
theorem map_map_left : ((map f).map g).left = g.left :=
  rfl

/--
Definition of `mapIso` / `mapIso` 的定义

English:
definition mapIso
  signature: (f : X ≅ Y)
  body: Comma.mapRightIso _ Discrete.natIso fun _ => f

中文:
定义 mapIso
  签名: (f : X ≅ Y)
  定义体: Comma.mapRightIso _ Discrete.natIso fun _ => f

Depends on / 依赖: Comma.mapRightIso, Discrete, Discrete.natIso, mapRightIso, natIso
-/
def mapIso (f : X ≅ Y) : Over X ≌ Over Y :=
Comma.mapRightIso _ Discrete.natIso fun _ => f

/--
lemma `mapIso_functor` / 引理 `mapIso_functor`

English:
lemma mapIso_functor
  given: (f : X ≅ Y)
  statement: (mapIso f).functor = map f.hom
  proof: rfl

中文:
引理 mapIso_functor
  条件: (f : X ≅ Y)
  结论: (mapIso f).functor = map f.hom
  证明: rfl
-/
@[simp] lemma mapIso_functor (f : X ≅ Y) : (mapIso f).functor = map f.hom := rfl
/--
lemma `mapIso_inverse` / 引理 `mapIso_inverse`

English:
lemma mapIso_inverse
  given: (f : X ≅ Y)
  statement: (mapIso f).inverse = map f.inv
  proof: rfl

中文:
引理 mapIso_inverse
  条件: (f : X ≅ Y)
  结论: (mapIso f).inverse = map f.inv
  证明: rfl
-/
@[simp] lemma mapIso_inverse (f : X ≅ Y) : (mapIso f).inverse = map f.inv := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIso
  signature: f] : (Over.map f).IsEquivalence
  body: (Over.mapIso <| asIso f).isEquivalence_functor

中文:
实例 [是同构
  签名: f] : (Over.map f).是等价
  定义体: (Over.mapIso <| asIso f).isEquivalence_functor

Depends on / 依赖: Over.mapIso, isEquivalence_functor, mapIso
-/
instance [IsIso f] : (Over.map f).IsEquivalence := (Over.mapIso <| asIso f).isEquivalence_functor

end

section coherences
/-!
This section proves various equalities between functors that
demonstrate, for instance, that over categories assemble into a
functor `mapFunctor : T ⥤ Cat`.

These equalities between functors are then converted to natural
isomorphisms using `eqToIso`. Such natural isomorphisms could be
obtained directly using `Iso.refl` but this method will have
better computational properties, when used, for instance, in
developing the theory of Beck-Chevalley transformations.
-/

set_option backward.isDefEq.respectTransparency.types false in
/-- The natural isomorphism arising from `mapForget_eq`. -/
@[simps!]
/--
Definition of `mapId` / `mapId` 的定义

English:
definition mapId
  signature: (Y : T)
  body: NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

中文:
定义 mapId
  签名: (Y : T)
  定义体: NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def mapId (Y : T) : map (𝟙 Y) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `mapId_eq` / 定理 `mapId_eq`

English:
theorem mapId_eq
  given: (Y : T)
  statement: map (𝟙 Y) = 𝟭 _
  proof: Functor.ext_of_iso (mapId Y) (fun _ => by simp [map, Comma.mapRight]; rfl)
    (fun _ => by ext; simp [eqToHom_left])

中文:
定理 mapId_eq
  条件: (Y : T)
  结论: map (𝟙 Y) = 𝟭 _
  证明: Functor.ext_of_iso (mapId Y) (fun _ => by simp [map, Comma.mapRight]; rfl)
    (fun _ => by ext; simp [eqToHom_left])

Depends on / 依赖: Comma.mapRight, Functor, Functor.ext_of_iso, eqToHom_left, ext_of_iso, mapRight
-/
theorem mapId_eq (Y : T) : map (𝟙 Y) = 𝟭 _ :=
  Functor.ext_of_iso (mapId Y) (fun _ => by simp [map, Comma.mapRight]; rfl)
    (fun _ => by ext; simp [eqToHom_left])

/--
theorem `mapForget_eq` / 定理 `mapForget_eq`

English:
theorem mapForget_eq
  given: {X Y : T} (f : X ⟶ Y)
  proof: rfl

中文:
定理 mapForget_eq
  条件: {X Y : T} (f : X ⟶ Y)
  证明: rfl
-/
theorem mapForget_eq {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget Y) = (forget X) := rfl

/--
Definition of `mapForget` / `mapForget` 的定义

English:
definition mapForget
  signature: {X Y : T} (f : X ⟶ Y)
  body: eqToIso (mapForget_eq f)

中文:
定义 mapForget
  签名: {X Y : T} (f : X ⟶ Y)
  定义体: eqToIso (mapForget_eq f)

Depends on / 依赖: eqToIso, mapForget_eq
-/
def mapForget {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget Y) ≅ (forget X) := eqToIso (mapForget_eq f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism arising from `mapComp_eq`. -/
@[simps!]
/--
Definition of `mapComp` / `mapComp` 的定义

English:
definition mapComp
  signature: {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
  body: NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

中文:
定义 mapComp
  签名: {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
  定义体: NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def mapComp {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) ≅ map f ⋙ map g :=
  NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `mapComp_eq` / 定理 `mapComp_eq`

English:
theorem mapComp_eq
  given: {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: Functor.ext_of_iso (mapComp f g)
    (fun _ => by simp [map, Comma.mapRight])
    (fun _ => by ext; simp [eqToHom_left])

中文:
定理 mapComp_eq
  条件: {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: Functor.ext_of_iso (mapComp f g)
    (fun _ => by simp [map, Comma.mapRight])
    (fun _ => by ext; simp [eqToHom_left])

Depends on / 依赖: Comma.mapRight, Functor, Functor.ext_of_iso, eqToHom_left, ext_of_iso, mapComp, mapRight
-/
theorem mapComp_eq {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = (map f) ⋙ (map g) :=
  Functor.ext_of_iso (mapComp f g)
    (fun _ => by simp [map, Comma.mapRight])
    (fun _ => by ext; simp [eqToHom_left])

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f = g`, then `map f` is naturally isomorphic to `map g`. -/
@[simps!]
/--
Definition of `mapCongr` / `mapCongr` 的定义

English:
definition mapCongr
  signature: {X Y : T} (f g : X ⟶ Y) (h : f = g)
  body: NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

中文:
定义 mapCongr
  签名: {X Y : T} (f g : X ⟶ Y) (h : f = g)
  定义体: NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def mapCongr {X Y : T} (f g : X ⟶ Y) (h : f = g) :
    map f ≅ map g :=
  NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `mapCongr_rfl` / 引理 `mapCongr_rfl`

English:
lemma mapCongr_rfl
  given: {X Y : T} (f : X ⟶ Y)
  proof: rfl

中文:
引理 mapCongr_rfl
  条件: {X Y : T} (f : X ⟶ Y)
  证明: rfl
-/
lemma mapCongr_rfl {X Y : T} (f : X ⟶ Y) :
    mapCongr f f rfl = Iso.refl _ := rfl

variable (T) in
/--
Definition of `mapFunctor` / `mapFunctor` 的定义

English:
definition mapFunctor
  signature: : T ⥤ Cat where
  body: Cat.of (Over X)
  map f := (map f).toCatHom
  map_id X := congr($(mapId_eq X).toCatHom)
  map_comp f g := congr($(mapComp_eq f g).toCatHom)

中文:
定义 mapFunctor
  签名: : T ⥤ Cat where
  定义体: Cat.of (Over X)
  map f := (map f).toCatHom
  map_id X := congr($(mapId_eq X).toCatHom)
  map_comp f g := congr($(mapComp_eq f g).toCatHom)
-/
@[simps] def mapFunctor : T ⥤ Cat where
  obj X := Cat.of (Over X)
  map f := (map f).toCatHom
  map_id X := congr($(mapId_eq X).toCatHom)
  map_comp f g := congr($(mapComp_eq f g).toCatHom)

end coherences

/--
Instance `forget_reflects_iso` / 实例 `forget_reflects_iso`

English:
instance forget_reflects_iso
  signature: : (forget X).ReflectsIsomorphisms where
  body: ⟨Over.homMk (inv ((forget X).map f) :), by cat_disch⟩

中文:
实例 forget_reflects_iso
  签名: : (forget X).反映同构 where
  定义体: ⟨Over.homMk (inv ((forget X).map f) :), by cat_disch⟩

Depends on / 依赖: Over.homMk, cat_disch, forget
-/
instance forget_reflects_iso : (forget X).ReflectsIsomorphisms where
  reflects f _ := ⟨Over.homMk (inv ((forget X).map f) :), by cat_disch⟩

/--
Definition of `mkIdTerminal` / `mkIdTerminal` 的定义

English:
definition mkIdTerminal
  signature: : Limits.IsTerminal (mk (𝟙 X))
  body: CostructuredArrow.mkIdTerminal

中文:
定义 mkIdTerminal
  签名: : Limits.是终止 (mk (𝟙 X))
  定义体: CostructuredArrow.mkIdTerminal

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mkIdTerminal, mkIdTerminal
-/
noncomputable def mkIdTerminal : Limits.IsTerminal (mk (𝟙 X)) :=
  CostructuredArrow.mkIdTerminal

set_option backward.defeqAttrib.useBackward true in
-- We could make this defeq if we care.
/--
lemma `mkIdTerminal_from_left` / 引理 `mkIdTerminal_from_left`

English:
lemma mkIdTerminal_from_left
  given: (Y : Over X)
  statement: (mkIdTerminal.from Y).left = Y.hom
  proof: by
  rw [mkIdTerminal.hom_ext (mkIdTerminal.from Y) (homMk Y.hom)]
  rfl

中文:
引理 mkIdTerminal_from_left
  条件: (Y : Over X)
  结论: (mkIdTerminal.from Y).left = Y.hom
  证明: by
  rw [mkIdTerminal.hom_ext (mkIdTerminal.from Y) (homMk Y.hom)]
  rfl
-/
@[simp] lemma mkIdTerminal_from_left (Y : Over X) : (mkIdTerminal.from Y).left = Y.hom := by
  rw [mkIdTerminal.hom_ext (mkIdTerminal.from Y) (homMk Y.hom)]
  rfl

/--
Instance `forget_faithful` / 实例 `forget_faithful`

English:
instance forget_faithful
  signature: : (forget X).Faithful where

中文:
实例 forget_faithful
  签名: : (forget X).忠实 where
-/
instance forget_faithful : (forget X).Faithful where

-- TODO: Show the converse holds if `T` has binary products.
/--
theorem `epi_of_epi_left` / 定理 `epi_of_epi_left`

English:
theorem epi_of_epi_left
  given: {f g : Over X} (k : f ⟶ g) [hk : Epi k.left]
  statement: Epi k
  proof: (forget X).epi_of_epi_map hk

中文:
定理 epi_of_epi_left
  条件: {f g : Over X} (k : f ⟶ g) [hk : 满态射 k.left]
  结论: 满态射 k
  证明: (forget X).epi_of_epi_map hk

Depends on / 依赖: epi_of_epi_map, forget
-/
theorem epi_of_epi_left {f g : Over X} (k : f ⟶ g) [hk : Epi k.left] : Epi k :=
  (forget X).epi_of_epi_map hk

/--
Instance `epi_homMk` / 实例 `epi_homMk`

English:
instance epi_homMk
  signature: {U V : Over X} {f : U.left ⟶ V.left} [Epi f] (w)
  body: (forget X).epi_of_epi_map ‹_›

中文:
实例 epi_homMk
  签名: {U V : Over X} {f : U.left ⟶ V.left} [满态射 f] (w)
  定义体: (forget X).epi_of_epi_map ‹_›

Depends on / 依赖: epi_of_epi_map, forget
-/
instance epi_homMk {U V : Over X} {f : U.left ⟶ V.left} [Epi f] (w) : Epi (homMk f w) :=
  (forget X).epi_of_epi_map ‹_›

/--
theorem `mono_of_mono_left` / 定理 `mono_of_mono_left`

English:
theorem mono_of_mono_left
  given: {f g : Over X} (k : f ⟶ g) [hk : Mono k.left]
  statement: Mono k
  proof: (forget X).mono_of_mono_map hk

中文:
定理 mono_of_mono_left
  条件: {f g : Over X} (k : f ⟶ g) [hk : 单态射 k.left]
  结论: 单态射 k
  证明: (forget X).mono_of_mono_map hk

Depends on / 依赖: forget, mono_of_mono_map
-/
theorem mono_of_mono_left {f g : Over X} (k : f ⟶ g) [hk : Mono k.left] : Mono k :=
  (forget X).mono_of_mono_map hk

/--
Instance `mono_homMk` / 实例 `mono_homMk`

English:
instance mono_homMk
  signature: {U V : Over X} {f : U.left ⟶ V.left} [Mono f] (w)
  body: (forget X).mono_of_mono_map ‹_›

中文:
实例 mono_homMk
  签名: {U V : Over X} {f : U.left ⟶ V.left} [单态射 f] (w)
  定义体: (forget X).mono_of_mono_map ‹_›

Depends on / 依赖: forget, mono_of_mono_map
-/
instance mono_homMk {U V : Over X} {f : U.left ⟶ V.left} [Mono f] (w) : Mono (homMk f w) :=
  (forget X).mono_of_mono_map ‹_›

set_option backward.defeqAttrib.useBackward true in
/--
Instance `mono_left_of_mono` / 实例 `mono_left_of_mono`

English:
instance mono_left_of_mono
  signature: {f g : Over X} (k : f ⟶ g) [Mono k]
  body: by
  refine ⟨fun {Y : T} l m a => ?_⟩
  let l' : mk (m ≫ f.hom) ⟶ f := homMk l (by
        dsimp; rw [← Over.w k, ← Category.assoc, congrArg (· ≫ g.hom) a, Category.assoc])
  suffices l' = (homMk m : mk (m ≫ f.hom) ⟶ f) by apply congrArg CommaMorphism.left this
  rw [← cancel_mono k]
  ext
  apply a

中文:
实例 mono_left_of_mono
  签名: {f g : Over X} (k : f ⟶ g) [单态射 k]
  定义体: by
  refine ⟨fun {Y : T} l m a => ?_⟩
  let l' : mk (m ≫ f.hom) ⟶ f := homMk l (by
        dsimp; rw [← Over.w k, ← Category.assoc, congrArg (· ≫ g.hom) a, Category.assoc])
  suffices l' = (homMk m : mk (m ≫ f.hom) ⟶ f) by apply congrArg CommaMorphism.left this
  rw [← cancel_mono k]
  ext
  apply a

Depends on / 依赖: Category, Category.assoc, CommaMorphism, CommaMorphism.left, Over.w, cancel_mono, f.hom, g.hom
-/
instance mono_left_of_mono {f g : Over X} (k : f ⟶ g) [Mono k] : Mono k.left := by
  refine ⟨fun {Y : T} l m a => ?_⟩
  let l' : mk (m ≫ f.hom) ⟶ f := homMk l (by
        dsimp; rw [← Over.w k, ← Category.assoc, congrArg (· ≫ g.hom) a, Category.assoc])
  suffices l' = (homMk m : mk (m ≫ f.hom) ⟶ f) by apply congrArg CommaMorphism.left this
  rw [← cancel_mono k]
  ext
  apply a

section IteratedSlice

variable (f : Over X)

/-- Given f : Y ⟶ X, this is the obvious functor from (T/X)/f to T/Y -/
@[simps]
/--
Definition of `iteratedSliceForward` / `iteratedSliceForward` 的定义

English:
definition iteratedSliceForward
  signature: : Over f ⥤ Over f.left where
  body: Over.mk α.hom.left
  map κ := Over.homMk κ.left.left (by dsimp; rw [← Over.w κ]; rfl)

中文:
定义 iteratedSliceForward
  签名: : Over f ⥤ Over f.left where
  定义体: Over.mk α.hom.left
  map κ := Over.homMk κ.left.left (by dsimp; rw [← Over.w κ]; rfl)

Depends on / 依赖: Over.mk, hom.left
-/
def iteratedSliceForward : Over f ⥤ Over f.left where
  obj α := Over.mk α.hom.left
  map κ := Over.homMk κ.left.left (by dsimp; rw [← Over.w κ]; rfl)

/-- Given f : Y ⟶ X, this is the obvious functor from T/Y to (T/X)/f -/
@[simps]
/--
Definition of `iteratedSliceBackward` / `iteratedSliceBackward` 的定义

English:
definition iteratedSliceBackward
  signature: : Over f.left ⥤ Over f where
  body: mk (homMk g.hom : mk (g.hom ≫ f.hom) ⟶ f)
  map α := homMk (homMk α.left (w_assoc α f.hom)) (OverMorphism.ext (w α))

中文:
定义 iteratedSliceBackward
  签名: : Over f.left ⥤ Over f where
  定义体: mk (homMk g.hom : mk (g.hom ≫ f.hom) ⟶ f)
  map α := homMk (homMk α.left (w_assoc α f.hom)) (OverMorphism.ext (w α))

Depends on / 依赖: f.hom, g.hom
-/
def iteratedSliceBackward : Over f.left ⥤ Over f where
  obj g := mk (homMk g.hom : mk (g.hom ≫ f.hom) ⟶ f)
  map α := homMk (homMk α.left (w_assoc α f.hom)) (OverMorphism.ext (w α))

/--
theorem `iteratedSliceBackward_forget` / 定理 `iteratedSliceBackward_forget`

English:
theorem iteratedSliceBackward_forget
  given: (f : Over X)
  proof: rfl

中文:
定理 iteratedSliceBackward_forget
  条件: (f : Over X)
  证明: rfl
-/
theorem iteratedSliceBackward_forget (f : Over X) :
    iteratedSliceBackward f ⋙ Over.forget f = Over.map f.hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given f : Y ⟶ X, we have an equivalence between (T/X)/f and T/Y -/
@[simps]
/--
Definition of `iteratedSliceEquiv` / `iteratedSliceEquiv` 的定义

English:
definition iteratedSliceEquiv
  signature: : Over f ≌ Over f.left where
  body: iteratedSliceForward f
  inverse := iteratedSliceBackward f
  unitIso := NatIso.ofComponents (fun g => Over.isoMk (Over.isoMk (Iso.refl _)))
  counitIso := NatIso.ofComponents (fun g => Over.isoMk (Iso.refl _))

中文:
定义 iteratedSliceEquiv
  签名: : Over f ≌ Over f.left where
  定义体: iteratedSliceForward f
  inverse := iteratedSliceBackward f
  unitIso := NatIso.ofComponents (fun g => Over.isoMk (Over.isoMk (Iso.refl _)))
  counitIso := NatIso.ofComponents (fun g => Over.isoMk (Iso.refl _))

Depends on / 依赖: iteratedSliceForward
-/
def iteratedSliceEquiv : Over f ≌ Over f.left where
  functor := iteratedSliceForward f
  inverse := iteratedSliceBackward f
  unitIso := NatIso.ofComponents (fun g => Over.isoMk (Over.isoMk (Iso.refl _)))
  counitIso := NatIso.ofComponents (fun g => Over.isoMk (Iso.refl _))

/--
theorem `iteratedSliceForward_forget` / 定理 `iteratedSliceForward_forget`

English:
theorem iteratedSliceForward_forget
  proof: rfl

中文:
定理 iteratedSliceForward_forget
  证明: rfl
-/
theorem iteratedSliceForward_forget :
    iteratedSliceForward f ⋙ forget f.left = forget f ⋙ forget X :=
  rfl

/--
theorem `iteratedSliceBackward_forget_forget` / 定理 `iteratedSliceBackward_forget_forget`

English:
theorem iteratedSliceBackward_forget_forget
  proof: rfl

中文:
定理 iteratedSliceBackward_forget_forget
  证明: rfl
-/
theorem iteratedSliceBackward_forget_forget :
    iteratedSliceBackward f ⋙ forget f ⋙ forget X = forget f.left :=
  rfl

variable {f}

/-- The naturality of the iterated slice equivalence up to isomorphism. -/
@[simps! hom_app inv_app]
/--
Definition of `iteratedSliceForwardNaturalityIso` / `iteratedSliceForwardNaturalityIso` 的定义

English:
definition iteratedSliceForwardNaturalityIso
  signature: {g : Over X} (p : f ⟶ g)
  body: Iso.refl _

中文:
定义 iteratedSliceForward自然数uralityIso
  签名: {g : Over X} (p : f ⟶ g)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def iteratedSliceForwardNaturalityIso {g : Over X} (p : f ⟶ g) :
    iteratedSliceForward f ⋙ Over.map p.left ≅ Over.map p ⋙ iteratedSliceForward g :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism relating the functor `Over.map p` to the functor `Over.map p.left`,
mediated by the underlying functor of the iterated slice equivalence.
Note that `iteratedSliceForward` can in fact be considered as a natural transformation from the
2-functor `Over (C := Over X) : Over X ⥤ Cat` to the composite 2-functor
`forget X ⋙ Over : Over X ⥤ Cat`, and the naturality isomorphism is then given by
`iteratedSliceEquivOverMapIso`.
-/
@[simps! hom_app_left_left inv_app_left_left]
/--
Definition of `iteratedSliceEquivOverMapIso` / `iteratedSliceEquivOverMapIso` 的定义

English:
definition iteratedSliceEquivOverMapIso
  signature: {f g : Over X} (p : f ⟶ g)
  body: NatIso.ofComponents (fun h => Over.isoMk (Over.isoMk (Iso.refl _)))

中文:
定义 iteratedSliceEquivOverMapIso
  签名: {f g : Over X} (p : f ⟶ g)
  定义体: NatIso.ofComponents (fun h => Over.isoMk (Over.isoMk (Iso.refl _)))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, Over.isoMk, ofComponents
-/
def iteratedSliceEquivOverMapIso {f g : Over X} (p : f ⟶ g) :
    f.iteratedSliceForward ⋙ Over.map p.left ⋙ g.iteratedSliceBackward ≅ Over.map p :=
  NatIso.ofComponents (fun h => Over.isoMk (Over.isoMk (Iso.refl _)))

end IteratedSlice

set_option backward.defeqAttrib.useBackward true in
/-- A functor `F : T ⥤ D` induces a functor `Over X ⥤ Over (F.obj X)` in the obvious way. -/
@[simps]
/--
Definition of `post` / `post` 的定义

English:
definition post
  signature: (F : T ⥤ D)
  body: mk F.map Y.hom
  map f := Over.homMk (F.map f.left) (by simp [← F.map_comp])

中文:
定义 post
  签名: (F : T ⥤ D)
  定义体: mk F.map Y.hom
  map f := Over.homMk (F.map f.left) (by simp [← F.map_comp])

Depends on / 依赖: F.map, Y.hom
-/
def post (F : T ⥤ D) : Over X ⥤ Over (F.obj X) where
obj Y := mk F.map Y.hom
  map f := Over.homMk (F.map f.left) (by simp [← F.map_comp])

/--
lemma `post_comp` / 引理 `post_comp`

English:
lemma post_comp
  given: {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E)
  proof: rfl

中文:
引理 post_comp
  条件: {E : 类型} [范畴* E] (F : T ⥤ D) (G : D ⥤ E)
  证明: rfl
-/
lemma post_comp {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) = post (X := X) F ⋙ post G :=
  rfl

/--
lemma `post_forget_eq_forget_comp` / 引理 `post_forget_eq_forget_comp`

English:
lemma post_forget_eq_forget_comp
  given: (F : T ⥤ D) (X : T)
  proof: rfl

中文:
引理 post_forget_eq_forget_comp
  条件: (F : T ⥤ D) (X : T)
  证明: rfl
-/
lemma post_forget_eq_forget_comp (F : T ⥤ D) (X : T) :
    post F ⋙ forget (F.obj X) = forget X ⋙ F :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `post (F ⋙ G)` is isomorphic (actually equal) to `post F ⋙ post G`. -/
@[simps!]
/--
Definition of `postComp` / `postComp` 的定义

English:
definition postComp
  signature: {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E)
  body: NatIso.ofComponents (fun X => Iso.refl _) (fun f => by
    ext
    dsimp only [Iso.refl_hom, Over.comp_left, Over.id_left]
    simp)

中文:
定义 postComp
  签名: {E : 类型} [范畴* E] (F : T ⥤ D) (G : D ⥤ E)
  定义体: NatIso.ofComponents (fun X => Iso.refl _) (fun f => by
    ext
    dsimp only [Iso.refl_hom, Over.comp_left, Over.id_left]
    simp)
-/
def postComp {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) ≅ post F ⋙ post G :=
  NatIso.ofComponents (fun X => Iso.refl _) (fun f => by
    ext
    dsimp only [Iso.refl_hom, Over.comp_left, Over.id_left]
    simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural transformation `F ⟶ G` induces a natural transformation on
`Over X` up to `Over.map`. -/
@[simps]
/--
Definition of `postMap` / `postMap` 的定义

English:
definition postMap
  signature: {F G : T ⥤ D} (e : F ⟶ G)
  body: Over.homMk (e.app Y.left)

中文:
定义 postMap
  签名: {F G : T ⥤ D} (e : F ⟶ G)
  定义体: Over.homMk (e.app Y.left)

Depends on / 依赖: Over.homMk, Y.left, e.app
-/
def postMap {F G : T ⥤ D} (e : F ⟶ G) : post F ⋙ map (e.app X) ⟶ post G where
  app Y := Over.homMk (e.app Y.left)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F` and `G` are naturally isomorphic, then `Over.post F` and `Over.post G` are also naturally
isomorphic up to `Over.map` -/
@[simps!]
/--
Definition of `postCongr` / `postCongr` 的定义

English:
definition postCongr
  signature: {F G : T ⥤ D} (e : F ≅ G)
  body: NatIso.ofComponents (fun A => Over.isoMk (e.app A.left))

中文:
定义 postCongr
  签名: {F G : T ⥤ D} (e : F ≅ G)
  定义体: NatIso.ofComponents (fun A => Over.isoMk (e.app A.left))

Depends on / 依赖: A.left, NatIso, NatIso.ofComponents, Over.isoMk, e.app, ofComponents
-/
def postCongr {F G : T ⥤ D} (e : F ≅ G) : post F ⋙ map (e.hom.app X) ≅ post G :=
  NatIso.ofComponents (fun A => Over.isoMk (e.app A.left))

variable (X) (F : T ⥤ D)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Faithful]
  signature: : (Over.post (X := X) F).Faithful where
  body: by
    ext
    exact F.map_injective (congrArg CommaMorphism.left h)

中文:
实例 [F.忠实]
  签名: : (Over.post (X := X) F).忠实 where
  定义体: by
    ext
    exact F.map_injective (congrArg CommaMorphism.left h)

Depends on / 依赖: Faithful
-/
instance [F.Faithful] : (Over.post (X := X) F).Faithful where
  map_injective {A B} f g h := by
    ext
    exact F.map_injective (congrArg CommaMorphism.left h)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Faithful]
  signature: [F.Full]
  body: by
    obtain ⟨a, ha⟩ := F.map_surjective f.left
    exact ⟨Over.homMk a (F.map_injective (by simp [ha, dsimp% f.w])), by cat_disch⟩

中文:
实例 [F.忠实]
  签名: [F.满]
  定义体: by
    obtain ⟨a, ha⟩ := F.map_surjective f.left
    exact ⟨Over.homMk a (F.map_injective (by simp [ha, dsimp% f.w])), by cat_disch⟩
-/
instance [F.Faithful] [F.Full] : (Over.post (X := X) F).Full where
  map_surjective {A B} f := by
    obtain ⟨a, ha⟩ := F.map_surjective f.left
    exact ⟨Over.homMk a (F.map_injective (by simp [ha, dsimp% f.w])), by cat_disch⟩

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Full]
  signature: [F.EssSurj]
  body: by
    obtain ⟨A', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) B.left
    obtain ⟨f, hf⟩ := F.map_surjective (e.hom ≫ B.hom)
    exact ⟨Over.mk f, ⟨Over.isoMk e⟩⟩

中文:
实例 [F.满]
  签名: [F.本质满射]
  定义体: by
    obtain ⟨A', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) B.left
    obtain ⟨f, hf⟩ := F.map_surjective (e.hom ≫ B.hom)
    exact ⟨Over.mk f, ⟨Over.isoMk e⟩⟩

Depends on / 依赖: EssSurj
-/
instance [F.Full] [F.EssSurj] : (Over.post (X := X) F).EssSurj where
  mem_essImage B := by
    obtain ⟨A', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) B.left
    obtain ⟨f, hf⟩ := F.map_surjective (e.hom ≫ B.hom)
    exact ⟨Over.mk f, ⟨Over.isoMk e⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.IsEquivalence]
  signature: : (Over.post (X := X) F).IsEquivalence where

中文:
实例 [F.是等价]
  签名: : (Over.post (X := X) F).是等价 where

Depends on / 依赖: IsEquivalence
-/
instance [F.IsEquivalence] : (Over.post (X := X) F).IsEquivalence where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `_root_.CategoryTheory.Functor.FullyFaithful.over` / `_root_.CategoryTheory.Functor.FullyFaithful.over` 的定义

English:
definition _root_.CategoryTheory.Functor.FullyFaithful.over
  signature: (h : F.FullyFaithful)
  body: Over.homMk (h.preimage f.left) h.map_injective (by simpa using Over.w f)

中文:
定义 _root_.范畴论.函子.满忠实.over
  签名: (h : F.满忠实)
  定义体: Over.homMk (h.preimage f.left) h.map_injective (by simpa using Over.w f)

Depends on / 依赖: FullyFaithful
-/
def _root_.CategoryTheory.Functor.FullyFaithful.over (h : F.FullyFaithful) :
    (post (X := X) F).FullyFaithful where
preimage {A B} f := Over.homMk (h.preimage f.left) h.map_injective (by simpa using Over.w f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `G` is a right adjoint, then so is `post G : Over Y ⥤ Over (G Y)`.

If the left adjoint of `G` is `F`, then the left adjoint of `post G` is given by
`(X ⟶ G Y) ↦ (F X ⟶ F G Y ⟶ Y)`. -/
@[simps]
/--
Definition of `postAdjunctionRight` / `postAdjunctionRight` 的定义

English:
definition postAdjunctionRight
  signature: {Y : D} {F : T ⥤ D} {G : D ⥤ T} (a : F ⊣ G)
  body: homMk a.unit.app A.left
counit.app A := homMk a.counit.app A.left
  counit.naturality _ _ f := by
    ext
    exact a.counit_naturality f.left
  left_triangle_components A := by
    ext
    simp [-Functor.id_obj]

中文:
定义 postAdjunctionRight
  签名: {Y : D} {F : T ⥤ D} {G : D ⥤ T} (a : F ⊣ G)
  定义体: homMk a.unit.app A.left
counit.app A := homMk a.counit.app A.left
  counit.naturality _ _ f := by
    ext
    exact a.counit_naturality f.left
  left_triangle_components A := by
    ext
    simp [-Functor.id_obj]

Depends on / 依赖: A.left, a.unit.app
-/
def postAdjunctionRight {Y : D} {F : T ⥤ D} {G : D ⥤ T} (a : F ⊣ G) :
    post F ⋙ map (a.counit.app Y) ⊣ post G where
unit.app A := homMk a.unit.app A.left
counit.app A := homMk a.counit.app A.left
  counit.naturality _ _ f := by
    ext
    exact a.counit_naturality f.left
  left_triangle_components A := by
    ext
    simp [-Functor.id_obj]

/--
Instance `isRightAdjoint_post` / 实例 `isRightAdjoint_post`

English:
instance isRightAdjoint_post
  signature: {Y : D} {G : D ⥤ T} [G.IsRightAdjoint]
  body: let ⟨F, ⟨a⟩⟩ := ‹G.IsRightAdjoint›; ⟨_, ⟨postAdjunctionRight a⟩⟩

中文:
实例 isRightAdjoint_post
  签名: {Y : D} {G : D ⥤ T} [G.是右伴随]
  定义体: let ⟨F, ⟨a⟩⟩ := ‹G.IsRightAdjoint›; ⟨_, ⟨postAdjunctionRight a⟩⟩

Depends on / 依赖: IsRightAdjoint
-/
instance isRightAdjoint_post {Y : D} {G : D ⥤ T} [G.IsRightAdjoint] :
    (post (X := Y) G).IsRightAdjoint :=
  let ⟨F, ⟨a⟩⟩ := ‹G.IsRightAdjoint›; ⟨_, ⟨postAdjunctionRight a⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories induces an equivalence on over categories. -/
@[simps]
/--
Definition of `postEquiv` / `postEquiv` 的定义

English:
definition postEquiv
  signature: (F : T ≌ D)
  body: Over.post F.functor
  inverse := Over.post (X := F.functor.obj X) F.inverse ⋙ Over.map (F.unitIso.inv.app X)
  unitIso := NatIso.ofComponents (fun A => Over.isoMk (F.unitIso.app A.left))
  counitIso := NatIso.ofComponents (fun A => Over.isoMk (F.counitIso.app A.left))

中文:
定义 postEquiv
  签名: (F : T ≌ D)
  定义体: Over.post F.functor
  inverse := Over.post (X := F.functor.obj X) F.inverse ⋙ Over.map (F.unitIso.inv.app X)
  unitIso := NatIso.ofComponents (fun A => Over.isoMk (F.unitIso.app A.left))
  counitIso := NatIso.ofComponents (fun A => Over.isoMk (F.counitIso.app A.left))

Depends on / 依赖: F.functor, Over.post, functor
-/
def postEquiv (F : T ≌ D) : Over X ≌ Over (F.functor.obj X) where
  functor := Over.post F.functor
  inverse := Over.post (X := F.functor.obj X) F.inverse ⋙ Over.map (F.unitIso.inv.app X)
  unitIso := NatIso.ofComponents (fun A => Over.isoMk (F.unitIso.app A.left))
  counitIso := NatIso.ofComponents (fun A => Over.isoMk (F.counitIso.app A.left))

/-- `post (Over.forget X) : Over f ⥤ Over (forget.obj f)` is naturally isomorphic to the
functor `Over.iteratedSliceForward : Over f ⥤ Over f.left`. -/
@[simps! hom_app inv_app]
/--
Definition of `iteratedSliceForwardIsoPost` / `iteratedSliceForwardIsoPost` 的定义

English:
definition iteratedSliceForwardIsoPost
  signature: (f : Over X)
  body: Iso.refl _

中文:
定义 iteratedSliceForwardIsoPost
  签名: (f : Over X)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def iteratedSliceForwardIsoPost (f : Over X) :
    post (Over.forget X) ≅ Over.iteratedSliceForward f :=
  Iso.refl _

open Limits

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {X} in
/-- If `X : T` is terminal, then the over category of `X` is equivalent to `T`. -/
@[simps]
/--
Definition of `equivalenceOfIsTerminal` / `equivalenceOfIsTerminal` 的定义

English:
definition equivalenceOfIsTerminal
  signature: (hX : IsTerminal X)
  body: forget X
  inverse := { obj Y := mk (hX.from Y), map f := homMk f }
  unitIso := NatIso.ofComponents fun Y => isoMk (.refl _) (hX.hom_ext _ _)
  counitIso := NatIso.ofComponents fun _ => .refl _

中文:
定义 equivalenceOfIsTerminal
  签名: (hX : 是终止 X)
  定义体: forget X
  inverse := { obj Y := mk (hX.from Y), map f := homMk f }
  unitIso := NatIso.ofComponents fun Y => isoMk (.refl _) (hX.hom_ext _ _)
  counitIso := NatIso.ofComponents fun _ => .refl _

Depends on / 依赖: forget
-/
def equivalenceOfIsTerminal (hX : IsTerminal X) : Over X ≌ T where
  functor := forget X
  inverse := { obj Y := mk (hX.from Y), map f := homMk f }
  unitIso := NatIso.ofComponents fun Y => isoMk (.refl _) (hX.hom_ext _ _)
  counitIso := NatIso.ofComponents fun _ => .refl _

set_option backward.defeqAttrib.useBackward true in
/-- The induced functor to `Over X` from a functor `J ⥤ C` and natural maps `sᵢ : X ⟶ Dᵢ`.
For the converse direction see `CategoryTheory.WithTerminal.commaFromOver`. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.const J).obj X)
  body: mk (s.app j)
  map f := homMk (D.map f) (by simp)

中文:
定义 lift
  签名: {J : 类型} [范畴* J] (D : J ⥤ T) {X : T} (s : D ⟶ (函子.const J).obj X)
  定义体: mk (s.app j)
  map f := homMk (D.map f) (by simp)
-/
protected def lift {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.const J).obj X) :
    J ⥤ Over X where
  obj j := mk (s.app j)
  map f := homMk (D.map f) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The induced cone on `Over X` on the lifted functor. -/
@[simps]
/--
Definition of `liftCone` / `liftCone` 的定义

English:
definition liftCone
  signature: {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.const J).obj X)
  body: mk p
  π.app j := homMk (c.π.app j)

中文:
定义 liftCone
  签名: {J : 类型} [范畴* J] (D : J ⥤ T) {X : T} (s : D ⟶ (函子.const J).obj X)
  定义体: mk p
  π.app j := homMk (c.π.app j)
-/
def liftCone {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.const J).obj X)
    (c : Cone D) (p : c.pt ⟶ X) (hp : forall j, c.π.app j ≫ s.app j = p) :
    Cone (Over.lift D s) where
  pt := mk p
  π.app j := homMk (c.π.app j)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimitLiftCone` / `isLimitLiftCone` 的定义

English:
definition isLimitLiftCone
  signature: {J : Type*} [Category* J] [Nonempty J]
  body: homMk (hc.lift ((forget _).mapCone t)) (by
    let j : J := Classical.arbitrary _
    simp [← hp j, dsimp% (t.π.app j).w, dsimp% hc.fac_assoc ((forget X).mapCone t) j])
  fac t j := by
    ext
    simp [dsimp% hc.fac ((forget X).mapCone t) j]
  uniq t _ hm := by
    ext
    refine hc.hom_ext (fun j 

中文:
定义 isLimitLiftCone
  签名: {J : 类型} [范畴* J] [非空 J]
  定义体: homMk (hc.lift ((forget _).mapCone t)) (by
    let j : J := Classical.arbitrary _
    simp [← hp j, dsimp% (t.π.app j).w, dsimp% hc.fac_assoc ((forget X).mapCone t) j])
  fac t j := by
    ext
    simp [dsimp% hc.fac ((forget X).mapCone t) j]
  uniq t _ hm := by
    ext
    refine hc.hom_ext (fun j 

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, fac_assoc, forget, hc.fac, hc.fac_assoc, hc.hom_ext, hc.lift, hom_ext, mapCone
-/
def isLimitLiftCone {J : Type*} [Category* J] [Nonempty J]
    (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.const J).obj X)
    (c : Cone D) (p : c.pt ⟶ X) (hp : forall j, c.π.app j ≫ s.app j = p)
    (hc : IsLimit c) :
    IsLimit (Over.liftCone D s c p hp) where
  lift t := homMk (hc.lift ((forget _).mapCone t)) (by
    let j : J := Classical.arbitrary _
    simp [← hp j, dsimp% (t.π.app j).w, dsimp% hc.fac_assoc ((forget X).mapCone t) j])
  fac t j := by
    ext
    simp [dsimp% hc.fac ((forget X).mapCone t) j]
  uniq t _ hm := by
    ext
    refine hc.hom_ext (fun j => ?_)
    simp [dsimp% hc.fac ((forget X).mapCone t) j, ← hm]

end Over

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Restrict a cone to the diagram over `j`. This preserves being limiting if the forgetful functor
`Over j ⥤ J` is initial (see `CategoryTheory.Limits.IsLimit.overPost`).
-/
@[simps]
/--
Definition of `Limits.Cone.overPost` / `Limits.Cone.overPost` 的定义

English:
definition Limits.Cone.overPost
  body: Over.mk (c.π.app j)
  π.app k := Over.homMk (c.π.app k.left)

中文:
定义 Limits.锥.overPost
  定义体: Over.mk (c.π.app j)
  π.app k := Over.homMk (c.π.app k.left)
-/
def Limits.Cone.overPost
    {J C : Type*} [Category* J] [Category* C] {D : J ⥤ C} (c : Cone D) (j : J) :
    Cone (Over.post (X := j) D) where
  pt := Over.mk (c.π.app j)
  π.app k := Over.homMk (c.π.app k.left)

namespace CostructuredArrow

/-- Reinterpreting an `F`-costructured arrow `F.obj d ⟶ X` as an arrow over `X` induces a functor
    `CostructuredArrow F X ⥤ Over X`. -/
@[simps! obj_left obj_hom map_left]
/--
Definition of `toOver` / `toOver` 的定义

English:
definition toOver
  signature: (F : D ⥤ T) (X : T)
  body: CostructuredArrow.pre F (𝟭 T) X

中文:
定义 toOver
  签名: (F : D ⥤ T) (X : T)
  定义体: CostructuredArrow.pre F (𝟭 T) X

Depends on / 依赖: CostructuredArrow, CostructuredArrow.pre
-/
def toOver (F : D ⥤ T) (X : T) : CostructuredArrow F X ⥤ Over X :=
  CostructuredArrow.pre F (𝟭 T) X

instance (F : D ⥤ T) (X : T) [F.Faithful] : (toOver F X).Faithful :=
  show (CostructuredArrow.pre _ _ _).Faithful from inferInstance

instance (F : D ⥤ T) (X : T) [F.Full] : (toOver F X).Full :=
  show (CostructuredArrow.pre _ _ _).Full from inferInstance

instance (F : D ⥤ T) (X : T) [F.EssSurj] : (toOver F X).EssSurj :=
  show (CostructuredArrow.pre _ _ _).EssSurj from inferInstance

/--
Instance `isEquivalence_toOver` / 实例 `isEquivalence_toOver`

English:
instance isEquivalence_toOver
  signature: (F : D ⥤ T) (X : T) [F.IsEquivalence]
  body: CostructuredArrow.isEquivalence_pre _ _ _

中文:
实例 isEquivalence_toOver
  签名: (F : D ⥤ T) (X : T) [F.是等价]
  定义体: CostructuredArrow.isEquivalence_pre _ _ _

Depends on / 依赖: CostructuredArrow, CostructuredArrow.isEquivalence_pre, isEquivalence_pre
-/
instance isEquivalence_toOver (F : D ⥤ T) (X : T) [F.IsEquivalence] :
    (toOver F X).IsEquivalence :=
  CostructuredArrow.isEquivalence_pre _ _ _

namespace costructuredArrowToOverEquivalence

variable (F : D ⥤ T) {X : T} (Y : Over X)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `costructuredArrowToOverEquivalence`. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : CostructuredArrow (toOver F X) Y ⥤ CostructuredArrow F Y.left where
  body: CostructuredArrow.mk Z.hom.left
  map f :=
    CostructuredArrow.homMk f.left.left (by rw [← CostructuredArrow.w f]; dsimp)

中文:
定义 functor
  签名: : CostructuredArrow (toOver F X) Y ⥤ CostructuredArrow F Y.left where
  定义体: CostructuredArrow.mk Z.hom.left
  map f :=
    CostructuredArrow.homMk f.left.left (by rw [← CostructuredArrow.w f]; dsimp)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, Z.hom.left
-/
def functor : CostructuredArrow (toOver F X) Y ⥤ CostructuredArrow F Y.left where
  obj Z := CostructuredArrow.mk Z.hom.left
  map f :=
    CostructuredArrow.homMk f.left.left (by rw [← CostructuredArrow.w f]; dsimp)

/-- Auxiliary definition for `costructuredArrowToOverEquivalence`. -/
@[simps]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : CostructuredArrow F Y.left ⥤ CostructuredArrow (toOver F X) Y where
  body: CostructuredArrow.mk (Y := CostructuredArrow.mk (Z.hom ≫ Y.hom))
      (Over.homMk Z.hom)
  map f :=
    CostructuredArrow.homMk
      (CostructuredArrow.homMk f.left)
        (by ext; exact CostructuredArrow.w f)

中文:
定义 inverse
  签名: : CostructuredArrow F Y.left ⥤ CostructuredArrow (toOver F X) Y where
  定义体: CostructuredArrow.mk (Y := CostructuredArrow.mk (Z.hom ≫ Y.hom))
      (Over.homMk Z.hom)
  map f :=
    CostructuredArrow.homMk
      (CostructuredArrow.homMk f.left)
        (by ext; exact CostructuredArrow.w f)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, CostructuredArrow.mk, CostructuredArrow.w, Over.homMk, Y.hom, Z.hom, f.left
-/
def inverse : CostructuredArrow F Y.left ⥤ CostructuredArrow (toOver F X) Y where
  obj Z :=
    CostructuredArrow.mk (Y := CostructuredArrow.mk (Z.hom ≫ Y.hom))
      (Over.homMk Z.hom)
  map f :=
    CostructuredArrow.homMk
      (CostructuredArrow.homMk f.left)
        (by ext; exact CostructuredArrow.w f)

end costructuredArrowToOverEquivalence

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `costructuredArrowToOverEquivalence` / `costructuredArrowToOverEquivalence` 的定义

English:
definition costructuredArrowToOverEquivalence
  signature: (F : D ⥤ T) {X : T} (Y : Over X)
  body: costructuredArrowToOverEquivalence.functor F Y
  inverse := costructuredArrowToOverEquivalence.inverse F Y
  unitIso :=
    NatIso.ofComponents (fun f =>
      CostructuredArrow.isoMk (CostructuredArrow.isoMk (Iso.refl _)
        (by simpa using f.hom.w)))
  counitIso := Iso.refl _

中文:
定义 costructuredArrowToOverEquivalence
  签名: (F : D ⥤ T) {X : T} (Y : Over X)
  定义体: costructuredArrowToOverEquivalence.functor F Y
  inverse := costructuredArrowToOverEquivalence.inverse F Y
  unitIso :=
    NatIso.ofComponents (fun f =>
      CostructuredArrow.isoMk (CostructuredArrow.isoMk (Iso.refl _)
        (by simpa using f.hom.w)))
  counitIso := Iso.refl _

Depends on / 依赖: costructuredArrowToOverEquivalence, costructuredArrowToOverEquivalence.functor, functor
-/
def costructuredArrowToOverEquivalence (F : D ⥤ T) {X : T} (Y : Over X) :
    CostructuredArrow (toOver F X) Y ≌ CostructuredArrow F Y.left where
  functor := costructuredArrowToOverEquivalence.functor F Y
  inverse := costructuredArrowToOverEquivalence.inverse F Y
  unitIso :=
    NatIso.ofComponents (fun f =>
      CostructuredArrow.isoMk (CostructuredArrow.isoMk (Iso.refl _)
        (by simpa using f.hom.w)))
  counitIso := Iso.refl _

end CostructuredArrow

/-- The under category has as objects arrows with domain `X` and as morphisms commutative
    triangles. -/
@[implicit_reducible]
/--
Definition of `Under` / `Under` 的定义

English:
definition Under
  signature: (X : T)
  body: StructuredArrow X (𝟭 T)

中文:
定义 Under
  签名: (X : T)
  定义体: StructuredArrow X (𝟭 T)

Depends on / 依赖: StructuredArrow
-/
def Under (X : T) :=
  StructuredArrow X (𝟭 T)

/--
Definition of `Under.Hom` / `Under.Hom` 的定义

English:
definition Under.Hom
  signature: {X : T} (f g : Under X)
  body: CommaMorphism f g

中文:
定义 Under.态射
  签名: {X : T} (f g : Under X)
  定义体: CommaMorphism f g
-/
protected def Under.Hom {X : T} (f g : Under X) := CommaMorphism f g

instance {X : T} : Category (Under X) where
  Hom := Under.Hom
  __ := (inferInstance : Category (Comma _ _))

-- Satisfying the inhabited linter
/--
Instance `Under.inhabited` / 实例 `Under.inhabited`

English:
instance Under.inhabited
  signature: [Inhabited T]
  body: { left := default
      right := default
      hom := 𝟙 _ }

中文:
实例 Under.inhabited
  签名: [可居 T]
  定义体: { left := default
      right := default
      hom := 𝟙 _ }
-/
instance Under.inhabited [Inhabited T] : Inhabited (Under (default : T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 _ }

namespace Under

variable {X : T}

/--
Definition of `right` / `right` 的定义

English:
abbreviation right
  signature: (f : Under X)
  body: Comma.right f

中文:
缩写 right
  签名: (f : Under X)
  定义体: Comma.right f

Depends on / 依赖: Comma.right
-/
abbrev right (f : Under X) : T := Comma.right f

/--
Definition of `hom` / `hom` 的定义

English:
abbreviation hom
  signature: (f : Under X)
  body: Comma.hom f

中文:
缩写 hom
  签名: (f : Under X)
  定义体: Comma.hom f

Depends on / 依赖: Comma.hom
-/
abbrev hom (f : Under X) : X ⟶ f.right := Comma.hom f

variable {f g : Under X} (φ : f ⟶ g)

/--
Definition of `Hom.right` / `Hom.right` 的定义

English:
abbreviation Hom.right
  signature: : f.right ⟶ g.right
  body: CommaMorphism.right φ

中文:
缩写 态射.right
  签名: : f.right ⟶ g.right
  定义体: CommaMorphism.right φ

Depends on / 依赖: CommaMorphism, CommaMorphism.right
-/
abbrev Hom.right : f.right ⟶ g.right := CommaMorphism.right φ

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
theorem `w` / 定理 `w`

English:
theorem w
  statement: f.hom ≫ φ.right = g.hom
  proof: by
  simpa using (CommaMorphism.w φ).symm

@[reassoc]

中文:
定理 w
  结论: f.hom ≫ φ.right = g.hom
  证明: by
  simpa using (CommaMorphism.w φ).symm

@[reassoc]

Depends on / 依赖: CommaMorphism, CommaMorphism.w
-/
theorem w : f.hom ≫ φ.right = g.hom := by
  simpa using (CommaMorphism.w φ).symm

@[reassoc]
/--
lemma `Hom.w` / 引理 `Hom.w`

English:
lemma Hom.w
  statement: f.hom ≫ φ.right = g.hom
  proof: Under.w φ

@[ext]

中文:
引理 态射.w
  结论: f.hom ≫ φ.right = g.hom
  证明: Under.w φ

@[ext]
-/
lemma Hom.w : f.hom ≫ φ.right = g.hom := Under.w φ

@[ext]
/--
theorem `UnderMorphism.ext` / 定理 `UnderMorphism.ext`

English:
theorem UnderMorphism.ext
  given: {X : T} {U V : Under X} {f g : U ⟶ V} (h : f.right = g.right)
  proof: by
  let ⟨_,b,_⟩ := f; let ⟨_,e,_⟩ := g
  congr; simp only [eq_iff_true_of_subsingleton]

@[simp]

中文:
定理 UnderMorphism.ext
  条件: {X : T} {U V : Under X} {f g : U ⟶ V} (h : f.right = g.right)
  证明: by
  let ⟨_,b,_⟩ := f; let ⟨_,e,_⟩ := g
  congr; simp only [eq_iff_true_of_subsingleton]

@[simp]

Depends on / 依赖: eq_iff_true_of_subsingleton
-/
theorem UnderMorphism.ext {X : T} {U V : Under X} {f g : U ⟶ V} (h : f.right = g.right) :
    f = g := by
  let ⟨_,b,_⟩ := f; let ⟨_,e,_⟩ := g
  congr; simp only [eq_iff_true_of_subsingleton]

@[simp]
/--
theorem `under_left` / 定理 `under_left`

English:
theorem under_left
  given: (U : Under X)
  statement: U.left = ⟨⟨⟩⟩
  proof: by simp only

@[simp]

中文:
定理 under_left
  条件: (U : Under X)
  结论: U.left = ⟨⟨⟩⟩
  证明: by simp only

@[simp]
-/
theorem under_left (U : Under X) : U.left = ⟨⟨⟩⟩ := by simp only

@[simp]
/--
theorem `id_right` / 定理 `id_right`

English:
theorem id_right
  given: (U : Under X)
  statement: Hom.right (𝟙 U) = 𝟙 U.right
  proof: rfl

@[simp]

中文:
定理 id_right
  条件: (U : Under X)
  结论: 态射.right (𝟙 U) = 𝟙 U.right
  证明: rfl

@[simp]
-/
theorem id_right (U : Under X) : Hom.right (𝟙 U) = 𝟙 U.right :=
  rfl

@[simp]
/--
theorem `comp_right` / 定理 `comp_right`

English:
theorem comp_right
  given: (a b c : Under X) (f : a ⟶ b) (g : b ⟶ c)
  statement: (f ≫ g).right = f.right ≫ g.right
  proof: rfl

中文:
定理 comp_right
  条件: (a b c : Under X) (f : a ⟶ b) (g : b ⟶ c)
  结论: (f ≫ g).right = f.right ≫ g.right
  证明: rfl
-/
theorem comp_right (a b c : Under X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).right = f.right ≫ g.right :=
  rfl

/-- To give an object in the under category, it suffices to give an arrow with domain `X`. -/
@[implicit_reducible, simps! right hom]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {X Y : T} (f : X ⟶ Y)
  body: StructuredArrow.mk f

中文:
定义 mk
  签名: {X Y : T} (f : X ⟶ Y)
  定义体: StructuredArrow.mk f

Depends on / 依赖: StructuredArrow, StructuredArrow.mk
-/
def mk {X Y : T} (f : X ⟶ Y) : Under X :=
  StructuredArrow.mk f

/-- To give a morphism in the under category, it suffices to give a morphism fitting in a
    commutative triangle. -/
@[simps! right]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {U V : Under X} (f : U.right ⟶ V.right) (w : U.hom ≫ f = V.hom := by cat_disch)
  body: StructuredArrow.homMk f w

@[simp]

中文:
定义 homMk
  签名: {U V : Under X} (f : U.right ⟶ V.right) (w : U.hom ≫ f = V.hom := by cat_disch)
  定义体: StructuredArrow.homMk f w

@[simp]

Depends on / 依赖: StructuredArrow, StructuredArrow.homMk, cat_disch
-/
def homMk {U V : Under X} (f : U.right ⟶ V.right) (w : U.hom ≫ f = V.hom := by cat_disch) : U ⟶ V :=
  StructuredArrow.homMk f w

@[simp]
/--
lemma `homMk_eta` / 引理 `homMk_eta`

English:
lemma homMk_eta
  given: {U V : Under X} (f : U ⟶ V) (h)
  proof: rfl

中文:
引理 homMk_eta
  条件: {U V : Under X} (f : U ⟶ V) (h)
  证明: rfl

Depends on / 依赖: preservesMonomorphisms_of_preservesLimitsOfShape
-/
lemma homMk_eta {U V : Under X} (f : U ⟶ V) (h) :
    homMk f.right h = f :=
  rfl

/--
lemma `homMk_comp` / 引理 `homMk_comp`

English:
lemma homMk_comp
  given: {U V W : Under X} (f : U.right ⟶ V.right) (g : V.right ⟶ W.right) (w_f w_g)
  proof: rfl

中文:
引理 homMk_comp
  条件: {U V W : Under X} (f : U.right ⟶ V.right) (g : V.right ⟶ W.right) (w_f w_g)
  证明: rfl
-/
lemma homMk_comp {U V W : Under X} (f : U.right ⟶ V.right) (g : V.right ⟶ W.right) (w_f w_g) :
    homMk (f ≫ g) (by simp only [reassoc_of% w_f, w_g]) = homMk f w_f ≫ homMk g w_g :=
  rfl

/-- Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
@[simps! hom_right inv_right]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {f g : Under X} (hr : f.right ≅ g.right)
  body: StructuredArrow.isoMk hr hw

@[simp]

中文:
定义 isoMk
  签名: {f g : Under X} (hr : f.right ≅ g.right)
  定义体: StructuredArrow.isoMk hr hw

@[simp]

Depends on / 依赖: StructuredArrow, StructuredArrow.isoMk, cat_disch, reflectsMonomorphisms_of_reflectsLimitsOfShape
-/
def isoMk {f g : Under X} (hr : f.right ≅ g.right)
    (hw : f.hom ≫ hr.hom = g.hom := by cat_disch) : f ≅ g :=
  StructuredArrow.isoMk hr hw

@[simp]
/--
lemma `eqToHom_right` / 引理 `eqToHom_right`

English:
lemma eqToHom_right
  given: {f g : Under X} (h : f = g)
  proof: by
  subst h
  rfl

@[reassoc (attr := simp)]

中文:
引理 eqToHom_right
  条件: {f g : Under X} (h : f = g)
  证明: by
  subst h
  rfl

@[reassoc (attr := simp)]
-/
lemma eqToHom_right {f g : Under X} (h : f = g) :
    (eqToHom h).right = eqToHom (by rw [h]) := by
  subst h
  rfl

@[reassoc (attr := simp)]
/--
lemma `hom_right_inv_right` / 引理 `hom_right_inv_right`

English:
lemma hom_right_inv_right
  given: {f g : Under X} (e : f ≅ g)
  proof: by
  simp [← Under.comp_right]

@[reassoc (attr := simp)]

中文:
引理 hom_right_inv_right
  条件: {f g : Under X} (e : f ≅ g)
  证明: by
  simp [← Under.comp_right]

@[reassoc (attr := simp)]

Depends on / 依赖: Under.comp_right, comp_right, preservesEpimorphisms_of_preservesColimitsOfShape
-/
lemma hom_right_inv_right {f g : Under X} (e : f ≅ g) :
    e.hom.right ≫ e.inv.right = 𝟙 f.right := by
  simp [← Under.comp_right]

@[reassoc (attr := simp)]
/--
lemma `inv_right_hom_right` / 引理 `inv_right_hom_right`

English:
lemma inv_right_hom_right
  given: {f g : Under X} (e : f ≅ g)
  proof: by
  simp [← Under.comp_right]

中文:
引理 inv_right_hom_right
  条件: {f g : Under X} (e : f ≅ g)
  证明: by
  simp [← Under.comp_right]

Depends on / 依赖: Under.comp_right, comp_right
-/
lemma inv_right_hom_right {f g : Under X} (e : f ≅ g) :
    e.inv.right ≫ e.hom.right = 𝟙 g.right := by
  simp [← Under.comp_right]

/--
lemma `forall_iff` / 引理 `forall_iff`

English:
lemma forall_iff
  given: (P : Under X -> Prop)
  proof: by
  aesop

中文:
引理 对任意_iff
  条件: (P : Under X -> 命题)
  证明: by
  aesop

Depends on / 依赖: reflectsEpimorphisms_of_reflectsColimitsOfShape
-/
lemma forall_iff (P : Under X -> Prop) :
    (forall Y, P Y) ↔ (forall (Y) (f : X ⟶ Y), P (.mk f)) := by
  aesop

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  given: {S : T} (X : Under S)
  proof: ⟨_, X.hom, rfl⟩

中文:
引理 mk_surjective
  条件: {S : T} (X : Under S)
  证明: ⟨_, X.hom, rfl⟩

Depends on / 依赖: X.hom
-/
lemma mk_surjective {S : T} (X : Under S) :
    exists (Y : T) (f : S ⟶ Y), Under.mk f = X :=
  ⟨_, X.hom, rfl⟩

/--
lemma `homMk_surjective` / 引理 `homMk_surjective`

English:
lemma homMk_surjective
  proof: ⟨f.right, by simp⟩

中文:
引理 homMk_surjective
  证明: ⟨f.right, by simp⟩

Depends on / 依赖: f.right
-/
lemma homMk_surjective
    {S : T} {X Y : Under S} (f : X ⟶ Y) :
    exists (g : X.right ⟶ Y.right) (hg : X.hom ≫ g = Y.hom), Under.homMk g = f :=
  ⟨f.right, by simp⟩

section

variable (X)

/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Under X ⥤ T
  body: Comma.snd _ _

中文:
定义 forget
  签名: : Under X ⥤ T
  定义体: Comma.snd _ _

Depends on / 依赖: Comma.snd
-/
def forget : Under X ⥤ T :=
  Comma.snd _ _

end

@[simp]
/--
theorem `forget_obj` / 定理 `forget_obj`

English:
theorem forget_obj
  given: {U : Under X}
  statement: (forget X).obj U = U.right
  proof: rfl

@[simp]

中文:
定理 forget_obj
  条件: {U : Under X}
  结论: (forget X).obj U = U.right
  证明: rfl

@[simp]
-/
theorem forget_obj {U : Under X} : (forget X).obj U = U.right :=
  rfl

@[simp]
/--
theorem `forget_map` / 定理 `forget_map`

English:
theorem forget_map
  given: {U V : Under X} {f : U ⟶ V}
  statement: (forget X).map f = f.right
  proof: rfl

中文:
定理 forget_map
  条件: {U V : Under X} {f : U ⟶ V}
  结论: (forget X).map f = f.right
  证明: rfl
-/
theorem forget_map {U V : Under X} {f : U ⟶ V} : (forget X).map f = f.right :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- The natural cone over the forgetful functor `Under X ⥤ T` with cone point `X`. -/
@[simps]
/--
Definition of `forgetCone` / `forgetCone` 的定义

English:
definition forgetCone
  signature: (X : T)
  body: { pt := X
    π := { app := Comma.hom } }

中文:
定义 forgetCone
  签名: (X : T)
  定义体: { pt := X
    π := { app := Comma.hom } }

Depends on / 依赖: Comma.hom
-/
def forgetCone (X : T) : Limits.Cone (forget X) :=
  { pt := X
    π := { app := Comma.hom } }

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {Y : T} (f : X ⟶ Y)
  body: Comma.mapLeft _ Discrete.natTrans fun _ => f

中文:
定义 map
  签名: {Y : T} (f : X ⟶ Y)
  定义体: Comma.mapLeft _ Discrete.natTrans fun _ => f

Depends on / 依赖: Comma.mapLeft, Discrete, Discrete.natTrans, mapLeft, natTrans
-/
def map {Y : T} (f : X ⟶ Y) : Under Y ⥤ Under X :=
Comma.mapLeft _ Discrete.natTrans fun _ => f

section

variable {Y : T} {f : X ⟶ Y} {U V : Under Y} {g : U ⟶ V}

@[simp]
/--
theorem `map_obj_right` / 定理 `map_obj_right`

English:
theorem map_obj_right
  statement: ((map f).obj U).right = U.right
  proof: rfl

@[simp]

中文:
定理 map_obj_right
  结论: ((map f).obj U).right = U.right
  证明: rfl

@[simp]
-/
theorem map_obj_right : ((map f).obj U).right = U.right :=
  rfl

@[simp]
/--
theorem `map_obj_hom` / 定理 `map_obj_hom`

English:
theorem map_obj_hom
  statement: ((map f).obj U).hom = f ≫ U.hom
  proof: rfl

@[simp]

中文:
定理 map_obj_hom
  结论: ((map f).obj U).hom = f ≫ U.hom
  证明: rfl

@[simp]
-/
theorem map_obj_hom : ((map f).obj U).hom = f ≫ U.hom :=
  rfl

@[simp]
/--
theorem `map_map_right` / 定理 `map_map_right`

English:
theorem map_map_right
  statement: ((map f).map g).right = g.right
  proof: rfl

中文:
定理 map_map_right
  结论: ((map f).map g).right = g.right
  证明: rfl
-/
theorem map_map_right : ((map f).map g).right = g.right :=
  rfl

/--
Definition of `mapIso` / `mapIso` 的定义

English:
definition mapIso
  signature: (f : X ≅ Y)
  body: Comma.mapLeftIso _ Discrete.natIso fun _ => f.symm

中文:
定义 mapIso
  签名: (f : X ≅ Y)
  定义体: Comma.mapLeftIso _ Discrete.natIso fun _ => f.symm

Depends on / 依赖: Comma.mapLeftIso, Discrete, Discrete.natIso, f.symm, mapLeftIso, natIso
-/
def mapIso (f : X ≅ Y) : Under Y ≌ Under X :=
Comma.mapLeftIso _ Discrete.natIso fun _ => f.symm

/--
lemma `mapIso_functor` / 引理 `mapIso_functor`

English:
lemma mapIso_functor
  given: (f : X ≅ Y)
  statement: (mapIso f).functor = map f.hom
  proof: rfl

中文:
引理 mapIso_functor
  条件: (f : X ≅ Y)
  结论: (mapIso f).functor = map f.hom
  证明: rfl
-/
@[simp] lemma mapIso_functor (f : X ≅ Y) : (mapIso f).functor = map f.hom := rfl
/--
lemma `mapIso_inverse` / 引理 `mapIso_inverse`

English:
lemma mapIso_inverse
  given: (f : X ≅ Y)
  statement: (mapIso f).inverse = map f.inv
  proof: rfl

中文:
引理 mapIso_inverse
  条件: (f : X ≅ Y)
  结论: (mapIso f).inverse = map f.inv
  证明: rfl
-/
@[simp] lemma mapIso_inverse (f : X ≅ Y) : (mapIso f).inverse = map f.inv := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIso
  signature: f] : (Under.map f).IsEquivalence
  body: (Under.mapIso <| asIso f).isEquivalence_functor

中文:
实例 [是同构
  签名: f] : (Under.map f).是等价
  定义体: (Under.mapIso <| asIso f).isEquivalence_functor

Depends on / 依赖: Under.mapIso, isEquivalence_functor, mapIso
-/
instance [IsIso f] : (Under.map f).IsEquivalence := (Under.mapIso <| asIso f).isEquivalence_functor

end

section coherences
/-!
This section proves various equalities between functors that
demonstrate, for instance, that under categories assemble into a
functor `mapFunctor : Tᵒᵖ ⥤ Cat`.
-/

set_option backward.isDefEq.respectTransparency.types false in
/-- Mapping by the identity morphism is just the identity functor. -/
@[simps!]
/--
Definition of `mapId` / `mapId` 的定义

English:
definition mapId
  signature: (Y : T)
  body: NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

中文:
定义 mapId
  签名: (Y : T)
  定义体: NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def mapId (Y : T) : map (𝟙 Y) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `mapId_eq` / 定理 `mapId_eq`

English:
theorem mapId_eq
  given: (Y : T)
  statement: map (𝟙 Y) = 𝟭 _
  proof: Functor.ext_of_iso (mapId Y) (fun _ => by simp [map, Comma.mapLeft]; rfl)
    (fun _ => by ext; simp [eqToHom_right])

中文:
定理 mapId_eq
  条件: (Y : T)
  结论: map (𝟙 Y) = 𝟭 _
  证明: Functor.ext_of_iso (mapId Y) (fun _ => by simp [map, Comma.mapLeft]; rfl)
    (fun _ => by ext; simp [eqToHom_right])

Depends on / 依赖: Comma.mapLeft, Functor, Functor.ext_of_iso, eqToHom_right, ext_of_iso, mapLeft
-/
theorem mapId_eq (Y : T) : map (𝟙 Y) = 𝟭 _ :=
  Functor.ext_of_iso (mapId Y) (fun _ => by simp [map, Comma.mapLeft]; rfl)
    (fun _ => by ext; simp [eqToHom_right])

/--
theorem `mapForget_eq` / 定理 `mapForget_eq`

English:
theorem mapForget_eq
  given: {X Y : T} (f : X ⟶ Y)
  proof: rfl

中文:
定理 mapForget_eq
  条件: {X Y : T} (f : X ⟶ Y)
  证明: rfl
-/
theorem mapForget_eq {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget X) = (forget Y) := rfl

/--
Definition of `mapForget` / `mapForget` 的定义

English:
definition mapForget
  signature: {X Y : T} (f : X ⟶ Y)
  body: eqToIso (mapForget_eq f)

中文:
定义 mapForget
  签名: {X Y : T} (f : X ⟶ Y)
  定义体: eqToIso (mapForget_eq f)

Depends on / 依赖: eqToIso, mapForget_eq
-/
def mapForget {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget X) ≅ (forget Y) := eqToIso (mapForget_eq f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `mapComp_eq` / 定理 `mapComp_eq`

English:
theorem mapComp_eq
  given: {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  fapply Functor.ext
  · simp [Under.map, Comma.mapLeft]
  · intro U V k
    ext
    simp

中文:
定理 mapComp_eq
  条件: {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  fapply Functor.ext
  · simp [Under.map, Comma.mapLeft]
  · intro U V k
    ext
    simp

Depends on / 依赖: Comma.mapLeft, Functor, Functor.ext, Under.map, fapply, mapLeft
-/
theorem mapComp_eq {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = (map g) ⋙ (map f) := by
  fapply Functor.ext
  · simp [Under.map, Comma.mapLeft]
  · intro U V k
    ext
    simp

/-- The natural isomorphism arising from `mapComp_eq`. -/
@[simps!]
/--
Definition of `mapComp` / `mapComp` 的定义

English:
definition mapComp
  signature: {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
  body: eqToIso (mapComp_eq f g)

中文:
定义 mapComp
  签名: {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
  定义体: eqToIso (mapComp_eq f g)

Depends on / 依赖: eqToIso, mapComp_eq
-/
def mapComp {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
  eqToIso (mapComp_eq f g)

/-- If `f = g`, then `map f` is naturally isomorphic to `map g`. -/
@[simps!]
/--
Definition of `mapCongr` / `mapCongr` 的定义

English:
definition mapCongr
  signature: {X Y : T} (f g : X ⟶ Y) (h : f = g)
  body: NatIso.ofComponents (fun A => eqToIso (by rw [h]))

中文:
定义 mapCongr
  签名: {X Y : T} (f g : X ⟶ Y) (h : f = g)
  定义体: NatIso.ofComponents (fun A => eqToIso (by rw [h]))

Depends on / 依赖: NatIso, NatIso.ofComponents, eqToIso, ofComponents
-/
def mapCongr {X Y : T} (f g : X ⟶ Y) (h : f = g) :
    map f ≅ map g :=
  NatIso.ofComponents (fun A => eqToIso (by rw [h]))

variable (T) in
/--
Definition of `mapFunctor` / `mapFunctor` 的定义

English:
definition mapFunctor
  signature: : Tᵒᵖ ⥤ Cat where
  body: Cat.of (Under X.unop)
  map f := (map f.unop).toCatHom
  map_id X := congr($(mapId_eq X.unop).toCatHom)
  map_comp f g := congr($(mapComp_eq (g.unop) (f.unop)).toCatHom)

中文:
定义 mapFunctor
  签名: : Tᵒᵖ ⥤ Cat where
  定义体: Cat.of (Under X.unop)
  map f := (map f.unop).toCatHom
  map_id X := congr($(mapId_eq X.unop).toCatHom)
  map_comp f g := congr($(mapComp_eq (g.unop) (f.unop)).toCatHom)
-/
@[simps] def mapFunctor : Tᵒᵖ ⥤ Cat where
  obj X := Cat.of (Under X.unop)
  map f := (map f.unop).toCatHom
  map_id X := congr($(mapId_eq X.unop).toCatHom)
  map_comp f g := congr($(mapComp_eq (g.unop) (f.unop)).toCatHom)

end coherences

/--
Instance `forget_reflects_iso` / 实例 `forget_reflects_iso`

English:
instance forget_reflects_iso
  signature: : (forget X).ReflectsIsomorphisms where
  body: ⟨Under.homMk (inv ((forget X).map f) :), by cat_disch⟩

中文:
实例 forget_reflects_iso
  签名: : (forget X).反映同构 where
  定义体: ⟨Under.homMk (inv ((forget X).map f) :), by cat_disch⟩

Depends on / 依赖: Under.homMk, cat_disch, forget
-/
instance forget_reflects_iso : (forget X).ReflectsIsomorphisms where
  reflects {Y Z} f t := ⟨Under.homMk (inv ((forget X).map f) :), by cat_disch⟩

/--
Definition of `mkIdInitial` / `mkIdInitial` 的定义

English:
definition mkIdInitial
  signature: : Limits.IsInitial (mk (𝟙 X))
  body: StructuredArrow.mkIdInitial

中文:
定义 mkIdInitial
  签名: : Limits.IsInitial (mk (𝟙 X))
  定义体: StructuredArrow.mkIdInitial

Depends on / 依赖: StructuredArrow, StructuredArrow.mkIdInitial, mkIdInitial
-/
noncomputable def mkIdInitial : Limits.IsInitial (mk (𝟙 X)) :=
  StructuredArrow.mkIdInitial

set_option backward.defeqAttrib.useBackward true in
-- We could make this defeq if we care.
/--
lemma `mkIdInitial_to_right` / 引理 `mkIdInitial_to_right`

English:
lemma mkIdInitial_to_right
  given: (Y : Under X)
  statement: (mkIdInitial.to Y).right = Y.hom
  proof: by
  rw [mkIdInitial.hom_ext (mkIdInitial.to Y) (homMk Y.hom)]
  rfl

中文:
引理 mkIdInitial_to_right
  条件: (Y : Under X)
  结论: (mkIdInitial.to Y).right = Y.hom
  证明: by
  rw [mkIdInitial.hom_ext (mkIdInitial.to Y) (homMk Y.hom)]
  rfl
-/
@[simp] lemma mkIdInitial_to_right (Y : Under X) : (mkIdInitial.to Y).right = Y.hom := by
  rw [mkIdInitial.hom_ext (mkIdInitial.to Y) (homMk Y.hom)]
  rfl

/--
Instance `forget_faithful` / 实例 `forget_faithful`

English:
instance forget_faithful
  signature: : (forget X).Faithful where

中文:
实例 forget_faithful
  签名: : (forget X).忠实 where
-/
instance forget_faithful : (forget X).Faithful where

-- TODO: Show the converse holds if `T` has binary coproducts.
/--
theorem `mono_of_mono_right` / 定理 `mono_of_mono_right`

English:
theorem mono_of_mono_right
  given: {f g : Under X} (k : f ⟶ g) [hk : Mono k.right]
  statement: Mono k
  proof: (forget X).mono_of_mono_map hk

中文:
定理 mono_of_mono_right
  条件: {f g : Under X} (k : f ⟶ g) [hk : 单态射 k.right]
  结论: 单态射 k
  证明: (forget X).mono_of_mono_map hk

Depends on / 依赖: forget, mono_of_mono_map
-/
theorem mono_of_mono_right {f g : Under X} (k : f ⟶ g) [hk : Mono k.right] : Mono k :=
  (forget X).mono_of_mono_map hk

/--
Instance `mono_homMk` / 实例 `mono_homMk`

English:
instance mono_homMk
  signature: {U V : Under X} {f : U.right ⟶ V.right} [Mono f] (w)
  body: (forget X).mono_of_mono_map ‹_›

中文:
实例 mono_homMk
  签名: {U V : Under X} {f : U.right ⟶ V.right} [单态射 f] (w)
  定义体: (forget X).mono_of_mono_map ‹_›

Depends on / 依赖: forget, mono_of_mono_map
-/
instance mono_homMk {U V : Under X} {f : U.right ⟶ V.right} [Mono f] (w) : Mono (homMk f w) :=
  (forget X).mono_of_mono_map ‹_›

/--
theorem `epi_of_epi_right` / 定理 `epi_of_epi_right`

English:
theorem epi_of_epi_right
  given: {f g : Under X} (k : f ⟶ g) [hk : Epi k.right]
  statement: Epi k
  proof: (forget X).epi_of_epi_map hk

中文:
定理 epi_of_epi_right
  条件: {f g : Under X} (k : f ⟶ g) [hk : 满态射 k.right]
  结论: 满态射 k
  证明: (forget X).epi_of_epi_map hk

Depends on / 依赖: epi_of_epi_map, forget
-/
theorem epi_of_epi_right {f g : Under X} (k : f ⟶ g) [hk : Epi k.right] : Epi k :=
  (forget X).epi_of_epi_map hk

/--
Instance `epi_homMk` / 实例 `epi_homMk`

English:
instance epi_homMk
  signature: {U V : Under X} {f : U.right ⟶ V.right} [Epi f] (w)
  body: (forget X).epi_of_epi_map ‹_›

中文:
实例 epi_homMk
  签名: {U V : Under X} {f : U.right ⟶ V.right} [满态射 f] (w)
  定义体: (forget X).epi_of_epi_map ‹_›

Depends on / 依赖: epi_of_epi_map, forget
-/
instance epi_homMk {U V : Under X} {f : U.right ⟶ V.right} [Epi f] (w) : Epi (homMk f w) :=
  (forget X).epi_of_epi_map ‹_›

set_option backward.defeqAttrib.useBackward true in
/--
Instance `epi_right_of_epi` / 实例 `epi_right_of_epi`

English:
instance epi_right_of_epi
  signature: {f g : Under X} (k : f ⟶ g) [Epi k]
  body: by
  refine ⟨fun {Y : T} l m a => ?_⟩
  let l' : g ⟶ mk (g.hom ≫ m) := homMk l (by
    dsimp; rw [← Under.w k, Category.assoc, a, Category.assoc])
  suffices l' = (homMk m) by apply congrArg CommaMorphism.right this
  rw [← cancel_epi k]; ext; apply a

中文:
实例 epi_right_of_epi
  签名: {f g : Under X} (k : f ⟶ g) [满态射 k]
  定义体: by
  refine ⟨fun {Y : T} l m a => ?_⟩
  let l' : g ⟶ mk (g.hom ≫ m) := homMk l (by
    dsimp; rw [← Under.w k, Category.assoc, a, Category.assoc])
  suffices l' = (homMk m) by apply congrArg CommaMorphism.right this
  rw [← cancel_epi k]; ext; apply a

Depends on / 依赖: Category, Category.assoc, CommaMorphism, CommaMorphism.right, Under.w, cancel_epi, g.hom
-/
instance epi_right_of_epi {f g : Under X} (k : f ⟶ g) [Epi k] : Epi k.right := by
  refine ⟨fun {Y : T} l m a => ?_⟩
  let l' : g ⟶ mk (g.hom ≫ m) := homMk l (by
    dsimp; rw [← Under.w k, Category.assoc, a, Category.assoc])
  suffices l' = (homMk m) by apply congrArg CommaMorphism.right this
  rw [← cancel_epi k]; ext; apply a

set_option backward.defeqAttrib.useBackward true in
/-- A functor `F : T ⥤ D` induces a functor `Under X ⥤ Under (F.obj X)` in the obvious way. -/
@[simps]
/--
Definition of `post` / `post` 的定义

English:
definition post
  signature: {X : T} (F : T ⥤ D)
  body: mk F.map Y.hom
  map f := Under.homMk (F.map f.right) (by simp [← F.map_comp])

中文:
定义 post
  签名: {X : T} (F : T ⥤ D)
  定义体: mk F.map Y.hom
  map f := Under.homMk (F.map f.right) (by simp [← F.map_comp])

Depends on / 依赖: F.map, Y.hom
-/
def post {X : T} (F : T ⥤ D) : Under X ⥤ Under (F.obj X) where
obj Y := mk F.map Y.hom
  map f := Under.homMk (F.map f.right) (by simp [← F.map_comp])

/--
lemma `post_comp` / 引理 `post_comp`

English:
lemma post_comp
  given: {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E)
  proof: rfl

中文:
引理 post_comp
  条件: {E : 类型} [范畴* E] (F : T ⥤ D) (G : D ⥤ E)
  证明: rfl
-/
lemma post_comp {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) = post (X := X) F ⋙ post G :=
  rfl

/--
lemma `post_forget_eq_forget_comp` / 引理 `post_forget_eq_forget_comp`

English:
lemma post_forget_eq_forget_comp
  given: (F : T ⥤ D) (X : T)
  proof: rfl

中文:
引理 post_forget_eq_forget_comp
  条件: (F : T ⥤ D) (X : T)
  证明: rfl
-/
lemma post_forget_eq_forget_comp (F : T ⥤ D) (X : T) :
    post F ⋙ forget (F.obj X) = forget X ⋙ F :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `post (F ⋙ G)` is isomorphic (actually equal) to `post F ⋙ post G`. -/
@[simps!]
/--
Definition of `postComp` / `postComp` 的定义

English:
definition postComp
  signature: {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E)
  body: NatIso.ofComponents (fun X => Iso.refl _) (fun f => by
    ext
    dsimp only [Iso.refl_hom, Under.comp_right, Under.id_right]
    simp)

中文:
定义 postComp
  签名: {E : 类型} [范畴* E] (F : T ⥤ D) (G : D ⥤ E)
  定义体: NatIso.ofComponents (fun X => Iso.refl _) (fun f => by
    ext
    dsimp only [Iso.refl_hom, Under.comp_right, Under.id_right]
    simp)
-/
def postComp {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) ≅ post F ⋙ post G :=
  NatIso.ofComponents (fun X => Iso.refl _) (fun f => by
    ext
    dsimp only [Iso.refl_hom, Under.comp_right, Under.id_right]
    simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural transformation `F ⟶ G` induces a natural transformation on
`Under X` up to `Under.map`. -/
@[simps]
/--
Definition of `postMap` / `postMap` 的定义

English:
definition postMap
  signature: {F G : T ⥤ D} (e : F ⟶ G)
  body: Under.homMk (e.app Y.right)

中文:
定义 postMap
  签名: {F G : T ⥤ D} (e : F ⟶ G)
  定义体: Under.homMk (e.app Y.right)

Depends on / 依赖: e.app
-/
def postMap {F G : T ⥤ D} (e : F ⟶ G) : post (X := X) F ⟶ post G ⋙ map (e.app X) where
  app Y := Under.homMk (e.app Y.right)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F` and `G` are naturally isomorphic, then `Under.post F` and `Under.post G` are also
naturally isomorphic up to `Under.map` -/
@[simps!]
/--
Definition of `postCongr` / `postCongr` 的定义

English:
definition postCongr
  signature: {F G : T ⥤ D} (e : F ≅ G)
  body: NatIso.ofComponents (fun A => Under.isoMk (e.app A.right))

中文:
定义 postCongr
  签名: {F G : T ⥤ D} (e : F ≅ G)
  定义体: NatIso.ofComponents (fun A => Under.isoMk (e.app A.right))

Depends on / 依赖: A.right, NatIso, NatIso.ofComponents, Under.isoMk, e.app, ofComponents
-/
def postCongr {F G : T ⥤ D} (e : F ≅ G) : post F ≅ post G ⋙ map (e.hom.app X) :=
  NatIso.ofComponents (fun A => Under.isoMk (e.app A.right))

variable (X) (F : T ⥤ D)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Faithful]
  signature: : (Under.post (X := X) F).Faithful where
  body: by
    ext
    exact F.map_injective (congrArg CommaMorphism.right h)

中文:
实例 [F.忠实]
  签名: : (Under.post (X := X) F).忠实 where
  定义体: by
    ext
    exact F.map_injective (congrArg CommaMorphism.right h)

Depends on / 依赖: Faithful
-/
instance [F.Faithful] : (Under.post (X := X) F).Faithful where
  map_injective {A B} f g h := by
    ext
    exact F.map_injective (congrArg CommaMorphism.right h)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Faithful]
  signature: [F.Full]
  body: by
    obtain ⟨a, ha⟩ := F.map_surjective f.right
    exact ⟨Under.homMk a (F.map_injective (by simp [ha, dsimp% f.w])), by ext; simpa⟩

中文:
实例 [F.忠实]
  签名: [F.满]
  定义体: by
    obtain ⟨a, ha⟩ := F.map_surjective f.right
    exact ⟨Under.homMk a (F.map_injective (by simp [ha, dsimp% f.w])), by ext; simpa⟩
-/
instance [F.Faithful] [F.Full] : (Under.post (X := X) F).Full where
  map_surjective {A B} f := by
    obtain ⟨a, ha⟩ := F.map_surjective f.right
    exact ⟨Under.homMk a (F.map_injective (by simp [ha, dsimp% f.w])), by ext; simpa⟩

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Full]
  signature: [F.EssSurj]
  body: by
    obtain ⟨B', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) B.right
    obtain ⟨f, hf⟩ := F.map_surjective (B.hom ≫ e.inv)
    exact ⟨Under.mk f, ⟨Under.isoMk e⟩⟩

中文:
实例 [F.满]
  签名: [F.本质满射]
  定义体: by
    obtain ⟨B', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) B.right
    obtain ⟨f, hf⟩ := F.map_surjective (B.hom ≫ e.inv)
    exact ⟨Under.mk f, ⟨Under.isoMk e⟩⟩

Depends on / 依赖: EssSurj
-/
instance [F.Full] [F.EssSurj] : (Under.post (X := X) F).EssSurj where
  mem_essImage B := by
    obtain ⟨B', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) B.right
    obtain ⟨f, hf⟩ := F.map_surjective (B.hom ≫ e.inv)
    exact ⟨Under.mk f, ⟨Under.isoMk e⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.IsEquivalence]
  signature: : (Under.post (X := X) F).IsEquivalence where

中文:
实例 [F.是等价]
  签名: : (Under.post (X := X) F).是等价 where

Depends on / 依赖: IsEquivalence
-/
instance [F.IsEquivalence] : (Under.post (X := X) F).IsEquivalence where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `_root_.CategoryTheory.Functor.FullyFaithful.under` / `_root_.CategoryTheory.Functor.FullyFaithful.under` 的定义

English:
definition _root_.CategoryTheory.Functor.FullyFaithful.under
  signature: (h : F.FullyFaithful)
  body: Under.homMk (h.preimage f.right) h.map_injective (by simpa using Under.w f)

中文:
定义 _root_.范畴论.函子.满忠实.under
  签名: (h : F.满忠实)
  定义体: Under.homMk (h.preimage f.right) h.map_injective (by simpa using Under.w f)

Depends on / 依赖: FullyFaithful
-/
def _root_.CategoryTheory.Functor.FullyFaithful.under (h : F.FullyFaithful) :
    (post (X := X) F).FullyFaithful where
preimage {A B} f := Under.homMk (h.preimage f.right) h.map_injective (by simpa using Under.w f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F` is a left adjoint, then so is `post F : Under X ⥤ Under (F X)`.

If the right adjoint of `F` is `G`, then the right adjoint of `post F` is given by
`(F X ⟶ Y) ↦ (X ⟶ G F X ⟶ G Y)`. -/
@[simps]
/--
Definition of `postAdjunctionLeft` / `postAdjunctionLeft` 的定义

English:
definition postAdjunctionLeft
  signature: {X : T} {F : T ⥤ D} {G : D ⥤ T} (a : F ⊣ G)
  body: homMk a.unit.app A.right
counit.app A := homMk a.counit.app A.right
  unit.naturality _ _ f := by
    ext
    exact (a.unit_naturality f.right).symm
  counit.naturality _ _ f := by
    ext
    exact (a.counit_naturality f.right)
  left_triangle_components A := by
    ext
    simp [-Functor.id_obj]
 

中文:
定义 postAdjunctionLeft
  签名: {X : T} {F : T ⥤ D} {G : D ⥤ T} (a : F ⊣ G)
  定义体: homMk a.unit.app A.right
counit.app A := homMk a.counit.app A.right
  unit.naturality _ _ f := by
    ext
    exact (a.unit_naturality f.right).symm
  counit.naturality _ _ f := by
    ext
    exact (a.counit_naturality f.right)
  left_triangle_components A := by
    ext
    simp [-Functor.id_obj]
 

Depends on / 依赖: A.right, a.unit.app
-/
def postAdjunctionLeft {X : T} {F : T ⥤ D} {G : D ⥤ T} (a : F ⊣ G) :
    post F ⊣ post G ⋙ map (a.unit.app X) where
unit.app A := homMk a.unit.app A.right
counit.app A := homMk a.counit.app A.right
  unit.naturality _ _ f := by
    ext
    exact (a.unit_naturality f.right).symm
  counit.naturality _ _ f := by
    ext
    exact (a.counit_naturality f.right)
  left_triangle_components A := by
    ext
    simp [-Functor.id_obj]
  right_triangle_components A := by
    ext
    simp [-Functor.id_obj]

/--
Instance `isLeftAdjoint_post` / 实例 `isLeftAdjoint_post`

English:
instance isLeftAdjoint_post
  signature: [F.IsLeftAdjoint]
  body: let ⟨G, ⟨a⟩⟩ := ‹F.IsLeftAdjoint›; ⟨_, ⟨postAdjunctionLeft a⟩⟩

中文:
实例 isLeftAdjoint_post
  签名: [F.是左伴随]
  定义体: let ⟨G, ⟨a⟩⟩ := ‹F.IsLeftAdjoint›; ⟨_, ⟨postAdjunctionLeft a⟩⟩

Depends on / 依赖: IsLeftAdjoint
-/
instance isLeftAdjoint_post [F.IsLeftAdjoint] : (post (X := X) F).IsLeftAdjoint :=
  let ⟨G, ⟨a⟩⟩ := ‹F.IsLeftAdjoint›; ⟨_, ⟨postAdjunctionLeft a⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories induces an equivalence on under categories. -/
@[simps]
/--
Definition of `postEquiv` / `postEquiv` 的定义

English:
definition postEquiv
  signature: (F : T ≌ D)
  body: post F.functor
  inverse := post (X := F.functor.obj X) F.inverse ⋙ Under.map (F.unitIso.hom.app X)
  unitIso := NatIso.ofComponents (fun A => Under.isoMk (F.unitIso.app A.right))
  counitIso := NatIso.ofComponents (fun A => Under.isoMk (F.counitIso.app A.right))

中文:
定义 postEquiv
  签名: (F : T ≌ D)
  定义体: post F.functor
  inverse := post (X := F.functor.obj X) F.inverse ⋙ Under.map (F.unitIso.hom.app X)
  unitIso := NatIso.ofComponents (fun A => Under.isoMk (F.unitIso.app A.right))
  counitIso := NatIso.ofComponents (fun A => Under.isoMk (F.counitIso.app A.right))

Depends on / 依赖: F.functor, functor
-/
def postEquiv (F : T ≌ D) : Under X ≌ Under (F.functor.obj X) where
  functor := post F.functor
  inverse := post (X := F.functor.obj X) F.inverse ⋙ Under.map (F.unitIso.hom.app X)
  unitIso := NatIso.ofComponents (fun A => Under.isoMk (F.unitIso.app A.right))
  counitIso := NatIso.ofComponents (fun A => Under.isoMk (F.counitIso.app A.right))

open Limits

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {X} in
/-- If `X : T` is initial, then the under category of `X` is equivalent to `T`. -/
@[simps]
/--
Definition of `equivalenceOfIsInitial` / `equivalenceOfIsInitial` 的定义

English:
definition equivalenceOfIsInitial
  signature: (hX : IsInitial X)
  body: forget X
  inverse := { obj Y := mk (hX.to Y), map f := homMk f }
  unitIso := NatIso.ofComponents fun Y => isoMk (.refl _) (hX.hom_ext _ _)
  counitIso := NatIso.ofComponents fun _ => .refl _

中文:
定义 equivalenceOfIsInitial
  签名: (hX : IsInitial X)
  定义体: forget X
  inverse := { obj Y := mk (hX.to Y), map f := homMk f }
  unitIso := NatIso.ofComponents fun Y => isoMk (.refl _) (hX.hom_ext _ _)
  counitIso := NatIso.ofComponents fun _ => .refl _

Depends on / 依赖: forget
-/
def equivalenceOfIsInitial (hX : IsInitial X) : Under X ≌ T where
  functor := forget X
  inverse := { obj Y := mk (hX.to Y), map f := homMk f }
  unitIso := NatIso.ofComponents fun Y => isoMk (.refl _) (hX.hom_ext _ _)
  counitIso := NatIso.ofComponents fun _ => .refl _

set_option backward.defeqAttrib.useBackward true in
/-- The induced functor to `Under X` from a functor `J ⥤ C` and natural maps `sᵢ : X ⟶ Dᵢ`. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : (Functor.const J).obj X ⟶ D)
  body: .mk (s.app j)
  map f := Under.homMk (D.map f) (by simpa using (s.naturality f).symm)

中文:
定义 lift
  签名: {J : 类型} [范畴* J] (D : J ⥤ T) {X : T} (s : (函子.const J).obj X ⟶ D)
  定义体: .mk (s.app j)
  map f := Under.homMk (D.map f) (by simpa using (s.naturality f).symm)
-/
protected def lift {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : (Functor.const J).obj X ⟶ D) :
    J ⥤ Under X where
  obj j := .mk (s.app j)
  map f := Under.homMk (D.map f) (by simpa using (s.naturality f).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The induced cocone on `Under X` from on the lifted functor. -/
@[simps]
/--
Definition of `liftCocone` / `liftCocone` 的定义

English:
definition liftCocone
  signature: {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : (Functor.const J).obj X ⟶ D)
  body: mk p
  ι.app j := homMk (c.ι.app j)

中文:
定义 liftCocone
  签名: {J : 类型} [范畴* J] (D : J ⥤ T) {X : T} (s : (函子.const J).obj X ⟶ D)
  定义体: mk p
  ι.app j := homMk (c.ι.app j)
-/
def liftCocone {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : (Functor.const J).obj X ⟶ D)
    (c : Cocone D) (p : X ⟶ c.pt) (hp : forall j, s.app j ≫ c.ι.app j = p) :
    Cocone (Under.lift D s) where
  pt := mk p
  ι.app j := homMk (c.ι.app j)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitLiftCocone` / `isColimitLiftCocone` 的定义

English:
definition isColimitLiftCocone
  signature: {J : Type*} [Category* J] [Nonempty J]
  body: Under.homMk (hc.desc ((Under.forget _).mapCocone t)) (by
    let j : J := Classical.arbitrary _
    simp [← dsimp% (t.ι.app j).w, ← dsimp% (hp j), dsimp% hc.fac ((forget X).mapCocone t)])
  fac t j := by
    ext
    simp [dsimp% hc.fac ((forget X).mapCocone t) j]
  uniq t _ hm := by
    ext
    refi

中文:
定义 isColimitLiftCocone
  签名: {J : 类型} [范畴* J] [非空 J]
  定义体: Under.homMk (hc.desc ((Under.forget _).mapCocone t)) (by
    let j : J := Classical.arbitrary _
    simp [← dsimp% (t.ι.app j).w, ← dsimp% (hp j), dsimp% hc.fac ((forget X).mapCocone t)])
  fac t j := by
    ext
    simp [dsimp% hc.fac ((forget X).mapCocone t) j]
  uniq t _ hm := by
    ext
    refi

Depends on / 依赖: Classical, Classical.arbitrary, Under.forget, Under.homMk, arbitrary, forget, hc.desc, hc.fac, hc.hom_ext, hom_ext, mapCocone
-/
def isColimitLiftCocone {J : Type*} [Category* J] [Nonempty J]
    (D : J ⥤ T) {X : T} (s : (Functor.const J).obj X ⟶ D)
    (c : Cocone D) (p : X ⟶ c.pt) (hp : forall j, s.app j ≫ c.ι.app j = p)
    (hc : IsColimit c) :
    IsColimit (liftCocone D s c p hp) where
  desc t := Under.homMk (hc.desc ((Under.forget _).mapCocone t)) (by
    let j : J := Classical.arbitrary _
    simp [← dsimp% (t.ι.app j).w, ← dsimp% (hp j), dsimp% hc.fac ((forget X).mapCocone t)])
  fac t j := by
    ext
    simp [dsimp% hc.fac ((forget X).mapCocone t) j]
  uniq t _ hm := by
    ext
    refine hc.hom_ext (fun j => ?_)
    simp [dsimp% hc.fac ((forget X).mapCocone t) j, ← hm]

end Under

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Restrict a cocone to the diagram under `j`. This preserves being colimiting if the forgetful functor
`Over j ⥤ J` is final (see `CategoryTheory.Limits.IsColimit.underPost`).
-/
@[simps]
/--
Definition of `Limits.Cocone.underPost` / `Limits.Cocone.underPost` 的定义

English:
definition Limits.Cocone.underPost
  signature: {J C : Type*} [Category* J] [Category* C]
  body: Under.mk (c.ι.app j)
  ι.app k := Under.homMk (c.ι.app k.right)

中文:
定义 Limits.余锥.underPost
  签名: {J C : 类型} [范畴* J] [范畴* C]
  定义体: Under.mk (c.ι.app j)
  ι.app k := Under.homMk (c.ι.app k.right)
-/
def Limits.Cocone.underPost {J C : Type*} [Category* J] [Category* C]
    {D : J ⥤ C} (c : Cocone D) (j : J) :
    Cocone (Under.post (X := j) D) where
  pt := Under.mk (c.ι.app j)
  ι.app k := Under.homMk (c.ι.app k.right)

namespace StructuredArrow

variable {D : Type u₂} [Category.{v₂} D]

/-- Reinterpreting an `F`-structured arrow `X ⟶ F.obj d` as an arrow under `X` induces a functor
    `StructuredArrow X F ⥤ Under X`. -/
@[simps! obj_right obj_hom map_right]
/--
Definition of `toUnder` / `toUnder` 的定义

English:
definition toUnder
  signature: (X : T) (F : D ⥤ T)
  body: StructuredArrow.pre X F (𝟭 T)

中文:
定义 toUnder
  签名: (X : T) (F : D ⥤ T)
  定义体: StructuredArrow.pre X F (𝟭 T)

Depends on / 依赖: StructuredArrow, StructuredArrow.pre
-/
def toUnder (X : T) (F : D ⥤ T) : StructuredArrow X F ⥤ Under X :=
  StructuredArrow.pre X F (𝟭 T)

instance (X : T) (F : D ⥤ T) [F.Faithful] : (toUnder X F).Faithful :=
  show (StructuredArrow.pre _ _ _).Faithful from inferInstance

instance (X : T) (F : D ⥤ T) [F.Full] : (toUnder X F).Full :=
  show (StructuredArrow.pre _ _ _).Full from inferInstance

instance (X : T) (F : D ⥤ T) [F.EssSurj] : (toUnder X F).EssSurj :=
  show (StructuredArrow.pre _ _ _).EssSurj from inferInstance

/--
Instance `isEquivalence_toUnder` / 实例 `isEquivalence_toUnder`

English:
instance isEquivalence_toUnder
  signature: (X : T) (F : D ⥤ T) [F.IsEquivalence]
  body: StructuredArrow.isEquivalence_pre _ _ _

中文:
实例 isEquivalence_toUnder
  签名: (X : T) (F : D ⥤ T) [F.是等价]
  定义体: StructuredArrow.isEquivalence_pre _ _ _

Depends on / 依赖: StructuredArrow, StructuredArrow.isEquivalence_pre, isEquivalence_pre
-/
instance isEquivalence_toUnder (X : T) (F : D ⥤ T) [F.IsEquivalence] :
    (toUnder X F).IsEquivalence :=
  StructuredArrow.isEquivalence_pre _ _ _

end StructuredArrow

namespace Functor
variable {X : T} {F : T ⥤ D}

/--
lemma `essImage.of_overPost` / 引理 `essImage.of_overPost`

English:
lemma essImage.of_overPost
  given: {Y : Over (F.obj X)}
  proof: fun ⟨Z, ⟨e⟩⟩ => ⟨Z.left, ⟨(Over.forget _).mapIso e⟩⟩

中文:
引理 essImage.of_overPost
  条件: {Y : Over (F.obj X)}
  证明: fun ⟨Z, ⟨e⟩⟩ => ⟨Z.left, ⟨(Over.forget _).mapIso e⟩⟩

Depends on / 依赖: F.essImage, Y.left, essImage
-/
lemma essImage.of_overPost {Y : Over (F.obj X)} :
    (Over.post F (X := X)).essImage Y -> F.essImage Y.left :=
  fun ⟨Z, ⟨e⟩⟩ => ⟨Z.left, ⟨(Over.forget _).mapIso e⟩⟩

/--
lemma `essImage.of_underPost` / 引理 `essImage.of_underPost`

English:
lemma essImage.of_underPost
  given: {Y : Under (F.obj X)}
  proof: fun ⟨Z, ⟨e⟩⟩ => ⟨Z.right, ⟨(Under.forget _).mapIso e⟩⟩

中文:
引理 essImage.of_underPost
  条件: {Y : Under (F.obj X)}
  证明: fun ⟨Z, ⟨e⟩⟩ => ⟨Z.right, ⟨(Under.forget _).mapIso e⟩⟩

Depends on / 依赖: F.essImage, Y.right, essImage
-/
lemma essImage.of_underPost {Y : Under (F.obj X)} :
    (Under.post F (X := X)).essImage Y -> F.essImage Y.right :=
  fun ⟨Z, ⟨e⟩⟩ => ⟨Z.right, ⟨(Under.forget _).mapIso e⟩⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `essImage_overPost` / 引理 `essImage_overPost`

English:
lemma essImage_overPost
  given: [F.Full] {Y : Over (F.obj X)}
  proof: .of_overPost
  mpr := fun ⟨Z, ⟨e⟩⟩ => let ⟨f, hf⟩ := F.map_surjective (e.hom ≫ Y.hom); ⟨.mk f, ⟨Over.isoMk e⟩⟩

中文:
引理 essImage_overPost
  条件: [F.满] {Y : Over (F.obj X)}
  证明: .of_overPost
  mpr := fun ⟨Z, ⟨e⟩⟩ => let ⟨f, hf⟩ := F.map_surjective (e.hom ≫ Y.hom); ⟨.mk f, ⟨Over.isoMk e⟩⟩
-/
@[simp] lemma essImage_overPost [F.Full] {Y : Over (F.obj X)} :
    (Over.post F (X := X)).essImage Y ↔ F.essImage Y.left where
  mp := .of_overPost
  mpr := fun ⟨Z, ⟨e⟩⟩ => let ⟨f, hf⟩ := F.map_surjective (e.hom ≫ Y.hom); ⟨.mk f, ⟨Over.isoMk e⟩⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `essImage_underPost` / 引理 `essImage_underPost`

English:
lemma essImage_underPost
  given: [F.Full] {Y : Under (F.obj X)}
  proof: .of_underPost
  mpr := fun ⟨Z, ⟨e⟩⟩ => let ⟨f, hf⟩ := F.map_surjective (Y.hom ≫ e.inv); ⟨.mk f, ⟨Under.isoMk e⟩⟩

中文:
引理 essImage_underPost
  条件: [F.满] {Y : Under (F.obj X)}
  证明: .of_underPost
  mpr := fun ⟨Z, ⟨e⟩⟩ => let ⟨f, hf⟩ := F.map_surjective (Y.hom ≫ e.inv); ⟨.mk f, ⟨Under.isoMk e⟩⟩
-/
@[simp] lemma essImage_underPost [F.Full] {Y : Under (F.obj X)} :
    (Under.post F (X := X)).essImage Y ↔ F.essImage Y.right where
  mp := .of_underPost
  mpr := fun ⟨Z, ⟨e⟩⟩ => let ⟨f, hf⟩ := F.map_surjective (Y.hom ≫ e.inv); ⟨.mk f, ⟨Under.isoMk e⟩⟩

variable {S : Type u₂} [Category.{v₂} S]

/-- Given `X : T`, to upgrade a functor `F : S ⥤ T` to a functor `S ⥤ Over X`, it suffices to
    provide maps `F.obj Y ⟶ X` for all `Y` making the obvious triangles involving all `F.map g`
    commute. -/
@[simps! obj_left map_left]
/--
Definition of `toOver` / `toOver` 的定义

English:
definition toOver
  signature: (F : S ⥤ T) (X : T) (f : (Y : S) -> F.obj Y ⟶ X)
  body: F.toCostructuredArrow (𝟭 _) X f h

中文:
定义 toOver
  签名: (F : S ⥤ T) (X : T) (f : (Y : S) -> F.obj Y ⟶ X)
  定义体: F.toCostructuredArrow (𝟭 _) X f h

Depends on / 依赖: F.toCostructuredArrow, toCostructuredArrow
-/
def toOver (F : S ⥤ T) (X : T) (f : (Y : S) -> F.obj Y ⟶ X)
    (h : forall {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : S ⥤ Over X :=
  F.toCostructuredArrow (𝟭 _) X f h

/--
Definition of `toOverCompForget` / `toOverCompForget` 的定义

English:
definition toOverCompForget
  signature: (F : S ⥤ T) (X : T) (f : (Y : S) -> F.obj Y ⟶ X)
  body: Iso.refl _

@[simp]

中文:
定义 toOverCompForget
  签名: (F : S ⥤ T) (X : T) (f : (Y : S) -> F.obj Y ⟶ X)
  定义体: Iso.refl _

@[simp]

Depends on / 依赖: Iso.refl
-/
def toOverCompForget (F : S ⥤ T) (X : T) (f : (Y : S) -> F.obj Y ⟶ X)
    (h : forall {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : F.toOver X f h ⋙ Over.forget _ ≅ F :=
  Iso.refl _

@[simp]
/--
lemma `toOver_comp_forget` / 引理 `toOver_comp_forget`

English:
lemma toOver_comp_forget
  statement: (F : S ⥤ T) (X : T) (f : (Y : S) -> F.obj Y ⟶ X)
  proof: rfl

中文:
引理 toOver_comp_forget
  结论: (F : S ⥤ T) (X : T) (f : (Y : S) -> F.obj Y ⟶ X)
  证明: rfl
-/
lemma toOver_comp_forget (F : S ⥤ T) (X : T) (f : (Y : S) -> F.obj Y ⟶ X)
    (h : forall {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : F.toOver X f h ⋙ Over.forget _ = F :=
  rfl

/-- Given `X : T`, to upgrade a functor `F : S ⥤ T` to a functor `S ⥤ Under X`, it suffices to
    provide maps `X ⟶ F.obj Y` for all `Y` making the obvious triangles involving all `F.map g`
    commute. -/
@[simps! obj_right map_right]
/--
Definition of `toUnder` / `toUnder` 的定义

English:
definition toUnder
  signature: (F : S ⥤ T) (X : T) (f : (Y : S) -> X ⟶ F.obj Y)
  body: F.toStructuredArrow X (𝟭 _) f h

中文:
定义 toUnder
  签名: (F : S ⥤ T) (X : T) (f : (Y : S) -> X ⟶ F.obj Y)
  定义体: F.toStructuredArrow X (𝟭 _) f h

Depends on / 依赖: F.toStructuredArrow, toStructuredArrow
-/
def toUnder (F : S ⥤ T) (X : T) (f : (Y : S) -> X ⟶ F.obj Y)
    (h : forall {Y Z : S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : S ⥤ Under X :=
  F.toStructuredArrow X (𝟭 _) f h

/--
Definition of `toUnderCompForget` / `toUnderCompForget` 的定义

English:
definition toUnderCompForget
  signature: (F : S ⥤ T) (X : T) (f : (Y : S) -> X ⟶ F.obj Y)
  body: Iso.refl _

@[simp]

中文:
定义 toUnderCompForget
  签名: (F : S ⥤ T) (X : T) (f : (Y : S) -> X ⟶ F.obj Y)
  定义体: Iso.refl _

@[simp]

Depends on / 依赖: Iso.refl
-/
def toUnderCompForget (F : S ⥤ T) (X : T) (f : (Y : S) -> X ⟶ F.obj Y)
    (h : forall {Y Z : S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : F.toUnder X f h ⋙ Under.forget _ ≅ F :=
  Iso.refl _

@[simp]
/--
lemma `toUnder_comp_forget` / 引理 `toUnder_comp_forget`

English:
lemma toUnder_comp_forget
  statement: (F : S ⥤ T) (X : T) (f : (Y : S) -> X ⟶ F.obj Y)
  proof: rfl

中文:
引理 toUnder_comp_forget
  结论: (F : S ⥤ T) (X : T) (f : (Y : S) -> X ⟶ F.obj Y)
  证明: rfl
-/
lemma toUnder_comp_forget (F : S ⥤ T) (X : T) (f : (Y : S) -> X ⟶ F.obj Y)
    (h : forall {Y Z : S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : F.toUnder X f h ⋙ Under.forget _ = F :=
  rfl

end Functor

namespace StructuredArrow

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor from the structured arrow category on the projection functor for any structured
arrow category. -/
@[simps!]
/--
Definition of `ofStructuredArrowProjEquivalence.functor` / `ofStructuredArrowProjEquivalence.functor` 的定义

English:
definition ofStructuredArrowProjEquivalence.functor
  signature: (F : D ⥤ T) (Y : T) (X : D)
  body: Functor.toStructuredArrow
    (Functor.toUnder (StructuredArrow.proj X _ ⋙ StructuredArrow.proj Y _) _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.right.hom) (by simp)

中文:
定义 ofStructuredArrowProjEquivalence.functor
  签名: (F : D ⥤ T) (Y : T) (X : D)
  定义体: Functor.toStructuredArrow
    (Functor.toUnder (StructuredArrow.proj X _ ⋙ StructuredArrow.proj Y _) _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.right.hom) (by simp)

Depends on / 依赖: Functor, Functor.toStructuredArrow, Functor.toUnder, StructuredArrow, StructuredArrow.proj, cat_disch, f.right.hom, g.hom, toStructuredArrow, toUnder
-/
def ofStructuredArrowProjEquivalence.functor (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow X (StructuredArrow.proj Y F) ⥤ StructuredArrow Y (Under.forget X ⋙ F) :=
  Functor.toStructuredArrow
    (Functor.toUnder (StructuredArrow.proj X _ ⋙ StructuredArrow.proj Y _) _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.right.hom) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor of `ofStructuredArrowProjEquivalence.functor`. -/
@[simps!]
/--
Definition of `ofStructuredArrowProjEquivalence.inverse` / `ofStructuredArrowProjEquivalence.inverse` 的定义

English:
definition ofStructuredArrowProjEquivalence.inverse
  signature: (F : D ⥤ T) (Y : T) (X : D)
  body: Functor.toStructuredArrow
    (Functor.toStructuredArrow (StructuredArrow.proj Y _ ⋙ Under.forget X) _ _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.right.hom) (by simp)

中文:
定义 ofStructuredArrowProjEquivalence.inverse
  签名: (F : D ⥤ T) (Y : T) (X : D)
  定义体: Functor.toStructuredArrow
    (Functor.toStructuredArrow (StructuredArrow.proj Y _ ⋙ Under.forget X) _ _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.right.hom) (by simp)

Depends on / 依赖: Functor, Functor.toStructuredArrow, StructuredArrow, StructuredArrow.proj, Under.forget, cat_disch, f.right.hom, forget, g.hom, toStructuredArrow
-/
def ofStructuredArrowProjEquivalence.inverse (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow Y (Under.forget X ⋙ F) ⥤ StructuredArrow X (StructuredArrow.proj Y F) :=
  Functor.toStructuredArrow
    (Functor.toStructuredArrow (StructuredArrow.proj Y _ ⋙ Under.forget X) _ _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.right.hom) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `ofStructuredArrowProjEquivalence` / `ofStructuredArrowProjEquivalence` 的定义

English:
definition ofStructuredArrowProjEquivalence
  signature: (F : D ⥤ T) (Y : T) (X : D)
  body: ofStructuredArrowProjEquivalence.functor F Y X
  inverse := ofStructuredArrowProjEquivalence.inverse F Y X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

中文:
定义 ofStructuredArrowProjEquivalence
  签名: (F : D ⥤ T) (Y : T) (X : D)
  定义体: ofStructuredArrowProjEquivalence.functor F Y X
  inverse := ofStructuredArrowProjEquivalence.inverse F Y X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

Depends on / 依赖: functor, ofStructuredArrowProjEquivalence, ofStructuredArrowProjEquivalence.functor
-/
def ofStructuredArrowProjEquivalence (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow X (StructuredArrow.proj Y F) ≌ StructuredArrow Y (Under.forget X ⋙ F) where
  functor := ofStructuredArrowProjEquivalence.functor F Y X
  inverse := ofStructuredArrowProjEquivalence.inverse F Y X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical functor from the structured arrow category on the diagonal functor
`T ⥤ T × T` to the structured arrow category on `Under.forget`. -/
@[simps!]
/--
Definition of `ofDiagEquivalence.functor` / `ofDiagEquivalence.functor` 的定义

English:
definition ofDiagEquivalence.functor
  signature: (X : T × T)
  body: Functor.toStructuredArrow
    (Functor.toUnder (StructuredArrow.proj X _) _
      (fun f => f.hom.1) (fun g => by simp [← w g])) _ _
    (fun f => f.hom.2) (fun g => by simp [← w g])

中文:
定义 ofDiagEquivalence.functor
  签名: (X : T × T)
  定义体: Functor.toStructuredArrow
    (Functor.toUnder (StructuredArrow.proj X _) _
      (fun f => f.hom.1) (fun g => by simp [← w g])) _ _
    (fun f => f.hom.2) (fun g => by simp [← w g])

Depends on / 依赖: Functor, Functor.toStructuredArrow, Functor.toUnder, StructuredArrow, StructuredArrow.proj, f.hom, toStructuredArrow, toUnder
-/
def ofDiagEquivalence.functor (X : T × T) :
    StructuredArrow X (Functor.diag _) ⥤ StructuredArrow X.2 (Under.forget X.1) :=
  Functor.toStructuredArrow
    (Functor.toUnder (StructuredArrow.proj X _) _
      (fun f => f.hom.1) (fun g => by simp [← w g])) _ _
    (fun f => f.hom.2) (fun g => by simp [← w g])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor of `ofDiagEquivalence.functor`. -/
@[simps!]
/--
Definition of `ofDiagEquivalence.inverse` / `ofDiagEquivalence.inverse` 的定义

English:
definition ofDiagEquivalence.inverse
  signature: (X : T × T)
  body: Functor.toStructuredArrow (StructuredArrow.proj _ _ ⋙ Under.forget _) _ _
    (fun f => (f.right.hom, f.hom)) (fun m => by have := m.w; cat_disch)

中文:
定义 ofDiagEquivalence.inverse
  签名: (X : T × T)
  定义体: Functor.toStructuredArrow (StructuredArrow.proj _ _ ⋙ Under.forget _) _ _
    (fun f => (f.right.hom, f.hom)) (fun m => by have := m.w; cat_disch)

Depends on / 依赖: Functor, Functor.toStructuredArrow, StructuredArrow, StructuredArrow.proj, Under.forget, cat_disch, f.hom, f.right.hom, forget, toStructuredArrow
-/
def ofDiagEquivalence.inverse (X : T × T) :
    StructuredArrow X.2 (Under.forget X.1) ⥤ StructuredArrow X (Functor.diag _) :=
  Functor.toStructuredArrow (StructuredArrow.proj _ _ ⋙ Under.forget _) _ _
    (fun f => (f.right.hom, f.hom)) (fun m => by have := m.w; cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `ofDiagEquivalence` / `ofDiagEquivalence` 的定义

English:
definition ofDiagEquivalence
  signature: (X : T × T)
  body: ofDiagEquivalence.functor X
  inverse := ofDiagEquivalence.inverse X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

中文:
定义 ofDiagEquivalence
  签名: (X : T × T)
  定义体: ofDiagEquivalence.functor X
  inverse := ofDiagEquivalence.inverse X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

Depends on / 依赖: functor, ofDiagEquivalence, ofDiagEquivalence.functor
-/
def ofDiagEquivalence (X : T × T) :
    StructuredArrow X (Functor.diag _) ≌ StructuredArrow X.2 (Under.forget X.1) where
  functor := ofDiagEquivalence.functor X
  inverse := ofDiagEquivalence.inverse X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

/--
Definition of `ofDiagEquivalence'` / `ofDiagEquivalence'` 的定义

English:
definition ofDiagEquivalence'
  signature: (X : T × T)
  body: (ofDiagEquivalence X).trans
(ofStructuredArrowProjEquivalence (𝟭 T) X.1 X.2).trans
    StructuredArrow.mapNatIso (Under.forget X.2).rightUnitor

中文:
定义 ofDiagEquivalence'
  签名: (X : T × T)
  定义体: (ofDiagEquivalence X).trans
(ofStructuredArrowProjEquivalence (𝟭 T) X.1 X.2).trans
    StructuredArrow.mapNatIso (Under.forget X.2).rightUnitor

Depends on / 依赖: StructuredArrow, StructuredArrow.mapNatIso, Under.forget, forget, mapNatIso, ofDiagEquivalence, ofStructuredArrowProjEquivalence, rightUnitor
-/
def ofDiagEquivalence' (X : T × T) :
    StructuredArrow X (Functor.diag _) ≌ StructuredArrow X.1 (Under.forget X.2) :=
(ofDiagEquivalence X).trans
(ofStructuredArrowProjEquivalence (𝟭 T) X.1 X.2).trans
    StructuredArrow.mapNatIso (Under.forget X.2).rightUnitor

section CommaFst

variable {C : Type u₃} [Category.{v₃} C] (F : C ⥤ T) (G : D ⥤ T)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor used to define the equivalence `ofCommaSndEquivalence`. -/
@[simps]
/--
Definition of `ofCommaSndEquivalenceFunctor` / `ofCommaSndEquivalenceFunctor` 的定义

English:
definition ofCommaSndEquivalenceFunctor
  signature: (c : C)
  body: ⟨Under.mk X.hom, X.right.right, X.right.hom⟩
  map f := ⟨Under.homMk f.right.left (by simp [dsimp% f.w]), f.right.right, by simp⟩

中文:
定义 ofCommaSndEquivalenceFunctor
  签名: (c : C)
  定义体: ⟨Under.mk X.hom, X.right.right, X.right.hom⟩
  map f := ⟨Under.homMk f.right.left (by simp [dsimp% f.w]), f.right.right, by simp⟩

Depends on / 依赖: Under.mk, X.hom, X.right.hom, X.right.right
-/
def ofCommaSndEquivalenceFunctor (c : C) :
    StructuredArrow c (Comma.fst F G) ⥤ Comma (Under.forget c ⋙ F) G where
  obj X := ⟨Under.mk X.hom, X.right.right, X.right.hom⟩
  map f := ⟨Under.homMk f.right.left (by simp [dsimp% f.w]), f.right.right, by simp⟩

set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor used to define the equivalence `ofCommaSndEquivalence`. -/
@[simps!]
/--
Definition of `ofCommaSndEquivalenceInverse` / `ofCommaSndEquivalenceInverse` 的定义

English:
definition ofCommaSndEquivalenceInverse
  signature: (c : C)
  body: Functor.toStructuredArrow (Comma.preLeft (Under.forget c) F G) _ _
    (fun Y => Y.left.hom) (fun _ => by simp)

中文:
定义 ofCommaSndEquivalenceInverse
  签名: (c : C)
  定义体: Functor.toStructuredArrow (Comma.preLeft (Under.forget c) F G) _ _
    (fun Y => Y.left.hom) (fun _ => by simp)

Depends on / 依赖: Comma.preLeft, Functor, Functor.toStructuredArrow, Under.forget, Y.left.hom, forget, preLeft, toStructuredArrow
-/
def ofCommaSndEquivalenceInverse (c : C) :
    Comma (Under.forget c ⋙ F) G ⥤ StructuredArrow c (Comma.fst F G) :=
  Functor.toStructuredArrow (Comma.preLeft (Under.forget c) F G) _ _
    (fun Y => Y.left.hom) (fun _ => by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- There is a canonical equivalence between the structured arrow category with domain `c` on
the functor `Comma.fst F G : Comma F G ⥤ F` and the comma category over
`Under.forget c ⋙ F : Under c ⥤ T` and `G`. -/
@[simps]
/--
Definition of `ofCommaSndEquivalence` / `ofCommaSndEquivalence` 的定义

English:
definition ofCommaSndEquivalence
  signature: (c : C)
  body: ofCommaSndEquivalenceFunctor F G c
  inverse := ofCommaSndEquivalenceInverse F G c
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 ofCommaSndEquivalence
  签名: (c : C)
  定义体: ofCommaSndEquivalenceFunctor F G c
  inverse := ofCommaSndEquivalenceInverse F G c
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: ofCommaSndEquivalenceFunctor
-/
def ofCommaSndEquivalence (c : C) :
    StructuredArrow c (Comma.fst F G) ≌ Comma (Under.forget c ⋙ F) G where
  functor := ofCommaSndEquivalenceFunctor F G c
  inverse := ofCommaSndEquivalenceInverse F G c
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

end CommaFst

end StructuredArrow

namespace CostructuredArrow

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor from the costructured arrow category on the projection functor for any costructured
arrow category. -/
@[simps!]
/--
Definition of `ofCostructuredArrowProjEquivalence.functor` / `ofCostructuredArrowProjEquivalence.functor` 的定义

English:
definition ofCostructuredArrowProjEquivalence.functor
  signature: (F : T ⥤ D) (Y : D) (X : T)
  body: Functor.toCostructuredArrow
    (Functor.toOver (CostructuredArrow.proj _ X ⋙ CostructuredArrow.proj F Y) _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.left.hom) (by simp)

中文:
定义 ofCostructuredArrowProjEquivalence.functor
  签名: (F : T ⥤ D) (Y : D) (X : T)
  定义体: Functor.toCostructuredArrow
    (Functor.toOver (CostructuredArrow.proj _ X ⋙ CostructuredArrow.proj F Y) _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.left.hom) (by simp)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, Functor, Functor.toCostructuredArrow, Functor.toOver, cat_disch, f.left.hom, g.hom, toCostructuredArrow, toOver
-/
def ofCostructuredArrowProjEquivalence.functor (F : T ⥤ D) (Y : D) (X : T) :
    CostructuredArrow (CostructuredArrow.proj F Y) X ⥤ CostructuredArrow (Over.forget X ⋙ F) Y :=
  Functor.toCostructuredArrow
    (Functor.toOver (CostructuredArrow.proj _ X ⋙ CostructuredArrow.proj F Y) _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.left.hom) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor of `ofCostructuredArrowProjEquivalence.functor`. -/
@[simps!]
/--
Definition of `ofCostructuredArrowProjEquivalence.inverse` / `ofCostructuredArrowProjEquivalence.inverse` 的定义

English:
definition ofCostructuredArrowProjEquivalence.inverse
  signature: (F : T ⥤ D) (Y : D) (X : T)
  body: Functor.toCostructuredArrow
    (Functor.toCostructuredArrow (CostructuredArrow.proj _ Y ⋙ Over.forget X) _ _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.left.hom) (by simp)

中文:
定义 ofCostructuredArrowProjEquivalence.inverse
  签名: (F : T ⥤ D) (Y : D) (X : T)
  定义体: Functor.toCostructuredArrow
    (Functor.toCostructuredArrow (CostructuredArrow.proj _ Y ⋙ Over.forget X) _ _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.left.hom) (by simp)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, Functor, Functor.toCostructuredArrow, Over.forget, cat_disch, f.left.hom, forget, g.hom, toCostructuredArrow
-/
def ofCostructuredArrowProjEquivalence.inverse (F : T ⥤ D) (Y : D) (X : T) :
    CostructuredArrow (Over.forget X ⋙ F) Y ⥤ CostructuredArrow (CostructuredArrow.proj F Y) X :=
  Functor.toCostructuredArrow
    (Functor.toCostructuredArrow (CostructuredArrow.proj _ Y ⋙ Over.forget X) _ _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.left.hom) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `ofCostructuredArrowProjEquivalence` / `ofCostructuredArrowProjEquivalence` 的定义

English:
definition ofCostructuredArrowProjEquivalence
  signature: (F : T ⥤ D) (Y : D) (X : T)
  body: ofCostructuredArrowProjEquivalence.functor F Y X
  inverse := ofCostructuredArrowProjEquivalence.inverse F Y X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

中文:
定义 ofCostructuredArrowProjEquivalence
  签名: (F : T ⥤ D) (Y : D) (X : T)
  定义体: ofCostructuredArrowProjEquivalence.functor F Y X
  inverse := ofCostructuredArrowProjEquivalence.inverse F Y X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

Depends on / 依赖: functor, ofCostructuredArrowProjEquivalence, ofCostructuredArrowProjEquivalence.functor
-/
def ofCostructuredArrowProjEquivalence (F : T ⥤ D) (Y : D) (X : T) :
    CostructuredArrow (CostructuredArrow.proj F Y) X
      ≌ CostructuredArrow (Over.forget X ⋙ F) Y where
  functor := ofCostructuredArrowProjEquivalence.functor F Y X
  inverse := ofCostructuredArrowProjEquivalence.inverse F Y X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical functor from the costructured arrow category on the diagonal functor
`T ⥤ T × T` to the costructured arrow category on `Under.forget`. -/
@[simps!]
/--
Definition of `ofDiagEquivalence.functor` / `ofDiagEquivalence.functor` 的定义

English:
definition ofDiagEquivalence.functor
  signature: (X : T × T)
  body: Functor.toCostructuredArrow
    (Functor.toOver (CostructuredArrow.proj _ X) _
      (fun g => by exact g.hom.1) (fun m => by have := congrArg (·.1) m.w; cat_disch))
    _ _
    (fun f => f.hom.2) (fun m => by have := congrArg (·.2) m.w; cat_disch)

中文:
定义 ofDiagEquivalence.functor
  签名: (X : T × T)
  定义体: Functor.toCostructuredArrow
    (Functor.toOver (CostructuredArrow.proj _ X) _
      (fun g => by exact g.hom.1) (fun m => by have := congrArg (·.1) m.w; cat_disch))
    _ _
    (fun f => f.hom.2) (fun m => by have := congrArg (·.2) m.w; cat_disch)
-/
def ofDiagEquivalence.functor (X : T × T) :
    CostructuredArrow (Functor.diag _) X ⥤ CostructuredArrow (Over.forget X.1) X.2 :=
  Functor.toCostructuredArrow
    (Functor.toOver (CostructuredArrow.proj _ X) _
      (fun g => by exact g.hom.1) (fun m => by have := congrArg (·.1) m.w; cat_disch))
    _ _
    (fun f => f.hom.2) (fun m => by have := congrArg (·.2) m.w; cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor of `ofDiagEquivalence.functor`. -/
@[simps!]
/--
Definition of `ofDiagEquivalence.inverse` / `ofDiagEquivalence.inverse` 的定义

English:
definition ofDiagEquivalence.inverse
  signature: (X : T × T)
  body: Functor.toCostructuredArrow (CostructuredArrow.proj _ _ ⋙ Over.forget _) _ X
    (fun f => (f.left.hom, f.hom)) (fun m => by have := m.w; cat_disch)

中文:
定义 ofDiagEquivalence.inverse
  签名: (X : T × T)
  定义体: Functor.toCostructuredArrow (CostructuredArrow.proj _ _ ⋙ Over.forget _) _ X
    (fun f => (f.left.hom, f.hom)) (fun m => by have := m.w; cat_disch)
-/
def ofDiagEquivalence.inverse (X : T × T) :
    CostructuredArrow (Over.forget X.1) X.2 ⥤ CostructuredArrow (Functor.diag _) X :=
  Functor.toCostructuredArrow (CostructuredArrow.proj _ _ ⋙ Over.forget _) _ X
    (fun f => (f.left.hom, f.hom)) (fun m => by have := m.w; cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `ofDiagEquivalence` / `ofDiagEquivalence` 的定义

English:
definition ofDiagEquivalence
  signature: (X : T × T)
  body: ofDiagEquivalence.functor X
  inverse := ofDiagEquivalence.inverse X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

中文:
定义 ofDiagEquivalence
  签名: (X : T × T)
  定义体: ofDiagEquivalence.functor X
  inverse := ofDiagEquivalence.inverse X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

Depends on / 依赖: functor, ofDiagEquivalence, ofDiagEquivalence.functor
-/
def ofDiagEquivalence (X : T × T) :
    CostructuredArrow (Functor.diag _) X ≌ CostructuredArrow (Over.forget X.1) X.2 where
  functor := ofDiagEquivalence.functor X
  inverse := ofDiagEquivalence.inverse X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

-- noncomputability is only for performance
/--
Definition of `ofDiagEquivalence'` / `ofDiagEquivalence'` 的定义

English:
definition ofDiagEquivalence'
  signature: (X : T × T)
  body: (ofDiagEquivalence X).trans
(ofCostructuredArrowProjEquivalence (𝟭 T) X.1 X.2).trans
    CostructuredArrow.mapNatIso (Over.forget X.2).rightUnitor

中文:
定义 ofDiagEquivalence'
  签名: (X : T × T)
  定义体: (ofDiagEquivalence X).trans
(ofCostructuredArrowProjEquivalence (𝟭 T) X.1 X.2).trans
    CostructuredArrow.mapNatIso (Over.forget X.2).rightUnitor

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mapNatIso, Over.forget, forget, mapNatIso, ofCostructuredArrowProjEquivalence, ofDiagEquivalence, rightUnitor
-/
noncomputable def ofDiagEquivalence' (X : T × T) :
    CostructuredArrow (Functor.diag _) X ≌ CostructuredArrow (Over.forget X.2) X.1 :=
(ofDiagEquivalence X).trans
(ofCostructuredArrowProjEquivalence (𝟭 T) X.1 X.2).trans
    CostructuredArrow.mapNatIso (Over.forget X.2).rightUnitor

section CommaFst

variable {C : Type u₃} [Category.{v₃} C] (F : C ⥤ T) (G : D ⥤ T)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor used to define the equivalence `ofCommaFstEquivalence`. -/
@[simps]
/--
Definition of `ofCommaFstEquivalenceFunctor` / `ofCommaFstEquivalenceFunctor` 的定义

English:
definition ofCommaFstEquivalenceFunctor
  signature: (c : C)
  body: ⟨Over.mk X.hom, X.left.right, X.left.hom⟩
  map f := ⟨Over.homMk f.left.left (by simpa using f.w), f.left.right, by simp⟩

中文:
定义 ofCommaFstEquivalenceFunctor
  签名: (c : C)
  定义体: ⟨Over.mk X.hom, X.left.right, X.left.hom⟩
  map f := ⟨Over.homMk f.left.left (by simpa using f.w), f.left.right, by simp⟩

Depends on / 依赖: Over.mk, X.hom, X.left.hom, X.left.right
-/
def ofCommaFstEquivalenceFunctor (c : C) :
    CostructuredArrow (Comma.fst F G) c ⥤ Comma (Over.forget c ⋙ F) G where
  obj X := ⟨Over.mk X.hom, X.left.right, X.left.hom⟩
  map f := ⟨Over.homMk f.left.left (by simpa using f.w), f.left.right, by simp⟩

set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor used to define the equivalence `ofCommaFstEquivalence`. -/
@[simps!]
/--
Definition of `ofCommaFstEquivalenceInverse` / `ofCommaFstEquivalenceInverse` 的定义

English:
definition ofCommaFstEquivalenceInverse
  signature: (c : C)
  body: Functor.toCostructuredArrow (Comma.preLeft (Over.forget c) F G) _ _
    (fun Y => Y.left.hom) (fun _ => by simp)

中文:
定义 ofCommaFstEquivalenceInverse
  签名: (c : C)
  定义体: Functor.toCostructuredArrow (Comma.preLeft (Over.forget c) F G) _ _
    (fun Y => Y.left.hom) (fun _ => by simp)

Depends on / 依赖: Comma.preLeft, Functor, Functor.toCostructuredArrow, Over.forget, Y.left.hom, forget, preLeft, toCostructuredArrow
-/
def ofCommaFstEquivalenceInverse (c : C) :
    Comma (Over.forget c ⋙ F) G ⥤ CostructuredArrow (Comma.fst F G) c :=
  Functor.toCostructuredArrow (Comma.preLeft (Over.forget c) F G) _ _
    (fun Y => Y.left.hom) (fun _ => by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- There is a canonical equivalence between the costructured arrow category with codomain `c` on
the functor `Comma.fst F G : Comma F G ⥤ F` and the comma category over
`Over.forget c ⋙ F : Over c ⥤ T` and `G`. -/
@[simps]
/--
Definition of `ofCommaFstEquivalence` / `ofCommaFstEquivalence` 的定义

English:
definition ofCommaFstEquivalence
  signature: (c : C)
  body: ofCommaFstEquivalenceFunctor F G c
  inverse := ofCommaFstEquivalenceInverse F G c
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 ofCommaFstEquivalence
  签名: (c : C)
  定义体: ofCommaFstEquivalenceFunctor F G c
  inverse := ofCommaFstEquivalenceInverse F G c
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: ofCommaFstEquivalenceFunctor
-/
def ofCommaFstEquivalence (c : C) :
    CostructuredArrow (Comma.fst F G) c ≌ Comma (Over.forget c ⋙ F) G where
  functor := ofCommaFstEquivalenceFunctor F G c
  inverse := ofCommaFstEquivalenceInverse F G c
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

end CommaFst

end CostructuredArrow

section Opposite

open Opposite

variable (X : T)

set_option backward.defeqAttrib.useBackward true in
/-- The canonical equivalence between over and under categories by reversing structure arrows. -/
@[simps]
/--
Definition of `Over.opEquivOpUnder` / `Over.opEquivOpUnder` 的定义

English:
definition Over.opEquivOpUnder
  signature: : Over (op X) ≌ (Under X)ᵒᵖ where
  body: ⟨Under.mk Y.hom.unop⟩
  functor.map {Z Y} f := ⟨Under.homMk (f.left.unop) (by dsimp; rw [← unop_comp, Over.w])⟩
  inverse.obj Y := Over.mk (Y.unop.hom.op)
inverse.map {Z Y} f := Over.homMk f.unop.right.op by dsimp; rw [← Under.w f.unop, op_comp]
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 Over.opEquivOpUnder
  签名: : Over (op X) ≌ (Under X)ᵒᵖ where
  定义体: ⟨Under.mk Y.hom.unop⟩
  functor.map {Z Y} f := ⟨Under.homMk (f.left.unop) (by dsimp; rw [← unop_comp, Over.w])⟩
  inverse.obj Y := Over.mk (Y.unop.hom.op)
inverse.map {Z Y} f := Over.homMk f.unop.right.op by dsimp; rw [← Under.w f.unop, op_comp]
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: Under.mk, Y.hom.unop
-/
def Over.opEquivOpUnder : Over (op X) ≌ (Under X)ᵒᵖ where
  functor.obj Y := ⟨Under.mk Y.hom.unop⟩
  functor.map {Z Y} f := ⟨Under.homMk (f.left.unop) (by dsimp; rw [← unop_comp, Over.w])⟩
  inverse.obj Y := Over.mk (Y.unop.hom.op)
inverse.map {Z Y} f := Over.homMk f.unop.right.op by dsimp; rw [← Under.w f.unop, op_comp]
  unitIso := Iso.refl _
  counitIso := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- The canonical equivalence between under and over categories by reversing structure arrows. -/
@[simps]
/--
Definition of `Under.opEquivOpOver` / `Under.opEquivOpOver` 的定义

English:
definition Under.opEquivOpOver
  signature: : Under (op X) ≌ (Over X)ᵒᵖ where
  body: ⟨Over.mk Y.hom.unop⟩
  functor.map {Z Y} f := ⟨Over.homMk (f.right.unop) (by dsimp; rw [← unop_comp, Under.w])⟩
  inverse.obj Y := Under.mk (Y.unop.hom.op)
inverse.map {Z Y} f := Under.homMk f.unop.left.op by dsimp; rw [← Over.w f.unop, op_comp]
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 Under.opEquivOpOver
  签名: : Under (op X) ≌ (Over X)ᵒᵖ where
  定义体: ⟨Over.mk Y.hom.unop⟩
  functor.map {Z Y} f := ⟨Over.homMk (f.right.unop) (by dsimp; rw [← unop_comp, Under.w])⟩
  inverse.obj Y := Under.mk (Y.unop.hom.op)
inverse.map {Z Y} f := Under.homMk f.unop.left.op by dsimp; rw [← Over.w f.unop, op_comp]
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: Over.mk, Y.hom.unop
-/
def Under.opEquivOpOver : Under (op X) ≌ (Over X)ᵒᵖ where
  functor.obj Y := ⟨Over.mk Y.hom.unop⟩
  functor.map {Z Y} f := ⟨Over.homMk (f.right.unop) (by dsimp; rw [← unop_comp, Under.w])⟩
  inverse.obj Y := Under.mk (Y.unop.hom.op)
inverse.map {Z Y} f := Under.homMk f.unop.left.op by dsimp; rw [← Over.w f.unop, op_comp]
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end Opposite

end CategoryTheory
