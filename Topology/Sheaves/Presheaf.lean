/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Mario Carneiro, Reid Barton, Andrew Yang
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.Topology.Sheaves.Init

/-!
# Presheaves on a topological space

We define `TopCat.Presheaf C X` simply as `(TopologicalSpace.Opens X)ᵒᵖ ⥤ C`,
and inherit the category structure with natural transformations as morphisms.

We define
* Given `{X Y : TopCat.{w}}` and `f : X ⟶ Y`, we define
  `TopCat.Presheaf.pushforward C f : X.Presheaf C ⥤ Y.Presheaf C`,
  with notation `f _* ℱ` for `ℱ : X.Presheaf C`.

and for `ℱ : X.Presheaf C` provide the natural isomorphisms
* `TopCat.Presheaf.Pushforward.id : (𝟙 X) _* ℱ ≅ ℱ`
* `TopCat.Presheaf.Pushforward.comp : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ)`
  along with their `@[simp]` lemmas.

We also define the functors `pullback C f : Y.Presheaf C ⥤ X.Presheaf c`,
and provide their adjunction at
`TopCat.Presheaf.pullbackPushforwardAdjunction`.
-/

@[expose] public section

universe w v u

open CategoryTheory TopologicalSpace Opposite Functor

variable (C : Type u) [Category.{v} C]

namespace TopCat

/-- The category of `C`-valued presheaves on a (bundled) topological space `X`. -/
@[implicit_reducible]
/--
Definition of `Presheaf` / `Presheaf` 的定义

English:
definition Presheaf
  signature: (X : TopCat.{w})
  body: (Opens X)ᵒᵖ ⥤ C

中文:
定义 Presheaf
  签名: (X : TopCat.{w})
  定义体: (Opens X)ᵒᵖ ⥤ C
-/
def Presheaf (X : TopCat.{w}) : Type max u v w :=
  (Opens X)ᵒᵖ ⥤ C

instance (X : TopCat.{w}) : Category (Presheaf.{w, v, u} C X) :=
  inferInstanceAs (Category ((Opens X)ᵒᵖ ⥤ C : Type max u v w))

variable {C}

namespace Presheaf

/--
theorem `comp_app` / 定理 `comp_app`

English:
theorem comp_app
  statement: {X : TopCat.{w}} {U : (Opens X)ᵒᵖ} {P Q R : Presheaf C X}
  proof: rfl

@[ext]

中文:
定理 comp_app
  结论: {X : TopCat.{w}} {U : (Opens X)ᵒᵖ} {P Q R : Presheaf C X}
  证明: rfl

@[ext]
-/
@[simp] theorem comp_app {X : TopCat.{w}} {U : (Opens X)ᵒᵖ} {P Q R : Presheaf C X}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).app U = f.app U ≫ g.app U := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P ⟶ Q}
  proof: by
  apply NatTrans.ext
  ext U
  induction U with | _ U => ?_
  apply w

中文:
引理 ext
  结论: {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P ⟶ Q}
  证明: by
  apply NatTrans.ext
  ext U
  induction U with | _ U => ?_
  apply w

Depends on / 依赖: NatTrans, NatTrans.ext
-/
lemma ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P ⟶ Q}
    (w : forall U : Opens X, f.app (op U) = g.app (op U)) :
    f = g := by
  apply NatTrans.ext
  ext U
  induction U with | _ U => ?_
  apply w

/-- attribute `sheaf_restrict` to mark lemmas related to restricting sheaves -/
macro "sheaf_restrict" : attr =>
  `(attr|aesop safe 50 apply (rule_sets := [$(Lean.mkIdent `Restrict):ident]))

attribute [sheaf_restrict] bot_le le_top le_refl inf_le_left inf_le_right
  le_sup_left le_sup_right

/-- `restrict_tac` solves relations among subsets (copied from `aesop cat`) -/
macro (name := restrict_tac) "restrict_tac" c:Aesop.tactic_clause* : tactic =>
`(tactic| first | assumption |
aesop c*
    (config := { terminal := true
                 assumptionTransparency := .reducible
                 enableSimp := false })
    (rule_sets := [-default, -builtin, $(Lean.mkIdent `Restrict):ident]))

/-- `restrict_tac?` passes along `Try this` from `aesop` -/
macro (name := restrict_tac?) "restrict_tac?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
aesop? c*
    (config := { terminal := true
                 assumptionTransparency := .reducible
                 enableSimp := false
                 maxRuleApplications := 300 })
  (rule_sets := [-default, -builtin, $(Lean.mkIdent `Restrict):ident]))

attribute [aesop 10% (rule_sets := [Restrict])] le_trans
attribute [aesop safe destruct (rule_sets := [Restrict])] Eq.trans_le
attribute [aesop safe -50 (rule_sets := [Restrict])] Aesop.BuiltinRules.assumption

example {X} [CompleteLattice X] (v : Nat -> X) (w x y z : X) (e : v 0 = v 1) (_ : v 1 = v 2)
    (h₀ : v 1 <= x) (_ : x <= z ⊓ w) (h₂ : x <= y ⊓ z) : v 0 <= y := by
  restrict_tac

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] {FC : C -> C -> Type*} {CC : C -> Type*}
variable [forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: {F : X.Presheaf C}
  body: F.map h.op x

中文:
定义 restrict
  签名: {F : X.Presheaf C}
  定义体: F.map h.op x

Depends on / 依赖: F.map, h.op
-/
def restrict {F : X.Presheaf C}
    {V : Opens X} (x : ToType (F.obj (op V))) {U : Opens X} (h : U ⟶ V) : ToType (F.obj (op U)) :=
  F.map h.op x

/-- restriction of a section along an inclusion -/
scoped[AlgebraicGeometry] infixl:80 " |_ₕ " => TopCat.Presheaf.restrict
/-- restriction of a section along a subset relation -/
scoped[AlgebraicGeometry] notation:80 x " |_ₗ " U " ⟪" e "⟫ " =>
  @TopCat.Presheaf.restrict _ _ _ _ _ _ _ _ _ x U (@homOfLE (Opens _) _ U _ e)

open AlgebraicGeometry

/--
Definition of `restrictOpen` / `restrictOpen` 的定义

English:
abbreviation restrictOpen
  signature: {F : X.Presheaf C}
  body: x |_ₗ U ⟪e⟫

中文:
缩写 restrictOpen
  签名: {F : X.Presheaf C}
  定义体: x |_ₗ U ⟪e⟫

Depends on / 依赖: F.obj, ToType, restrict_tac
-/
abbrev restrictOpen {F : X.Presheaf C}
    {V : Opens X} (x : ToType (F.obj (op V))) (U : Opens X)
    (e : U <= V := by restrict_tac) :
    ToType (F.obj (op U)) :=
  x |_ₗ U ⟪e⟫

/-- restriction of a section to open subset -/
scoped[AlgebraicGeometry] infixl:80 " |_ " => TopCat.Presheaf.restrictOpen

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `restrict_restrict` / 定理 `restrict_restrict`

English:
theorem restrict_restrict
  proof: by
  delta restrictOpen restrict
  rw [← ConcreteCategory.comp_apply]; rw [← Functor.map_comp]
  rfl

中文:
定理 restrict_restrict
  证明: by
  delta restrictOpen restrict
  rw [← ConcreteCategory.comp_apply]; rw [← Functor.map_comp]
  rfl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, Functor, Functor.map_comp, comp_apply, map_comp, restrict, restrictOpen
-/
theorem restrict_restrict
    {F : X.Presheaf C} {U V W : Opens X} (e₁ : U <= V) (e₂ : V <= W) (x : ToType (F.obj (op W))) :
    x |_ V |_ U = x |_ U := by
  delta restrictOpen restrict
  rw [← ConcreteCategory.comp_apply]; rw [← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `map_restrict` / 定理 `map_restrict`

English:
theorem map_restrict
  proof: by
  delta restrictOpen restrict
  rw [← ConcreteCategory.comp_apply]; rw [NatTrans.naturality]; rw [ConcreteCategory.comp_apply]

中文:
定理 map_restrict
  证明: by
  delta restrictOpen restrict
  rw [← ConcreteCategory.comp_apply]; rw [NatTrans.naturality]; rw [ConcreteCategory.comp_apply]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, NatTrans, NatTrans.naturality, comp_apply, naturality, restrict, restrictOpen
-/
theorem map_restrict
    {F G : X.Presheaf C} (e : F ⟶ G) {U V : Opens X} (h : U <= V) (x : ToType (F.obj (op V))) :
    e.app _ (x |_ U) = e.app _ x |_ U := by
  delta restrictOpen restrict
  rw [← ConcreteCategory.comp_apply]; rw [NatTrans.naturality]; rw [ConcreteCategory.comp_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `restrict_self` / 引理 `restrict_self`

English:
lemma restrict_self
  given: {F : X.Presheaf C} {U : Opens X} (x : ToType (F.obj (op U)))
  proof: by
  simp [restrictOpen, restrict]

中文:
引理 restrict_self
  条件: {F : X.Presheaf C} {U : Opens X} (x : ToType (F.obj (op U)))
  证明: by
  simp [restrictOpen, restrict]

Depends on / 依赖: restrict, restrictOpen
-/
lemma restrict_self {F : X.Presheaf C} {U : Opens X} (x : ToType (F.obj (op U))) :
    x |_ U = x := by
  simp [restrictOpen, restrict]

open CategoryTheory.Limits

variable (C)

/-- The pushforward functor. -/
@[simps!, implicit_reducible]
/--
Definition of `pushforward` / `pushforward` 的定义

English:
definition pushforward
  signature: {X Y : TopCat.{w}} (f : X ⟶ Y)
  body: (whiskeringLeft _ _ _).obj (Opens.map f).op

中文:
定义 pushforward
  签名: {X Y : TopCat.{w}} (f : X ⟶ Y)
  定义体: (whiskeringLeft _ _ _).obj (Opens.map f).op

Depends on / 依赖: Opens.map, whiskeringLeft
-/
def pushforward {X Y : TopCat.{w}} (f : X ⟶ Y) : X.Presheaf C ⥤ Y.Presheaf C :=
  (whiskeringLeft _ _ _).obj (Opens.map f).op

/-- push forward of a presheaf -/
scoped[AlgebraicGeometry] notation f:80 " _* " P:81 =>
  Functor.obj (TopCat.Presheaf.pushforward _ f) P

@[simp]
/--
theorem `pushforward_map_app'` / 定理 `pushforward_map_app'`

English:
theorem pushforward_map_app'
  statement: {X Y : TopCat.{w}} (f : X ⟶ Y) {ℱ 𝒢 : X.Presheaf C} (α : ℱ ⟶ 𝒢)
  proof: rfl

中文:
定理 pushforward_map_app'
  结论: {X Y : TopCat.{w}} (f : X ⟶ Y) {ℱ 𝒢 : X.Presheaf C} (α : ℱ ⟶ 𝒢)
  证明: rfl
-/
theorem pushforward_map_app' {X Y : TopCat.{w}} (f : X ⟶ Y) {ℱ 𝒢 : X.Presheaf C} (α : ℱ ⟶ 𝒢)
    {U : (Opens Y)ᵒᵖ} : ((pushforward C f).map α).app U = α.app (op <| (Opens.map f).obj U.unop) :=
  rfl

/--
lemma `id_pushforward` / 引理 `id_pushforward`

English:
lemma id_pushforward
  given: (X : TopCat.{w})
  statement: pushforward C (𝟙 X) = 𝟭 (X.Presheaf C)
  proof: rfl

中文:
引理 id_pushforward
  条件: (X : TopCat.{w})
  结论: pushforward C (𝟙 X) = 𝟭 (X.Presheaf C)
  证明: rfl
-/
lemma id_pushforward (X : TopCat.{w}) : pushforward C (𝟙 X) = 𝟭 (X.Presheaf C) := rfl

variable {C}

namespace Pushforward

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: {X : TopCat.{w}} (ℱ : X.Presheaf C)
  body: Iso.refl _

@[simp]

中文:
定义 id
  签名: {X : TopCat.{w}} (ℱ : X.Presheaf C)
  定义体: Iso.refl _

@[simp]

Depends on / 依赖: Iso.refl
-/
def id {X : TopCat.{w}} (ℱ : X.Presheaf C) : 𝟙 X _* ℱ ≅ ℱ := Iso.refl _

@[simp]
/--
theorem `id_hom_app` / 定理 `id_hom_app`

English:
theorem id_hom_app
  given: {X : TopCat.{w}} (ℱ : X.Presheaf C) (U)
  statement: (id ℱ).hom.app U = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 id_hom_app
  条件: {X : TopCat.{w}} (ℱ : X.Presheaf C) (U)
  结论: (id ℱ).hom.app U = 𝟙 _
  证明: rfl

@[simp]
-/
theorem id_hom_app {X : TopCat.{w}} (ℱ : X.Presheaf C) (U) : (id ℱ).hom.app U = 𝟙 _ := rfl

@[simp]
/--
theorem `id_inv_app` / 定理 `id_inv_app`

English:
theorem id_inv_app
  given: {X : TopCat.{w}} (ℱ : X.Presheaf C) (U)
  proof: rfl

中文:
定理 id_inv_app
  条件: {X : TopCat.{w}} (ℱ : X.Presheaf C) (U)
  证明: rfl
-/
theorem id_inv_app {X : TopCat.{w}} (ℱ : X.Presheaf C) (U) :
    (id ℱ).inv.app U = 𝟙 _ := rfl

/--
theorem `id_eq` / 定理 `id_eq`

English:
theorem id_eq
  given: {X : TopCat.{w}} (ℱ : X.Presheaf C)
  statement: 𝟙 X _* ℱ = ℱ
  proof: rfl

中文:
定理 id_eq
  条件: {X : TopCat.{w}} (ℱ : X.Presheaf C)
  结论: 𝟙 X _* ℱ = ℱ
  证明: rfl
-/
theorem id_eq {X : TopCat.{w}} (ℱ : X.Presheaf C) : 𝟙 X _* ℱ = ℱ := rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C)
  body: Iso.refl _

中文:
定义 comp
  签名: {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def comp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) :
    (f ≫ g) _* ℱ ≅ g _* (f _* ℱ) := Iso.refl _

/--
theorem `comp_eq` / 定理 `comp_eq`

English:
theorem comp_eq
  given: {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C)
  proof: rfl

@[simp]

中文:
定理 comp_eq
  条件: {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C)
  证明: rfl

@[simp]
-/
theorem comp_eq {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) :
    (f ≫ g) _* ℱ = g _* (f _* ℱ) :=
  rfl

@[simp]
/--
theorem `comp_hom_app` / 定理 `comp_hom_app`

English:
theorem comp_hom_app
  given: {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) (U)
  proof: rfl

@[simp]

中文:
定理 comp_hom_app
  条件: {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) (U)
  证明: rfl

@[simp]
-/
theorem comp_hom_app {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) (U) :
    (comp f g ℱ).hom.app U = 𝟙 _ := rfl

@[simp]
/--
theorem `comp_inv_app` / 定理 `comp_inv_app`

English:
theorem comp_inv_app
  given: {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) (U)
  proof: rfl

中文:
定理 comp_inv_app
  条件: {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) (U)
  证明: rfl
-/
theorem comp_inv_app {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) (U) :
    (comp f g ℱ).inv.app U = 𝟙 _ := rfl

end Pushforward

/--
Definition of `pushforwardEq` / `pushforwardEq` 的定义

English:
definition pushforwardEq
  signature: {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C)
  body: isoWhiskerRight (NatIso.op (Opens.mapIso f g h).symm) ℱ

中文:
定义 pushforwardEq
  签名: {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C)
  定义体: isoWhiskerRight (NatIso.op (Opens.mapIso f g h).symm) ℱ

Depends on / 依赖: NatIso, NatIso.op, Opens.mapIso, isoWhiskerRight, mapIso
-/
def pushforwardEq {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) :
    f _* ℱ ≅ g _* ℱ :=
  isoWhiskerRight (NatIso.op (Opens.mapIso f g h).symm) ℱ

/--
theorem `pushforward_eq'` / 定理 `pushforward_eq'`

English:
theorem pushforward_eq'
  given: {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C)
  proof: by rw [h]

中文:
定理 pushforward_eq'
  条件: {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C)
  证明: by rw [h]
-/
theorem pushforward_eq' {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) :
    f _* ℱ = g _* ℱ := by rw [h]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `pushforwardEq_hom_app` / 定理 `pushforwardEq_hom_app`

English:
theorem pushforwardEq_hom_app
  statement: {X Y : TopCat.{w}} {f g : X ⟶ Y}
  proof: by
  simp [pushforwardEq]

中文:
定理 pushforwardEq_hom_app
  结论: {X Y : TopCat.{w}} {f g : X ⟶ Y}
  证明: by
  simp [pushforwardEq]

Depends on / 依赖: pushforwardEq
-/
theorem pushforwardEq_hom_app {X Y : TopCat.{w}} {f g : X ⟶ Y}
    (h : f = g) (ℱ : X.Presheaf C) (U) :
    (pushforwardEq h ℱ).hom.app U = ℱ.map (eqToHom (by cat_disch)) := by
  simp [pushforwardEq]

variable (C)

section Iso

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A homeomorphism of spaces gives an equivalence of categories of presheaves. -/
@[simps!]
/--
Definition of `presheafEquivOfIso` / `presheafEquivOfIso` 的定义

English:
definition presheafEquivOfIso
  signature: {X Y : TopCat.{w}} (H : X ≅ Y)
  body: Equivalence.congrLeft (Opens.mapMapIso H).symm.op

中文:
定义 presheafEquivOfIso
  签名: {X Y : TopCat.{w}} (H : X ≅ Y)
  定义体: Equivalence.congrLeft (Opens.mapMapIso H).symm.op

Depends on / 依赖: Equivalence, Equivalence.congrLeft, Opens.mapMapIso, congrLeft, mapMapIso, symm.op
-/
def presheafEquivOfIso {X Y : TopCat.{w}} (H : X ≅ Y) : X.Presheaf C ≌ Y.Presheaf C :=
  Equivalence.congrLeft (Opens.mapMapIso H).symm.op

variable {C}

/--
Definition of `toPushforwardOfIso` / `toPushforwardOfIso` 的定义

English:
definition toPushforwardOfIso
  signature: {X Y : TopCat.{w}} (H : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : Y.Presheaf C}
  body: (presheafEquivOfIso _ H).toAdjunction.homEquiv ℱ 𝒢 α

中文:
定义 toPushforwardOfIso
  签名: {X Y : TopCat.{w}} (H : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : Y.Presheaf C}
  定义体: (presheafEquivOfIso _ H).toAdjunction.homEquiv ℱ 𝒢 α

Depends on / 依赖: homEquiv, presheafEquivOfIso, toAdjunction, toAdjunction.homEquiv
-/
def toPushforwardOfIso {X Y : TopCat.{w}} (H : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : Y.Presheaf C}
    (α : H.hom _* ℱ ⟶ 𝒢) : ℱ ⟶ H.inv _* 𝒢 :=
  (presheafEquivOfIso _ H).toAdjunction.homEquiv ℱ 𝒢 α

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `toPushforwardOfIso_app` / 定理 `toPushforwardOfIso_app`

English:
theorem toPushforwardOfIso_app
  statement: {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : Y.Presheaf C}
  proof: by
  simp [toPushforwardOfIso, Adjunction.homEquiv_unit]

中文:
定理 toPushforwardOfIso_app
  结论: {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : Y.Presheaf C}
  证明: by
  simp [toPushforwardOfIso, Adjunction.homEquiv_unit]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, homEquiv_unit, toPushforwardOfIso
-/
theorem toPushforwardOfIso_app {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : Y.Presheaf C}
    (H₂ : H₁.hom _* ℱ ⟶ 𝒢) (U : (Opens X)ᵒᵖ) :
    (toPushforwardOfIso H₁ H₂).app U =
      ℱ.map (eqToHom (by simp [Opens.map_def, Set.preimage_preimage])) ≫
        H₂.app (op ((Opens.map H₁.inv).obj (unop U))) := by
  simp [toPushforwardOfIso, Adjunction.homEquiv_unit]

/--
Definition of `pushforwardToOfIso` / `pushforwardToOfIso` 的定义

English:
definition pushforwardToOfIso
  signature: {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 : X.Presheaf C}
  body: ((presheafEquivOfIso _ H₁.symm).toAdjunction.homEquiv ℱ 𝒢).symm H₂

中文:
定义 pushforwardToOfIso
  签名: {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 : X.Presheaf C}
  定义体: ((presheafEquivOfIso _ H₁.symm).toAdjunction.homEquiv ℱ 𝒢).symm H₂

Depends on / 依赖: homEquiv, presheafEquivOfIso, toAdjunction, toAdjunction.homEquiv
-/
def pushforwardToOfIso {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 : X.Presheaf C}
    (H₂ : ℱ ⟶ H₁.hom _* 𝒢) : H₁.inv _* ℱ ⟶ 𝒢 :=
  ((presheafEquivOfIso _ H₁.symm).toAdjunction.homEquiv ℱ 𝒢).symm H₂

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `pushforwardToOfIso_app` / 定理 `pushforwardToOfIso_app`

English:
theorem pushforwardToOfIso_app
  statement: {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 : X.Presheaf C}
  proof: by
  simp [pushforwardToOfIso, Equivalence.toAdjunction, Adjunction.homEquiv_counit]

中文:
定理 pushforwardToOfIso_app
  结论: {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 : X.Presheaf C}
  证明: by
  simp [pushforwardToOfIso, Equivalence.toAdjunction, Adjunction.homEquiv_counit]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_counit, Equivalence, Equivalence.toAdjunction, homEquiv_counit, pushforwardToOfIso, toAdjunction
-/
theorem pushforwardToOfIso_app {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 : X.Presheaf C}
    (H₂ : ℱ ⟶ H₁.hom _* 𝒢) (U : (Opens X)ᵒᵖ) :
    (pushforwardToOfIso H₁ H₂).app U =
      H₂.app (op ((Opens.map H₁.inv).obj (unop U))) ≫
        𝒢.map (eqToHom (by simp [Opens.map_def, Set.preimage_preimage])) := by
  simp [pushforwardToOfIso, Equivalence.toAdjunction, Adjunction.homEquiv_counit]

end Iso

variable [HasColimits C]

noncomputable section

/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: {X Y : TopCat.{v}} (f : X ⟶ Y)
  body: (Opens.map f).op.lan

中文:
定义 pullback
  签名: {X Y : TopCat.{v}} (f : X ⟶ Y)
  定义体: (Opens.map f).op.lan

Depends on / 依赖: Opens.map, op.lan
-/
def pullback {X Y : TopCat.{v}} (f : X ⟶ Y) : Y.Presheaf C ⥤ X.Presheaf C :=
  (Opens.map f).op.lan

/--
Definition of `pullbackPushforwardAdjunction` / `pullbackPushforwardAdjunction` 的定义

English:
definition pullbackPushforwardAdjunction
  signature: {X Y : TopCat.{v}} (f : X ⟶ Y)
  body: Functor.lanAdjunction _ _

@[deprecated (since := "2026-03-03")]
alias pushforwardPullbackAdjunction := pullbackPushforwardAdjunction

中文:
定义 pullbackPushforwardAdjunction
  签名: {X Y : TopCat.{v}} (f : X ⟶ Y)
  定义体: Functor.lanAdjunction _ _

@[deprecated (since := "2026-03-03")]
alias pushforwardPullbackAdjunction := pullbackPushforwardAdjunction

Depends on / 依赖: Functor, Functor.lanAdjunction, lanAdjunction
-/
def pullbackPushforwardAdjunction {X Y : TopCat.{v}} (f : X ⟶ Y) :
    pullback C f ⊣ pushforward C f :=
  Functor.lanAdjunction _ _

@[deprecated (since := "2026-03-03")]
alias pushforwardPullbackAdjunction := pullbackPushforwardAdjunction

/--
Definition of `pullbackHomIsoPushforwardInv` / `pullbackHomIsoPushforwardInv` 的定义

English:
definition pullbackHomIsoPushforwardInv
  signature: {X Y : TopCat.{v}} (H : X ≅ Y)
  body: Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction C H.hom)
    (presheafEquivOfIso C H.symm).toAdjunction

中文:
定义 pullbackHomIsoPushforwardInv
  签名: {X Y : TopCat.{v}} (H : X ≅ Y)
  定义体: Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction C H.hom)
    (presheafEquivOfIso C H.symm).toAdjunction

Depends on / 依赖: Adjunction, Adjunction.leftAdjointUniq, H.hom, H.symm, leftAdjointUniq, presheafEquivOfIso, pullbackPushforwardAdjunction, toAdjunction
-/
def pullbackHomIsoPushforwardInv {X Y : TopCat.{v}} (H : X ≅ Y) :
    pullback C H.hom ≅ pushforward C H.inv :=
  Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction C H.hom)
    (presheafEquivOfIso C H.symm).toAdjunction

/--
Definition of `pullbackInvIsoPushforwardHom` / `pullbackInvIsoPushforwardHom` 的定义

English:
definition pullbackInvIsoPushforwardHom
  signature: {X Y : TopCat.{v}} (H : X ≅ Y)
  body: Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction C H.inv)
    (presheafEquivOfIso C H).toAdjunction

中文:
定义 pullbackInvIsoPushforwardHom
  签名: {X Y : TopCat.{v}} (H : X ≅ Y)
  定义体: Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction C H.inv)
    (presheafEquivOfIso C H).toAdjunction

Depends on / 依赖: Adjunction, Adjunction.leftAdjointUniq, H.inv, leftAdjointUniq, presheafEquivOfIso, pullbackPushforwardAdjunction, toAdjunction
-/
def pullbackInvIsoPushforwardHom {X Y : TopCat.{v}} (H : X ≅ Y) :
    pullback C H.inv ≅ pushforward C H.hom :=
  Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction C H.inv)
    (presheafEquivOfIso C H).toAdjunction

variable {C}

/--
Definition of `pullbackObjObjOfImageOpen` / `pullbackObjObjOfImageOpen` 的定义

English:
definition pullbackObjObjOfImageOpen
  signature: {X Y : TopCat.{v}} (f : X ⟶ Y) (ℱ : Y.Presheaf C) (U : Opens X)
  body: by
  let x : CostructuredArrow (Opens.map f).op (op U) := CostructuredArrow.mk
    (@homOfLE _ _ _ ((Opens.map f).obj ⟨_, H⟩) (Set.image_preimage.le_u_l _)).op
  have hx : IsTerminal x :=
    { lift := fun s => by
        fapply CostructuredArrow.homMk
        · change op (unop _) ⟶ op (⟨_, H⟩ : Ope

中文:
定义 pullbackObjObjOfImageOpen
  签名: {X Y : TopCat.{v}} (f : X ⟶ Y) (ℱ : Y.Presheaf C) (U : Opens X)
  定义体: by
  let x : CostructuredArrow (Opens.map f).op (op U) := CostructuredArrow.mk
    (@homOfLE _ _ _ ((Opens.map f).obj ⟨_, H⟩) (Set.image_preimage.le_u_l _)).op
  have hx : IsTerminal x :=
    { lift := fun s => by
        fapply CostructuredArrow.homMk
        · change op (unop _) ⟶ op (⟨_, H⟩ : Ope

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, CostructuredArrow.mk, IsColimit, IsColimit.coconePointUniqueUpToIso, IsTerminal, Opens.map, Set.image_mono, Set.image_preimage.l_u_le, Set.image_preimage.le_u_l, SetLike, SetLike.coe, coconePointUniqueUpToIso, eq_iff_true_of_subsingleton, fapply, homOfLE, image_mono, image_preimage, l_u_le, le_u_l
-/
def pullbackObjObjOfImageOpen {X Y : TopCat.{v}} (f : X ⟶ Y) (ℱ : Y.Presheaf C) (U : Opens X)
    (H : IsOpen (f '' U)) : ((pullback C f).obj ℱ).obj (op U) ≅ ℱ.obj (op ⟨_, H⟩) := by
  let x : CostructuredArrow (Opens.map f).op (op U) := CostructuredArrow.mk
    (@homOfLE _ _ _ ((Opens.map f).obj ⟨_, H⟩) (Set.image_preimage.le_u_l _)).op
  have hx : IsTerminal x :=
    { lift := fun s => by
        fapply CostructuredArrow.homMk
        · change op (unop _) ⟶ op (⟨_, H⟩ : Opens _)
          refine (homOfLE ?_).op
          apply (Set.image_mono s.pt.hom.unop.le).trans
          exact Set.image_preimage.l_u_le (SetLike.coe s.pt.left.unop)
        · simp [eq_iff_true_of_subsingleton] }
  exact IsColimit.coconePointUniqueUpToIso
    ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit ℱ (op U))
    (colimitOfDiagramTerminal hx _)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pullbackObjObjOfImageOpen_hom_naturality` / 定理 `pullbackObjObjOfImageOpen_hom_naturality`

English:
theorem pullbackObjObjOfImageOpen_hom_naturality
  statement: {X Y : TopCat.{v}} (f : X ⟶ Y) (ℱ : Y.Presheaf C)
  proof: by
  dsimp [pullbackObjObjOfImageOpen]
  refine ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit ℱ (op V)).hom_ext
    (fun j => ?_)
  have eq : ((LeftExtension.mk ((Opens.map f).op.leftKanExtension ℱ)
      ((Opens.map f).op.leftKanExtensionUnit ℱ)).coconeAt
      (op V)).ι.app j ≫

中文:
定理 pullbackObjObjOfImageOpen_hom_naturality
  结论: {X Y : TopCat.{v}} (f : X ⟶ Y) (ℱ : Y.Presheaf C)
  证明: by
  dsimp [pullbackObjObjOfImageOpen]
  refine ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit ℱ (op V)).hom_ext
    (fun j => ?_)
  have eq : ((LeftExtension.mk ((Opens.map f).op.leftKanExtension ℱ)
      ((Opens.map f).op.leftKanExtensionUnit ℱ)).coconeAt
      (op V)).ι.app j ≫

Depends on / 依赖: CostructuredArrow, CostructuredArrow.map, LeftExtension, LeftExtension.mk, Opens.map, coconeAt, homOfLE, hom_ext, isPointwiseLeftKanExtensionLeftKanExtensionUnit, leftKanExtension, leftKanExtensionUnit, op.isPointwiseLeftKanExtensionLeftKanExtensionUnit, op.leftKanExtension, op.leftKanExtensionUnit, pullback, pullbackObjObjOfImageOpen
-/
theorem pullbackObjObjOfImageOpen_hom_naturality {X Y : TopCat.{v}} (f : X ⟶ Y) (ℱ : Y.Presheaf C)
    {U V : Opens X} (HU : IsOpen (f '' U)) (HV : IsOpen (f '' V)) (le : U <= V) :
    ((pullback C f).obj ℱ).map (homOfLE le).op ≫ (pullbackObjObjOfImageOpen f ℱ U HU).hom =
    (pullbackObjObjOfImageOpen f ℱ V HV).hom ≫ ℱ.map (IsOpenMap.functorMap HU HV le).op := by
  dsimp [pullbackObjObjOfImageOpen]
  refine ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit ℱ (op V)).hom_ext
    (fun j => ?_)
  have eq : ((LeftExtension.mk ((Opens.map f).op.leftKanExtension ℱ)
      ((Opens.map f).op.leftKanExtensionUnit ℱ)).coconeAt
      (op V)).ι.app j ≫ ((pullback C f).obj ℱ).map (homOfLE le).op =
      ((LeftExtension.mk ((Opens.map f).op.leftKanExtension ℱ)
      ((Opens.map f).op.leftKanExtensionUnit ℱ)).coconeAt
      (op U)).ι.app ((CostructuredArrow.map (homOfLE le).op).obj j) := by cat_disch
  rw [Limits.IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]; rw [reassoc_of% eq]; rw [Limits.IsColimit.comp_coconePointUniqueUpToIso_hom]; rw [Limits.coconeOfDiagramTerminal_ι_app]; rw [Limits.coconeOfDiagramTerminal_ι_app]
  dsimp
  rw [← Functor.map_comp]
  cat_disch

end

end TopCat.Presheaf

namespace IsOpenMap

noncomputable section

variable {C} [Limits.HasColimits C]

open TopCat.Presheaf

/--
If `f : X ⟶ Y` is an open map and `ℱ` is a presheaf on `Y`, then the pullback of `ℱ` by `f` is
isomorphic to the composition of `ℱ` and of the functor `(Open X)ᵒᵖ ⥤ (Open Y)ᵒᵖ` induced by `f`.
-/
@[simps!]
/--
Definition of `pullbackObjIso` / `pullbackObjIso` 的定义

English:
definition pullbackObjIso
  signature: {X Y : TopCat.{v}} {f : X ⟶ Y} (hf : IsOpenMap f) (ℱ : Y.Presheaf C)
  body: NatIso.ofComponents
    (fun U => pullbackObjObjOfImageOpen f ℱ U.1 (hf (unop U).1 (unop U).2))
    (fun {U V} i => (pullbackObjObjOfImageOpen_hom_naturality f ℱ (hf (unop V).1 (unop V).2)
      (hf (unop U).1 (unop U).2) (leOfHom i.unop)))

中文:
定义 pullbackObjIso
  签名: {X Y : TopCat.{v}} {f : X ⟶ Y} (hf : IsOpenMap f) (ℱ : Y.Presheaf C)
  定义体: NatIso.ofComponents
    (fun U => pullbackObjObjOfImageOpen f ℱ U.1 (hf (unop U).1 (unop U).2))
    (fun {U V} i => (pullbackObjObjOfImageOpen_hom_naturality f ℱ (hf (unop V).1 (unop V).2)
      (hf (unop U).1 (unop U).2) (leOfHom i.unop)))

Depends on / 依赖: NatIso, NatIso.ofComponents, i.unop, leOfHom, ofComponents, pullbackObjObjOfImageOpen, pullbackObjObjOfImageOpen_hom_naturality
-/
def pullbackObjIso {X Y : TopCat.{v}} {f : X ⟶ Y} (hf : IsOpenMap f) (ℱ : Y.Presheaf C) :
    (pullback C f).obj ℱ ≅ hf.functor.op ⋙ ℱ :=
  NatIso.ofComponents
    (fun U => pullbackObjObjOfImageOpen f ℱ U.1 (hf (unop U).1 (unop U).2))
    (fun {U V} i => (pullbackObjObjOfImageOpen_hom_naturality f ℱ (hf (unop V).1 (unop V).2)
      (hf (unop U).1 (unop U).2) (leOfHom i.unop)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `pullbackObjIso_hom_naturality` / 引理 `pullbackObjIso_hom_naturality`

English:
lemma pullbackObjIso_hom_naturality
  statement: {X Y : TopCat.{v}} {f : X ⟶ Y} (hf : IsOpenMap f)
  proof: by
  ext U
  dsimp [pullbackObjIso, pullbackObjObjOfImageOpen]
  refine ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit ℱ (op U)).hom_ext
    (fun j => ?_)
  have eq : ((LeftExtension.mk ((Opens.map f).op.leftKanExtension ℱ)
      ((Opens.map f).op.leftKanExtensionUnit ℱ)).coconeAt

中文:
引理 pullbackObjIso_hom_naturality
  结论: {X Y : TopCat.{v}} {f : X ⟶ Y} (hf : IsOpenMap f)
  证明: by
  ext U
  dsimp [pullbackObjIso, pullbackObjObjOfImageOpen]
  refine ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit ℱ (op U)).hom_ext
    (fun j => ?_)
  have eq : ((LeftExtension.mk ((Opens.map f).op.leftKanExtension ℱ)
      ((Opens.map f).op.leftKanExtensionUnit ℱ)).coconeAt

Depends on / 依赖: Functor, Functor.whiskerLeft, LeftExtension, LeftExtension.mk, NatTrans, NatTrans.app, Opens.map, coconeAt, hom_ext, isPointwiseLeftKanExtensionLeftKanExtensionUnit, leftKanExtension, leftKanExtensionUnit, op.isPointwiseLeftKanExtensionLeftKanExtensionUnit, op.leftKanExtension, op.leftKanExtensionUnit, pullback, pullbackObjIso, pullbackObjObjOfImageOpen, whiskerLeft
-/
lemma pullbackObjIso_hom_naturality {X Y : TopCat.{v}} {f : X ⟶ Y} (hf : IsOpenMap f)
   {ℱ 𝒢 : Y.Presheaf C} (u : ℱ ⟶ 𝒢) :
   (pullback C f).map u ≫ (hf.pullbackObjIso 𝒢).hom =
   (hf.pullbackObjIso ℱ).hom ≫ Functor.whiskerLeft hf.functor.op u := by
  ext U
  dsimp [pullbackObjIso, pullbackObjObjOfImageOpen]
  refine ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit ℱ (op U)).hom_ext
    (fun j => ?_)
  have eq : ((LeftExtension.mk ((Opens.map f).op.leftKanExtension ℱ)
      ((Opens.map f).op.leftKanExtensionUnit ℱ)).coconeAt (op U)).ι.app j
      ≫ ((pullback C f).map u).app (op U) = NatTrans.app (Functor.whiskerLeft _ u) j ≫
      ((LeftExtension.mk ((Opens.map f).op.leftKanExtension 𝒢)
      ((Opens.map f).op.leftKanExtensionUnit 𝒢)).coconeAt (op U)).ι.app j := by
    dsimp [pullback]
    simp only [Category.assoc, NatTrans.naturality]
    have := NatTrans.congr_app ((Opens.map f).op.lanUnit.naturality u) j.left
    dsimp [lanUnit] at this
    rw [reassoc_of% this]
    rfl
  rw [Limits.IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]; rw [reassoc_of% eq]; rw [Limits.IsColimit.comp_coconePointUniqueUpToIso_hom]
  dsimp
  rw [← u.naturality]
  rfl

/--
If `f : X ⟶ Y`, this is the isomorphism between the pullback functor by `f` and the
"naive" pullback given by composing presheaves with the functor `(Open X)ᵒᵖ ⥤ (Open Y)ᵒᵖ`
induced by `f`.
-/
@[simps!]
/--
Definition of `pullbackIso` / `pullbackIso` 的定义

English:
definition pullbackIso
  signature: {X Y : TopCat.{v}} {f : X ⟶ Y} (hf : IsOpenMap f)
  body: NatIso.ofComponents hf.pullbackObjIso hf.pullbackObjIso_hom_naturality

中文:
定义 pullbackIso
  签名: {X Y : TopCat.{v}} {f : X ⟶ Y} (hf : IsOpenMap f)
  定义体: NatIso.ofComponents hf.pullbackObjIso hf.pullbackObjIso_hom_naturality

Depends on / 依赖: NatIso, NatIso.ofComponents, hf.pullbackObjIso, hf.pullbackObjIso_hom_naturality, ofComponents, pullbackObjIso, pullbackObjIso_hom_naturality
-/
def pullbackIso {X Y : TopCat.{v}} {f : X ⟶ Y} (hf : IsOpenMap f) :
    pullback C f ≅ (Functor.whiskeringLeft _ _ _).obj hf.functor.op :=
  NatIso.ofComponents hf.pullbackObjIso hf.pullbackObjIso_hom_naturality

end

end IsOpenMap
