/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplexCategory.Truncated
public import Mathlib.CategoryTheory.Category.ReflQuiv
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Category.Cat.Terminal

/-!

# The homotopy category of a simplicial set

The homotopy category of a simplicial set is defined as a quotient of the free category on its
underlying reflexive quiver (equivalently its one truncation). The quotient imposes an additional
hom relation on this free category, asserting that `f ≫ g = h` whenever `f`, `g`, and `h` are
respectively the 2nd, 0th, and 1st faces of a 2-simplex.

In fact, the associated functor

`SSet.hoFunctor : SSet.{u} ⥤ Cat.{u, u} := SSet.truncation 2 ⋙ SSet.hoFunctor₂`

is defined by first restricting from simplicial sets to 2-truncated simplicial sets (throwing away
the data that is not used for the construction of the homotopy category) and then composing with an
analogously defined `SSet.hoFunctor₂ : SSet.Truncated.{u} 2 ⥤ Cat.{u,u}` implemented relative to
the syntax of the 2-truncated simplex category.

In the file `Mathlib/AlgebraicTopology/SimplicialSet/NerveAdjunction.lean` we show the functor
`SSet.hoFunctor` to be left adjoint to the nerve by providing an analogous decomposition of the
nerve functor, made by possible by the fact that nerves of categories are 2-coskeletal, and then
composing a pair of adjunctions, which factor through the category of 2-truncated simplicial sets.
-/

@[expose] public section

namespace SSet
open CategoryTheory Category Limits Functor Opposite Simplicial Nerve
open SimplexCategory.Truncated SimplicialObject.Truncated

universe v u

/--
Definition of `OneTruncation₂` / `OneTruncation₂` 的定义

English:
definition OneTruncation₂
  signature: (S : SSet.Truncated 2)
  body: S _⦋0⦌₂

中文:
定义 OneTruncation₂
  签名: (S : SSet.Truncated 2)
  定义体: S _⦋0⦌₂
-/
def OneTruncation₂ (S : SSet.Truncated 2) := S _⦋0⦌₂

namespace OneTruncation₂

/-- A 2-truncated simplicial set `S` has an underlying refl quiver `SSet.OneTruncation₂ S`. -/
@[simps -isSimp]
/--
Instance `reflQuiver` / 实例 `reflQuiver`

English:
instance reflQuiver
  signature: (S : SSet.Truncated 2)
  body: Truncated.Edge
  id := Truncated.Edge.id

@[ext]

中文:
实例 reflQuiver
  签名: (S : SSet.Truncated 2)
  定义体: Truncated.Edge
  id := Truncated.Edge.id

@[ext]

Depends on / 依赖: Truncated, Truncated.Edge
-/
instance reflQuiver (S : SSet.Truncated 2) : ReflQuiver (OneTruncation₂ S) where
  Hom := Truncated.Edge
  id := Truncated.Edge.id

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  proof: Truncated.Edge.ext h

中文:
引理 hom_ext
  证明: Truncated.Edge.ext h

Depends on / 依赖: Truncated, Truncated.Edge.ext
-/
lemma hom_ext
    {S : SSet.Truncated 2} {x y : OneTruncation₂ S} {f g : x ⟶ y}
    (h : f.edge = g.edge) : f = g :=
  Truncated.Edge.ext h

set_option backward.isDefEq.respectTransparency.types false in
/-- The prefunctor on refl quivers `OneTruncation₂` induced by a morphism
of `2`-truncated simplicial sets. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {S T : SSet.Truncated 2} (f : S ⟶ T)
  body: f.app _ x
  map e := e.map f
  map_id x := by ext; simp [← NatTrans.naturality_apply, reflQuiver_id]

中文:
定义 map
  签名: {S T : SSet.Truncated 2} (f : S ⟶ T)
  定义体: f.app _ x
  map e := e.map f
  map_id x := by ext; simp [← NatTrans.naturality_apply, reflQuiver_id]

Depends on / 依赖: f.app
-/
def map {S T : SSet.Truncated 2} (f : S ⟶ T) :
    OneTruncation₂ S ⥤rq OneTruncation₂ T where
  obj x := f.app _ x
  map e := e.map f
  map_id x := by ext; simp [← NatTrans.naturality_apply, reflQuiver_id]

end OneTruncation₂

/-- The functor that carries a 2-truncated simplicial set to its underlying refl quiver. -/
@[simps]
/--
Definition of `oneTruncation₂` / `oneTruncation₂` 的定义

English:
definition oneTruncation₂
  signature: : SSet.Truncated.{u} 2 ⥤ ReflQuiv.{u, u} where
  body: ReflQuiv.of (OneTruncation₂ S)
  map f := OneTruncation₂.map f

中文:
定义 oneTruncation₂
  签名: : SSet.Truncated.{u} 2 ⥤ ReflQuiv.{u, u} where
  定义体: ReflQuiv.of (OneTruncation₂ S)
  map f := OneTruncation₂.map f

Depends on / 依赖: ReflQuiv, ReflQuiv.of
-/
def oneTruncation₂ : SSet.Truncated.{u} 2 ⥤ ReflQuiv.{u, u} where
  obj S := ReflQuiv.of (OneTruncation₂ S)
  map f := OneTruncation₂.map f

namespace OneTruncation₂

@[simp]
/--
lemma `homOfEq_edge` / 引理 `homOfEq_edge`

English:
lemma homOfEq_edge
  proof: by
  subst hx hy
  rfl

中文:
引理 homOfEq_edge
  证明: by
  subst hx hy
  rfl
-/
lemma homOfEq_edge
    {X : SSet.Truncated.{u} 2} {x₁ y₁ x₂ y₂ : OneTruncation₂ X}
    (f : x₁ ⟶ y₁) (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Quiver.homOfEq f hx hy).edge = f.edge := by
  subst hx hy
  rfl

section
variable {C : Type u} [Category.{v} C]

/-- An equivalence between the type of objects underlying a category and the type of 0-simplices in
the 2-truncated nerve. -/
@[simps! -isSimp]
/--
Definition of `nerveEquiv` / `nerveEquiv` 的定义

English:
definition nerveEquiv
  signature: : OneTruncation₂ ((SSet.truncation 2).obj (nerve C)) ≃ C
  body: CategoryTheory.nerveEquiv

中文:
定义 nerveEquiv
  签名: : OneTruncation₂ ((SSet.truncation 2).obj (nerve C)) ≃ C
  定义体: CategoryTheory.nerveEquiv

Depends on / 依赖: CategoryTheory, CategoryTheory.nerveEquiv, nerveEquiv
-/
def nerveEquiv : OneTruncation₂ ((SSet.truncation 2).obj (nerve C)) ≃ C :=
  CategoryTheory.nerveEquiv

/--
Definition of `nerveHomEquiv` / `nerveHomEquiv` 的定义

English:
definition nerveHomEquiv
  signature: {X Y : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))}
  body: nerve.homEquiv

中文:
定义 nerveHomEquiv
  签名: {X Y : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))}
  定义体: nerve.homEquiv

Depends on / 依赖: homEquiv, nerve.homEquiv
-/
def nerveHomEquiv {X Y : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))} :
    (X ⟶ Y) ≃ (nerveEquiv X ⟶ nerveEquiv Y) :=
  nerve.homEquiv

/--
lemma `nerveHomEquiv_apply` / 引理 `nerveHomEquiv_apply`

English:
lemma nerveHomEquiv_apply
  statement: {X Y : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))}
  proof: rfl

@[simp]

中文:
引理 nerveHomEquiv_apply
  结论: {X Y : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))}
  证明: rfl

@[simp]
-/
lemma nerveHomEquiv_apply {X Y : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))}
    (f : X ⟶ Y) :
    nerveHomEquiv f = eqToHom (congr_arg ComposableArrows.left f.src_eq.symm) ≫
      f.edge.hom ≫ eqToHom (congr_arg ComposableArrows.left f.tgt_eq) :=
  rfl

@[simp]
/--
lemma `nerveHomEquiv_id` / 引理 `nerveHomEquiv_id`

English:
lemma nerveHomEquiv_id
  given: (X : OneTruncation₂ ((SSet.truncation 2).obj (nerve C)))
  proof: nerve.homEquiv_id _

中文:
引理 nerveHomEquiv_id
  条件: (X : OneTruncation₂ ((SSet.truncation 2).obj (nerve C)))
  证明: nerve.homEquiv_id _

Depends on / 依赖: homEquiv_id, nerve.homEquiv_id
-/
lemma nerveHomEquiv_id (X : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))) :
    nerveHomEquiv (𝟙rq X) = 𝟙 _ :=
  nerve.homEquiv_id _

/--
Definition of `ofNerve₂` / `ofNerve₂` 的定义

English:
definition ofNerve₂
  signature: (C : Type u) [Category.{u} C]
  body: ReflQuiv.isoOfEquiv.{u, u} OneTruncation₂.nerveEquiv
    (fun _ _ => OneTruncation₂.nerveHomEquiv) nerveHomEquiv_id

中文:
定义 ofNerve₂
  签名: (C : 类型u) [范畴.{u} C]
  定义体: ReflQuiv.isoOfEquiv.{u, u} OneTruncation₂.nerveEquiv
    (fun _ _ => OneTruncation₂.nerveHomEquiv) nerveHomEquiv_id

Depends on / 依赖: ReflQuiv, ReflQuiv.isoOfEquiv, isoOfEquiv, nerveEquiv, nerveHomEquiv, nerveHomEquiv_id
-/
def ofNerve₂ (C : Type u) [Category.{u} C] :
    ReflQuiv.of (OneTruncation₂ ((truncation 2).obj (nerve C))) ≅ ReflQuiv.of C :=
  ReflQuiv.isoOfEquiv.{u, u} OneTruncation₂.nerveEquiv
    (fun _ _ => OneTruncation₂.nerveHomEquiv) nerveHomEquiv_id

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `nerve_hom_ext` / 引理 `nerve_hom_ext`

English:
lemma nerve_hom_ext
  statement: {X : (SSet.Truncated 2)} {C : Type u} [Category.{u} C]
  proof: SSet.Truncated.IsStrictSegal.hom_ext (fun f => by
    obtain ⟨x₀, x₁, f, rfl⟩ := Truncated.Edge.exists_of_simplex f
    simpa using congr_arg Truncated.Edge.edge (ReflPrefunctor.congr_hom h f))

中文:
引理 nerve_hom_ext
  结论: {X : (SSet.Truncated 2)} {C : 类型u} [范畴.{u} C]
  证明: SSet.Truncated.IsStrictSegal.hom_ext (fun f => by
    obtain ⟨x₀, x₁, f, rfl⟩ := Truncated.Edge.exists_of_simplex f
    simpa using congr_arg Truncated.Edge.edge (ReflPrefunctor.congr_hom h f))

Depends on / 依赖: IsStrictSegal, ReflPrefunctor, ReflPrefunctor.congr_hom, SSet.Truncated.IsStrictSegal.hom_ext, Truncated, Truncated.Edge.edge, Truncated.Edge.exists_of_simplex, congr_arg, congr_hom, exists_of_simplex, hom_ext
-/
lemma nerve_hom_ext {X : (SSet.Truncated 2)} {C : Type u} [Category.{u} C]
    {F G : X ⟶ ((truncation 2).obj (nerve C))}
    (h : OneTruncation₂.map F = OneTruncation₂.map G) : F = G :=
  SSet.Truncated.IsStrictSegal.hom_ext (fun f => by
    obtain ⟨x₀, x₁, f, rfl⟩ := Truncated.Edge.exists_of_simplex f
    simpa using congr_arg Truncated.Edge.edge (ReflPrefunctor.congr_hom h f))

end
end OneTruncation₂

set_option backward.isDefEq.respectTransparency false in
/-- The refl quiver underlying a nerve is naturally isomorphic to the refl quiver underlying the
category. -/
@[simps! hom_app_obj hom_app_map inv_app_obj_obj inv_app_obj_map inv_app_map]
/--
Definition of `OneTruncation₂.ofNerve₂.natIso` / `OneTruncation₂.ofNerve₂.natIso` 的定义

English:
definition OneTruncation₂.ofNerve₂.natIso
  signature: :
  body: NatIso.ofComponents (fun C => OneTruncation₂.ofNerve₂ C)
    (fun F => ReflPrefunctor.ext (by cat_disch) (fun x y f => by
      obtain ⟨f, rfl, rfl⟩ := f
      dsimp [ofNerve₂, ReflQuiv.isoOfEquiv, ReflQuiv.isoOfQuivIso,
        Quiv.isoOfEquiv, nerveHomEquiv_apply]
      simp only [comp_id, id_comp

中文:
定义 OneTruncation₂.ofNerve₂.natIso
  签名: :
  定义体: NatIso.ofComponents (fun C => OneTruncation₂.ofNerve₂ C)
    (fun F => ReflPrefunctor.ext (by cat_disch) (fun x y f => by
      obtain ⟨f, rfl, rfl⟩ := f
      dsimp [ofNerve₂, ReflQuiv.isoOfEquiv, ReflQuiv.isoOfQuivIso,
        Quiv.isoOfEquiv, nerveHomEquiv_apply]
      simp only [comp_id, id_comp

Depends on / 依赖: NatIso, NatIso.ofComponents, Quiv.isoOfEquiv, ReflPrefunctor, ReflPrefunctor.ext, ReflQuiv, ReflQuiv.isoOfEquiv, ReflQuiv.isoOfQuivIso, cat_disch, comp_id, id_comp, isoOfEquiv, isoOfQuivIso, nerveHomEquiv_apply, ofComponents
-/
def OneTruncation₂.ofNerve₂.natIso :
    nerveFunctor₂.{u, u} ⋙ SSet.oneTruncation₂ ≅ ReflQuiv.forget :=
  NatIso.ofComponents (fun C => OneTruncation₂.ofNerve₂ C)
    (fun F => ReflPrefunctor.ext (by cat_disch) (fun x y f => by
      obtain ⟨f, rfl, rfl⟩ := f
      dsimp [ofNerve₂, ReflQuiv.isoOfEquiv, ReflQuiv.isoOfQuivIso,
        Quiv.isoOfEquiv, nerveHomEquiv_apply]
      simp only [comp_id, id_comp]
      rfl))

set_option backward.privateInPublic true in
/--
lemma `map_map_of_eq.` / 引理 `map_map_of_eq.`

English:
lemma map_map_of_eq.{w}
  statement: {C : Type u} [Category.{v} C] (V : Cᵒᵖ ⥤ Type w) {X Y Z : C}
  proof: by
  rintro rfl
  simp

中文:
引理 map_map_of_eq.{w}
  结论: {C : 类型u} [范畴.{v} C] (V : Cᵒᵖ ⥤ 类型 w) {X Y Z : C}
  证明: by
  rintro rfl
  simp
-/
private lemma map_map_of_eq.{w} {C : Type u} [Category.{v} C] (V : Cᵒᵖ ⥤ Type w) {X Y Z : C}
    {α : X ⟶ Y} {β : Y ⟶ Z} {γ : X ⟶ Z} {φ} :
    α ≫ β = γ -> V.map α.op (V.map β.op φ) = V.map γ.op φ := by
  rintro rfl
  simp

namespace Truncated

/--
Definition of `ι0₂` / `ι0₂` 的定义

English:
definition ι0₂
  signature: : ⦋0⦌₂ ⟶ ⦋2⦌₂
  body: δ₂ (n := 0) 1 ≫ δ₂ (n := 1) 1

中文:
定义 ι0₂
  签名: : ⦋0⦌₂ ⟶ ⦋2⦌₂
  定义体: δ₂ (n := 0) 1 ≫ δ₂ (n := 1) 1
-/
def ι0₂ : ⦋0⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 0) 1 ≫ δ₂ (n := 1) 1

/--
Definition of `ι1₂` / `ι1₂` 的定义

English:
definition ι1₂
  signature: : ⦋0⦌₂ ⟶ ⦋2⦌₂
  body: δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 2

中文:
定义 ι1₂
  签名: : ⦋0⦌₂ ⟶ ⦋2⦌₂
  定义体: δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 2
-/
def ι1₂ : ⦋0⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 2

/--
Definition of `ι2₂` / `ι2₂` 的定义

English:
definition ι2₂
  signature: : ⦋0⦌₂ ⟶ ⦋2⦌₂
  body: δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 1

中文:
定义 ι2₂
  签名: : ⦋0⦌₂ ⟶ ⦋2⦌₂
  定义体: δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 1
-/
def ι2₂ : ⦋0⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 1

/--
Definition of `ev0₂` / `ev0₂` 的定义

English:
definition ev0₂
  signature: {V : SSet.Truncated 2} (φ : V _⦋2⦌₂)
  body: V.map ι0₂.op φ

中文:
定义 ev0₂
  签名: {V : SSet.Truncated 2} (φ : V _⦋2⦌₂)
  定义体: V.map ι0₂.op φ

Depends on / 依赖: V.map
-/
def ev0₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : OneTruncation₂ V := V.map ι0₂.op φ

/--
Definition of `ev1₂` / `ev1₂` 的定义

English:
definition ev1₂
  signature: {V : SSet.Truncated 2} (φ : V _⦋2⦌₂)
  body: V.map ι1₂.op φ

中文:
定义 ev1₂
  签名: {V : SSet.Truncated 2} (φ : V _⦋2⦌₂)
  定义体: V.map ι1₂.op φ

Depends on / 依赖: V.map
-/
def ev1₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : OneTruncation₂ V := V.map ι1₂.op φ

/--
Definition of `ev2₂` / `ev2₂` 的定义

English:
definition ev2₂
  signature: {V : SSet.Truncated 2} (φ : V _⦋2⦌₂)
  body: V.map ι2₂.op φ

中文:
定义 ev2₂
  签名: {V : SSet.Truncated 2} (φ : V _⦋2⦌₂)
  定义体: V.map ι2₂.op φ

Depends on / 依赖: V.map
-/
def ev2₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : OneTruncation₂ V := V.map ι2₂.op φ

/--
Definition of `δ0₂` / `δ0₂` 的定义

English:
definition δ0₂
  signature: : ⦋1⦌₂ ⟶ ⦋2⦌₂
  body: δ₂ (n := 1) 0

中文:
定义 δ0₂
  签名: : ⦋1⦌₂ ⟶ ⦋2⦌₂
  定义体: δ₂ (n := 1) 0
-/
def δ0₂ : ⦋1⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 1) 0

/--
Definition of `δ1₂` / `δ1₂` 的定义

English:
definition δ1₂
  signature: : ⦋1⦌₂ ⟶ ⦋2⦌₂
  body: δ₂ (n := 1) 1

中文:
定义 δ1₂
  签名: : ⦋1⦌₂ ⟶ ⦋2⦌₂
  定义体: δ₂ (n := 1) 1
-/
def δ1₂ : ⦋1⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 1) 1

/--
Definition of `δ2₂` / `δ2₂` 的定义

English:
definition δ2₂
  signature: : ⦋1⦌₂ ⟶ ⦋2⦌₂
  body: δ₂ (n := 1) 2

中文:
定义 δ2₂
  签名: : ⦋1⦌₂ ⟶ ⦋2⦌₂
  定义体: δ₂ (n := 1) 2
-/
def δ2₂ : ⦋1⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 1) 2

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `ev12₂` / `ev12₂` 的定义

English:
definition ev12₂
  signature: {V : SSet.Truncated 2} (φ : V _⦋2⦌₂)
  body: ⟨V.map δ0₂.op φ,
    map_map_of_eq V (InducedCategory.hom_ext
      (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm),
    map_map_of_eq V rfl⟩

中文:
定义 ev12₂
  签名: {V : SSet.Truncated 2} (φ : V _⦋2⦌₂)
  定义体: ⟨V.map δ0₂.op φ,
    map_map_of_eq V (InducedCategory.hom_ext
      (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm),
    map_map_of_eq V rfl⟩

Depends on / 依赖: InducedCategory, InducedCategory.hom_ext, SimplexCategory, V.map, hom_ext, map_map_of_eq
-/
def ev12₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : ev1₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ0₂.op φ,
    map_map_of_eq V (InducedCategory.hom_ext
      (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm),
    map_map_of_eq V rfl⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `ev02₂` / `ev02₂` 的定义

English:
definition ev02₂
  signature: {V : SSet.Truncated 2} (φ : V _⦋2⦌₂)
  body: ⟨V.map δ1₂.op φ, map_map_of_eq V rfl, map_map_of_eq V rfl⟩

中文:
定义 ev02₂
  签名: {V : SSet.Truncated 2} (φ : V _⦋2⦌₂)
  定义体: ⟨V.map δ1₂.op φ, map_map_of_eq V rfl, map_map_of_eq V rfl⟩

Depends on / 依赖: V.map, map_map_of_eq
-/
def ev02₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : ev0₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ1₂.op φ, map_map_of_eq V rfl, map_map_of_eq V rfl⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `ev01₂` / `ev01₂` 的定义

English:
definition ev01₂
  signature: {V : SSet.Truncated 2} (φ : V _⦋2⦌₂)
  body: ⟨V.map δ2₂.op φ,
    map_map_of_eq V (InducedCategory.hom_ext (SimplexCategory.δ_comp_δ (j := 1) le_rfl)),
    map_map_of_eq V rfl⟩

中文:
定义 ev01₂
  签名: {V : SSet.Truncated 2} (φ : V _⦋2⦌₂)
  定义体: ⟨V.map δ2₂.op φ,
    map_map_of_eq V (InducedCategory.hom_ext (SimplexCategory.δ_comp_δ (j := 1) le_rfl)),
    map_map_of_eq V rfl⟩

Depends on / 依赖: InducedCategory, InducedCategory.hom_ext, SimplexCategory, V.map, hom_ext, le_rfl, map_map_of_eq
-/
def ev01₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : ev0₂ φ ⟶ ev1₂ φ :=
  ⟨V.map δ2₂.op φ,
    map_map_of_eq V (InducedCategory.hom_ext (SimplexCategory.δ_comp_δ (j := 1) le_rfl)),
    map_map_of_eq V rfl⟩

end Truncated

namespace OneTruncation₂

variable (V : SSet.Truncated.{u} 2)

/--
Inductive type `HoRel₂` / 归纳类型 `HoRel₂`

English:
inductive HoRel₂
  parameters: : HomRel (Cat.FreeRefl (OneTruncation₂ V)) where
  constructors (1):
    - of_compStruct: {x₀ x₁ x₂ : V _⦋0⦌₂} {e₀₁ : Truncated.Edge x₀ x₁} {e₁₂ : Truncated.Edge x₁ x₂} {e₀₂ : Truncated.Edge x₀ x₂} (h : Truncated.Edge.CompStruct e₀₁ e₁₂ e₀₂) : HoRel₂ ((Cat.FreeRefl.quotientFunctor (OneTruncation₂ V)).map (Quiver.Hom.toPath e₀₁ ≫ Quiver.Hom.toPath e₁₂)) ((Cat.FreeRefl.quotientFunctor (OneTruncation₂ V)).map (Quiver.Hom.toPath e₀₂))

中文:
归纳类型 HoRel₂
  参数: : HomRel (Cat.FreeRefl (OneTruncation₂ V)) where
  构造子 (1 个):
    - of_compStruct: {x₀ x₁ x₂ : V _⦋0⦌₂} {e₀₁ : Truncated.边 x₀ x₁} {e₁₂ : Truncated.边 x₁ x₂} {e₀₂ : Truncated.边 x₀ x₂} (h : Truncated.边.余mpStruct e₀₁ e₁₂ e₀₂) : HoRel₂ ((Cat.FreeRefl.quotientFunctor (OneTruncation₂ V)).map (箭图.态射.toPath e₀₁ ≫ 箭图.态射.toPath e₁₂)) ((Cat.FreeRefl.quotientFunctor (OneTruncation₂ V)).map (箭图.态射.toPath e₀₂))
-/
inductive HoRel₂ : HomRel (Cat.FreeRefl (OneTruncation₂ V)) where
  | of_compStruct {x₀ x₁ x₂ : V _⦋0⦌₂} {e₀₁ : Truncated.Edge x₀ x₁}
    {e₁₂ : Truncated.Edge x₁ x₂} {e₀₂ : Truncated.Edge x₀ x₂}
    (h : Truncated.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    HoRel₂
      ((Cat.FreeRefl.quotientFunctor (OneTruncation₂ V)).map
        (Quiver.Hom.toPath e₀₁ ≫ Quiver.Hom.toPath e₁₂))
      ((Cat.FreeRefl.quotientFunctor (OneTruncation₂ V)).map (Quiver.Hom.toPath e₀₂))

end OneTruncation₂

namespace Truncated

variable (V W : SSet.Truncated.{u} 2)

/--
Definition of `HomotopyCategory` / `HomotopyCategory` 的定义

English:
definition HomotopyCategory
  signature: : Type u
  body: Quotient (OneTruncation₂.HoRel₂ V)
  deriving Category.{u}

中文:
定义 HomotopyCategory
  签名: : 类型u
  定义体: Quotient (OneTruncation₂.HoRel₂ V)
  deriving Category.{u}

Depends on / 依赖: Quotient
-/
def HomotopyCategory : Type u :=
  Quotient (OneTruncation₂.HoRel₂ V)
  deriving Category.{u}

namespace HomotopyCategory

/--
Definition of `quotientFunctor` / `quotientFunctor` 的定义

English:
definition quotientFunctor
  signature: :
  body: Quotient.functor _

中文:
定义 quotientFunctor
  签名: :
  定义体: Quotient.functor _

Depends on / 依赖: Quotient, Quotient.functor, functor
-/
def quotientFunctor :
    Cat.FreeRefl (OneTruncation₂ V) ⥤ V.HomotopyCategory :=
  Quotient.functor _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quotientFunctor V).Full
  body: Quotient.full_functor _

中文:
实例 :
  签名: (quotientFunctor V).满
  定义体: Quotient.full_functor _

Depends on / 依赖: Quotient, Quotient.full_functor, full_functor
-/
instance : (quotientFunctor V).Full :=
  Quotient.full_functor _

variable {V}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x : V _⦋0⦌₂)
  body: (quotientFunctor V).obj (.mk x)

中文:
定义 mk
  签名: (x : V _⦋0⦌₂)
  定义体: (quotientFunctor V).obj (.mk x)

Depends on / 依赖: quotientFunctor
-/
def mk (x : V _⦋0⦌₂) : V.HomotopyCategory :=
  (quotientFunctor V).obj (.mk x)

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  statement: Function.Surjective (mk (V := V))
  proof: by
  rintro ⟨⟨x⟩⟩
  exact ⟨x, rfl⟩

中文:
引理 mk_surjective
  结论: 函数.满射 (mk (V := V))
  证明: by
  rintro ⟨⟨x⟩⟩
  exact ⟨x, rfl⟩
-/
lemma mk_surjective : Function.Surjective (mk (V := V)) := by
  rintro ⟨⟨x⟩⟩
  exact ⟨x, rfl⟩

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {x y : V.HomotopyCategory} (h : x.as.as = y.as.as)
  statement: x = y
  proof: by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  obtain rfl : x = y := h
  rfl

@[elab_as_elim, cases_eliminator]

中文:
引理 ext
  条件: {x y : V.HomotopyCategory} (h : x.as.as = y.as.as)
  结论: x = y
  证明: by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  obtain rfl : x = y := h
  rfl

@[elab_as_elim, cases_eliminator]

Depends on / 依赖: mk_surjective, x.mk_surjective, y.mk_surjective
-/
lemma ext {x y : V.HomotopyCategory} (h : x.as.as = y.as.as) : x = y := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  obtain rfl : x = y := h
  rfl

@[elab_as_elim, cases_eliminator]
/--
lemma `cases_on` / 引理 `cases_on`

English:
lemma cases_on
  statement: {motive : V.HomotopyCategory -> Prop}
  proof: by
  obtain ⟨x', rfl⟩ := mk_surjective x
  exact h x'

中文:
引理 cases_on
  结论: {motive : V.HomotopyCategory -> 命题}
  证明: by
  obtain ⟨x', rfl⟩ := mk_surjective x
  exact h x'
-/
protected lemma cases_on {motive : V.HomotopyCategory -> Prop}
    (h : forall (x : V _⦋0⦌₂), motive (.mk x))
    (x : V.HomotopyCategory) :
    motive x := by
  obtain ⟨x', rfl⟩ := mk_surjective x
  exact h x'

/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {x₀ x₁ : V _⦋0⦌₂} (e : Edge x₀ x₁)
  body: (quotientFunctor V).map (Cat.FreeRefl.homMk e)

中文:
定义 homMk
  签名: {x₀ x₁ : V _⦋0⦌₂} (e : 边 x₀ x₁)
  定义体: (quotientFunctor V).map (Cat.FreeRefl.homMk e)

Depends on / 依赖: Cat.FreeRefl.homMk, FreeRefl, quotientFunctor
-/
def homMk {x₀ x₁ : V _⦋0⦌₂} (e : Edge x₀ x₁) : mk x₀ ⟶ mk x₁ :=
  (quotientFunctor V).map (Cat.FreeRefl.homMk e)

/--
lemma `congr_arrowMk_homMk` / 引理 `congr_arrowMk_homMk`

English:
lemma congr_arrowMk_homMk
  statement: {x₀ x₁ : V _⦋0⦌₂} (e : Edge x₀ x₁)
  proof: by
  obtain rfl : x₀ = y₀ := by rw [← e.src_eq, ← e'.src_eq, h]
  obtain rfl : x₁ = y₁ := by rw [← e.tgt_eq, ← e'.tgt_eq, h]
  obtain rfl : e = e' := by aesop
  rfl

中文:
引理 congr_arrowMk_homMk
  结论: {x₀ x₁ : V _⦋0⦌₂} (e : 边 x₀ x₁)
  证明: by
  obtain rfl : x₀ = y₀ := by rw [← e.src_eq, ← e'.src_eq, h]
  obtain rfl : x₁ = y₁ := by rw [← e.tgt_eq, ← e'.tgt_eq, h]
  obtain rfl : e = e' := by aesop
  rfl

Depends on / 依赖: e.src_eq, e.tgt_eq, src_eq, tgt_eq
-/
lemma congr_arrowMk_homMk {x₀ x₁ : V _⦋0⦌₂} (e : Edge x₀ x₁)
    {y₀ y₁ : V _⦋0⦌₂} (e' : Edge y₀ y₁) (h : e.edge = e'.edge) :
    Arrow.mk (homMk e) = Arrow.mk (homMk e') := by
  obtain rfl : x₀ = y₀ := by rw [← e.src_eq, ← e'.src_eq, h]
  obtain rfl : x₁ = y₁ := by rw [← e.tgt_eq, ← e'.tgt_eq, h]
  obtain rfl : e = e' := by aesop
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `homMk_id` / 引理 `homMk_id`

English:
lemma homMk_id
  given: (x : V _⦋0⦌₂)
  proof: by
  rw [homMk]; rw [← OneTruncation₂.reflQuiver_id]; rw [Cat.FreeRefl.homMk_id]; rw [CategoryTheory.Functor.map_id]
  rfl

@[reassoc]

中文:
引理 homMk_id
  条件: (x : V _⦋0⦌₂)
  证明: by
  rw [homMk]; rw [← OneTruncation₂.reflQuiver_id]; rw [Cat.FreeRefl.homMk_id]; rw [CategoryTheory.Functor.map_id]
  rfl

@[reassoc]

Depends on / 依赖: Cat.FreeRefl.homMk_id, CategoryTheory, CategoryTheory.Functor.map_id, FreeRefl, Functor, homMk_id, map_id, reflQuiver_id
-/
lemma homMk_id (x : V _⦋0⦌₂) :
    homMk (.id x) = 𝟙 (mk x) := by
  rw [homMk]; rw [← OneTruncation₂.reflQuiver_id]; rw [Cat.FreeRefl.homMk_id]; rw [CategoryTheory.Functor.map_id]
  rfl

@[reassoc]
/--
lemma `homMk_comp_homMk` / 引理 `homMk_comp_homMk`

English:
lemma homMk_comp_homMk
  statement: {x₀ x₁ x₂ : V _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂}
  proof: by
  simpa [homMk] using! CategoryTheory.Quotient.sound _
    (OneTruncation₂.HoRel₂.of_compStruct h)

中文:
引理 homMk_comp_homMk
  结论: {x₀ x₁ x₂ : V _⦋0⦌₂} {e₀₁ : 边 x₀ x₁} {e₁₂ : 边 x₁ x₂}
  证明: by
  simpa [homMk] using! CategoryTheory.Quotient.sound _
    (OneTruncation₂.HoRel₂.of_compStruct h)

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.sound, Quotient, of_compStruct, one_lt_two, zero_lt_one
-/
lemma homMk_comp_homMk {x₀ x₁ x₂ : V _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂}
    {e₀₂ : Edge x₀ x₂} (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    homMk e₀₁ ≫ homMk e₁₂ = homMk e₀₂ := by
  simpa [homMk] using! CategoryTheory.Quotient.sound _
    (OneTruncation₂.HoRel₂.of_compStruct h)

variable (V) in
/--
Definition of `morphismPropertyHomMk` / `morphismPropertyHomMk` 的定义

English:
definition morphismPropertyHomMk
  signature: : MorphismProperty V.HomotopyCategory
  body: .ofHoms (fun (e : Σ (x y : V _⦋0⦌₂), Edge x y) => homMk e.2.2)

中文:
定义 morphismPropertyHomMk
  签名: : MorphismProperty V.HomotopyCategory
  定义体: .ofHoms (fun (e : Σ (x y : V _⦋0⦌₂), Edge x y) => homMk e.2.2)

Depends on / 依赖: ofHoms
-/
def morphismPropertyHomMk : MorphismProperty V.HomotopyCategory :=
  .ofHoms (fun (e : Σ (x y : V _⦋0⦌₂), Edge x y) => homMk e.2.2)

/--
lemma `morphismPropertyHomMk_of_edge` / 引理 `morphismPropertyHomMk_of_edge`

English:
lemma morphismPropertyHomMk_of_edge
  given: {x y : V _⦋0⦌₂} (e : Edge x y)
  proof: by
  dsimp only [morphismPropertyHomMk]
  rw [MorphismProperty.ofHoms_iff]
  exact ⟨⟨x, y, e⟩, rfl⟩

中文:
引理 morphismPropertyHomMk_of_edge
  条件: {x y : V _⦋0⦌₂} (e : 边 x y)
  证明: by
  dsimp only [morphismPropertyHomMk]
  rw [MorphismProperty.ofHoms_iff]
  exact ⟨⟨x, y, e⟩, rfl⟩

Depends on / 依赖: MorphismProperty, MorphismProperty.ofHoms_iff, morphismPropertyHomMk, ofHoms_iff
-/
lemma morphismPropertyHomMk_of_edge {x y : V _⦋0⦌₂} (e : Edge x y) :
    morphismPropertyHomMk V (homMk e) := by
  dsimp only [morphismPropertyHomMk]
  rw [MorphismProperty.ofHoms_iff]
  exact ⟨⟨x, y, e⟩, rfl⟩

/--
lemma `morphismPropertyHomMk_eq_strictMap` / 引理 `morphismPropertyHomMk_eq_strictMap`

English:
lemma morphismPropertyHomMk_eq_strictMap
  proof: by
  ext _ _ f
  constructor
  · rintro ⟨_⟩
    exact MorphismProperty.map_mem_strictMap _ _ _ ⟨_⟩
  · rintro ⟨⟨_, _, e⟩⟩
    exact morphismPropertyHomMk_of_edge e

中文:
引理 morphismPropertyHomMk_eq_strictMap
  证明: by
  ext _ _ f
  constructor
  · rintro ⟨_⟩
    exact MorphismProperty.map_mem_strictMap _ _ _ ⟨_⟩
  · rintro ⟨⟨_, _, e⟩⟩
    exact morphismPropertyHomMk_of_edge e

Depends on / 依赖: MorphismProperty, MorphismProperty.map_mem_strictMap, map_mem_strictMap, morphismPropertyHomMk_of_edge
-/
lemma morphismPropertyHomMk_eq_strictMap :
    morphismPropertyHomMk V =
      (Cat.FreeRefl.morphismPropertyHomMk (OneTruncation₂ V)).strictMap (quotientFunctor V) := by
  ext _ _ f
  constructor
  · rintro ⟨_⟩
    exact MorphismProperty.map_mem_strictMap _ _ _ ⟨_⟩
  · rintro ⟨⟨_, _, e⟩⟩
    exact morphismPropertyHomMk_of_edge e

open MorphismProperty in
/--
lemma `multiplicativeClosure_morphismPropertyHomMk` / 引理 `multiplicativeClosure_morphismPropertyHomMk`

English:
lemma multiplicativeClosure_morphismPropertyHomMk
  proof: le_antisymm (by simp) (fun x y f _ => by
    obtain ⟨f, rfl⟩ := (quotientFunctor _).map_surjective f
    rw [morphismPropertyHomMk_eq_strictMap]
    refine strictMap_multiplicativeClosure_le _ _ _ ?_
    rw [Cat.FreeRefl.multiplicativeClosure_morphismPropertyHomMk]
    exact map_mem_strictMap _ _ _ 

中文:
引理 multiplicativeClosure_morphismPropertyHomMk
  证明: le_antisymm (by simp) (fun x y f _ => by
    obtain ⟨f, rfl⟩ := (quotientFunctor _).map_surjective f
    rw [morphismPropertyHomMk_eq_strictMap]
    refine strictMap_multiplicativeClosure_le _ _ _ ?_
    rw [Cat.FreeRefl.multiplicativeClosure_morphismPropertyHomMk]
    exact map_mem_strictMap _ _ _ 

Depends on / 依赖: Cat.FreeRefl.multiplicativeClosure_morphismPropertyHomMk, FreeRefl, le_antisymm, map_mem_strictMap, map_surjective, morphismPropertyHomMk_eq_strictMap, multiplicativeClosure_morphismPropertyHomMk, quotientFunctor, strictMap_multiplicativeClosure_le
-/
lemma multiplicativeClosure_morphismPropertyHomMk :
    (morphismPropertyHomMk V).multiplicativeClosure = ⊤ :=
  le_antisymm (by simp) (fun x y f _ => by
    obtain ⟨f, rfl⟩ := (quotientFunctor _).map_surjective f
    rw [morphismPropertyHomMk_eq_strictMap]
    refine strictMap_multiplicativeClosure_le _ _ _ ?_
    rw [Cat.FreeRefl.multiplicativeClosure_morphismPropertyHomMk]
    exact map_mem_strictMap _ _ _ (by simp))

/--
lemma `morphismProperty_eq_top` / 引理 `morphismProperty_eq_top`

English:
lemma morphismProperty_eq_top
  statement: {W : MorphismProperty V.HomotopyCategory}
  proof: le_antisymm (by simp) (by
    rw [← multiplicativeClosure_morphismPropertyHomMk]; rw [MorphismProperty.multiplicativeClosure_le_iff]
    rintro _ _ _ ⟨_, _, e⟩
    exact hW e)

中文:
引理 morphismProperty_eq_top
  结论: {W : MorphismProperty V.HomotopyCategory}
  证明: le_antisymm (by simp) (by
    rw [← multiplicativeClosure_morphismPropertyHomMk]; rw [MorphismProperty.multiplicativeClosure_le_iff]
    rintro _ _ _ ⟨_, _, e⟩
    exact hW e)

Depends on / 依赖: MorphismProperty, MorphismProperty.multiplicativeClosure_le_iff, le_antisymm, multiplicativeClosure_le_iff, multiplicativeClosure_morphismPropertyHomMk
-/
lemma morphismProperty_eq_top {W : MorphismProperty V.HomotopyCategory}
    [W.IsMultiplicative]
    (hW : forall {x y : V _⦋0⦌₂} (e : Edge x y), W (homMk e)) :
    W = ⊤ :=
  le_antisymm (by simp) (by
    rw [← multiplicativeClosure_morphismPropertyHomMk]; rw [MorphismProperty.multiplicativeClosure_le_iff]
    rintro _ _ _ ⟨_, _, e⟩
    exact hW e)

section

variable {D : Type*} [Category* D]

section

variable (obj : V _⦋0⦌₂ -> D) (map : forall {x y : V _⦋0⦌₂}, Edge x y -> (obj x ⟶ obj y))
  (map_id : forall (x : V _⦋0⦌₂), map (.id x) = 𝟙 _)
  (map_comp : forall {x₀ x₁ x₂ : V _⦋0⦌₂}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (_ : Edge.CompStruct e₀₁ e₁₂ e₀₂), map e₀₁ ≫ map e₁₂ = map e₀₂)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : V.HomotopyCategory ⥤ D
  body: CategoryTheory.Quotient.lift _
    (Cat.FreeRefl.lift' obj (fun f => map f) map_id) (by
      rintro _ _ _ _ ⟨h⟩
      simp only [Functor.map_comp]
      convert! map_comp h <;> apply Cat.FreeRefl.lift'_map)

中文:
定义 lift
  签名: : V.HomotopyCategory ⥤ D
  定义体: CategoryTheory.Quotient.lift _
    (Cat.FreeRefl.lift' obj (fun f => map f) map_id) (by
      rintro _ _ _ _ ⟨h⟩
      simp only [Functor.map_comp]
      convert! map_comp h <;> apply Cat.FreeRefl.lift'_map)

Depends on / 依赖: Cat.FreeRefl.lift, CategoryTheory, CategoryTheory.Quotient.lift, FreeRefl, Functor, Functor.map_comp, Quotient, _map, convert, map_comp, map_id
-/
def lift : V.HomotopyCategory ⥤ D :=
  CategoryTheory.Quotient.lift _
    (Cat.FreeRefl.lift' obj (fun f => map f) map_id) (by
      rintro _ _ _ _ ⟨h⟩
      simp only [Functor.map_comp]
      convert! map_comp h <;> apply Cat.FreeRefl.lift'_map)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `lift_obj_mk` / 引理 `lift_obj_mk`

English:
lemma lift_obj_mk
  given: (x : V _⦋0⦌₂)
  statement: (lift obj map map_id map_comp).obj (mk x) = obj x
  proof: rfl

中文:
引理 lift_obj_mk
  条件: (x : V _⦋0⦌₂)
  结论: (lift obj map map_id map_comp).obj (mk x) = obj x
  证明: rfl
-/
lemma lift_obj_mk (x : V _⦋0⦌₂) : (lift obj map map_id map_comp).obj (mk x) = obj x := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `lift_map_homMk` / 引理 `lift_map_homMk`

English:
lemma lift_map_homMk
  given: {x y : V _⦋0⦌₂} (e : Edge x y)
  proof: Category.id_comp _

中文:
引理 lift_map_homMk
  条件: {x y : V _⦋0⦌₂} (e : 边 x y)
  证明: Category.id_comp _

Depends on / 依赖: Category, Category.id_comp, id_comp
-/
lemma lift_map_homMk {x y : V _⦋0⦌₂} (e : Edge x y) :
    (lift obj map map_id map_comp).map (homMk e) = map e :=
  Category.id_comp _

end

variable {F G : V.HomotopyCategory ⥤ D}

section

variable (φ : forall (x : V _⦋0⦌₂), F.obj (mk x) ⟶ G.obj (mk x))
  (hφ : forall ⦃x y : V _⦋0⦌₂⦄ (e : Edge x y),
    F.map (homMk e) ≫ φ y = φ x ≫ G.map (homMk e) := by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/--
Definition of `mkNatTrans` / `mkNatTrans` 的定义

English:
definition mkNatTrans
  signature: : F ⟶ G where
  body: φ _
  naturality _ _ f := by
    have : MorphismProperty.naturalityProperty (fun (x : V.HomotopyCategory) => φ _) = ⊤ :=
      morphismProperty_eq_top (fun e => hφ e)
    exact this.symm.le f (by simp)

中文:
定义 mk自然数Trans
  签名: : F ⟶ G where
  定义体: φ _
  naturality _ _ f := by
    have : MorphismProperty.naturalityProperty (fun (x : V.HomotopyCategory) => φ _) = ⊤ :=
      morphismProperty_eq_top (fun e => hφ e)
    exact this.symm.le f (by simp)
-/
def mkNatTrans : F ⟶ G where
  app _ := φ _
  naturality _ _ f := by
    have : MorphismProperty.naturalityProperty (fun (x : V.HomotopyCategory) => φ _) = ⊤ :=
      morphismProperty_eq_top (fun e => hφ e)
    exact this.symm.le f (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
@[simp]
/--
lemma `mkNatTrans_app_mk` / 引理 `mkNatTrans_app_mk`

English:
lemma mkNatTrans_app_mk
  given: (v : V _⦋0⦌₂)
  proof: rfl

中文:
引理 mk自然数Trans_app_mk
  条件: (v : V _⦋0⦌₂)
  证明: rfl
-/
lemma mkNatTrans_app_mk (v : V _⦋0⦌₂) :
    (mkNatTrans φ hφ).app (mk v) = φ v := rfl

end

section

variable (iso : forall (x : V _⦋0⦌₂), F.obj (mk x) ≅ G.obj (mk x))
  (hiso : forall ⦃x y : V _⦋0⦌₂⦄ (e : Edge x y), F.map (homMk e) ≫ (iso y).hom =
    (iso x).hom ≫ G.map (homMk e) := by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/--
Definition of `mkNatIso` / `mkNatIso` 的定义

English:
definition mkNatIso
  signature: : F ≅ G
  body: NatIso.ofComponents (fun _ => iso _) (fun f => (mkNatTrans _ hiso).naturality f)

中文:
定义 mk自然数Iso
  签名: : F ≅ G
  定义体: NatIso.ofComponents (fun _ => iso _) (fun f => (mkNatTrans _ hiso).naturality f)

Depends on / 依赖: NatIso, NatIso.ofComponents, mkNatTrans, naturality, ofComponents
-/
def mkNatIso : F ≅ G :=
  NatIso.ofComponents (fun _ => iso _) (fun f => (mkNatTrans _ hiso).naturality f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
@[simp]
/--
lemma `mkNatIso_hom_app_mk` / 引理 `mkNatIso_hom_app_mk`

English:
lemma mkNatIso_hom_app_mk
  given: (v : V _⦋0⦌₂)
  proof: rfl

中文:
引理 mk自然数Iso_hom_app_mk
  条件: (v : V _⦋0⦌₂)
  证明: rfl
-/
lemma mkNatIso_hom_app_mk (v : V _⦋0⦌₂) :
    (mkNatIso iso hiso).hom.app (mk v) = (iso v).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
@[simp]
/--
lemma `mkNatIso_inv_app_mk` / 引理 `mkNatIso_inv_app_mk`

English:
lemma mkNatIso_inv_app_mk
  given: (v : V _⦋0⦌₂)
  proof: rfl

中文:
引理 mk自然数Iso_inv_app_mk
  条件: (v : V _⦋0⦌₂)
  证明: rfl
-/
lemma mkNatIso_inv_app_mk (v : V _⦋0⦌₂) :
    (mkNatIso iso hiso).inv.app (mk v) = (iso v).inv := rfl

end

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `functor_ext` / 引理 `functor_ext`

English:
lemma functor_ext
  statement: {F G : V.HomotopyCategory ⥤ D}
  proof: Functor.ext_of_iso (mkNatIso (fun x => eqToIso (h₁ x))
    (fun _ _ e => by simp [h₂ e])) (fun _ => h₁ _)

中文:
引理 functor_ext
  结论: {F G : V.HomotopyCategory ⥤ D}
  证明: Functor.ext_of_iso (mkNatIso (fun x => eqToIso (h₁ x))
    (fun _ _ e => by simp [h₂ e])) (fun _ => h₁ _)

Depends on / 依赖: Functor, Functor.ext_of_iso, eqToIso, ext_of_iso, mkNatIso
-/
lemma functor_ext {F G : V.HomotopyCategory ⥤ D}
    (h₁ : forall (x : V _⦋0⦌₂), F.obj (mk x) = G.obj (mk x))
    (h₂ : forall ⦃x y : V _⦋0⦌₂⦄ (e : Edge x y),
      F.map (homMk e) = eqToHom (h₁ x) ≫ G.map (homMk e) ≫ eqToHom (h₁ y).symm) :
    F = G :=
  Functor.ext_of_iso (mkNatIso (fun x => eqToIso (h₁ x))
    (fun _ _ e => by simp [h₂ e])) (fun _ => h₁ _)

end

instance (X : Truncated.{u} 2) [Subsingleton (X _⦋0⦌₂)] :
    Subsingleton X.HomotopyCategory where
  allEq x y := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    obtain rfl := Subsingleton.elim x y
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `subsingleton_hom` / 实例 `subsingleton_hom`

English:
instance subsingleton_hom
  signature: (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)]
  body: letI : Unique (OneTruncation₂ X) := inferInstanceAs (Unique (X _⦋0⦌₂))
  letI (x y : (OneTruncation₂ X)) : Subsingleton (x ⟶ y) :=
    inferInstanceAs (Subsingleton <| X.Edge _ _)
  CategoryTheory.Quotient.instSubsingletonHom _ _ _

中文:
实例 subsingleton_hom
  签名: (X : Truncated.{u} 2) [唯一 (X _⦋0⦌₂)] [子单例 (X _⦋1⦌₂)]
  定义体: letI : Unique (OneTruncation₂ X) := inferInstanceAs (Unique (X _⦋0⦌₂))
  letI (x y : (OneTruncation₂ X)) : Subsingleton (x ⟶ y) :=
    inferInstanceAs (Subsingleton <| X.Edge _ _)
  CategoryTheory.Quotient.instSubsingletonHom _ _ _

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.instSubsingletonHom, Quotient, Subsingleton, Unique, X.Edge, instSubsingletonHom
-/
instance subsingleton_hom (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)]
    (x y : X.HomotopyCategory) :
    Subsingleton (x ⟶ y) :=
  letI : Unique (OneTruncation₂ X) := inferInstanceAs (Unique (X _⦋0⦌₂))
  letI (x y : (OneTruncation₂ X)) : Subsingleton (x ⟶ y) :=
    inferInstanceAs (Subsingleton <| X.Edge _ _)
  CategoryTheory.Quotient.instSubsingletonHom _ _ _

instance (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] : Unique X.HomotopyCategory :=
  letI : Unique (OneTruncation₂ X) := inferInstanceAs (Unique (X _⦋0⦌₂))
  CategoryTheory.Quotient.instUnique _

/--
Definition of `isTerminal` / `isTerminal` 的定义

English:
definition isTerminal
  signature: (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)]
  body: letI : IsDiscrete (X.HomotopyCategory) := { eq_of_hom := by subsingleton }
  Cat.isTerminalOfUniqueOfIsDiscrete

中文:
定义 isTerminal
  签名: (X : Truncated.{u} 2) [唯一 (X _⦋0⦌₂)] [子单例 (X _⦋1⦌₂)]
  定义体: letI : IsDiscrete (X.HomotopyCategory) := { eq_of_hom := by subsingleton }
  Cat.isTerminalOfUniqueOfIsDiscrete

Depends on / 依赖: Cat.isTerminalOfUniqueOfIsDiscrete, HomotopyCategory, IsDiscrete, X.HomotopyCategory, eq_of_hom, isTerminalOfUniqueOfIsDiscrete, subsingleton
-/
def isTerminal (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)] :
    IsTerminal (Cat.of X.HomotopyCategory) :=
  letI : IsDiscrete (X.HomotopyCategory) := { eq_of_hom := by subsingleton }
  Cat.isTerminalOfUniqueOfIsDiscrete

end HomotopyCategory

section

open HomotopyCategory

variable {V W} (f : V ⟶ W)

/--
Definition of `mapHomotopyCategory` / `mapHomotopyCategory` 的定义

English:
definition mapHomotopyCategory
  signature: :
  body: CategoryTheory.Quotient.lift _
    (((oneTruncation₂ ⋙ Cat.freeRefl).map f).toFunctor ⋙ quotientFunctor W) (by
      rintro _ _ _ _ ⟨h⟩
      exact CategoryTheory.Quotient.sound _ ⟨h.map f⟩)

@[simp]

中文:
定义 mapHomotopyCategory
  签名: :
  定义体: CategoryTheory.Quotient.lift _
    (((oneTruncation₂ ⋙ Cat.freeRefl).map f).toFunctor ⋙ quotientFunctor W) (by
      rintro _ _ _ _ ⟨h⟩
      exact CategoryTheory.Quotient.sound _ ⟨h.map f⟩)

@[simp]

Depends on / 依赖: Cat.freeRefl, CategoryTheory, CategoryTheory.Quotient.lift, CategoryTheory.Quotient.sound, Quotient, freeRefl, h.map, quotientFunctor, toFunctor
-/
def mapHomotopyCategory :
    V.HomotopyCategory ⥤ W.HomotopyCategory :=
  CategoryTheory.Quotient.lift _
    (((oneTruncation₂ ⋙ Cat.freeRefl).map f).toFunctor ⋙ quotientFunctor W) (by
      rintro _ _ _ _ ⟨h⟩
      exact CategoryTheory.Quotient.sound _ ⟨h.map f⟩)

@[simp]
/--
lemma `mapHomotopyCategory_obj` / 引理 `mapHomotopyCategory_obj`

English:
lemma mapHomotopyCategory_obj
  given: (x : V _⦋0⦌₂)
  proof: rfl

@[simp]

中文:
引理 mapHomotopyCategory_obj
  条件: (x : V _⦋0⦌₂)
  证明: rfl

@[simp]
-/
lemma mapHomotopyCategory_obj (x : V _⦋0⦌₂) :
    (mapHomotopyCategory f).obj (.mk x) = .mk (f.app _ x) := rfl

@[simp]
/--
lemma `mapHomotopyCategory_homMk` / 引理 `mapHomotopyCategory_homMk`

English:
lemma mapHomotopyCategory_homMk
  given: {x y : V _⦋0⦌₂} (e : Edge x y)
  proof: rfl

中文:
引理 mapHomotopyCategory_homMk
  条件: {x y : V _⦋0⦌₂} (e : 边 x y)
  证明: rfl
-/
lemma mapHomotopyCategory_homMk {x y : V _⦋0⦌₂} (e : Edge x y) :
    (mapHomotopyCategory f).map (homMk e) = homMk (e.map f) := rfl

end

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `hoFunctor₂` / `hoFunctor₂` 的定义

English:
definition hoFunctor₂
  signature: : SSet.Truncated.{u} 2 ⥤ Cat.{u, u} where
  body: Cat.of V.HomotopyCategory
  map F := (mapHomotopyCategory F).toCatHom
  map_id _ := by ext1; exact HomotopyCategory.functor_ext (by simp) (by cat_disch)
  map_comp _ _ := by ext1; exact HomotopyCategory.functor_ext (by simp) (by cat_disch)

中文:
定义 hoFunctor₂
  签名: : SSet.Truncated.{u} 2 ⥤ Cat.{u, u} where
  定义体: Cat.of V.HomotopyCategory
  map F := (mapHomotopyCategory F).toCatHom
  map_id _ := by ext1; exact HomotopyCategory.functor_ext (by simp) (by cat_disch)
  map_comp _ _ := by ext1; exact HomotopyCategory.functor_ext (by simp) (by cat_disch)

Depends on / 依赖: Cat.of, HomotopyCategory, V.HomotopyCategory
-/
def hoFunctor₂ : SSet.Truncated.{u} 2 ⥤ Cat.{u, u} where
  obj V := Cat.of V.HomotopyCategory
  map F := (mapHomotopyCategory F).toCatHom
  map_id _ := by ext1; exact HomotopyCategory.functor_ext (by simp) (by cat_disch)
  map_comp _ _ := by ext1; exact HomotopyCategory.functor_ext (by simp) (by cat_disch)

/--
theorem `hoFunctor₂_naturality` / 定理 `hoFunctor₂_naturality`

English:
theorem hoFunctor₂_naturality
  given: {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y)
  proof: rfl

中文:
定理 hoFunctor₂_naturality
  条件: {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y)
  证明: rfl
-/
theorem hoFunctor₂_naturality {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y) :
    ((oneTruncation₂ ⋙ Cat.freeRefl).map f).toFunctor ⋙
      SSet.Truncated.HomotopyCategory.quotientFunctor Y =
      SSet.Truncated.HomotopyCategory.quotientFunctor X ⋙ mapHomotopyCategory f := rfl

/--
theorem `HomotopyCategory.lift_unique'` / 定理 `HomotopyCategory.lift_unique'`

English:
theorem HomotopyCategory.lift_unique'
  statement: (V : SSet.Truncated.{u} 2) {D : Type*} [Category* D]
  proof: Quotient.lift_unique' _ _ _ h

中文:
定理 HomotopyCategory.lift_unique'
  结论: (V : SSet.Truncated.{u} 2) {D : 类型} [范畴* D]
  证明: Quotient.lift_unique' _ _ _ h

Depends on / 依赖: Quotient, Quotient.lift_unique, lift_unique
-/
theorem HomotopyCategory.lift_unique' (V : SSet.Truncated.{u} 2) {D : Type*} [Category* D]
    (F₁ F₂ : V.HomotopyCategory ⥤ D)
    (h : HomotopyCategory.quotientFunctor V ⋙ F₁ = HomotopyCategory.quotientFunctor V ⋙ F₂) :
    F₁ = F₂ :=
  Quotient.lift_unique' _ _ _ h

end Truncated

/--
Definition of `hoFunctor` / `hoFunctor` 的定义

English:
definition hoFunctor
  signature: : SSet.{u} ⥤ Cat.{u, u}
  body: SSet.truncation 2 ⋙ Truncated.hoFunctor₂

中文:
定义 hoFunctor
  签名: : SSet.{u} ⥤ Cat.{u, u}
  定义体: SSet.truncation 2 ⋙ Truncated.hoFunctor₂

Depends on / 依赖: SSet.truncation, Truncated, Truncated.hoFunctor, truncation
-/
def hoFunctor : SSet.{u} ⥤ Cat.{u, u} := SSet.truncation 2 ⋙ Truncated.hoFunctor₂

/--
Definition of `hoFunctor.obj.equiv` / `hoFunctor.obj.equiv` 的定义

English:
definition hoFunctor.obj.equiv
  signature: (X : SSet)
  body: (Quotient.equiv.{u, u} _).trans (Quotient.equiv _)

中文:
定义 hoFunctor.obj.equiv
  签名: (X : SSet)
  定义体: (Quotient.equiv.{u, u} _).trans (Quotient.equiv _)

Depends on / 依赖: Quotient, Quotient.equiv
-/
def hoFunctor.obj.equiv (X : SSet) : hoFunctor.obj X ≃ X _⦋0⦌ :=
  (Quotient.equiv.{u, u} _).trans (Quotient.equiv _)

/--
Instance `instUniqueOneTruncation₂DeltaZero` / 实例 `instUniqueOneTruncation₂DeltaZero`

English:
instance instUniqueOneTruncation₂DeltaZero
  signature: : Unique (OneTruncation₂ ((truncation 2).obj Δ[0]))
  body: inferInstanceAs (Unique (ULift.{_, 0} (⦋0⦌ ⟶ ⦋0⦌)))

中文:
实例 instUniqueOneTruncation₂DeltaZero
  签名: : 唯一 (OneTruncation₂ ((truncation 2).obj Δ[0]))
  定义体: inferInstanceAs (Unique (ULift.{_, 0} (⦋0⦌ ⟶ ⦋0⦌)))

Depends on / 依赖: Unique
-/
instance instUniqueOneTruncation₂DeltaZero : Unique (OneTruncation₂ ((truncation 2).obj Δ[0])) :=
  inferInstanceAs (Unique (ULift.{_, 0} (⦋0⦌ ⟶ ⦋0⦌)))

/-- Since `⦋0⦌ : SimplexCategory` is terminal, `Δ[0]` has a unique edge and thus the homs of
`OneTruncation₂ ((truncation 2).obj Δ[0])` have unique inhabitants. -/
instance (x y : OneTruncation₂ ((truncation 2).obj Δ[0])) : Unique (x ⟶ y) where
  default := by
    obtain rfl : x = default := Unique.uniq _ _
    obtain rfl : y = default := Unique.uniq _ _
    exact 𝟙rq instUniqueOneTruncation₂DeltaZero.default
  uniq _ := by
    let : Subsingleton (((truncation 2).obj Δ[0]).obj (.op ⦋1⦌₂)) :=
      inferInstanceAs (Subsingleton (ULift.{_, 0} (⦋1⦌ ⟶ ⦋0⦌)))
    ext
    exact this.allEq _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique ((truncation.{u} 2).obj Δ[0]).HomotopyCategory
  body: inferInstanceAs (Unique <| CategoryTheory.Quotient _)

中文:
实例 :
  签名: 唯一 ((truncation.{u} 2).obj Δ[0]).HomotopyCategory
  定义体: inferInstanceAs (Unique <| CategoryTheory.Quotient _)

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient, Quotient, Unique
-/
instance : Unique ((truncation.{u} 2).obj Δ[0]).HomotopyCategory :=
  inferInstanceAs (Unique <| CategoryTheory.Quotient _)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDiscrete ((truncation.{u} 2).obj Δ[0]).HomotopyCategory
  body: inferInstanceAs (Subsingleton ((_ : CategoryTheory.Quotient _) ⟶ _))
  eq_of_hom _ := by subsingleton

中文:
实例 :
  签名: 是离散 ((truncation.{u} 2).obj Δ[0]).HomotopyCategory
  定义体: inferInstanceAs (Subsingleton ((_ : CategoryTheory.Quotient _) ⟶ _))
  eq_of_hom _ := by subsingleton

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient, Quotient, Subsingleton, eq_of_hom, subsingleton
-/
instance : IsDiscrete ((truncation.{u} 2).obj Δ[0]).HomotopyCategory where
  subsingleton x y :=
    inferInstanceAs (Subsingleton ((_ : CategoryTheory.Quotient _) ⟶ _))
  eq_of_hom _ := by subsingleton

/--
Definition of `isTerminalHoFunctorDeltaZero` / `isTerminalHoFunctorDeltaZero` 的定义

English:
definition isTerminalHoFunctorDeltaZero
  signature: : IsTerminal (hoFunctor.{u}.obj (Δ[0]))
  body: Cat.isTerminalOfUniqueOfIsDiscrete

中文:
定义 isTerminalHoFunctorDeltaZero
  签名: : 是终止 (hoFunctor.{u}.obj (Δ[0]))
  定义体: Cat.isTerminalOfUniqueOfIsDiscrete

Depends on / 依赖: Cat.isTerminalOfUniqueOfIsDiscrete, isTerminalOfUniqueOfIsDiscrete
-/
def isTerminalHoFunctorDeltaZero : IsTerminal (hoFunctor.{u}.obj (Δ[0])) :=
  Cat.isTerminalOfUniqueOfIsDiscrete

/--
Definition of `hoFunctor.terminalIso` / `hoFunctor.terminalIso` 的定义

English:
definition hoFunctor.terminalIso
  signature: : hoFunctor.obj (⊤_ SSet) ≅ ⊤_ Cat
  body: hoFunctor.mapIso (terminalIsoIsTerminal stdSimplex.isTerminalObj₀) ≪≫
    (terminalIsoIsTerminal isTerminalHoFunctorDeltaZero).symm

中文:
定义 hoFunctor.terminalIso
  签名: : hoFunctor.obj (⊤_ SSet) ≅ ⊤_ Cat
  定义体: hoFunctor.mapIso (terminalIsoIsTerminal stdSimplex.isTerminalObj₀) ≪≫
    (terminalIsoIsTerminal isTerminalHoFunctorDeltaZero).symm

Depends on / 依赖: hoFunctor, hoFunctor.mapIso, isTerminalHoFunctorDeltaZero, mapIso, stdSimplex, stdSimplex.isTerminalObj, terminalIsoIsTerminal
-/
noncomputable def hoFunctor.terminalIso : hoFunctor.obj (⊤_ SSet) ≅ ⊤_ Cat :=
  hoFunctor.mapIso (terminalIsoIsTerminal stdSimplex.isTerminalObj₀) ≪≫
    (terminalIsoIsTerminal isTerminalHoFunctorDeltaZero).symm

/--
Instance `hoFunctor.preservesTerminal` / 实例 `hoFunctor.preservesTerminal`

English:
instance hoFunctor.preservesTerminal
  signature: : PreservesLimit (empty.{0} SSet) hoFunctor
  body: preservesTerminal_of_iso hoFunctor hoFunctor.terminalIso

中文:
实例 hoFunctor.preservesTerminal
  签名: : 保持极限 (empty.{0} SSet) hoFunctor
  定义体: preservesTerminal_of_iso hoFunctor hoFunctor.terminalIso

Depends on / 依赖: hoFunctor, hoFunctor.terminalIso, preservesTerminal_of_iso, terminalIso
-/
instance hoFunctor.preservesTerminal : PreservesLimit (empty.{0} SSet) hoFunctor :=
  preservesTerminal_of_iso hoFunctor hoFunctor.terminalIso

/--
Instance `hoFunctor.preservesTerminal'` / 实例 `hoFunctor.preservesTerminal'`

English:
instance hoFunctor.preservesTerminal'
  signature: :
  body: preservesLimitsOfShape_pempty_of_preservesTerminal _

中文:
实例 hoFunctor.preservesTerminal'
  签名: :
  定义体: preservesLimitsOfShape_pempty_of_preservesTerminal _

Depends on / 依赖: preservesLimitsOfShape_pempty_of_preservesTerminal
-/
instance hoFunctor.preservesTerminal' :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) hoFunctor :=
  preservesLimitsOfShape_pempty_of_preservesTerminal _

end SSet
