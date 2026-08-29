/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.CategoryTheory.Functor.CurryingThree
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat

/-!
# The homotopy category functor is monoidal

Given `2`-truncated simplicial sets `X` and `Y`, we introduce ad operation
`Truncated.Edge.tensor : Edge x x' → Edge y y' → Edge (x, y) (x', y')`.
We use this in order to construct an equivalence of categories
`(X ⊗ Y).HomotopyCategory ≌ X.HomotopyCategory × Y.HomotopyCategory`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Simplicial SimplicialObject.Truncated
  CartesianMonoidalCategory Limits

namespace SSet

namespace Truncated

namespace Edge

variable {X Y X' Y' Z : Truncated.{u} 2}

/-- The external product of edges of `2`-truncated simplicial sets. -/
@[simps]
/--
Definition of `tensor` / `tensor` 的定义

English:
definition tensor
  signature: {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
  body: (e₁.edge, e₂.edge)
  src_eq := Prod.ext e₁.src_eq e₂.src_eq
  tgt_eq := Prod.ext e₁.tgt_eq e₂.tgt_eq

中文:
定义 tensor
  签名: {x x' : X _⦋0⦌₂} (e₁ : 边 x x') {y y' : Y _⦋0⦌₂}
  定义体: (e₁.edge, e₂.edge)
  src_eq := Prod.ext e₁.src_eq e₂.src_eq
  tgt_eq := Prod.ext e₁.tgt_eq e₂.tgt_eq

Depends on / 依赖: otimes
-/
def tensor {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') :
    Edge (X := X otimes Y) (x, y) (x', y') where
  edge := (e₁.edge, e₂.edge)
  src_eq := Prod.ext e₁.src_eq e₂.src_eq
  tgt_eq := Prod.ext e₁.tgt_eq e₂.tgt_eq

/--
lemma `tensor_surjective` / 引理 `tensor_surjective`

English:
lemma tensor_surjective
  statement: {x x' : X _⦋0⦌₂} {y y' : Y _⦋0⦌₂}
  proof: ⟨e.map (fst _ _), e.map (snd _ _), rfl⟩

@[simp]

中文:
引理 tensor_surjective
  结论: {x x' : X _⦋0⦌₂} {y y' : Y _⦋0⦌₂}
  证明: ⟨e.map (fst _ _), e.map (snd _ _), rfl⟩

@[simp]

Depends on / 依赖: otimes
-/
lemma tensor_surjective {x x' : X _⦋0⦌₂} {y y' : Y _⦋0⦌₂}
    (e : Edge (X := X otimes Y) (x, y) (x', y')) :
    exists (e₁ : Edge x x') (e₂ : Edge y y'), e₁.tensor e₂ = e :=
  ⟨e.map (fst _ _), e.map (snd _ _), rfl⟩

@[simp]
/--
lemma `id_tensor_id` / 引理 `id_tensor_id`

English:
lemma id_tensor_id
  given: (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂)
  proof: rfl

@[simp]

中文:
引理 id_tensor_id
  条件: (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂)
  证明: rfl

@[simp]

Depends on / 依赖: otimes
-/
lemma id_tensor_id (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (id x).tensor (id y) = id (X := X otimes Y) (x, y) := rfl

@[simp]
/--
lemma `map_tensorHom` / 引理 `map_tensorHom`

English:
lemma map_tensorHom
  statement: {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
  proof: rfl

@[simp]

中文:
引理 map_tensorHom
  结论: {x x' : X _⦋0⦌₂} (e₁ : 边 x x') {y y' : Y _⦋0⦌₂}
  证明: rfl

@[simp]
-/
lemma map_tensorHom {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') (f : X ⟶ X') (g : Y ⟶ Y') :
    (e₁.tensor e₂).map (f otimesₘ g) =
      (e₁.map f).tensor (e₂.map g) := rfl

@[simp]
/--
lemma `map_whiskerRight` / 引理 `map_whiskerRight`

English:
lemma map_whiskerRight
  statement: {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
  proof: rfl

@[simp]

中文:
引理 map_whiskerRight
  结论: {x x' : X _⦋0⦌₂} (e₁ : 边 x x') {y y' : Y _⦋0⦌₂}
  证明: rfl

@[simp]
-/
lemma map_whiskerRight {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') (f : X ⟶ X') :
    (e₁.tensor e₂).map (f ▷ _) =
      (e₁.map f).tensor e₂ := rfl

@[simp]
/--
lemma `map_whiskerLeft` / 引理 `map_whiskerLeft`

English:
lemma map_whiskerLeft
  statement: {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
  proof: rfl

@[simp]

中文:
引理 map_whiskerLeft
  结论: {x x' : X _⦋0⦌₂} (e₁ : 边 x x') {y y' : Y _⦋0⦌₂}
  证明: rfl

@[simp]
-/
lemma map_whiskerLeft {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') (g : Y ⟶ Y') :
    (e₁.tensor e₂).map (_ ◁ g) =
      e₁.tensor (e₂.map g) := rfl

@[simp]
/--
lemma `map_associator_hom` / 引理 `map_associator_hom`

English:
lemma map_associator_hom
  statement: {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂} (e₂ : Edge y y')
  proof: rfl

@[simp]

中文:
引理 map_associator_hom
  结论: {x x' : X _⦋0⦌₂} (e₁ : 边 x x') {y y' : Y _⦋0⦌₂} (e₂ : 边 y y')
  证明: rfl

@[simp]
-/
lemma map_associator_hom {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂} (e₂ : Edge y y')
    {z z' : Z _⦋0⦌₂} (e₃ : Edge z z') :
    ((e₁.tensor e₂).tensor e₃).map (α_ _ _ _).hom = e₁.tensor (e₂.tensor e₃) :=
  rfl

@[simp]
/--
lemma `map_fst` / 引理 `map_fst`

English:
lemma map_fst
  statement: {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
  proof: rfl

@[simp]

中文:
引理 map_fst
  结论: {x x' : X _⦋0⦌₂} (e₁ : 边 x x') {y y' : Y _⦋0⦌₂}
  证明: rfl

@[simp]
-/
lemma map_fst {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') :
    (e₁.tensor e₂).map (fst _ _) = e₁ := rfl

@[simp]
/--
lemma `map_snd` / 引理 `map_snd`

English:
lemma map_snd
  statement: {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
  proof: rfl

中文:
引理 map_snd
  结论: {x x' : X _⦋0⦌₂} (e₁ : 边 x x') {y y' : Y _⦋0⦌₂}
  证明: rfl
-/
lemma map_snd {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') :
    (e₁.tensor e₂).map (snd _ _) = e₂ := rfl

/-- The external product of `CompStruct` between edges of `2`-truncated simplicial sets. -/
@[simps simplex_fst simplex_snd]
/--
Definition of `CompStruct.tensor` / `CompStruct.tensor` 的定义

English:
definition CompStruct.tensor
  body: (hx.simplex, hy.simplex)
  d₂ := Prod.ext hx.d₂ hy.d₂
  d₀ := Prod.ext hx.d₀ hy.d₀
  d₁ := Prod.ext hx.d₁ hy.d₁

中文:
定义 余mpStruct.tensor
  定义体: (hx.simplex, hy.simplex)
  d₂ := Prod.ext hx.d₂ hy.d₂
  d₀ := Prod.ext hx.d₀ hy.d₀
  d₁ := Prod.ext hx.d₁ hy.d₁

Depends on / 依赖: hx.simplex, hy.simplex, simplex
-/
def CompStruct.tensor
    {x₀ x₁ x₂ : X _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (hx : CompStruct e₀₁ e₁₂ e₀₂)
    {y₀ y₁ y₂ : Y _⦋0⦌₂} {e'₀₁ : Edge y₀ y₁} {e'₁₂ : Edge y₁ y₂} {e'₀₂ : Edge y₀ y₂}
    (hy : CompStruct e'₀₁ e'₁₂ e'₀₂) :
    CompStruct (e₀₁.tensor e'₀₁) (e₁₂.tensor e'₁₂) (e₀₂.tensor e'₀₂) where
  simplex := (hx.simplex, hy.simplex)
  d₂ := Prod.ext hx.d₂ hy.d₂
  d₀ := Prod.ext hx.d₀ hy.d₀
  d₁ := Prod.ext hx.d₁ hy.d₁

end Edge

namespace HomotopyCategory

instance {n : Nat} (d : (SimplexCategory.Truncated n)ᵒᵖ) :
    Unique ((𝟙_ (Truncated.{u} n)).obj d) :=
  inferInstanceAs (Unique PUnit)

/--
Definition of `isoTerminal` / `isoTerminal` 的定义

English:
definition isoTerminal
  signature: (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)]
  body: IsTerminal.uniqueUpToIso (isTerminal _) Cat.chosenTerminalIsTerminal

中文:
定义 isoTerminal
  签名: (X : Truncated.{u} 2) [唯一 (X _⦋0⦌₂)] [子单例 (X _⦋1⦌₂)]
  定义体: IsTerminal.uniqueUpToIso (isTerminal _) Cat.chosenTerminalIsTerminal

Depends on / 依赖: Cat.chosenTerminalIsTerminal, IsTerminal, IsTerminal.uniqueUpToIso, chosenTerminalIsTerminal, isTerminal, uniqueUpToIso
-/
def isoTerminal (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)] :
    Cat.of X.HomotopyCategory ≅ Cat.chosenTerminal :=
  IsTerminal.uniqueUpToIso (isTerminal _) Cat.chosenTerminalIsTerminal

namespace BinaryProduct

/--
lemma `square` / 引理 `square`

English:
lemma square
  statement: {X Y : Truncated.{u} 2}
  proof: by
  rw [homMk_comp_homMk ((Edge.CompStruct.idComp ex).tensor (Edge.CompStruct.compId ey))]; rw [homMk_comp_homMk ((Edge.CompStruct.compId ex).tensor (Edge.CompStruct.idComp ey))]

中文:
引理 square
  结论: {X Y : Truncated.{u} 2}
  证明: by
  rw [homMk_comp_homMk ((Edge.CompStruct.idComp ex).tensor (Edge.CompStruct.compId ey))]; rw [homMk_comp_homMk ((Edge.CompStruct.compId ex).tensor (Edge.CompStruct.idComp ey))]

Depends on / 依赖: CompStruct, Edge.CompStruct.compId, Edge.CompStruct.idComp, compId, homMk_comp_homMk, idComp, tensor
-/
lemma square {X Y : Truncated.{u} 2}
    {x₀ x₁ : X _⦋0⦌₂} (ex : Edge x₀ x₁) {y₀ y₁ : Y _⦋0⦌₂} (ey : Edge y₀ y₁) :
    homMk (ex.tensor (.id y₀)) ≫ homMk (Edge.tensor (.id x₁) ey) =
      homMk (Edge.tensor (.id x₀) ey) ≫ homMk (ex.tensor (.id y₁)) := by
  rw [homMk_comp_homMk ((Edge.CompStruct.idComp ex).tensor (Edge.CompStruct.compId ey))]; rw [homMk_comp_homMk ((Edge.CompStruct.compId ex).tensor (Edge.CompStruct.idComp ey))]

variable {X X' Y Y' Z : Truncated.{u} 2}

variable (X Y) in
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : (X otimes Y).HomotopyCategory ⥤ X.HomotopyCategory × Y.HomotopyCategory
  body: (mapHomotopyCategory (fst _ _)).prod' (mapHomotopyCategory (snd _ _))

@[simp]

中文:
定义 functor
  签名: : (X otimes Y).HomotopyCategory ⥤ X.HomotopyCategory × Y.HomotopyCategory
  定义体: (mapHomotopyCategory (fst _ _)).prod' (mapHomotopyCategory (snd _ _))

@[simp]

Depends on / 依赖: mapHomotopyCategory
-/
def functor : (X otimes Y).HomotopyCategory ⥤ X.HomotopyCategory × Y.HomotopyCategory :=
  (mapHomotopyCategory (fst _ _)).prod' (mapHomotopyCategory (snd _ _))

@[simp]
/--
lemma `functor_obj` / 引理 `functor_obj`

English:
lemma functor_obj
  given: (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂)
  proof: rfl

@[simp]

中文:
引理 functor_obj
  条件: (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂)
  证明: rfl

@[simp]
-/
lemma functor_obj (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (functor X Y).obj (mk (x, y)) = (mk x, mk y) := rfl

@[simp]
/--
lemma `functor_map` / 引理 `functor_map`

English:
lemma functor_map
  statement: {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁)
  proof: rfl

中文:
引理 functor_map
  结论: {x₀ x₁ : X _⦋0⦌₂} (e : 边 x₀ x₁)
  证明: rfl
-/
lemma functor_map {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁)
    {y₀ y₁ : Y _⦋0⦌₂} (e' : Edge y₀ y₁) :
    (functor X Y).map (homMk (e.tensor e')) = (homMk e, homMk e') := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (X Y) in
/--
Definition of `curriedInverse` / `curriedInverse` 的定义

English:
definition curriedInverse
  signature: : X.HomotopyCategory ⥤ Y.HomotopyCategory ⥤ (X otimes Y).HomotopyCategory
  body: lift (fun x => lift (fun y => mk (x, y)) (fun {y₀ y₁} e => homMk (Edge.tensor (.id _) e)) (by simp)
    (fun {y₀ y₁ y₁ e₀₁ e₁₂ e₀₂ h} => homMk_comp_homMk ((Edge.CompStruct.idCompId x).tensor h)))
    (fun {x₀ x₁} e => mkNatTrans (fun y => homMk (V := X otimes Y) (x₀ := (x₀, y))
      (x₁ := (x₁, y))

中文:
定义 curriedInverse
  签名: : X.HomotopyCategory ⥤ Y.HomotopyCategory ⥤ (X otimes Y).HomotopyCategory
  定义体: lift (fun x => lift (fun y => mk (x, y)) (fun {y₀ y₁} e => homMk (Edge.tensor (.id _) e)) (by simp)
    (fun {y₀ y₁ y₁ e₀₁ e₁₂ e₀₂ h} => homMk_comp_homMk ((Edge.CompStruct.idCompId x).tensor h)))
    (fun {x₀ x₁} e => mkNatTrans (fun y => homMk (V := X otimes Y) (x₀ := (x₀, y))
      (x₁ := (x₁, y))

Depends on / 依赖: CompStruct, Edge.CompStruct.idCompId, Edge.tensor, cat_disch, e.tensor, h.tensor, homMk_comp_homMk, idCompId, mkNatTrans, mk_surjective, otimes, square, tensor
-/
def curriedInverse : X.HomotopyCategory ⥤ Y.HomotopyCategory ⥤ (X otimes Y).HomotopyCategory :=
  lift (fun x => lift (fun y => mk (x, y)) (fun {y₀ y₁} e => homMk (Edge.tensor (.id _) e)) (by simp)
    (fun {y₀ y₁ y₁ e₀₁ e₁₂ e₀₂ h} => homMk_comp_homMk ((Edge.CompStruct.idCompId x).tensor h)))
    (fun {x₀ x₁} e => mkNatTrans (fun y => homMk (V := X otimes Y) (x₀ := (x₀, y))
      (x₁ := (x₁, y)) (e.tensor (.id y))) (fun y₀ y₁ e' => by simp [square]))
    (by cat_disch) (fun {x₀ x₁ x₂ e₀₁ e₁₂ e₀₂} h => by
      ext y
      obtain ⟨y, rfl⟩ := mk_surjective y
      simpa using homMk_comp_homMk (h.tensor (.idCompId y)))

set_option backward.isDefEq.respectTransparency.types false in
variable (X Y) in
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : X.HomotopyCategory × Y.HomotopyCategory ⥤ (X otimes Y).HomotopyCategory
  body: Functor.uncurry.obj (curriedInverse X Y)

中文:
定义 inverse
  签名: : X.HomotopyCategory × Y.HomotopyCategory ⥤ (X otimes Y).HomotopyCategory
  定义体: Functor.uncurry.obj (curriedInverse X Y)

Depends on / 依赖: Functor, Functor.uncurry.obj, curriedInverse, uncurry
-/
def inverse : X.HomotopyCategory × Y.HomotopyCategory ⥤ (X otimes Y).HomotopyCategory :=
  Functor.uncurry.obj (curriedInverse X Y)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `inverse_obj` / 引理 `inverse_obj`

English:
lemma inverse_obj
  given: (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂)
  statement: (inverse X Y).obj (mk x, mk y) = mk (x, y)
  proof: rfl

中文:
引理 inverse_obj
  条件: (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂)
  结论: (inverse X Y).obj (mk x, mk y) = mk (x, y)
  证明: rfl
-/
lemma inverse_obj (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) : (inverse X Y).obj (mk x, mk y) = mk (x, y) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `inverse_map_mkHom_homMk_id` / 引理 `inverse_map_mkHom_homMk_id`

English:
lemma inverse_map_mkHom_homMk_id
  given: {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) (y : Y _⦋0⦌₂)
  proof: rfl

中文:
引理 inverse_map_mkHom_homMk_id
  条件: {x₀ x₁ : X _⦋0⦌₂} (e : 边 x₀ x₁) (y : Y _⦋0⦌₂)
  证明: rfl
-/
lemma inverse_map_mkHom_homMk_id {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) (y : Y _⦋0⦌₂) :
    (inverse X Y).map (Prod.mkHom (homMk e) (𝟙 (mk y))) = homMk (e.tensor (.id y)) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `inverse_map_mkHom_id_homMk` / 引理 `inverse_map_mkHom_id_homMk`

English:
lemma inverse_map_mkHom_id_homMk
  given: (x : X _⦋0⦌₂) {y₀ y₁ : Y _⦋0⦌₂} (e : Edge y₀ y₁)
  proof: rfl

中文:
引理 inverse_map_mkHom_id_homMk
  条件: (x : X _⦋0⦌₂) {y₀ y₁ : Y _⦋0⦌₂} (e : 边 y₀ y₁)
  证明: rfl
-/
lemma inverse_map_mkHom_id_homMk (x : X _⦋0⦌₂) {y₀ y₁ : Y _⦋0⦌₂} (e : Edge y₀ y₁) :
    (inverse X Y).map (Prod.mkHom (𝟙 (mk x)) (homMk e)) = homMk ((Edge.id x).tensor e) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `inverse_map_mkHom_homMk_homMk` / 引理 `inverse_map_mkHom_homMk_homMk`

English:
lemma inverse_map_mkHom_homMk_homMk
  statement: {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁)
  proof: homMk_comp_homMk ((Edge.CompStruct.compId e).tensor (Edge.CompStruct.idComp e'))

中文:
引理 inverse_map_mkHom_homMk_homMk
  结论: {x₀ x₁ : X _⦋0⦌₂} (e : 边 x₀ x₁)
  证明: homMk_comp_homMk ((Edge.CompStruct.compId e).tensor (Edge.CompStruct.idComp e'))

Depends on / 依赖: CompStruct, Edge.CompStruct.compId, Edge.CompStruct.idComp, compId, homMk_comp_homMk, idComp, tensor
-/
lemma inverse_map_mkHom_homMk_homMk {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁)
    {y₀ y₁ : Y _⦋0⦌₂} (e' : Edge y₀ y₁) :
    (inverse X Y).map (Prod.mkHom (homMk e) (homMk e')) = homMk (e.tensor e') :=
  homMk_comp_homMk ((Edge.CompStruct.compId e).tensor (Edge.CompStruct.idComp e'))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (X Y) in
/--
Definition of `functorCompInverseIso` / `functorCompInverseIso` 的定义

English:
definition functorCompInverseIso
  signature: : functor X Y ⋙ inverse X Y ≅ 𝟭 _
  body: mkNatIso (fun _ => Iso.refl _) (by
    rintro ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ e
    obtain ⟨ex, ey, rfl⟩ := e.tensor_surjective
    dsimp
    rw [Category.comp_id]; rw [Category.id_comp]; rw [inverse_map_mkHom_homMk_homMk])

中文:
定义 functorCompInverseIso
  签名: : functor X Y ⋙ inverse X Y ≅ 𝟭 _
  定义体: mkNatIso (fun _ => Iso.refl _) (by
    rintro ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ e
    obtain ⟨ex, ey, rfl⟩ := e.tensor_surjective
    dsimp
    rw [Category.comp_id]; rw [Category.id_comp]; rw [inverse_map_mkHom_homMk_homMk])

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Iso.refl, comp_id, e.tensor_surjective, id_comp, inverse_map_mkHom_homMk_homMk, mkNatIso, tensor_surjective
-/
def functorCompInverseIso : functor X Y ⋙ inverse X Y ≅ 𝟭 _ :=
  mkNatIso (fun _ => Iso.refl _) (by
    rintro ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ e
    obtain ⟨ex, ey, rfl⟩ := e.tensor_surjective
    dsimp
    rw [Category.comp_id]; rw [Category.id_comp]; rw [inverse_map_mkHom_homMk_homMk])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `functorCompInverseIso_hom_app` / 引理 `functorCompInverseIso_hom_app`

English:
lemma functorCompInverseIso_hom_app
  given: (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂)
  proof: rfl

中文:
引理 functorCompInverseIso_hom_app
  条件: (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂)
  证明: rfl
-/
lemma functorCompInverseIso_hom_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (functorCompInverseIso X Y).hom.app (mk (x, y)) = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `functorCompInverseIso_inv_app` / 引理 `functorCompInverseIso_inv_app`

English:
lemma functorCompInverseIso_inv_app
  given: (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂)
  proof: rfl

中文:
引理 functorCompInverseIso_inv_app
  条件: (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂)
  证明: rfl
-/
lemma functorCompInverseIso_inv_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (functorCompInverseIso X Y).inv.app (mk (x, y)) = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (X Y) in
/--
Definition of `inverseCompFunctorIso` / `inverseCompFunctorIso` 的定义

English:
definition inverseCompFunctorIso
  signature: : inverse X Y ⋙ functor X Y ≅ 𝟭 _
  body: Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _))
      (fun x₀ x₁ e => by
        ext y : 2
        obtain ⟨y, rfl⟩ := y.mk_surjective
        cat_disch))

中文:
定义 inverseCompFunctorIso
  签名: : inverse X Y ⋙ functor X Y ≅ 𝟭 _
  定义体: Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _))
      (fun x₀ x₁ e => by
        ext y : 2
        obtain ⟨y, rfl⟩ := y.mk_surjective
        cat_disch))

Depends on / 依赖: Functor, Functor.fullyFaithfulCurry.preimageIso, Iso.refl, cat_disch, fullyFaithfulCurry, mkNatIso, mk_surjective, preimageIso, y.mk_surjective
-/
def inverseCompFunctorIso : inverse X Y ⋙ functor X Y ≅ 𝟭 _ :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _))
      (fun x₀ x₁ e => by
        ext y : 2
        obtain ⟨y, rfl⟩ := y.mk_surjective
        cat_disch))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `inverseCompFunctorIso_hom_app` / 引理 `inverseCompFunctorIso_hom_app`

English:
lemma inverseCompFunctorIso_hom_app
  given: (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂)
  proof: rfl

中文:
引理 inverseCompFunctorIso_hom_app
  条件: (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂)
  证明: rfl
-/
lemma inverseCompFunctorIso_hom_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (inverseCompFunctorIso X Y).hom.app (mk x, mk y) = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `inverseCompFunctorIso_inv_app` / 引理 `inverseCompFunctorIso_inv_app`

English:
lemma inverseCompFunctorIso_inv_app
  given: (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂)
  proof: rfl

中文:
引理 inverseCompFunctorIso_inv_app
  条件: (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂)
  证明: rfl
-/
lemma inverseCompFunctorIso_inv_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (inverseCompFunctorIso X Y).inv.app (mk x, mk y) = 𝟙 _ := rfl

variable (X Y)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `functor_comp_inverse` / 引理 `functor_comp_inverse`

English:
lemma functor_comp_inverse
  statement: functor X Y ⋙ inverse X Y = 𝟭 _
  proof: Functor.ext_of_iso (functorCompInverseIso X Y) (fun _ => rfl)

中文:
引理 functor_comp_inverse
  结论: functor X Y ⋙ inverse X Y = 𝟭 _
  证明: Functor.ext_of_iso (functorCompInverseIso X Y) (fun _ => rfl)

Depends on / 依赖: Functor, Functor.ext_of_iso, ext_of_iso, functorCompInverseIso
-/
lemma functor_comp_inverse : functor X Y ⋙ inverse X Y = 𝟭 _ :=
  Functor.ext_of_iso (functorCompInverseIso X Y) (fun _ => rfl)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `inverse_comp_functor` / 引理 `inverse_comp_functor`

English:
lemma inverse_comp_functor
  statement: inverse X Y ⋙ functor X Y = 𝟭 _
  proof: Functor.ext_of_iso (inverseCompFunctorIso X Y) (fun _ => rfl)

中文:
引理 inverse_comp_functor
  结论: inverse X Y ⋙ functor X Y = 𝟭 _
  证明: Functor.ext_of_iso (inverseCompFunctorIso X Y) (fun _ => rfl)

Depends on / 依赖: Functor, Functor.ext_of_iso, ext_of_iso, inverseCompFunctorIso
-/
lemma inverse_comp_functor : inverse X Y ⋙ functor X Y = 𝟭 _ :=
  Functor.ext_of_iso (inverseCompFunctorIso X Y) (fun _ => rfl)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: :
  body: functor X Y
  inverse := inverse X Y
  unitIso := (functorCompInverseIso X Y).symm
  counitIso := inverseCompFunctorIso X Y

中文:
定义 equivalence
  签名: :
  定义体: functor X Y
  inverse := inverse X Y
  unitIso := (functorCompInverseIso X Y).symm
  counitIso := inverseCompFunctorIso X Y

Depends on / 依赖: functor
-/
def equivalence :
    (X otimes Y).HomotopyCategory ≌ X.HomotopyCategory × Y.HomotopyCategory where
  functor := functor X Y
  inverse := inverse X Y
  unitIso := (functorCompInverseIso X Y).symm
  counitIso := inverseCompFunctorIso X Y

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism of categories between
`(X ⊗ Y).HomotopyCategory` and `X.HomotopyCategory ⥤ Y.HomotopyCategory`. -/
@[simps]
/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: :
  body: Cat.Hom.ofFunctor (functor X Y)
  inv := Cat.Hom.ofFunctor (inverse X Y)
  hom_inv_id := by ext; exact functor_comp_inverse X Y
  inv_hom_id := by ext; exact inverse_comp_functor X Y

中文:
定义 iso
  签名: :
  定义体: Cat.Hom.ofFunctor (functor X Y)
  inv := Cat.Hom.ofFunctor (inverse X Y)
  hom_inv_id := by ext; exact functor_comp_inverse X Y
  inv_hom_id := by ext; exact inverse_comp_functor X Y

Depends on / 依赖: Cat.Hom.ofFunctor, functor, ofFunctor
-/
def iso :
    Cat.of ((X otimes Y).HomotopyCategory) ≅ Cat.of (X.HomotopyCategory × Y.HomotopyCategory) where
  hom := Cat.Hom.ofFunctor (functor X Y)
  inv := Cat.Hom.ofFunctor (inverse X Y)
  hom_inv_id := by ext; exact functor_comp_inverse X Y
  inv_hom_id := by ext; exact inverse_comp_functor X Y

set_option backward.isDefEq.respectTransparency.types false in
variable {X} in
/--
Definition of `mapHomotopyCategoryProdIdCompInverseIso` / `mapHomotopyCategoryProdIdCompInverseIso` 的定义

English:
definition mapHomotopyCategoryProdIdCompInverseIso
  signature: (f : X ⟶ X')
  body: Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _)) (fun x₀ x₁ e => by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp
      rfl))

中文:
定义 mapHomotopyCategoryProdIdCompInverseIso
  签名: (f : X ⟶ X')
  定义体: Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _)) (fun x₀ x₁ e => by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp
      rfl))

Depends on / 依赖: Functor, Functor.fullyFaithfulCurry.preimageIso, Iso.refl, fullyFaithfulCurry, mkNatIso, mk_surjective, preimageIso, y.mk_surjective
-/
def mapHomotopyCategoryProdIdCompInverseIso (f : X ⟶ X') :
    (mapHomotopyCategory f).prod (𝟭 _) ⋙ inverse X' Y ≅
      inverse X Y ⋙ mapHomotopyCategory (f ▷ Y) :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _)) (fun x₀ x₁ e => by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp
      rfl))

set_option backward.isDefEq.respectTransparency.types false in
variable {Y} in
/--
Definition of `idProdMapHomotopyCategoryCompInverseIso` / `idProdMapHomotopyCategoryCompInverseIso` 的定义

English:
definition idProdMapHomotopyCategoryCompInverseIso
  signature: (g : Y ⟶ Y')
  body: Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _)) (fun x₀ x₁ e => by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp
      rfl))

中文:
定义 idProdMapHomotopyCategoryCompInverseIso
  签名: (g : Y ⟶ Y')
  定义体: Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _)) (fun x₀ x₁ e => by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp
      rfl))

Depends on / 依赖: Functor, Functor.fullyFaithfulCurry.preimageIso, Iso.refl, fullyFaithfulCurry, mkNatIso, mk_surjective, preimageIso, y.mk_surjective
-/
def idProdMapHomotopyCategoryCompInverseIso (g : Y ⟶ Y') :
    Functor.prod (𝟭 _) (mapHomotopyCategory g) ⋙ inverse X Y' ≅
      inverse X Y ⋙ mapHomotopyCategory (X ◁ g) :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _)) (fun x₀ x₁ e => by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp
      rfl))

set_option backward.isDefEq.respectTransparency.types false in
variable {X} in
/--
lemma `mapHomotopyCategory_prod_id_comp_inverse` / 引理 `mapHomotopyCategory_prod_id_comp_inverse`

English:
lemma mapHomotopyCategory_prod_id_comp_inverse
  given: (f : X ⟶ X')
  proof: Functor.ext_of_iso (mapHomotopyCategoryProdIdCompInverseIso _ _) (fun _ => rfl)

中文:
引理 mapHomotopyCategory_prod_id_comp_inverse
  条件: (f : X ⟶ X')
  证明: Functor.ext_of_iso (mapHomotopyCategoryProdIdCompInverseIso _ _) (fun _ => rfl)

Depends on / 依赖: Functor, Functor.ext_of_iso, ext_of_iso, mapHomotopyCategoryProdIdCompInverseIso
-/
lemma mapHomotopyCategory_prod_id_comp_inverse (f : X ⟶ X') :
    (mapHomotopyCategory f).prod (𝟭 _) ⋙ inverse X' Y =
      inverse X Y ⋙ mapHomotopyCategory (f ▷ Y) :=
  Functor.ext_of_iso (mapHomotopyCategoryProdIdCompInverseIso _ _) (fun _ => rfl)

set_option backward.isDefEq.respectTransparency.types false in
variable {Y} in
/--
lemma `id_prod_mapHomotopyCategory_comp_inverse` / 引理 `id_prod_mapHomotopyCategory_comp_inverse`

English:
lemma id_prod_mapHomotopyCategory_comp_inverse
  given: (g : Y ⟶ Y')
  proof: Functor.ext_of_iso (idProdMapHomotopyCategoryCompInverseIso _ _) (fun _ => rfl)

中文:
引理 id_prod_mapHomotopyCategory_comp_inverse
  条件: (g : Y ⟶ Y')
  证明: Functor.ext_of_iso (idProdMapHomotopyCategoryCompInverseIso _ _) (fun _ => rfl)

Depends on / 依赖: Functor, Functor.ext_of_iso, ext_of_iso, idProdMapHomotopyCategoryCompInverseIso
-/
lemma id_prod_mapHomotopyCategory_comp_inverse (g : Y ⟶ Y') :
    Functor.prod (𝟭 _) (mapHomotopyCategory g) ⋙ inverse X Y' =
      inverse X Y ⋙ mapHomotopyCategory (X ◁ g) :=
  Functor.ext_of_iso (idProdMapHomotopyCategoryCompInverseIso _ _) (fun _ => rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `inverseCompMapHomotopyCategoryFstIso` / `inverseCompMapHomotopyCategoryFstIso` 的定义

English:
definition inverseCompMapHomotopyCategoryFstIso
  signature: :
  body: Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _) (fun y₀ y₁ e => by
      dsimp
      rw [Category.comp_id]
      exact homMk_id x)) (fun x₀ x₁ e => by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp))

中文:
定义 inverseCompMapHomotopyCategoryFstIso
  签名: :
  定义体: Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _) (fun y₀ y₁ e => by
      dsimp
      rw [Category.comp_id]
      exact homMk_id x)) (fun x₀ x₁ e => by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp))

Depends on / 依赖: Category, Category.comp_id, Functor, Functor.fullyFaithfulCurry.preimageIso, Iso.refl, comp_id, fullyFaithfulCurry, homMk_id, mkNatIso, mk_surjective, preimageIso, y.mk_surjective
-/
def inverseCompMapHomotopyCategoryFstIso :
    inverse X Y ⋙ mapHomotopyCategory (fst _ _) ≅ CategoryTheory.Prod.fst _ _ :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _) (fun y₀ y₁ e => by
      dsimp
      rw [Category.comp_id]
      exact homMk_id x)) (fun x₀ x₁ e => by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `inverseCompMapHomotopyCategorySndIso` / `inverseCompMapHomotopyCategorySndIso` 的定义

English:
definition inverseCompMapHomotopyCategorySndIso
  signature: :
  body: Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _)) (fun x₀ x₁ e => by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      dsimp
      simp only [Category.comp_id]
      exact homMk_id y))

中文:
定义 inverseCompMapHomotopyCategorySndIso
  签名: :
  定义体: Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _)) (fun x₀ x₁ e => by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      dsimp
      simp only [Category.comp_id]
      exact homMk_id y))

Depends on / 依赖: Category, Category.comp_id, Functor, Functor.fullyFaithfulCurry.preimageIso, Iso.refl, comp_id, fullyFaithfulCurry, homMk_id, mkNatIso, mk_surjective, preimageIso, y.mk_surjective
-/
def inverseCompMapHomotopyCategorySndIso :
    inverse X Y ⋙ mapHomotopyCategory (snd _ _) ≅ CategoryTheory.Prod.snd _ _ :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => Iso.refl _)) (fun x₀ x₁ e => by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      dsimp
      simp only [Category.comp_id]
      exact homMk_id y))

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `inverse_comp_mapHomotopyCategory_fst` / 引理 `inverse_comp_mapHomotopyCategory_fst`

English:
lemma inverse_comp_mapHomotopyCategory_fst
  proof: Functor.ext_of_iso (inverseCompMapHomotopyCategoryFstIso _ _) (fun _ => rfl)

中文:
引理 inverse_comp_mapHomotopyCategory_fst
  证明: Functor.ext_of_iso (inverseCompMapHomotopyCategoryFstIso _ _) (fun _ => rfl)

Depends on / 依赖: Functor, Functor.ext_of_iso, ext_of_iso, inverseCompMapHomotopyCategoryFstIso
-/
lemma inverse_comp_mapHomotopyCategory_fst :
    inverse X Y ⋙ mapHomotopyCategory (fst _ _) = CategoryTheory.Prod.fst _ _ :=
  Functor.ext_of_iso (inverseCompMapHomotopyCategoryFstIso _ _) (fun _ => rfl)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `inverse_comp_mapHomotopyCategory_snd` / 引理 `inverse_comp_mapHomotopyCategory_snd`

English:
lemma inverse_comp_mapHomotopyCategory_snd
  proof: Functor.ext_of_iso (inverseCompMapHomotopyCategorySndIso _ _) (fun _ => rfl)

中文:
引理 inverse_comp_mapHomotopyCategory_snd
  证明: Functor.ext_of_iso (inverseCompMapHomotopyCategorySndIso _ _) (fun _ => rfl)

Depends on / 依赖: Functor, Functor.ext_of_iso, ext_of_iso, inverseCompMapHomotopyCategorySndIso
-/
lemma inverse_comp_mapHomotopyCategory_snd :
    inverse X Y ⋙ mapHomotopyCategory (snd _ _) = CategoryTheory.Prod.snd _ _ :=
  Functor.ext_of_iso (inverseCompMapHomotopyCategorySndIso _ _) (fun _ => rfl)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `left_unitality` / 引理 `left_unitality`

English:
lemma left_unitality
  given: [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)]
  proof: by
  rw [inverse_comp_mapHomotopyCategory_snd]
  rfl

中文:
引理 left_unitality
  条件: [唯一 (X _⦋0⦌₂)] [子单例 (X _⦋1⦌₂)]
  证明: by
  rw [inverse_comp_mapHomotopyCategory_snd]
  rfl

Depends on / 依赖: inverse_comp_mapHomotopyCategory_snd
-/
lemma left_unitality [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)] :
    CategoryTheory.Prod.snd _ _ = Functor.prod (isoTerminal X).inv.toFunctor (𝟭 _) ⋙
      inverse X Y ⋙ mapHomotopyCategory (snd _ _) := by
  rw [inverse_comp_mapHomotopyCategory_snd]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `right_unitality` / 引理 `right_unitality`

English:
lemma right_unitality
  given: [Unique (Y _⦋0⦌₂)] [Subsingleton (Y _⦋1⦌₂)]
  proof: by
  rw [inverse_comp_mapHomotopyCategory_fst]
  rfl

中文:
引理 right_unitality
  条件: [唯一 (Y _⦋0⦌₂)] [子单例 (Y _⦋1⦌₂)]
  证明: by
  rw [inverse_comp_mapHomotopyCategory_fst]
  rfl

Depends on / 依赖: inverse_comp_mapHomotopyCategory_fst
-/
lemma right_unitality [Unique (Y _⦋0⦌₂)] [Subsingleton (Y _⦋1⦌₂)] :
    CategoryTheory.Prod.fst _ _ = Functor.prod (𝟭 _) (isoTerminal Y).inv.toFunctor ⋙
      inverse X Y ⋙ mapHomotopyCategory (fst _ _) := by
  rw [inverse_comp_mapHomotopyCategory_fst]
  rfl

variable (Z)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `associativity'Iso` / `associativity'Iso` 的定义

English:
definition associativity'Iso
  signature: :
  body: Functor.fullyFaithfulCurry₃.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => mkNatIso (fun z => Iso.refl _)
      (fun z₀ z₁ e => by
        dsimp
        rw [Category.comp_id]; rw [Category.id_comp]; rw [← prod_id]; rw [inverse_map_mkHom_id_homMk]; rw [inverse_map_mkHom_id_homMk]; rw [Categor

中文:
定义 associativity'同构
  签名: :
  定义体: Functor.fullyFaithfulCurry₃.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => mkNatIso (fun z => Iso.refl _)
      (fun z₀ z₁ e => by
        dsimp
        rw [Category.comp_id]; rw [Category.id_comp]; rw [← prod_id]; rw [inverse_map_mkHom_id_homMk]; rw [inverse_map_mkHom_id_homMk]; rw [Categor

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, CategoryTheory, CategoryTheory.Functor.map_id, Edge.id_tensor_id, Functor, Functor.fullyFaithfulCurry, Iso.refl, comp_id, id_comp, id_tensor_id, inverse_map_mkHom_homMk_id, inverse_map_mkHom_id_ho, inverse_map_mkHom_id_homMk, map_id, mkNatIso, mk_surjective, preimageIso, prod_id
-/
def associativity'Iso :
    (prod.associativity ..).inverse ⋙ (inverse X Y).prod (𝟭 _) ⋙ inverse (X otimes Y) Z ⋙
      mapHomotopyCategory (α_ _ _ _).hom ≅
    Functor.prod (𝟭 _) (inverse Y Z) ⋙ inverse X (Y otimes Z) :=
  Functor.fullyFaithfulCurry₃.preimageIso
    (mkNatIso (fun x => mkNatIso (fun y => mkNatIso (fun z => Iso.refl _)
      (fun z₀ z₁ e => by
        dsimp
        rw [Category.comp_id]; rw [Category.id_comp]; rw [← prod_id]; rw [inverse_map_mkHom_id_homMk]; rw [inverse_map_mkHom_id_homMk]; rw [CategoryTheory.Functor.map_id]
        dsimp [← Edge.id_tensor_id]))
      (fun y₀ y₁ e => by
        ext z
        obtain ⟨z, rfl⟩ := z.mk_surjective
        dsimp
        rw [Category.comp_id]; rw [Category.id_comp]; rw [inverse_map_mkHom_homMk_id]; rw [inverse_map_mkHom_id_homMk]))
      (fun x₀ x₁ e => by
        ext y z
        obtain ⟨y, rfl⟩ := y.mk_surjective
        obtain ⟨z, rfl⟩ := z.mk_surjective
        dsimp
        simp only [Category.comp_id, Category.id_comp, ← prod_id',
          CategoryTheory.Functor.map_id, inverse_obj, inverse_map_mkHom_homMk_id]))

set_option backward.isDefEq.respectTransparency.types false in
variable {X Y Z} in
/--
lemma `associativity'Iso_hom_app` / 引理 `associativity'Iso_hom_app`

English:
lemma associativity'Iso_hom_app
  given: (xyz)
  proof: by
  change 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.id_comp]; rw [Category.comp_id]
  rfl

中文:
引理 associativity'Iso_hom_app
  条件: (xyz)
  证明: by
  change 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.id_comp]; rw [Category.comp_id]
  rfl
-/
lemma associativity'Iso_hom_app (xyz) :
    (associativity'Iso X Y Z).hom.app xyz = 𝟙 _ := by
  change 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.id_comp]; rw [Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
open Functor in
/--
Definition of `associativityIso` / `associativityIso` 的定义

English:
definition associativityIso
  signature: :
  body: (Functor.leftUnitor _).symm ≪≫ isoWhiskerRight (Equivalence.unitIso _) _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (prod.associativity _ _ _).functor (associativity'Iso X Y Z)

中文:
定义 associativityIso
  签名: :
  定义体: (Functor.leftUnitor _).symm ≪≫ isoWhiskerRight (Equivalence.unitIso _) _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (prod.associativity _ _ _).functor (associativity'Iso X Y Z)

Depends on / 依赖: Equivalence, Equivalence.unitIso, Functor, Functor.leftUnitor, associativity, associator, functor, isoWhiskerLeft, isoWhiskerRight, leftUnitor, prod.associativity, unitIso
-/
def associativityIso :
    (inverse X Y).prod (𝟭 _) ⋙ inverse (X otimes Y) Z ⋙ mapHomotopyCategory (α_ _ _ _).hom ≅
      (prod.associativity _ _ _).functor ⋙ Functor.prod (𝟭 _) (inverse Y Z) ⋙
        inverse X (Y otimes Z) :=
  (Functor.leftUnitor _).symm ≪≫ isoWhiskerRight (Equivalence.unitIso _) _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (prod.associativity _ _ _).functor (associativity'Iso X Y Z)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {X Y Z} in
/--
lemma `associativityIso_hom_app` / 引理 `associativityIso_hom_app`

English:
lemma associativityIso_hom_app
  given: (xyz)
  proof: by
  dsimp [associativityIso]
  rw [associativity'Iso_hom_app _]
  dsimp
  rw [CategoryTheory.Functor.map_id]; rw [Category.id_comp]; rw [Category.comp_id]; rw [Category.comp_id]; rw [← prod_id]; rw [CategoryTheory.Functor.map_id]; rw [CategoryTheory.Functor.map_id]

中文:
引理 associativityIso_hom_app
  条件: (xyz)
  证明: by
  dsimp [associativityIso]
  rw [associativity'Iso_hom_app _]
  dsimp
  rw [CategoryTheory.Functor.map_id]; rw [Category.id_comp]; rw [Category.comp_id]; rw [Category.comp_id]; rw [← prod_id]; rw [CategoryTheory.Functor.map_id]; rw [CategoryTheory.Functor.map_id]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, CategoryTheory, CategoryTheory.Functor.map_id, Functor, Iso_hom_app, associativity, associativityIso, comp_id, id_comp, map_id, prod_id
-/
lemma associativityIso_hom_app (xyz) :
    (associativityIso X Y Z).hom.app xyz = 𝟙 _ := by
  dsimp [associativityIso]
  rw [associativity'Iso_hom_app _]
  dsimp
  rw [CategoryTheory.Functor.map_id]; rw [Category.id_comp]; rw [Category.comp_id]; rw [Category.comp_id]; rw [← prod_id]; rw [CategoryTheory.Functor.map_id]; rw [CategoryTheory.Functor.map_id]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `associativity` / 引理 `associativity`

English:
lemma associativity
  proof: Functor.ext_of_iso (associativityIso _ _ _) (fun _ => rfl) associativityIso_hom_app

中文:
引理 associativity
  证明: Functor.ext_of_iso (associativityIso _ _ _) (fun _ => rfl) associativityIso_hom_app

Depends on / 依赖: Functor, Functor.ext_of_iso, associativityIso, associativityIso_hom_app, ext_of_iso
-/
lemma associativity :
    (inverse X Y).prod (𝟭 _) ⋙ inverse (X otimes Y) Z ⋙ mapHomotopyCategory (α_ _ _ _).hom =
    (prod.associativity _ _ _).functor ⋙ Functor.prod (𝟭 _) (inverse Y Z) ⋙
      inverse X (Y otimes Z) :=
  Functor.ext_of_iso (associativityIso _ _ _) (fun _ => rfl) associativityIso_hom_app

end BinaryProduct

end HomotopyCategory

set_option backward.isDefEq.respectTransparency.types false in
open HomotopyCategory.BinaryProduct in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: hoFunctor₂.{u}.Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := (HomotopyCategory.isoTerminal _).symm
      μIso X Y := (iso X Y).symm
      μIso_hom_natural_left _ _ := by ext; apply mapHomotopyCategory_prod_id_comp_inverse
      μIso_hom_natural_right _ _ := by ext; apply id_prod_mapHomotopyCategory_comp_inverse
  

中文:
实例 :
  签名: hoFunctor₂.{u}.幺半群
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := (HomotopyCategory.isoTerminal _).symm
      μIso X Y := (iso X Y).symm
      μIso_hom_natural_left _ _ := by ext; apply mapHomotopyCategory_prod_id_comp_inverse
      μIso_hom_natural_right _ _ := by ext; apply id_prod_mapHomotopyCategory_comp_inverse
  

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, HomotopyCategory, HomotopyCategory.isoTerminal, associativity, id_prod_mapHomotopyCategory_comp_inverse, isoTerminal, left_unitality, mapHomotopyCategory_prod_id_comp_inverse, right_unitality, toMonoidal
-/
instance : hoFunctor₂.{u}.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := (HomotopyCategory.isoTerminal _).symm
      μIso X Y := (iso X Y).symm
      μIso_hom_natural_left _ _ := by ext; apply mapHomotopyCategory_prod_id_comp_inverse
      μIso_hom_natural_right _ _ := by ext; apply id_prod_mapHomotopyCategory_comp_inverse
      left_unitality Y := by ext; apply left_unitality
      right_unitality X := by ext; apply right_unitality
      associativity _ _ _ := by ext; apply associativity }

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `hoFunctor.monoidal` / 实例 `hoFunctor.monoidal`

English:
instance hoFunctor.monoidal
  signature: : hoFunctor.{u}.Monoidal
  body: inferInstanceAs (truncation 2 ⋙ hoFunctor₂).Monoidal

中文:
实例 hoFunctor.monoidal
  签名: : hoFunctor.{u}.幺半群
  定义体: inferInstanceAs (truncation 2 ⋙ hoFunctor₂).Monoidal

Depends on / 依赖: Monoidal, truncation
-/
instance hoFunctor.monoidal : hoFunctor.{u}.Monoidal :=
  inferInstanceAs (truncation 2 ⋙ hoFunctor₂).Monoidal

end Truncated

/--
Definition of `hoFunctor.unitHomEquiv` / `hoFunctor.unitHomEquiv` 的定义

English:
definition hoFunctor.unitHomEquiv
  signature: (X : SSet.{u})
  body: (SSet.unitHomEquiv X).trans
    (hoFunctor.obj.equiv.{u} X).symm.trans Cat.fromChosenTerminalEquiv.symm

中文:
定义 hoFunctor.unitHomEquiv
  签名: (X : SSet.{u})
  定义体: (SSet.unitHomEquiv X).trans
    (hoFunctor.obj.equiv.{u} X).symm.trans Cat.fromChosenTerminalEquiv.symm

Depends on / 依赖: Cat.fromChosenTerminalEquiv.symm, SSet.unitHomEquiv, fromChosenTerminalEquiv, hoFunctor, hoFunctor.obj.equiv, symm.trans, unitHomEquiv
-/
def hoFunctor.unitHomEquiv (X : SSet.{u}) :
    (𝟙_ SSet ⟶ X) ≃ Cat.chosenTerminal ⥤ hoFunctor.obj X :=
(SSet.unitHomEquiv X).trans
    (hoFunctor.obj.equiv.{u} X).symm.trans Cat.fromChosenTerminalEquiv.symm

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `hoFunctor.unitHomEquiv_eq` / 定理 `hoFunctor.unitHomEquiv_eq`

English:
theorem hoFunctor.unitHomEquiv_eq
  given: (X : SSet.{u}) (x : 𝟙_ SSet ⟶ X)
  proof: rfl

中文:
定理 hoFunctor.unitHomEquiv_eq
  条件: (X : SSet.{u}) (x : 𝟙_ SSet ⟶ X)
  证明: rfl
-/
theorem hoFunctor.unitHomEquiv_eq (X : SSet.{u}) (x : 𝟙_ SSet ⟶ X) :
    hoFunctor.unitHomEquiv X x =
      (Functor.LaxMonoidal.ε hoFunctor.{u}).toFunctor ⋙ (hoFunctor.map x).toFunctor :=
  rfl

end SSet
