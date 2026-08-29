/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Junyan Xu
-/
module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Bicategory.Free
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# The coherence theorem for bicategories

In this file, we prove the coherence theorem for bicategories, stated in the following form: the
free bicategory over any quiver is locally thin.

The proof is almost the same as the proof of the coherence theorem for monoidal categories that
has been previously formalized in mathlib, which is based on the proof described by Ilya Beylin
and Peter Dybjer. The idea is to view a path on a quiver as a normal form of a 1-morphism in the
free bicategory on the same quiver. A normalization procedure is then described by
`normalize : FreeBicategory B ⥤ᵖ (LocallyDiscrete (Paths B))`, which is a
pseudofunctor from the free bicategory to the locally discrete bicategory on the path category.
It turns out that this pseudofunctor is locally an equivalence of categories, and the coherence
theorem follows immediately from this fact.

## Main statements

* `locally_thin` : the free bicategory is locally thin, that is, there is at most one
  2-morphism between two fixed 1-morphisms.

## References

* [Ilya Beylin and Peter Dybjer, Extracting a proof of coherence for monoidal categories from a
  proof of normalization for monoids][beylin1996]
-/

@[expose] public section


open Quiver (Path)

open Quiver.Path

namespace CategoryTheory

open Bicategory Category

universe v u

namespace FreeBicategory

variable {B : Type u} [Quiver.{v} B]

/-- Auxiliary definition for `inclusionPath`. -/
@[simp]
/--
Definition of `inclusionPathAux` / `inclusionPathAux` 的定义

English:
definition inclusionPathAux
  signature: {a : B}

中文:
定义 inclusionPathAux
  签名: {a : B}

Depends on / 依赖: homCategory
-/
def inclusionPathAux {a : B} : forall {b : B}, Path a b -> Hom a b
  | _, nil => Hom.id a
  | _, cons p f => (inclusionPathAux p).comp (Hom.of f)

/-- Category structure on `Hom a b`. In this file, we will use `Hom a b` for `a b : B`
(precisely, `FreeBicategory.Hom a b`) instead of the definitionally equal expression
`a ⟶ b` for `a b : FreeBicategory B`. The main reason is that we have to annoyingly write
`@Quiver.Hom (FreeBicategory B) _ a b` to get the latter expression when given `a b : B`. -/
local instance homCategory' (a b : B) : Category (Hom a b) :=
  homCategory a b

/--
Definition of `inclusionPath` / `inclusionPath` 的定义

English:
definition inclusionPath
  signature: (a b : B)
  body: Discrete.functor inclusionPathAux

中文:
定义 inclusionPath
  签名: (a b : B)
  定义体: Discrete.functor inclusionPathAux

Depends on / 依赖: Discrete, Discrete.functor, functor, inclusionPathAux
-/
def inclusionPath (a b : B) : Discrete (Path.{v} a b) ⥤ Hom a b :=
  Discrete.functor inclusionPathAux

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `preinclusion` / `preinclusion` 的定义

English:
definition preinclusion
  signature: (B : Type u) [Quiver.{v} B]
  body: a.as
  map {a b} f := (@inclusionPath B _ a.as b.as).obj f
  map₂ η := (inclusionPath _ _).map η

@[simp]

中文:
定义 preinclusion
  签名: (B : 类型u) [箭图.{v} B]
  定义体: a.as
  map {a b} f := (@inclusionPath B _ a.as b.as).obj f
  map₂ η := (inclusionPath _ _).map η

@[simp]

Depends on / 依赖: a.as
-/
def preinclusion (B : Type u) [Quiver.{v} B] :
    PrelaxFunctor (LocallyDiscrete (Paths B)) (FreeBicategory B) where
  obj a := a.as
  map {a b} f := (@inclusionPath B _ a.as b.as).obj f
  map₂ η := (inclusionPath _ _).map η

@[simp]
/--
theorem `preinclusion_obj` / 定理 `preinclusion_obj`

English:
theorem preinclusion_obj
  given: (a : B)
  statement: (preinclusion B).obj ⟨a⟩ = a
  proof: rfl

中文:
定理 preinclusion_obj
  条件: (a : B)
  结论: (preinclusion B).obj ⟨a⟩ = a
  证明: rfl
-/
theorem preinclusion_obj (a : B) : (preinclusion B).obj ⟨a⟩ = a :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `preinclusion_map₂` / 定理 `preinclusion_map₂`

English:
theorem preinclusion_map₂
  given: {a b : B} (f g : Discrete (Path.{v} a b)) (η : f ⟶ g)
  proof: rfl

中文:
定理 preinclusion_map₂
  条件: {a b : B} (f g : 离散 (道路.{v} a b)) (η : f ⟶ g)
  证明: rfl
-/
theorem preinclusion_map₂ {a b : B} (f g : Discrete (Path.{v} a b)) (η : f ⟶ g) :
    (preinclusion B).map₂ η = eqToHom (congr_arg _ (Discrete.ext (Discrete.eq_of_hom η))) :=
  rfl

/-- The normalization of the composition of `p : Path a b` and `f : Hom b c`.
`p` will eventually be taken to be `nil` and we then get the normalization
of `f` alone, but the auxiliary `p` is necessary for Lean to accept the definition of
`normalizeIso` and the `whisker_left` case of `normalizeAux_congr` and `normalize_naturality`.
-/
@[simp]
/--
Definition of `normalizeAux` / `normalizeAux` 的定义

English:
definition normalizeAux
  signature: {a : B}

中文:
定义 normalizeAux
  签名: {a : B}
-/
def normalizeAux {a : B} : forall {b c : B}, Path a b -> Hom b c -> Path a c
  | _, _, p, Hom.of f => p.cons f
  | _, _, p, Hom.id _ => p
  | _, _, p, Hom.comp f g => normalizeAux (normalizeAux p f) g

/-
We may define
```
def normalizeAux' : ∀ {a b : B}, Hom a b → Path a b
  | _, _, (Hom.of f) => f.toPath
  | _, _, (Hom.id b) => nil
  | _, _, (Hom.comp f g) => (normalizeAux' f).comp (normalizeAux' g)
```
and define `normalizeAux p f` to be `p.comp (normalizeAux' f)` and this will be
equal to the above definition, but the equality proof requires `comp_assoc`, and it
thus lacks the correct definitional property to make the definition of `normalizeIso`
typecheck.
```
example {a b c : B} (p : Path a b) (f : Hom b c) :
    normalizeAux p f = p.comp (normalizeAux' f) := by
  induction f; rfl; rfl;
  case comp _ _ _ _ _ ihf ihg => rw [normalizeAux, ihf, ihg]; apply comp_assoc
```
-/
set_option backward.isDefEq.respectTransparency.types false in
/-- A 2-isomorphism between a partially-normalized 1-morphism in the free bicategory to the
fully-normalized 1-morphism.
-/
@[simp]
/--
Definition of `normalizeIso` / `normalizeIso` 的定义

English:
definition normalizeIso
  signature: {a : B}

中文:
定义 normalizeIso
  签名: {a : B}
-/
def normalizeIso {a : B} :
    forall {b c : B} (p : Path a b) (f : Hom b c),
      (preinclusion B).map ⟨p⟩ ≫ f ≅ (preinclusion B).map ⟨normalizeAux p f⟩
  | _, _, _, Hom.of _ => Iso.refl _
  | _, _, _, Hom.id b => ρ_ _
  | _, _, p, Hom.comp f g =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIso p f) g ≪≫ normalizeIso (normalizeAux p f) g

-- Equation lemmas for `normalizeIso`/`normalizeAux` matching `≫`/`𝟙`
-- (i.e., `CategoryStruct.comp`/`CategoryStruct.id` for `FreeBicategory`) instead of
-- `Hom.comp`/`Hom.id`. Needed because after leanprover/lean4#13363, `canUnfoldAtMatcher`
-- no longer unfolds class projections in match discriminants.
/--
theorem `normalizeAux_comp` / 定理 `normalizeAux_comp`

English:
theorem normalizeAux_comp
  statement: {a : B} {b c d : FreeBicategory B}
  proof: rfl

中文:
定理 normalizeAux_comp
  结论: {a : B} {b c d : FreeBicategory B}
  证明: rfl
-/
@[simp] theorem normalizeAux_comp {a : B} {b c d : FreeBicategory B}
    (p : Path a b) (f : b ⟶ c) (g : c ⟶ d) :
    normalizeAux p (f ≫ g) = normalizeAux (normalizeAux p f) g := rfl

/--
theorem `normalizeAux_id` / 定理 `normalizeAux_id`

English:
theorem normalizeAux_id
  given: {a : B} {b : FreeBicategory B} (p : Path a b)
  proof: rfl

中文:
定理 normalizeAux_id
  条件: {a : B} {b : FreeBicategory B} (p : 道路 a b)
  证明: rfl
-/
@[simp] theorem normalizeAux_id {a : B} {b : FreeBicategory B} (p : Path a b) :
    normalizeAux p (𝟙 b) = p := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `normalizeIso_comp` / 定理 `normalizeIso_comp`

English:
theorem normalizeIso_comp
  statement: {a : B} {b c d : FreeBicategory B}
  proof: rfl

中文:
定理 normalizeIso_comp
  结论: {a : B} {b c d : FreeBicategory B}
  证明: rfl
-/
@[simp] theorem normalizeIso_comp {a : B} {b c d : FreeBicategory B}
    (p : Path a b) (f : b ⟶ c) (g : c ⟶ d) :
    normalizeIso p (f ≫ g) =
      (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIso p f) g ≪≫
        normalizeIso (normalizeAux p f) g := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `normalizeIso_id` / 定理 `normalizeIso_id`

English:
theorem normalizeIso_id
  given: {a : B} {b : FreeBicategory B} (p : Path a b)
  proof: rfl

中文:
定理 normalizeIso_id
  条件: {a : B} {b : FreeBicategory B} (p : 道路 a b)
  证明: rfl
-/
@[simp] theorem normalizeIso_id {a : B} {b : FreeBicategory B} (p : Path a b) :
    normalizeIso p (𝟙 b) = ρ_ _ := rfl

/--
theorem `quot_whisker_left` / 定理 `quot_whisker_left`

English:
theorem quot_whisker_left
  statement: {a b c : FreeBicategory B} (f : a ⟶ b) {g h : b ⟶ c}
  proof: rfl

中文:
定理 quot_whisker_left
  结论: {a b c : FreeBicategory B} (f : a ⟶ b) {g h : b ⟶ c}
  证明: rfl
-/
@[simp] theorem quot_whisker_left {a b c : FreeBicategory B} (f : a ⟶ b) {g h : b ⟶ c}
    (η : Hom₂ g h) : Quot.mk Rel (Hom₂.whisker_left f η) = f ◁ (Quot.mk Rel η) := rfl

/--
theorem `normalizeAux_congr` / 定理 `normalizeAux_congr`

English:
theorem normalizeAux_congr
  given: {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g)
  proof: by
  rcases η with ⟨η'⟩
  apply @congr_fun _ _ fun p => normalizeAux p f
  clear p η
  induction η' with
  | vcomp _ _ _ _ => apply Eq.trans <;> assumption
  | whisker_left _ _ ih => funext; apply congr_fun ih
  | whisker_right _ _ ih => funext; apply congr_arg₂ _ (congr_fun ih _) rfl
  | _ => funex

中文:
定理 normalizeAux_congr
  条件: {a b c : B} (p : 道路 a b) {f g : 态射 b c} (η : f ⟶ g)
  证明: by
  rcases η with ⟨η'⟩
  apply @congr_fun _ _ fun p => normalizeAux p f
  clear p η
  induction η' with
  | vcomp _ _ _ _ => apply Eq.trans <;> assumption
  | whisker_left _ _ ih => funext; apply congr_fun ih
  | whisker_right _ _ ih => funext; apply congr_arg₂ _ (congr_fun ih _) rfl
  | _ => funex

Depends on / 依赖: Eq.trans, congr_fun, normalizeAux, whisker_left, whisker_right
-/
theorem normalizeAux_congr {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g) :
    normalizeAux p f = normalizeAux p g := by
  rcases η with ⟨η'⟩
  apply @congr_fun _ _ fun p => normalizeAux p f
  clear p η
  induction η' with
  | vcomp _ _ _ _ => apply Eq.trans <;> assumption
  | whisker_left _ _ ih => funext; apply congr_fun ih
  | whisker_right _ _ ih => funext; apply congr_arg₂ _ (congr_fun ih _) rfl
  | _ => funext; rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `normalize_naturality` / 定理 `normalize_naturality`

English:
theorem normalize_naturality
  given: {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g)
  proof: by
  rcases η with ⟨η'⟩; clear η
  induction η' with
  | id => simp
  | vcomp η θ ihf ihg =>
    simp only [mk_vcomp, whiskerLeft_comp]
    slice_lhs 2 3 => rw [ihg]
    slice_lhs 1 2 => rw [ihf]
    simp
  -- p ≠ nil required! See the docstring of `normalizeAux`.
  | whisker_left _ _ ih =>
    dsim

中文:
定理 normalize_naturality
  条件: {a b c : B} (p : 道路 a b) {f g : 态射 b c} (η : f ⟶ g)
  证明: by
  rcases η with ⟨η'⟩; clear η
  induction η' with
  | id => simp
  | vcomp η θ ihf ihg =>
    simp only [mk_vcomp, whiskerLeft_comp]
    slice_lhs 2 3 => rw [ihg]
    slice_lhs 1 2 => rw [ihf]
    simp
  -- p ≠ nil required! See the docstring of `normalizeAux`.
  | whisker_left _ _ ih =>
    dsim

Depends on / 依赖: mk_vcomp, slice_lhs, whiskerLeft_comp
-/
theorem normalize_naturality {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g) :
    (preinclusion B).map ⟨p⟩ ◁ η ≫ (normalizeIso p g).hom =
      (normalizeIso p f).hom ≫
        (preinclusion B).map₂ (eqToHom (Discrete.ext (normalizeAux_congr p η))) := by
  rcases η with ⟨η'⟩; clear η
  induction η' with
  | id => simp
  | vcomp η θ ihf ihg =>
    simp only [mk_vcomp, whiskerLeft_comp]
    slice_lhs 2 3 => rw [ihg]
    slice_lhs 1 2 => rw [ihf]
    simp
  -- p ≠ nil required! See the docstring of `normalizeAux`.
  | whisker_left _ _ ih =>
    dsimp
    rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange_assoc]; rw [ih]
    simp
  | whisker_right h η' ih =>
    dsimp
    rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; rw [ih]; rw [comp_whiskerRight]
    have := dcongr_arg (fun x => (normalizeIso x h).hom) (normalizeAux_congr p (Quot.mk _ η'))
    dsimp at this; simp [this]
  | _ => simp

-- Not `@[simp]` because it is not in `simp`-normal form.
/--
theorem `normalizeAux_nil_comp` / 定理 `normalizeAux_nil_comp`

English:
theorem normalizeAux_nil_comp
  given: {a b c : B} (f : Hom a b) (g : Hom b c)
  proof: by
  induction g generalizing a with
  | id => rfl
  | of => rfl
  | comp g _ ihf ihg => erw [ihg (f.comp g), ihf f, ihg g, comp_assoc]

中文:
定理 normalizeAux_nil_comp
  条件: {a b c : B} (f : 态射 a b) (g : 态射 b c)
  证明: by
  induction g generalizing a with
  | id => rfl
  | of => rfl
  | comp g _ ihf ihg => erw [ihg (f.comp g), ihf f, ihg g, comp_assoc]

Depends on / 依赖: comp_assoc, f.comp, generalizing
-/
theorem normalizeAux_nil_comp {a b c : B} (f : Hom a b) (g : Hom b c) :
    normalizeAux nil (f.comp g) = (normalizeAux nil f).comp (normalizeAux nil g) := by
  induction g generalizing a with
  | id => rfl
  | of => rfl
  | comp g _ ihf ihg => erw [ihg (f.comp g), ihf f, ihg g, comp_assoc]

/--
Definition of `normalize` / `normalize` 的定义

English:
definition normalize
  signature: (B : Type u) [Quiver.{v} B]
  body: ⟨a⟩
  map f := ⟨normalizeAux nil f⟩
map₂ η := eqToHom Discrete.ext normalizeAux_congr nil η
mapId _ := eqToIso Discrete.ext rfl
mapComp f g := eqToIso Discrete.ext normalizeAux_nil_comp f g

中文:
定义 normalize
  签名: (B : 类型u) [箭图.{v} B]
  定义体: ⟨a⟩
  map f := ⟨normalizeAux nil f⟩
map₂ η := eqToHom Discrete.ext normalizeAux_congr nil η
mapId _ := eqToIso Discrete.ext rfl
mapComp f g := eqToIso Discrete.ext normalizeAux_nil_comp f g
-/
def normalize (B : Type u) [Quiver.{v} B] :
    FreeBicategory B ⥤ᵖ (LocallyDiscrete (Paths B)) where
  obj a := ⟨a⟩
  map f := ⟨normalizeAux nil f⟩
map₂ η := eqToHom Discrete.ext normalizeAux_congr nil η
mapId _ := eqToIso Discrete.ext rfl
mapComp f g := eqToIso Discrete.ext normalizeAux_nil_comp f g

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `normalizeUnitIso` / `normalizeUnitIso` 的定义

English:
definition normalizeUnitIso
  signature: (a b : FreeBicategory B)
  body: NatIso.ofComponents (fun f => (fun_ f).symm ≪≫ normalizeIso nil f)
    (by
      intro f g η
      erw [leftUnitor_inv_naturality_assoc, assoc]
      congr 1
      exact normalize_naturality nil η)

中文:
定义 normalizeUnitIso
  签名: (a b : FreeBicategory B)
  定义体: NatIso.ofComponents (fun f => (fun_ f).symm ≪≫ normalizeIso nil f)
    (by
      intro f g η
      erw [leftUnitor_inv_naturality_assoc, assoc]
      congr 1
      exact normalize_naturality nil η)

Depends on / 依赖: NatIso, NatIso.ofComponents, fun_, leftUnitor_inv_naturality_assoc, normalizeIso, normalize_naturality, ofComponents
-/
def normalizeUnitIso (a b : FreeBicategory B) :
    𝟭 (a ⟶ b) ≅ (normalize B).mapFunctor a b ⋙ @inclusionPath B _ a b :=
  NatIso.ofComponents (fun f => (fun_ f).symm ≪≫ normalizeIso nil f)
    (by
      intro f g η
      erw [leftUnitor_inv_naturality_assoc, assoc]
      congr 1
      exact normalize_naturality nil η)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `normalizeEquiv` / `normalizeEquiv` 的定义

English:
definition normalizeEquiv
  signature: (a b : B)
  body: Equivalence.mk ((normalize _).mapFunctor a b) (inclusionPath a b) (normalizeUnitIso a b)
    (Discrete.natIso fun f => eqToIso (by
      obtain ⟨f⟩ := f
      induction f with
      | nil => rfl
      | cons _ _ ih =>
        ext1 -- Porting note: `tidy` closes the goal in mathlib3 but `aesop` doesn

中文:
定义 normalizeEquiv
  签名: (a b : B)
  定义体: Equivalence.mk ((normalize _).mapFunctor a b) (inclusionPath a b) (normalizeUnitIso a b)
    (Discrete.natIso fun f => eqToIso (by
      obtain ⟨f⟩ := f
      induction f with
      | nil => rfl
      | cons _ _ ih =>
        ext1 -- Porting note: `tidy` closes the goal in mathlib3 but `aesop` doesn

Depends on / 依赖: Discrete, Discrete.natIso, Equivalence, Equivalence.mk, Porting, closes, conv_rhs, eqToIso, inclusionPath, injection, mapFunctor, mathlib3, natIso, normalize, normalizeUnitIso
-/
def normalizeEquiv (a b : B) : Hom a b ≌ Discrete (Path.{v} a b) :=
  Equivalence.mk ((normalize _).mapFunctor a b) (inclusionPath a b) (normalizeUnitIso a b)
    (Discrete.natIso fun f => eqToIso (by
      obtain ⟨f⟩ := f
      induction f with
      | nil => rfl
      | cons _ _ ih =>
        ext1 -- Porting note: `tidy` closes the goal in mathlib3 but `aesop` doesn't here.
        injection ih with ih
        conv_rhs => rw [← ih]
        rfl))

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `locally_thin` / 实例 `locally_thin`

English:
instance locally_thin
  signature: {a b : FreeBicategory B}
  body: fun _ _ =>
  ⟨fun _ _ =>
    (@normalizeEquiv B _ a b).functor.map_injective (Subsingleton.elim _ _)⟩

中文:
实例 locally_thin
  签名: {a b : FreeBicategory B}
  定义体: fun _ _ =>
  ⟨fun _ _ =>
    (@normalizeEquiv B _ a b).functor.map_injective (Subsingleton.elim _ _)⟩
-/
instance locally_thin {a b : FreeBicategory B} : Quiver.IsThin (a ⟶ b) := fun _ _ =>
  ⟨fun _ _ =>
    (@normalizeEquiv B _ a b).functor.map_injective (Subsingleton.elim _ _)⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `inclusionMapCompAux` / `inclusionMapCompAux` 的定义

English:
definition inclusionMapCompAux
  signature: {a b : B}

中文:
定义 inclusionMapCompAux
  签名: {a b : B}
-/
def inclusionMapCompAux {a b : B} :
    forall {c : B} (f : Path a b) (g : Path b c),
      (preinclusion _).map (⟨f⟩ ≫ ⟨g⟩) ≅ (preinclusion _).map ⟨f⟩ ≫ (preinclusion _).map ⟨g⟩
  | _, f, nil => (ρ_ ((preinclusion _).map ⟨f⟩)).symm
  | _, f, cons g₁ g₂ => whiskerRightIso (inclusionMapCompAux f g₁) (Hom.of g₂) ≪≫ α_ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: (B : Type u) [Quiver.{v} B]
  body: { -- All the conditions for 2-morphisms are trivial thanks to the coherence theorem!
    preinclusion B with
    mapId := fun _ => Iso.refl _
    mapComp := fun f g => inclusionMapCompAux f.as g.as }

中文:
定义 inclusion
  签名: (B : 类型u) [箭图.{v} B]
  定义体: { -- All the conditions for 2-morphisms are trivial thanks to the coherence theorem!
    preinclusion B with
    mapId := fun _ => Iso.refl _
    mapComp := fun f g => inclusionMapCompAux f.as g.as }

Depends on / 依赖: Iso.refl, coherence, conditions, f.as, g.as, inclusionMapCompAux, mapComp, morphisms, preinclusion, thanks, theorem
-/
def inclusion (B : Type u) [Quiver.{v} B] :
    LocallyDiscrete (Paths B) ⥤ᵖ (FreeBicategory B) :=
  { -- All the conditions for 2-morphisms are trivial thanks to the coherence theorem!
    preinclusion B with
    mapId := fun _ => Iso.refl _
    mapComp := fun f g => inclusionMapCompAux f.as g.as }

end FreeBicategory

end CategoryTheory
