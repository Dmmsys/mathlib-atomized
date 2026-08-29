/-
Copyright (c) 2026 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar, Arnoud van der Leer
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveCodiscrete
public import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
public import Mathlib.CategoryTheory.CodiscreteCategory

/-!
# The Coherent Isomorphism

We define the free walking isomorphism `WalkingIso`; the category with objects `zero` and
`one` and unique morphisms `zero ⟶ one` and `one ⟶ zero`. We construct an equivalence
`WalkingIso.equiv` between the type of functors from `WalkingIso` into any category `C` and the type
`Σ (X : C) (Y : C), (X ≅ Y)` of isomorphisms in that category.

The simplicial set `SSet.coherentIso` is defined as the nerve of `WalkingIso`, with
`coherentIso.x₀` and `coherentIso.x₁` the `0`-simplices corresponding to `WalkingIso.zero`
and `WalkingIso.one` respectively, and `coherentIso.hom : Edge x₀ x₁` and
`coherentIso.inv : Edge x₁ x₀` forward and backward edges corresponding to the morphisms in
`WalkingIso`. Given any simplicial set `X`, with a morphism `g : coherentIso ⟶ X`, `0`-simplices
`x₀ x₁: X _⦋0⦌` and an edge between them `f : Edge x₀ x₁`, such that `g` sends `coherentIso.hom` to
`f`, then `f` has an inverse (in the sense of `Edge.InvStruct`), see `invStructOfEqMapHom`.

-/

@[expose] public section

universe w u v

open CategoryTheory

namespace CategoryTheory

/--
Definition of `WalkingIso` / `WalkingIso` 的定义

English:
abbreviation WalkingIso
  signature: : Type w
  body: Codiscrete (ULift Bool)

中文:
缩写 WalkingIso
  签名: : Type w
  定义体: Codiscrete (ULift Bool)

Depends on / 依赖: Codiscrete
-/
abbrev WalkingIso : Type w := Codiscrete (ULift Bool)

namespace WalkingIso

/--
Definition of `equivBool` / `equivBool` 的定义

English:
definition equivBool
  signature: : WalkingIso.{w} ≃ Bool
  body: codiscreteEquiv.trans Equiv.ulift

中文:
定义 equivBool
  签名: : WalkingIso.{w} ≃ 布尔
  定义体: codiscreteEquiv.trans Equiv.ulift

Depends on / 依赖: Equiv.ulift, codiscreteEquiv, codiscreteEquiv.trans
-/
def equivBool : WalkingIso.{w} ≃ Bool := codiscreteEquiv.trans Equiv.ulift

section

variable {C : Type u} [Category.{v} C]

/--
Definition of `zero` / `zero` 的定义

English:
definition zero
  signature: : WalkingIso.{w}
  body: .mk (.up false)

中文:
定义 zero
  签名: : WalkingIso.{w}
  定义体: .mk (.up false)
-/
def zero : WalkingIso.{w} := .mk (.up false)

/--
Definition of `one` / `one` 的定义

English:
definition one
  signature: : WalkingIso.{w}
  body: .mk (.up true)

中文:
定义 one
  签名: : WalkingIso.{w}
  定义体: .mk (.up true)
-/
def one : WalkingIso.{w} := .mk (.up true)

/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: : zero.{w} ≅ one
  body: Codiscrete.iso zero one

中文:
定义 iso
  签名: : zero.{w} ≅ one
  定义体: Codiscrete.iso zero one

Depends on / 依赖: Codiscrete, Codiscrete.iso
-/
def iso : zero.{w} ≅ one := Codiscrete.iso zero one

/--
lemma `eq_iso_hom` / 引理 `eq_iso_hom`

English:
lemma eq_iso_hom
  given: (f : zero.{w} ⟶ one)
  statement: f = iso.{w}.hom
  proof: Codiscrete.eq_iso_hom f

中文:
引理 eq_iso_hom
  条件: (f : zero.{w} ⟶ one)
  结论: f = iso.{w}.hom
  证明: Codiscrete.eq_iso_hom f

Depends on / 依赖: Codiscrete, Codiscrete.eq_iso_hom, eq_iso_hom
-/
lemma eq_iso_hom (f : zero.{w} ⟶ one) : f = iso.{w}.hom := Codiscrete.eq_iso_hom f

/--
lemma `eq_iso_inv` / 引理 `eq_iso_inv`

English:
lemma eq_iso_inv
  given: (f : one.{w} ⟶ zero)
  statement: f = iso.{w}.inv
  proof: Codiscrete.eq_iso_inv f

中文:
引理 eq_iso_inv
  条件: (f : one.{w} ⟶ zero)
  结论: f = iso.{w}.inv
  证明: Codiscrete.eq_iso_inv f

Depends on / 依赖: Codiscrete, Codiscrete.eq_iso_inv, eq_iso_inv
-/
lemma eq_iso_inv (f : one.{w} ⟶ zero) : f = iso.{w}.inv := Codiscrete.eq_iso_inv f

/-- Functors out of `WalkingIso` define isomorphisms in the target category. -/
@[simps!]
/--
Definition of `toIso` / `toIso` 的定义

English:
definition toIso
  signature: (F : WalkingIso.{w} ⥤ C)
  body: F.mapIso iso

中文:
定义 toIso
  签名: (F : WalkingIso.{w} ⥤ C)
  定义体: F.mapIso iso

Depends on / 依赖: F.mapIso, mapIso
-/
def toIso (F : WalkingIso.{w} ⥤ C) : F.obj zero ≅ F.obj one := F.mapIso iso

section induction

variable {motive : WalkingIso.{u} -> Sort*} (zero : motive zero) (one : motive one)

/-- The recursor for WalkingIso, which constructs a term of `∏ (x : WalkingIso), A x` from
a term of `A zero` and a term of `A one`. -/
@[elab_as_elim, induction_eliminator]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: : forall a, motive a

中文:
定义 rec
  签名: : 对任意 a, motive a
-/
protected def rec : forall a, motive a
  | .mk (.up false) => zero
  | .mk (.up true) => one

/--
lemma `rec_zero` / 引理 `rec_zero`

English:
lemma rec_zero
  statement: WalkingIso.rec zero one .zero = zero
  proof: rfl

中文:
引理 rec_zero
  结论: WalkingIso.rec zero one .zero = zero
  证明: rfl
-/
@[simp] lemma rec_zero : WalkingIso.rec zero one .zero = zero := rfl
/--
lemma `rec_one` / 引理 `rec_one`

English:
lemma rec_one
  statement: WalkingIso.rec zero one .one = one
  proof: rfl

中文:
引理 rec_one
  结论: WalkingIso.rec zero one .one = one
  证明: rfl
-/
@[simp] lemma rec_one : WalkingIso.rec zero one .one = one := rfl

end induction

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `fromIso` / `fromIso` 的定义

English:
definition fromIso
  signature: {X Y : C} (e : X ≅ Y)
  body: by induction x; exacts [X, Y]
  map {x y} _ := by induction x <;> induction y; exacts [𝟙 X, e.hom, e.inv, 𝟙 Y]
  map_comp {x y z} _ _ := by induction x <;> induction y <;> induction z <;> simp
  map_id {x} := by induction x <;> rfl

中文:
定义 fromIso
  签名: {X Y : C} (e : X ≅ Y)
  定义体: by induction x; exacts [X, Y]
  map {x y} _ := by induction x <;> induction y; exacts [𝟙 X, e.hom, e.inv, 𝟙 Y]
  map_comp {x y z} _ _ := by induction x <;> induction y <;> induction z <;> simp
  map_id {x} := by induction x <;> rfl

Depends on / 依赖: e.hom, e.inv, exacts, map_comp, map_id
-/
def fromIso {X Y : C} (e : X ≅ Y) : WalkingIso.{w} ⥤ C where
  obj x := by induction x; exacts [X, Y]
  map {x y} _ := by induction x <;> induction y; exacts [𝟙 X, e.hom, e.inv, 𝟙 Y]
  map_comp {x y z} _ _ := by induction x <;> induction y <;> induction z <;> simp
  map_id {x} := by induction x <;> rfl

section

variable {X Y : C} (e : X ≅ Y)

@[simp]
/--
lemma `fromIso_zero` / 引理 `fromIso_zero`

English:
lemma fromIso_zero
  statement: (fromIso.{w} e).obj .zero = X
  proof: rfl

@[simp]

中文:
引理 fromIso_zero
  结论: (fromIso.{w} e).obj .zero = X
  证明: rfl

@[simp]
-/
lemma fromIso_zero : (fromIso.{w} e).obj .zero = X := rfl

@[simp]
/--
lemma `fromIso_one` / 引理 `fromIso_one`

English:
lemma fromIso_one
  statement: (fromIso.{w} e).obj .one = Y
  proof: rfl

@[simp]

中文:
引理 fromIso_one
  结论: (fromIso.{w} e).obj .one = Y
  证明: rfl

@[simp]
-/
lemma fromIso_one : (fromIso.{w} e).obj .one = Y := rfl

@[simp]
/--
lemma `fromIso_map_zero_zero` / 引理 `fromIso_map_zero_zero`

English:
lemma fromIso_map_zero_zero
  given: (f : zero ⟶ zero)
  statement: (fromIso.{w} e).map f = 𝟙 X
  proof: rfl

@[simp]

中文:
引理 fromIso_map_zero_zero
  条件: (f : zero ⟶ zero)
  结论: (fromIso.{w} e).map f = 𝟙 X
  证明: rfl

@[simp]
-/
lemma fromIso_map_zero_zero (f : zero ⟶ zero) : (fromIso.{w} e).map f = 𝟙 X := rfl

@[simp]
/--
lemma `fromIso_hom` / 引理 `fromIso_hom`

English:
lemma fromIso_hom
  given: (f : zero ⟶ one)
  statement: (fromIso.{w} e).map f = e.hom
  proof: rfl

@[simp]

中文:
引理 fromIso_hom
  条件: (f : zero ⟶ one)
  结论: (fromIso.{w} e).map f = e.hom
  证明: rfl

@[simp]
-/
lemma fromIso_hom (f : zero ⟶ one) : (fromIso.{w} e).map f = e.hom := rfl

@[simp]
/--
lemma `fromIso_inv` / 引理 `fromIso_inv`

English:
lemma fromIso_inv
  given: (f : one ⟶ zero)
  statement: (fromIso.{w} e).map f = e.inv
  proof: rfl

@[simp]

中文:
引理 fromIso_inv
  条件: (f : one ⟶ zero)
  结论: (fromIso.{w} e).map f = e.inv
  证明: rfl

@[simp]
-/
lemma fromIso_inv (f : one ⟶ zero) : (fromIso.{w} e).map f = e.inv := rfl

@[simp]
/--
lemma `fromIso_map_one_one` / 引理 `fromIso_map_one_one`

English:
lemma fromIso_map_one_one
  given: (f : one ⟶ one)
  statement: (fromIso.{w} e).map f = 𝟙 Y
  proof: rfl

中文:
引理 fromIso_map_one_one
  条件: (f : one ⟶ one)
  结论: (fromIso.{w} e).map f = 𝟙 Y
  证明: rfl
-/
lemma fromIso_map_one_one (f : one ⟶ one) : (fromIso.{w} e).map f = 𝟙 Y := rfl

end

set_option backward.isDefEq.respectTransparency false in
/-- An equivalence between the type of `WalkingIso`s in `C` and the type of isomorphisms in `C`. -/
@[simps]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : (WalkingIso.{w} ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where
  body: ⟨F.obj zero, F.obj one, toIso F⟩
  invFun p := fromIso p.2.2
  right_inv := fun ⟨X, Y, e⟩ => rfl
left_inv F := Functor.ext (by rintro (_ | _) <;> rfl) by
      intro X Y f
      induction X <;>
      induction Y <;>
      simp [Codiscrete.eq_id] <;>
      rfl

中文:
定义 equiv
  签名: : (WalkingIso.{w} ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where
  定义体: ⟨F.obj zero, F.obj one, toIso F⟩
  invFun p := fromIso p.2.2
  right_inv := fun ⟨X, Y, e⟩ => rfl
left_inv F := Functor.ext (by rintro (_ | _) <;> rfl) by
      intro X Y f
      induction X <;>
      induction Y <;>
      simp [Codiscrete.eq_id] <;>
      rfl

Depends on / 依赖: F.obj
-/
def equiv : (WalkingIso.{w} ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where
  toFun F := ⟨F.obj zero, F.obj one, toIso F⟩
  invFun p := fromIso p.2.2
  right_inv := fun ⟨X, Y, e⟩ => rfl
left_inv F := Functor.ext (by rintro (_ | _) <;> rfl) by
      intro X Y f
      induction X <;>
      induction Y <;>
      simp [Codiscrete.eq_id] <;>
      rfl

end

end WalkingIso

end CategoryTheory

namespace SSet

open Simplicial Edge

/--
Definition of `coherentIso` / `coherentIso` 的定义

English:
abbreviation coherentIso
  signature: : SSet
  body: nerve WalkingIso.{u}

中文:
缩写 coherentIso
  签名: : SSet
  定义体: nerve WalkingIso.{u}

Depends on / 依赖: WalkingIso
-/
abbrev coherentIso : SSet := nerve WalkingIso.{u}

namespace coherentIso

/--
Definition of `x₀` / `x₀` 的定义

English:
definition x₀
  signature: : coherentIso.{u} _⦋0⦌
  body: ComposableArrows.mk₀ WalkingIso.zero

中文:
定义 x₀
  签名: : coherentIso.{u} _⦋0⦌
  定义体: ComposableArrows.mk₀ WalkingIso.zero

Depends on / 依赖: ComposableArrows, ComposableArrows.mk, WalkingIso, WalkingIso.zero
-/
def x₀ : coherentIso.{u} _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.zero

/--
Definition of `x₁` / `x₁` 的定义

English:
definition x₁
  signature: : coherentIso.{u} _⦋0⦌
  body: ComposableArrows.mk₀ WalkingIso.one

中文:
定义 x₁
  签名: : coherentIso.{u} _⦋0⦌
  定义体: ComposableArrows.mk₀ WalkingIso.one

Depends on / 依赖: ComposableArrows, ComposableArrows.mk, WalkingIso, WalkingIso.one
-/
def x₁ : coherentIso.{u} _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.one

/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: : Edge.{u} x₀ x₁ where
  body: ComposableArrows.mk₁ WalkingIso.iso.hom
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

中文:
定义 hom
  签名: : Edge.{u} x₀ x₁ where
  定义体: ComposableArrows.mk₁ WalkingIso.iso.hom
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

Depends on / 依赖: ComposableArrows, ComposableArrows.mk, WalkingIso, WalkingIso.iso.hom
-/
def hom : Edge.{u} x₀ x₁ where
  edge := ComposableArrows.mk₁ WalkingIso.iso.hom
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : Edge.{u} x₁ x₀ where
  body: ComposableArrows.mk₁ WalkingIso.iso.inv
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

中文:
定义 inv
  签名: : Edge.{u} x₁ x₀ where
  定义体: ComposableArrows.mk₁ WalkingIso.iso.inv
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

Depends on / 依赖: ComposableArrows, ComposableArrows.mk, WalkingIso, WalkingIso.iso.inv
-/
def inv : Edge.{u} x₁ x₀ where
  edge := ComposableArrows.mk₁ WalkingIso.iso.inv
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/--
Definition of `homInvId` / `homInvId` 的定义

English:
definition homInvId
  signature: : Edge.CompStruct.{u} hom inv (Edge.id x₀) where
  body: ComposableArrows.mk₂ WalkingIso.iso.hom WalkingIso.iso.inv
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

中文:
定义 homInvId
  签名: : Edge.CompStruct.{u} hom inv (Edge.id x₀) where
  定义体: ComposableArrows.mk₂ WalkingIso.iso.hom WalkingIso.iso.inv
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

Depends on / 依赖: ComposableArrows, ComposableArrows.mk, WalkingIso, WalkingIso.iso.hom, WalkingIso.iso.inv
-/
def homInvId : Edge.CompStruct.{u} hom inv (Edge.id x₀) where
  simplex := ComposableArrows.mk₂ WalkingIso.iso.hom WalkingIso.iso.inv
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/--
Definition of `invHomId` / `invHomId` 的定义

English:
definition invHomId
  signature: : Edge.CompStruct.{u} inv hom (Edge.id x₁) where
  body: ComposableArrows.mk₂ WalkingIso.iso.inv WalkingIso.iso.hom
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

中文:
定义 invHomId
  签名: : Edge.CompStruct.{u} inv hom (Edge.id x₁) where
  定义体: ComposableArrows.mk₂ WalkingIso.iso.inv WalkingIso.iso.hom
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

Depends on / 依赖: ComposableArrows, ComposableArrows.mk, WalkingIso, WalkingIso.iso.hom, WalkingIso.iso.inv
-/
def invHomId : Edge.CompStruct.{u} inv hom (Edge.id x₁) where
  simplex := ComposableArrows.mk₂ WalkingIso.iso.inv WalkingIso.iso.hom
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The forwards edge of `coherentIso` has an inverse. -/
@[simps]
/--
Definition of `invStructHom` / `invStructHom` 的定义

English:
definition invStructHom
  signature: : Edge.InvStruct.{u} coherentIso.hom where
  body: inv
  homInvId := homInvId
  invHomId := invHomId

中文:
定义 invStructHom
  签名: : Edge.InvStruct.{u} coherentIso.hom where
  定义体: inv
  homInvId := homInvId
  invHomId := invHomId
-/
def invStructHom : Edge.InvStruct.{u} coherentIso.hom where
  inv := inv
  homInvId := homInvId
  invHomId := invHomId

/--
Definition of `invStructOfEqMapHom` / `invStructOfEqMapHom` 的定义

English:
abbreviation invStructOfEqMapHom
  signature: {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}
  body: (invStructHom.map g).ofEq hfg.symm

中文:
缩写 invStructOfEqMapHom
  签名: {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}
  定义体: (invStructHom.map g).ofEq hfg.symm

Depends on / 依赖: hfg.symm, invStructHom, invStructHom.map
-/
abbrev invStructOfEqMapHom {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}
    {f : Edge x₀ x₁}
    {g : coherentIso ⟶ X}
    (hfg : f.edge = g.app _ hom.edge) :
    f.InvStruct :=
  (invStructHom.map g).ofEq hfg.symm

end coherentIso

end SSet
