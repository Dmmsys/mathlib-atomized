/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Category of topological commutative rings

We introduce the category `TopCommRingCat` of topological commutative rings together with the
relevant forgetful functors to topological spaces and commutative rings.
-/

@[expose] public section


universe u

open CategoryTheory


/--
Definition of `TopCommRingCat` / `TopCommRingCat` 的定义

English:
structure TopCommRingCat
  parameters: where
  axioms and operations (5):
    - of : :
    - α : Type u
    - [isCommRing : CommRing α]
    - [isTopologicalSpace : TopologicalSpace α]
    - [isTopologicalRing : IsTopologicalRing α]

中文:
结构 TopComm环范畴
  参数: where
  公理与运算 (5 个):
    - of : :
    - α : 类型u
    - [isCommRing : 交换环 α]
    - [isTopologicalSpace : 拓扑空间 α]
    - [isTopologicalRing : 是拓扑环 α]
-/
structure TopCommRingCat where
  /-- Construct a bundled `TopCommRingCat` from the underlying type and the appropriate typeclasses.
  -/
  of ::
  /-- carrier of a topological commutative ring. -/
  α : Type u
  [isCommRing : CommRing α]
  [isTopologicalSpace : TopologicalSpace α]
  [isTopologicalRing : IsTopologicalRing α]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `TopCommRingCat.of R` being printed as `{ α := R, ... }` by
`delabStructureInstance`. -/
@[app_delab TopCommRingCat.of]
meta def TopCommRingCat.delabOf : Delab := delabApp

end Notation

namespace TopCommRingCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited TopCommRingCat
  body: ⟨⟨PUnit⟩⟩

中文:
实例 :
  签名: 可居 TopComm环范畴
  定义体: ⟨⟨PUnit⟩⟩
-/
instance : Inhabited TopCommRingCat :=
  ⟨⟨PUnit⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort TopCommRingCat (Type u)
  body: ⟨TopCommRingCat.α⟩

中文:
实例 :
  签名: CoeSort TopComm环范畴 (类型u)
  定义体: ⟨TopCommRingCat.α⟩

Depends on / 依赖: TopCommRingCat
-/
instance : CoeSort TopCommRingCat (Type u) :=
  ⟨TopCommRingCat.α⟩

attribute [instance] isCommRing isTopologicalSpace isTopologicalRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category TopCommRingCat.{u}
  body: { f : R ->+* S // Continuous f }
  id R := ⟨RingHom.id R, by rw [RingHom.id]; dsimp; fun_prop⟩
  comp f g :=
    ⟨g.val.comp f.val, by
      -- TODO automate
      cases f
      cases g
      dsimp
      fun_prop⟩

中文:
实例 :
  签名: 范畴 TopComm环范畴.{u}
  定义体: { f : R ->+* S // Continuous f }
  id R := ⟨RingHom.id R, by rw [RingHom.id]; dsimp; fun_prop⟩
  comp f g :=
    ⟨g.val.comp f.val, by
      -- TODO automate
      cases f
      cases g
      dsimp
      fun_prop⟩

Depends on / 依赖: Continuous
-/
instance : Category TopCommRingCat.{u} where
  Hom R S := { f : R ->+* S // Continuous f }
  id R := ⟨RingHom.id R, by rw [RingHom.id]; dsimp; fun_prop⟩
  comp f g :=
    ⟨g.val.comp f.val, by
      -- TODO automate
      cases f
      cases g
      dsimp
      fun_prop⟩

instance (R S : TopCommRingCat.{u}) : FunLike { f : R ->+* S // Continuous f } R S where
  coe f := f.val
  coe_injective _ _ h := Subtype.ext (DFunLike.coe_injective h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory TopCommRingCat.{u} fun R S => { f : R ->+* S // Continuous f }
  body: f
  ofHom f := f

中文:
实例 :
  签名: 余ncrete范畴 TopComm环范畴.{u} fun R S => { f : R ->+* S // 连续 f }
  定义体: f
  ofHom f := f
-/
instance : ConcreteCategory TopCommRingCat.{u} fun R S => { f : R ->+* S // Continuous f } where
  hom f := f
  ofHom f := f

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (X : Type u) [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
  proof: rfl

中文:
定理 coe_of
  条件: (X : 类型u) [交换环 X] [拓扑空间 X] [是拓扑环 X]
  证明: rfl
-/
theorem coe_of (X : Type u) [CommRing X] [TopologicalSpace X] [IsTopologicalRing X] :
    (of X : Type u) = X := rfl

/--
Instance `hasForgetToCommRingCat` / 实例 `hasForgetToCommRingCat`

English:
instance hasForgetToCommRingCat
  signature: : HasForget₂ TopCommRingCat CommRingCat
  body: HasForget₂.mk' (fun R => CommRingCat.of R) (fun _ => rfl)
    (fun f => CommRingCat.ofHom f.val) HEq.rfl

中文:
实例 hasForgetToCommRingCat
  签名: : 有Forget₂ TopComm环范畴 交换环范畴
  定义体: HasForget₂.mk' (fun R => CommRingCat.of R) (fun _ => rfl)
    (fun f => CommRingCat.ofHom f.val) HEq.rfl

Depends on / 依赖: CommRingCat, CommRingCat.of, CommRingCat.ofHom, HEq.rfl, f.val
-/
instance hasForgetToCommRingCat : HasForget₂ TopCommRingCat CommRingCat :=
  HasForget₂.mk' (fun R => CommRingCat.of R) (fun _ => rfl)
    (fun f => CommRingCat.ofHom f.val) HEq.rfl

/--
Instance `forgetToCommRingCatTopologicalSpace` / 实例 `forgetToCommRingCatTopologicalSpace`

English:
instance forgetToCommRingCatTopologicalSpace
  signature: (R : TopCommRingCat)
  body: R.isTopologicalSpace

中文:
实例 forgetToCommRingCatTopologicalSpace
  签名: (R : TopComm环范畴)
  定义体: R.isTopologicalSpace

Depends on / 依赖: R.isTopologicalSpace, isTopologicalSpace
-/
instance forgetToCommRingCatTopologicalSpace (R : TopCommRingCat) :
    TopologicalSpace ((forget₂ TopCommRingCat CommRingCat).obj R) :=
  R.isTopologicalSpace

/--
Instance `hasForgetToTopCat` / 实例 `hasForgetToTopCat`

English:
instance hasForgetToTopCat
  signature: : HasForget₂ TopCommRingCat TopCat
  body: HasForget₂.mk' (fun R => TopCat.of R) (fun _ => rfl) (fun f => TopCat.ofHom ⟨⇑f.1, f.2⟩) HEq.rfl

中文:
实例 hasForgetToTopCat
  签名: : 有Forget₂ TopComm环范畴 顶元素范畴
  定义体: HasForget₂.mk' (fun R => TopCat.of R) (fun _ => rfl) (fun f => TopCat.ofHom ⟨⇑f.1, f.2⟩) HEq.rfl

Depends on / 依赖: HEq.rfl, TopCat, TopCat.of, TopCat.ofHom
-/
instance hasForgetToTopCat : HasForget₂ TopCommRingCat TopCat :=
  HasForget₂.mk' (fun R => TopCat.of R) (fun _ => rfl) (fun f => TopCat.ofHom ⟨⇑f.1, f.2⟩) HEq.rfl

/--
Instance `forgetToTopCatCommRing` / 实例 `forgetToTopCatCommRing`

English:
instance forgetToTopCatCommRing
  signature: (R : TopCommRingCat)
  body: R.isCommRing

中文:
实例 forgetToTopCatCommRing
  签名: (R : TopComm环范畴)
  定义体: R.isCommRing

Depends on / 依赖: R.isCommRing, isCommRing
-/
instance forgetToTopCatCommRing (R : TopCommRingCat) :
    CommRing ((forget₂ TopCommRingCat TopCat).obj R) :=
  R.isCommRing

/--
Instance `forgetToTopCatTopologicalRing` / 实例 `forgetToTopCatTopologicalRing`

English:
instance forgetToTopCatTopologicalRing
  signature: (R : TopCommRingCat)
  body: R.isTopologicalRing

中文:
实例 forgetToTopCatTopologicalRing
  签名: (R : TopComm环范畴)
  定义体: R.isTopologicalRing

Depends on / 依赖: R.isTopologicalRing, isTopologicalRing
-/
instance forgetToTopCatTopologicalRing (R : TopCommRingCat) :
    IsTopologicalRing ((forget₂ TopCommRingCat TopCat).obj R) :=
  R.isTopologicalRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ TopCommRingCat.{u} TopCat.{u}).ReflectsIsomorphisms
  body: by
    -- We have an isomorphism in `TopCat`,
    let i_Top := asIso ((forget₂ TopCommRingCat TopCat).map f)
    -- and a `RingEquiv`.
    let e_Ring : X ≃+* Y := { f.1, ((forget TopCat).mapIso i_Top).toEquiv with }
    -- Putting these together we obtain the isomorphism we're after:
    exact
     

中文:
实例 :
  签名: (forget₂ TopComm环范畴.{u} 顶元素范畴.{u}).反映同构
  定义体: by
    -- We have an isomorphism in `TopCat`,
    let i_Top := asIso ((forget₂ TopCommRingCat TopCat).map f)
    -- and a `RingEquiv`.
    let e_Ring : X ≃+* Y := { f.1, ((forget TopCat).mapIso i_Top).toEquiv with }
    -- Putting these together we obtain the isomorphism we're after:
    exact
     
-/
instance : (forget₂ TopCommRingCat.{u} TopCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    -- We have an isomorphism in `TopCat`,
    let i_Top := asIso ((forget₂ TopCommRingCat TopCat).map f)
    -- and a `RingEquiv`.
    let e_Ring : X ≃+* Y := { f.1, ((forget TopCat).mapIso i_Top).toEquiv with }
    -- Putting these together we obtain the isomorphism we're after:
    exact
      ⟨⟨⟨e_Ring.symm, i_Top.inv.hom.2⟩,
          ⟨by
            ext x
            exact e_Ring.left_inv x, by
            ext x
            exact e_Ring.right_inv x⟩⟩⟩

end TopCommRingCat
