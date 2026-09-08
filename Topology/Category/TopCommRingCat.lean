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


/-- A bundled topological commutative ring. -/
/-
**TopCommRingCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bundled topological commutative ring.
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

/-
**TopCommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited TopCommRingCat :=
  ⟨⟨PUnit⟩⟩
/-
**TopCommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort TopCommRingCat (Type u) :=
  ⟨TopCommRingCat.α⟩

attribute [instance] isCommRing isTopologicalSpace isTopologicalRing
/-
**TopCommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category TopCommRingCat.{u} where
  Hom R S := { f : R →+* S // Continuous f }
  id R := ⟨RingHom.id R, by rw [RingHom.id]; dsimp; fun_prop⟩
  comp f g :=
    ⟨g.val.comp f.val, by
      -- TODO automate
      cases f
      cases g
      dsimp
      fun_prop⟩
/-
**TopCommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R S : TopCommRingCat.{u}) : FunLike { f : R →+* S // Continuous f } R S where
  coe f := f.val
  coe_injective _ _ h := Subtype.ext (DFunLike.coe_injective h)
/-
**TopCommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory TopCommRingCat.{u} fun R S => { f : R →+* S // Continuous f } where
  hom f := f
  ofHom f := f
/-
**TopCommRingCat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `TopCommRingCat`。
形式化陈述：coe_of (X : Type u) [CommRing X] [TopologicalSpace X] [IsTopologicalRing X
] : (of X : Type u) = X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (X : Type u) [CommRing X] [TopologicalSpace X] [IsTopologicalRing X] :
    (of X : Type u) = X := rfl
/-
**TopCommRingCat.hasForgetToCommRingCat** 是 Mathlib 中的一个实例，位于命名空间 `TopCommRingCa
t`。
形式化陈述：hasForgetToCommRingCat : HasForget₂ TopCommRingCat CommRingCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToCommRingCat : HasForget₂ TopCommRingCat CommRingCat :=
  HasForget₂.mk' (fun R => CommRingCat.of R) (fun _ => rfl)
    (fun f => CommRingCat.ofHom f.val) HEq.rfl
/-
**TopCommRingCat.forgetToCommRingCatTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `
TopCommRingCat`。
形式化陈述：forgetToCommRingCatTopologicalSpace (R : TopCommRingCat) : TopologicalSpac
e ((forget₂ TopCommRingCat CommRingCat).obj R)
参数：R : TopCommRingCat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forgetToCommRingCatTopologicalSpace (R : TopCommRingCat) :
    TopologicalSpace ((forget₂ TopCommRingCat CommRingCat).obj R) :=
  R.isTopologicalSpace

/-- The forgetful functor to `TopCat`. -/
/-
**TopCommRingCat.hasForgetToTopCat** 是 Mathlib 中的一个实例，位于命名空间 `TopCommRingCat`。
形式化陈述：hasForgetToTopCat : HasForget₂ TopCommRingCat TopCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor to `TopCat`.
-/
instance hasForgetToTopCat : HasForget₂ TopCommRingCat TopCat :=
  HasForget₂.mk' (fun R => TopCat.of R) (fun _ => rfl) (fun f => TopCat.ofHom ⟨⇑f.1, f.2⟩) HEq.rfl
/-
**TopCommRingCat.forgetToTopCatCommRing** 是 Mathlib 中的一个实例，位于命名空间 `TopCommRingCa
t`。
形式化陈述：forgetToTopCatCommRing (R : TopCommRingCat) : CommRing ((forget₂ TopCommRi
ngCat TopCat).obj R)
参数：R : TopCommRingCat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forgetToTopCatCommRing (R : TopCommRingCat) :
    CommRing ((forget₂ TopCommRingCat TopCat).obj R) :=
  R.isCommRing
/-
**TopCommRingCat.forgetToTopCatTopologicalRing** 是 Mathlib 中的一个实例，位于命名空间 `TopCom
mRingCat`。
形式化陈述：forgetToTopCatTopologicalRing (R : TopCommRingCat) : IsTopologicalRing ((f
orget₂ TopCommRingCat TopCat).obj R)
参数：R : TopCommRingCat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCommRingCat.isTopologicalRing`：∀ (self : TopCommRingCat), IsTopologic
alRing self.α
-/
instance forgetToTopCatTopologicalRing (R : TopCommRingCat) :
    IsTopologicalRing ((forget₂ TopCommRingCat TopCat).obj R) :=
  R.isTopologicalRing

/-- The forgetful functors to `Type` do not reflect isomorphisms,
but the forgetful functor from `TopCommRingCat` to `TopCat` does.
-/
/-
**TopCommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functors to `Type` do not reflect isomorphisms,
but the forgetful functor from `TopCommRingCat` to `TopCat` does.
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

