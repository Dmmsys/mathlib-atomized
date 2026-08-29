/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Monoidal.End
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!

# The equivalence between `Monad C` and `Mon (C ⥤ C)`.

A monad "is just" a monoid in the category of endofunctors.

## Definitions/Theorems

1. `toMon` associates a monoid object in `C ⥤ C` to any monad on `C`.
2. `monadToMon` is the functorial version of `toMon`.
3. `ofMon` associates a monad on `C` to any monoid object in `C ⥤ C`.
4. `monadMonEquiv` is the equivalence between `Monad C` and `Mon (C ⥤ C)`.

-/

@[expose] public section


namespace CategoryTheory

open Category MonObj

universe v u -- morphism levels before object levels. See note [category_theory universes].

variable {C : Type u} [Category.{v} C]

namespace Monad

attribute [local instance] endofunctorMonoidalCategory

@[simps]
instance (M : Monad C) : MonObj (M : C ⥤ C) where
  one := M.η
  mul := M.μ
  mul_assoc := by ext; simp [M.assoc]

/-- To every `Monad C` we associated a monoid object in `C ⥤ C`. -/
@[simps]
/--
Definition of `toMon` / `toMon` 的定义

English:
definition toMon
  signature: (M : Monad C)
  body: (M : C ⥤ C)

中文:
定义 toMon
  签名: (M : 单子 C)
  定义体: (M : C ⥤ C)
-/
def toMon (M : Monad C) : Mon (C ⥤ C) where
  X := (M : C ⥤ C)

set_option backward.isDefEq.respectTransparency false in
variable (C) in
/-- Passing from `Monad C` to `Mon (C ⥤ C)` is functorial. -/
@[simps]
/--
Definition of `monadToMon` / `monadToMon` 的定义

English:
definition monadToMon
  signature: : Monad C ⥤ Mon (C ⥤ C) where
  body: toMon
  map f := .mk' f.toNatTrans

中文:
定义 monadToMon
  签名: : 单子 C ⥤ 幺半群 (C ⥤ C) where
  定义体: toMon
  map f := .mk' f.toNatTrans
-/
def monadToMon : Monad C ⥤ Mon (C ⥤ C) where
  obj := toMon
  map f := .mk' f.toNatTrans

/-- To every monoid object in `C ⥤ C` we associate a `Monad C`. -/
@[simps «η» «μ»]
/--
Definition of `ofMon` / `ofMon` 的定义

English:
definition ofMon
  signature: (M : Mon (C ⥤ C))
  body: M.X
  «η» := η[M.X]
  «μ» := μ[M.X]
  left_unit := fun X => by
    simpa [-MonObj.mul_one] using! congrArg (fun t => t.app X) (mul_one M.X)
  right_unit := fun X => by
    simpa [-MonObj.one_mul] using! congrArg (fun t => t.app X) (one_mul M.X)
  assoc := fun X => by
    simpa [-MonObj.mul_assoc] us

中文:
定义 ofMon
  签名: (M : 幺半群 (C ⥤ C))
  定义体: M.X
  «η» := η[M.X]
  «μ» := μ[M.X]
  left_unit := fun X => by
    simpa [-MonObj.mul_one] using! congrArg (fun t => t.app X) (mul_one M.X)
  right_unit := fun X => by
    simpa [-MonObj.one_mul] using! congrArg (fun t => t.app X) (one_mul M.X)
  assoc := fun X => by
    simpa [-MonObj.mul_assoc] us
-/
def ofMon (M : Mon (C ⥤ C)) : Monad C where
  toFunctor := M.X
  «η» := η[M.X]
  «μ» := μ[M.X]
  left_unit := fun X => by
    simpa [-MonObj.mul_one] using! congrArg (fun t => t.app X) (mul_one M.X)
  right_unit := fun X => by
    simpa [-MonObj.one_mul] using! congrArg (fun t => t.app X) (one_mul M.X)
  assoc := fun X => by
    simpa [-MonObj.mul_assoc] using! congrArg (fun t => t.app X) (mul_assoc M.X)

-- Porting note: `@[simps]` fails to generate `ofMon_obj`:
/--
lemma `ofMon_obj` / 引理 `ofMon_obj`

English:
lemma ofMon_obj
  given: (M : Mon (C ⥤ C)) (X : C)
  statement: (ofMon M).obj X = M.X.obj X
  proof: rfl

中文:
引理 ofMon_obj
  条件: (M : 幺半群 (C ⥤ C)) (X : C)
  结论: (ofMon M).obj X = M.X.obj X
  证明: rfl
-/
@[simp] lemma ofMon_obj (M : Mon (C ⥤ C)) (X : C) : (ofMon M).obj X = M.X.obj X := rfl

variable (C)

set_option backward.isDefEq.respectTransparency false in
/-- Passing from `Mon (C ⥤ C)` to `Monad C` is functorial. -/
@[simps]
/--
Definition of `monToMonad` / `monToMonad` 的定义

English:
definition monToMonad
  signature: : Mon (C ⥤ C) ⥤ Monad C where
  body: ofMon
  map {X Y} f :=
    { f.hom with
      app_η X := by
        simpa [-IsMonHom.one_hom] using congrArg (fun t => t.app X) (IsMonHom.one_hom f.hom)
      app_μ Z := by
        simpa [-IsMonHom.mul_hom] using congrArg (fun t => t.app Z) (IsMonHom.mul_hom f.hom) }

中文:
定义 monToMonad
  签名: : 幺半群 (C ⥤ C) ⥤ 单子 C where
  定义体: ofMon
  map {X Y} f :=
    { f.hom with
      app_η X := by
        simpa [-IsMonHom.one_hom] using congrArg (fun t => t.app X) (IsMonHom.one_hom f.hom)
      app_μ Z := by
        simpa [-IsMonHom.mul_hom] using congrArg (fun t => t.app Z) (IsMonHom.mul_hom f.hom) }
-/
def monToMonad : Mon (C ⥤ C) ⥤ Monad C where
  obj := ofMon
  map {X Y} f :=
    { f.hom with
      app_η X := by
        simpa [-IsMonHom.one_hom] using congrArg (fun t => t.app X) (IsMonHom.one_hom f.hom)
      app_μ Z := by
        simpa [-IsMonHom.mul_hom] using congrArg (fun t => t.app Z) (IsMonHom.mul_hom f.hom) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Oh, monads are just monoids in the category of endofunctors (equivalence of categories). -/
@[simps]
/--
Definition of `monadMonEquiv` / `monadMonEquiv` 的定义

English:
definition monadMonEquiv
  signature: : Monad C ≌ Mon (C ⥤ C) where
  body: monadToMon _
  inverse := monToMonad _
  unitIso :=
  { hom := { app := fun _ => { app := fun _ => 𝟙 _ } }
    inv := { app := fun _ => { app := fun _ => 𝟙 _ } } }
  counitIso :=
  { hom := { app := fun _ => { hom := 𝟙 _ } }
    inv := { app := fun _ => { hom := 𝟙 _ } } }

中文:
定义 monadMonEquiv
  签名: : 单子 C ≌ 幺半群 (C ⥤ C) where
  定义体: monadToMon _
  inverse := monToMonad _
  unitIso :=
  { hom := { app := fun _ => { app := fun _ => 𝟙 _ } }
    inv := { app := fun _ => { app := fun _ => 𝟙 _ } } }
  counitIso :=
  { hom := { app := fun _ => { hom := 𝟙 _ } }
    inv := { app := fun _ => { hom := 𝟙 _ } } }

Depends on / 依赖: monadToMon
-/
def monadMonEquiv : Monad C ≌ Mon (C ⥤ C) where
  functor := monadToMon _
  inverse := monToMonad _
  unitIso :=
  { hom := { app := fun _ => { app := fun _ => 𝟙 _ } }
    inv := { app := fun _ => { app := fun _ => 𝟙 _ } } }
  counitIso :=
  { hom := { app := fun _ => { hom := 𝟙 _ } }
    inv := { app := fun _ => { hom := 𝟙 _ } } }

-- Sanity check
example (A : Monad C) {X : C} : ((monadMonEquiv C).unitIso.app A).hom.app X = 𝟙 _ :=
  rfl

end Monad

end CategoryTheory
