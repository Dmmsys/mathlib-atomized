/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
The forgetful functor from ℤ-modules to additive commutative groups is
an equivalence of categories.

TODO:
either use this equivalence to transport the monoidal structure from `Module ℤ` to `Ab`,
or, having constructed that monoidal structure directly, show this functor is monoidal.
-/

public section

open CategoryTheory

universe u

namespace ModuleCat

/--
Instance `forget₂_addCommGroup_full` / 实例 `forget₂_addCommGroup_full`

English:
instance forget₂_addCommGroup_full
  signature: : (forget₂ (ModuleCat Int) AddCommGrpCat.{u}).Full where
  body: ⟨@ModuleCat.ofHom _ _ _ _ _ A.isModule _ B.isModule
            @LinearMap.mk _ _ _ _ _ _ _ _ _ A.isModule B.isModule
            { toFun := f,
              map_add' := map_add f.hom }
            (fun n x => by
              convert! AddMonoidHom.map_zsmul f.hom n x <;>
                ext <;> apply int_smul_eq_zsmul), rfl⟩

中文:
实例 forget₂_addCommGroup_full
  签名: : (forget₂ (模范畴 整数) 加法交换群范畴.{u}).满 where
  定义体: ⟨@ModuleCat.ofHom _ _ _ _ _ A.isModule _ B.isModule
            @LinearMap.mk _ _ _ _ _ _ _ _ _ A.isModule B.isModule
            { toFun := f,
              map_add' := map_add f.hom }
            (fun n x => by
              convert! AddMonoidHom.map_zsmul f.hom n x <;>
                ext <;> apply int_smul_eq_zsmul), rfl⟩

Depends on / 依赖: A.isModule, B.isModule, ModuleCat, ModuleCat.ofHom, isModule
-/
instance forget₂_addCommGroup_full : (forget₂ (ModuleCat Int) AddCommGrpCat.{u}).Full where
  map_surjective {A B}
    -- `AddMonoidHom.toIntLinearMap` doesn't work here because `A` and `B` are not
    -- definitionally equal to the canonical `AddCommGroup.toIntModule` module
    -- instances it expects.
f := ⟨@ModuleCat.ofHom _ _ _ _ _ A.isModule _ B.isModule
            @LinearMap.mk _ _ _ _ _ _ _ _ _ A.isModule B.isModule
            { toFun := f,
              map_add' := map_add f.hom }
            (fun n x => by
              convert! AddMonoidHom.map_zsmul f.hom n x <;>
                ext <;> apply int_smul_eq_zsmul), rfl⟩

/--
Instance `forget₂_addCommGrp_essSurj` / 实例 `forget₂_addCommGrp_essSurj`

English:
instance forget₂_addCommGrp_essSurj
  signature: : (forget₂ (ModuleCat Int) AddCommGrpCat.{u}).EssSurj where
  body: ⟨ModuleCat.of Int A,
      ⟨{ hom := 𝟙 A
          inv := 𝟙 A }⟩⟩

中文:
实例 forget₂_addCommGrp_essSurj
  签名: : (forget₂ (模范畴 整数) 加法交换群范畴.{u}).本质满射 where
  定义体: ⟨ModuleCat.of Int A,
      ⟨{ hom := 𝟙 A
          inv := 𝟙 A }⟩⟩

Depends on / 依赖: ModuleCat, ModuleCat.of, S.carrier, carrier
-/
instance forget₂_addCommGrp_essSurj : (forget₂ (ModuleCat Int) AddCommGrpCat.{u}).EssSurj where
  mem_essImage A :=
    ⟨ModuleCat.of Int A,
      ⟨{ hom := 𝟙 A
          inv := 𝟙 A }⟩⟩

/--
Instance `forget₂AddCommGroupIsEquivalence` / 实例 `forget₂AddCommGroupIsEquivalence`

English:
instance forget₂AddCommGroupIsEquivalence
  signature: :

中文:
实例 forget₂AddCommGroupIsEquivalence
  签名: :

Depends on / 依赖: Algebra, S.carrier, carrier
-/
noncomputable instance forget₂AddCommGroupIsEquivalence :
    (forget₂ (ModuleCat Int) AddCommGrpCat.{u}).IsEquivalence where

end ModuleCat
