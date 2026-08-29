/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Adam Topaz, Johan Commelin, Joël Riou
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# If `C` is preadditive, `Cᵒᵖ` has a natural preadditive structure.

-/

@[expose] public section


open Opposite

namespace CategoryTheory

variable (C : Type*) [Category* C] [Preadditive C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive Cᵒᵖ
  body: fast_instance% Equiv.addCommGroup (opEquiv X Y)
  add_comp _ _ _ f f' g := Quiver.Hom.unop_inj (Preadditive.comp_add _ _ _ g.unop f.unop f'.unop)
  comp_add _ _ _ f g g' := Quiver.Hom.unop_inj (Preadditive.add_comp _ _ _ g.unop g'.unop f.unop)

中文:
实例 :
  签名: Preadditive Cᵒᵖ
  定义体: fast_instance% Equiv.addCommGroup (opEquiv X Y)
  add_comp _ _ _ f f' g := Quiver.Hom.unop_inj (Preadditive.comp_add _ _ _ g.unop f.unop f'.unop)
  comp_add _ _ _ f g g' := Quiver.Hom.unop_inj (Preadditive.add_comp _ _ _ g.unop g'.unop f.unop)
-/
instance : Preadditive Cᵒᵖ where
  homGroup X Y := fast_instance% Equiv.addCommGroup (opEquiv X Y)
  add_comp _ _ _ f f' g := Quiver.Hom.unop_inj (Preadditive.comp_add _ _ _ g.unop f.unop f'.unop)
  comp_add _ _ _ f g g' := Quiver.Hom.unop_inj (Preadditive.add_comp _ _ _ g.unop g'.unop f.unop)

/-- Test that the two ways to obtain the `HasZeroMorphisms Cᵒᵖ` instance
from `Preadditive C` are the same. -/
example : (instPreadditiveOpposite C).preadditiveHasZeroMorphisms =
    @Limits.hasZeroMorphismsOpposite C _ Preadditive.preadditiveHasZeroMorphisms := by
  with_reducible_and_instances rfl

/--
Instance `moduleEndLeft` / 实例 `moduleEndLeft`

English:
instance moduleEndLeft
  signature: {X Y : C}
  body: Preadditive.comp_add _ _ _ _ _ _
  smul_zero _ := Limits.comp_zero
  add_smul _ _ _ := Preadditive.add_comp _ _ _ _ _ _
  zero_smul _ := Limits.zero_comp

@[simp]

中文:
实例 moduleEndLeft
  签名: {X Y : C}
  定义体: Preadditive.comp_add _ _ _ _ _ _
  smul_zero _ := Limits.comp_zero
  add_smul _ _ _ := Preadditive.add_comp _ _ _ _ _ _
  zero_smul _ := Limits.zero_comp

@[simp]

Depends on / 依赖: Preadditive, Preadditive.comp_add, comp_add
-/
instance moduleEndLeft {X Y : C} : Module (End X)ᵐᵒᵖ (X ⟶ Y) where
  smul_add _ _ _ := Preadditive.comp_add _ _ _ _ _ _
  smul_zero _ := Limits.comp_zero
  add_smul _ _ _ := Preadditive.add_comp _ _ _ _ _ _
  zero_smul _ := Limits.zero_comp

@[simp]
/--
theorem `unop_add` / 定理 `unop_add`

English:
theorem unop_add
  given: {X Y : Cᵒᵖ} (f g : X ⟶ Y)
  statement: (f + g).unop = f.unop + g.unop
  proof: rfl

@[simp]

中文:
定理 unop_add
  条件: {X Y : Cᵒᵖ} (f g : X ⟶ Y)
  结论: (f + g).unop = f.unop + g.unop
  证明: rfl

@[simp]
-/
theorem unop_add {X Y : Cᵒᵖ} (f g : X ⟶ Y) : (f + g).unop = f.unop + g.unop :=
  rfl

@[simp]
/--
theorem `unop_sub` / 定理 `unop_sub`

English:
theorem unop_sub
  given: {X Y : Cᵒᵖ} (f g : X ⟶ Y)
  statement: (f - g).unop = f.unop - g.unop
  proof: rfl

@[simp]

中文:
定理 unop_sub
  条件: {X Y : Cᵒᵖ} (f g : X ⟶ Y)
  结论: (f - g).unop = f.unop - g.unop
  证明: rfl

@[simp]
-/
theorem unop_sub {X Y : Cᵒᵖ} (f g : X ⟶ Y) : (f - g).unop = f.unop - g.unop :=
  rfl

@[simp]
/--
theorem `unop_zsmul` / 定理 `unop_zsmul`

English:
theorem unop_zsmul
  given: {X Y : Cᵒᵖ} (k : Int) (f : X ⟶ Y)
  statement: (k • f).unop = k • f.unop
  proof: rfl

@[simp]

中文:
定理 unop_zsmul
  条件: {X Y : Cᵒᵖ} (k : 整数) (f : X ⟶ Y)
  结论: (k • f).unop = k • f.unop
  证明: rfl

@[simp]
-/
theorem unop_zsmul {X Y : Cᵒᵖ} (k : Int) (f : X ⟶ Y) : (k • f).unop = k • f.unop :=
  rfl

@[simp]
/--
theorem `unop_neg` / 定理 `unop_neg`

English:
theorem unop_neg
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  statement: (-f).unop = -f.unop
  proof: rfl

@[simp]

中文:
定理 unop_neg
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  结论: (-f).unop = -f.unop
  证明: rfl

@[simp]
-/
theorem unop_neg {X Y : Cᵒᵖ} (f : X ⟶ Y) : (-f).unop = -f.unop :=
  rfl

@[simp]
/--
theorem `op_add` / 定理 `op_add`

English:
theorem op_add
  given: {X Y : C} (f g : X ⟶ Y)
  statement: (f + g).op = f.op + g.op
  proof: rfl

@[simp]

中文:
定理 op_add
  条件: {X Y : C} (f g : X ⟶ Y)
  结论: (f + g).op = f.op + g.op
  证明: rfl

@[simp]
-/
theorem op_add {X Y : C} (f g : X ⟶ Y) : (f + g).op = f.op + g.op :=
  rfl

@[simp]
/--
theorem `op_sub` / 定理 `op_sub`

English:
theorem op_sub
  given: {X Y : C} (f g : X ⟶ Y)
  statement: (f - g).op = f.op - g.op
  proof: rfl

@[simp]

中文:
定理 op_sub
  条件: {X Y : C} (f g : X ⟶ Y)
  结论: (f - g).op = f.op - g.op
  证明: rfl

@[simp]
-/
theorem op_sub {X Y : C} (f g : X ⟶ Y) : (f - g).op = f.op - g.op :=
  rfl

@[simp]
/--
theorem `op_zsmul` / 定理 `op_zsmul`

English:
theorem op_zsmul
  given: {X Y : C} (k : Int) (f : X ⟶ Y)
  statement: (k • f).op = k • f.op
  proof: rfl

@[simp]

中文:
定理 op_zsmul
  条件: {X Y : C} (k : 整数) (f : X ⟶ Y)
  结论: (k • f).op = k • f.op
  证明: rfl

@[simp]
-/
theorem op_zsmul {X Y : C} (k : Int) (f : X ⟶ Y) : (k • f).op = k • f.op :=
  rfl

@[simp]
/--
theorem `op_neg` / 定理 `op_neg`

English:
theorem op_neg
  given: {X Y : C} (f : X ⟶ Y)
  statement: (-f).op = -f.op
  proof: rfl

中文:
定理 op_neg
  条件: {X Y : C} (f : X ⟶ Y)
  结论: (-f).op = -f.op
  证明: rfl
-/
theorem op_neg {X Y : C} (f : X ⟶ Y) : (-f).op = -f.op :=
  rfl

variable {C}

/-- `unop` induces morphisms of monoids on hom groups of a preadditive category -/
@[simps!]
/--
Definition of `unopHom` / `unopHom` 的定义

English:
definition unopHom
  signature: (X Y : Cᵒᵖ)
  body: AddMonoidHom.mk' (fun f => f.unop) fun f g => unop_add _ f g

@[simp]

中文:
定义 unopHom
  签名: (X Y : Cᵒᵖ)
  定义体: AddMonoidHom.mk' (fun f => f.unop) fun f g => unop_add _ f g

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, f.unop, unop_add
-/
def unopHom (X Y : Cᵒᵖ) : (X ⟶ Y) ->+ (Opposite.unop Y ⟶ Opposite.unop X) :=
  AddMonoidHom.mk' (fun f => f.unop) fun f g => unop_add _ f g

@[simp]
/--
theorem `unop_sum` / 定理 `unop_sum`

English:
theorem unop_sum
  given: (X Y : Cᵒᵖ) {ι : Type*} (s : Finset ι) (f : ι -> (X ⟶ Y))
  proof: map_sum (unopHom X Y) _ _

中文:
定理 unop_sum
  条件: (X Y : Cᵒᵖ) {ι : 类型} (s : Finset ι) (f : ι -> (X ⟶ Y))
  证明: map_sum (unopHom X Y) _ _

Depends on / 依赖: map_sum, unopHom
-/
theorem unop_sum (X Y : Cᵒᵖ) {ι : Type*} (s : Finset ι) (f : ι -> (X ⟶ Y)) :
    (s.sum f).unop = s.sum fun i => (f i).unop :=
  map_sum (unopHom X Y) _ _

/-- `op` induces morphisms of monoids on hom groups of a preadditive category -/
@[simps!]
/--
Definition of `opHom` / `opHom` 的定义

English:
definition opHom
  signature: (X Y : C)
  body: AddMonoidHom.mk' (fun f => f.op) fun f g => op_add _ f g

@[simp]

中文:
定义 opHom
  签名: (X Y : C)
  定义体: AddMonoidHom.mk' (fun f => f.op) fun f g => op_add _ f g

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, f.op, op_add
-/
def opHom (X Y : C) : (X ⟶ Y) ->+ (Opposite.op Y ⟶ Opposite.op X) :=
  AddMonoidHom.mk' (fun f => f.op) fun f g => op_add _ f g

@[simp]
/--
theorem `op_sum` / 定理 `op_sum`

English:
theorem op_sum
  given: (X Y : C) {ι : Type*} (s : Finset ι) (f : ι -> (X ⟶ Y))
  proof: map_sum (opHom X Y) _ _

中文:
定理 op_sum
  条件: (X Y : C) {ι : 类型} (s : Finset ι) (f : ι -> (X ⟶ Y))
  证明: map_sum (opHom X Y) _ _

Depends on / 依赖: map_sum
-/
theorem op_sum (X Y : C) {ι : Type*} (s : Finset ι) (f : ι -> (X ⟶ Y)) :
    (s.sum f).op = s.sum fun i => (f i).op :=
  map_sum (opHom X Y) _ _

/-- `G ⟶ G` and `(End G)ᵐᵒᵖ` are isomorphic as `(End G)ᵐᵒᵖ`-modules. -/
@[simps]
/--
Definition of `Preadditive.homSelfLinearEquivEndMulOpposite` / `Preadditive.homSelfLinearEquivEndMulOpposite` 的定义

English:
definition Preadditive.homSelfLinearEquivEndMulOpposite
  signature: (G : C)
  body: ⟨f⟩
  map_add' := by cat_disch
  map_smul' := by cat_disch
  invFun := fun ⟨f⟩ => f
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 Preadditive.homSelfLinearEquivEndMulOpposite
  签名: (G : C)
  定义体: ⟨f⟩
  map_add' := by cat_disch
  map_smul' := by cat_disch
  invFun := fun ⟨f⟩ => f
  left_inv := by cat_disch
  right_inv := by cat_disch
-/
def Preadditive.homSelfLinearEquivEndMulOpposite (G : C) : (G ⟶ G) ≃ₗ[(End G)ᵐᵒᵖ] (End G)ᵐᵒᵖ where
  toFun f := ⟨f⟩
  map_add' := by cat_disch
  map_smul' := by cat_disch
  invFun := fun ⟨f⟩ => f
  left_inv := by cat_disch
  right_inv := by cat_disch

variable {D : Type*} [Category* D] [Preadditive D]

/--
Instance `Functor.op_additive` / 实例 `Functor.op_additive`

English:
instance Functor.op_additive
  signature: (F : C ⥤ D) [F.Additive]

中文:
实例 Functor.op_additive
  签名: (F : C ⥤ D) [F.Additive]
-/
instance Functor.op_additive (F : C ⥤ D) [F.Additive] : F.op.Additive where

/--
Instance `Functor.rightOp_additive` / 实例 `Functor.rightOp_additive`

English:
instance Functor.rightOp_additive
  signature: (F : Cᵒᵖ ⥤ D) [F.Additive]

中文:
实例 Functor.rightOp_additive
  签名: (F : Cᵒᵖ ⥤ D) [F.Additive]
-/
instance Functor.rightOp_additive (F : Cᵒᵖ ⥤ D) [F.Additive] : F.rightOp.Additive where

/--
Instance `Functor.leftOp_additive` / 实例 `Functor.leftOp_additive`

English:
instance Functor.leftOp_additive
  signature: (F : C ⥤ Dᵒᵖ) [F.Additive]

中文:
实例 Functor.leftOp_additive
  签名: (F : C ⥤ Dᵒᵖ) [F.Additive]
-/
instance Functor.leftOp_additive (F : C ⥤ Dᵒᵖ) [F.Additive] : F.leftOp.Additive where

/--
Instance `Functor.unop_additive` / 实例 `Functor.unop_additive`

English:
instance Functor.unop_additive
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [F.Additive]

中文:
实例 Functor.unop_additive
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [F.Additive]
-/
instance Functor.unop_additive (F : Cᵒᵖ ⥤ Dᵒᵖ) [F.Additive] : F.unop.Additive where

end CategoryTheory
