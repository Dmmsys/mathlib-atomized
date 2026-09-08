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

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive Cᵒᵖ where
  homGroup X Y := fast_instance% Equiv.addCommGroup (opEquiv X Y)
  add_comp _ _ _ f f' g := Quiver.Hom.unop_inj (Preadditive.comp_add _ _ _ g.unop f.unop f'.unop)
  comp_add _ _ _ f g g' := Quiver.Hom.unop_inj (Preadditive.add_comp _ _ _ g.unop g'.unop f.unop)

/-- Test that the two ways to obtain the `HasZeroMorphisms Cᵒᵖ` instance
from `Preadditive C` are the same. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Test that the two ways to obtain the `HasZeroMorphisms Cᵒᵖ` instance
from `Preadditive C` are the same.
-/
example : (instPreadditiveOpposite C).preadditiveHasZeroMorphisms =
    @Limits.hasZeroMorphismsOpposite  C _ Preadditive.preadditiveHasZeroMorphisms := by
  with_reducible_and_instances rfl
/-
**CategoryTheory.moduleEndLeft** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：moduleEndLeft {X Y : C} : Module (End X)ᵐᵒᵖ (X ⟶ Y) where smul_add _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance moduleEndLeft {X Y : C} : Module (End X)ᵐᵒᵖ (X ⟶ Y) where
  smul_add _ _ _ := Preadditive.comp_add _ _ _ _ _ _
  smul_zero _ := Limits.comp_zero
  add_smul _ _ _ := Preadditive.add_comp _ _ _ _ _ _
  zero_smul _ := Limits.zero_comp

@[simp]
/-
**CategoryTheory.unop_add** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：unop_add {X Y : Cᵒᵖ} (f g : X ⟶ Y) : (f + g).unop = f.unop + g.unop
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_add {X Y : Cᵒᵖ} (f g : X ⟶ Y) : (f + g).unop = f.unop + g.unop :=
  rfl

@[simp]
/-
**CategoryTheory.unop_sub** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：unop_sub {X Y : Cᵒᵖ} (f g : X ⟶ Y) : (f - g).unop = f.unop - g.unop
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_sub {X Y : Cᵒᵖ} (f g : X ⟶ Y) : (f - g).unop = f.unop - g.unop :=
  rfl

@[simp]
/-
**CategoryTheory.unop_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：unop_zsmul {X Y : Cᵒᵖ} (k : Int) (f : X ⟶ Y) : (k • f).unop = k • f.unop
参数：k : Int；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_zsmul {X Y : Cᵒᵖ} (k : ℤ) (f : X ⟶ Y) : (k • f).unop = k • f.unop :=
  rfl

@[simp]
/-
**CategoryTheory.unop_neg** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：unop_neg {X Y : Cᵒᵖ} (f : X ⟶ Y) : (-f).unop = -f.unop
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_neg {X Y : Cᵒᵖ} (f : X ⟶ Y) : (-f).unop = -f.unop :=
  rfl

@[simp]
/-
**CategoryTheory.op_add** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：op_add {X Y : C} (f g : X ⟶ Y) : (f + g).op = f.op + g.op
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_add {X Y : C} (f g : X ⟶ Y) : (f + g).op = f.op + g.op :=
  rfl

@[simp]
/-
**CategoryTheory.op_sub** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：op_sub {X Y : C} (f g : X ⟶ Y) : (f - g).op = f.op - g.op
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_sub {X Y : C} (f g : X ⟶ Y) : (f - g).op = f.op - g.op :=
  rfl

@[simp]
/-
**CategoryTheory.op_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：op_zsmul {X Y : C} (k : Int) (f : X ⟶ Y) : (k • f).op = k • f.op
参数：k : Int；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_zsmul {X Y : C} (k : ℤ) (f : X ⟶ Y) : (k • f).op = k • f.op :=
  rfl

@[simp]
/-
**CategoryTheory.op_neg** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：op_neg {X Y : C} (f : X ⟶ Y) : (-f).op = -f.op
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_neg {X Y : C} (f : X ⟶ Y) : (-f).op = -f.op :=
  rfl

variable {C}

/-- `unop` induces morphisms of monoids on hom groups of a preadditive category -/
@[simps!]
/-
**CategoryTheory.unopHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：unopHom (X Y : Cᵒᵖ) : (X ⟶ Y) ->+ (Opposite.unop Y ⟶ Opposite.unop X)
参数：X Y : Cᵒᵖ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.unop_add`：unop_add {X Y : Cᵒᵖ} (f g : X ⟶ Y) : (f + g).un
op = f.unop + g.unop

--- 原说明 ---
`unop` induces morphisms of monoids on hom groups of a preadditive category
-/
def unopHom (X Y : Cᵒᵖ) : (X ⟶ Y) →+ (Opposite.unop Y ⟶ Opposite.unop X) :=
  AddMonoidHom.mk' (fun f => f.unop) fun f g => unop_add _ f g

@[simp]
/-
**CategoryTheory.unop_sum** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：unop_sum (X Y : Cᵒᵖ) {ι : Type*} (s : Finset ι) (f : ι -> (X ⟶ Y)) : (s.su
m f).unop = s.sum fun i => (f i).unop
参数：X Y : Cᵒᵖ；s : Finset ι；f : ι -> (X ⟶ Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem unop_sum (X Y : Cᵒᵖ) {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (s.sum f).unop = s.sum fun i => (f i).unop :=
  map_sum (unopHom X Y) _ _

/-- `op` induces morphisms of monoids on hom groups of a preadditive category -/
@[simps!]
/-
**CategoryTheory.opHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：opHom (X Y : C) : (X ⟶ Y) ->+ (Opposite.op Y ⟶ Opposite.op X)
参数：X Y : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.op_add`：op_add {X Y : C} (f g : X ⟶ Y) : (f + g).op = f.o
p + g.op

--- 原说明 ---
`op` induces morphisms of monoids on hom groups of a preadditive category
-/
def opHom (X Y : C) : (X ⟶ Y) →+ (Opposite.op Y ⟶ Opposite.op X) :=
  AddMonoidHom.mk' (fun f => f.op) fun f g => op_add _ f g

@[simp]
/-
**CategoryTheory.op_sum** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：op_sum (X Y : C) {ι : Type*} (s : Finset ι) (f : ι -> (X ⟶ Y)) : (s.sum f)
.op = s.sum fun i => (f i).op
参数：X Y : C；s : Finset ι；f : ι -> (X ⟶ Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem op_sum (X Y : C) {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (s.sum f).op = s.sum fun i => (f i).op :=
  map_sum (opHom X Y) _ _

/-- `G ⟶ G` and `(End G)ᵐᵒᵖ` are isomorphic as `(End G)ᵐᵒᵖ`-modules. -/
@[simps]
/-
**CategoryTheory.Preadditive.homSelfLinearEquivEndMulOpposite** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Preadditive`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] → (G : C) → (G ⟶ G) ≃ₗ[(CategoryTheory.End 
G)ᵐᵒᵖ] (CategoryTheory.End G)ᵐᵒᵖ
参数：G : C；G ⟶ G；CategoryTheory.End G；CategoryTheory.End G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G ⟶ G` and `(End G)ᵐᵒᵖ` are isomorphic as `(End G)ᵐᵒᵖ`-modules.
-/
def Preadditive.homSelfLinearEquivEndMulOpposite (G : C) : (G ⟶ G) ≃ₗ[(End G)ᵐᵒᵖ] (End G)ᵐᵒᵖ where
  toFun f := ⟨f⟩
  map_add' := by cat_disch
  map_smul' := by cat_disch
  invFun := fun ⟨f⟩ => f
  left_inv := by cat_disch
  right_inv := by cat_disch

variable {D : Type*} [Category* D] [Preadditive D]
/-
**CategoryTheory.Functor.op_additive** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C] {D : Type u_2}   [inst_2 : CategoryTheory.Category.
{v_2, u_2} D] [inst_3 : CategoryTheory.Preadditive D]   (F : CategoryTheory.Func
tor C D) [F.Additive], F.op.Additive
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Functor.op_additive (F : C ⥤ D) [F.Additive] : F.op.Additive where
/-
**CategoryTheory.Functor.rightOp_additive** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C] {D : Type u_2}   [inst_2 : CategoryTheory.Category.
{v_2, u_2} D] [inst_3 : CategoryTheory.Preadditive D]   (F : CategoryTheory.Func
tor Cᵒᵖ D) [F.Additive], F.rightOp.Additive
参数：F : CategoryTheory.Functor Cᵒᵖ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Functor.rightOp_additive (F : Cᵒᵖ ⥤ D) [F.Additive] : F.rightOp.Additive where
/-
**CategoryTheory.Functor.leftOp_additive** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C] {D : Type u_2}   [inst_2 : CategoryTheory.Category.
{v_2, u_2} D] [inst_3 : CategoryTheory.Preadditive D]   (F : CategoryTheory.Func
tor C Dᵒᵖ) [F.Additive], F.leftOp.Additive
参数：F : CategoryTheory.Functor C Dᵒᵖ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Functor.leftOp_additive (F : C ⥤ Dᵒᵖ) [F.Additive] : F.leftOp.Additive where
/-
**CategoryTheory.Functor.unop_additive** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C] {D : Type u_2}   [inst_2 : CategoryTheory.Category.
{v_2, u_2} D] [inst_3 : CategoryTheory.Preadditive D]   (F : CategoryTheory.Func
tor Cᵒᵖ Dᵒᵖ) [F.Additive], F.unop.Additive
参数：F : CategoryTheory.Functor Cᵒᵖ Dᵒᵖ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Functor.unop_additive (F : Cᵒᵖ ⥤ Dᵒᵖ) [F.Additive] : F.unop.Additive where

end CategoryTheory

