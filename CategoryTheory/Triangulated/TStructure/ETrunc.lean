/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Order.WithBotTop

/-!
# Truncations for a t-structure

Let `t` be a t-structure on a triangulated category `C`.
In this file, we extend the definition of the truncation functors
`truncLT` and `truncGE` for indices in `ℤ` to `EInt`,
as `t.eTruncLT : EInt ⥤ C ⥤ C` and `t.eTruncGE : EInt ⥤ C ⥤ C`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `EInt ⥤ C ⥤ C` which sends `⊥` to the zero functor,
`n : ℤ` to `t.truncLT n` and `⊤` to `𝟭 C`. -/
/-
**CategoryTheory.Triangulated.TStructure.eTruncLT** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLT : EInt ⥤ C ⥤ C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…

--- 原说明 ---
The functor `EInt ⥤ C ⥤ C` which sends `⊥` to the zero functor,
`n : ℤ` to `t.truncLT n` and `⊤` to `𝟭 C`.
-/
noncomputable def eTruncLT : EInt ⥤ C ⥤ C where
  obj := WithBotTop.rec 0 t.truncLT (𝟭 C)
  map {x y} f := by
    induction x using WithBotTop.rec with
    | bot =>
      induction y using WithBotTop.rec with
      | bot => exact 𝟙 _
      | coe b => exact 0
      | top => exact 0
    | coe a =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact t.natTransTruncLTOfLE a b (by simpa using leOfHom f)
      | top => exact t.truncLTι a
    | top =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact 0
      | top => exact 𝟙 _
  map_id n := by induction n using WithBotTop.rec <;> simp
  map_comp {x y z} f g := by
    have f' := leOfHom f
    have g' := leOfHom g
    induction x using WithBotTop.rec <;> induction y using WithBotTop.rec <;>
      induction z using WithBotTop.rec <;> cat_disch

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLT_obj_top** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLT_obj_top : t.eTruncLT.obj ⊤ = 𝟭 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eTruncLT_obj_top : t.eTruncLT.obj ⊤ = 𝟭 _ := rfl

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLT_obj_bot** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLT_obj_bot : t.eTruncLT.obj ⊥ = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eTruncLT_obj_bot : t.eTruncLT.obj ⊥ = 0 := rfl

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLT_obj_coe** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLT_obj_coe (n : Int) : t.eTruncLT.obj n = t.truncLT n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eTruncLT_obj_coe (n : ℤ) : t.eTruncLT.obj n = t.truncLT n := rfl

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLT_map_eq_truncLT** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eTruncLT_map_eq_truncLTι (n : ℤ) :
    t.eTruncLT.map (homOfLE (show (n : EInt) ≤ ⊤ by simp)) = t.truncLTι n := rfl
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : EInt) : (t.eTruncLT.obj i).Additive := by
  induction i using WithBotTop.rec
  all_goals dsimp; infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `EInt ⥤ C ⥤ C` which sends `⊥` to `𝟭 C`,
`n : ℤ` to `t.truncGE n` and `⊤` to the zero functor. -/
/-
**CategoryTheory.Triangulated.TStructure.eTruncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGE : EInt ⥤ C ⥤ C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…

--- 原说明 ---
The functor `EInt ⥤ C ⥤ C` which sends `⊥` to `𝟭 C`,
`n : ℤ` to `t.truncGE n` and `⊤` to the zero functor.
-/
noncomputable def eTruncGE : EInt ⥤ C ⥤ C where
  obj := WithBotTop.rec (𝟭 C) t.truncGE 0
  map {x y} f := by
    induction x using WithBotTop.rec with
    | bot =>
      induction y using WithBotTop.rec with
      | bot => exact 𝟙 _
      | coe b => exact t.truncGEπ b
      | top => exact 0
    | coe a =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact t.natTransTruncGEOfLE a b (by simpa using leOfHom f)
      | top => exact 0
    | top =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact 0
      | top => exact 𝟙 _
  map_id n := by induction n using WithBotTop.rec <;> simp
  map_comp {x y z} f g := by
    have f' := leOfHom f
    have g' := leOfHom g
    induction x using WithBotTop.rec <;> induction y using WithBotTop.rec <;>
      induction z using WithBotTop.rec <;> cat_disch

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.eTruncGE_obj_bot** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGE_obj_bot : t.eTruncGE.obj ⊥ = 𝟭 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eTruncGE_obj_bot :
    t.eTruncGE.obj ⊥ = 𝟭 _ := rfl

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.eTruncGE_obj_top** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGE_obj_top : t.eTruncGE.obj ⊤ = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eTruncGE_obj_top :
    t.eTruncGE.obj ⊤ = 0 := rfl

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.eTruncGE_obj_coe** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGE_obj_coe (n : Int) : t.eTruncGE.obj n = t.truncGE n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eTruncGE_obj_coe (n : ℤ) : t.eTruncGE.obj n = t.truncGE n := rfl
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : EInt) : (t.eTruncGE.obj i).Additive := by
  induction i using WithBotTop.rec
  all_goals dsimp; infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The connecting homomorphism from `t.eTruncGE` to the
shift by `1` of `t.eTruncLT`. -/
/-
**CategoryTheory.Triangulated.TStructure.eTruncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGE : EInt ⥤ C ⥤ C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…

--- 原说明 ---
The connecting homomorphism from `t.eTruncGE` to the
shift by `1` of `t.eTruncLT`.
-/
noncomputable def eTruncGEδLT :
    t.eTruncGE ⟶ t.eTruncLT ⋙ ((Functor.whiskeringRight ..).obj (shiftFunctor C (1 : ℤ))) where
  app := WithBotTop.rec 0 t.truncGEδLT 0
  naturality {a b} hab := by
    replace hab := leOfHom hab
    induction a using WithBotTop.rec; rotate_right
    · apply (isZero_zero _).eq_of_src
    all_goals
      induction b using WithBotTop.rec <;> simp at hab <;>
        dsimp [eTruncGE, eTruncLT] <;>
        simp [t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE]

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.eTruncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGE : EInt ⥤ C ⥤ C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
-/
lemma eTruncGEδLT_coe (n : ℤ) :
    t.eTruncGEδLT.app n = t.truncGEδLT n := rfl

/-- The natural transformation `t.eTruncLT.obj i ⟶ 𝟭 C` for all `i : EInt`. -/
/-
**CategoryTheory.Triangulated.TStructure.eTruncLT** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLT : EInt ⥤ C ⥤ C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…

--- 原说明 ---
The natural transformation `t.eTruncLT.obj i ⟶ 𝟭 C` for all `i : EInt`.
-/
noncomputable abbrev eTruncLTι (i : EInt) : t.eTruncLT.obj i ⟶ 𝟭 _ :=
  t.eTruncLT.map (homOfLE (le_top))
/-
**CategoryTheory.Triangulated.TStructure.eTruncLT_** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma eTruncLT_ι_bot : t.eTruncLTι ⊥ = 0 := rfl
/-
**CategoryTheory.Triangulated.TStructure.eTruncLT_** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma eTruncLT_ι_coe (n : ℤ) : t.eTruncLTι n = t.truncLTι n := rfl
/-
**CategoryTheory.Triangulated.TStructure.eTruncLT_** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma eTruncLT_ι_top : t.eTruncLTι ⊤ = 𝟙 _ := rfl

@[reassoc]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLT** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLT : EInt ⥤ C ⥤ C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
-/
lemma eTruncLTι_naturality (i : EInt) {X Y : C} (f : X ⟶ Y) :
    (t.eTruncLT.obj i).map f ≫ (t.eTruncLTι i).app Y = (t.eTruncLTι i).app X ≫ f :=
  (t.eTruncLTι i).naturality f
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (t.eTruncLTι ⊤) := by
  dsimp [eTruncLTι]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLT_map_app_eTruncLT** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eTruncLT_map_app_eTruncLTι_app {i j : EInt} (f : i ⟶ j) (X : C) :
    (t.eTruncLT.map f).app X ≫ (t.eTruncLTι j).app X = (t.eTruncLTι i).app X := by
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLT_obj_map_eTruncLT** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eTruncLT_obj_map_eTruncLTι_app (i : EInt) (X : C) :
    (t.eTruncLT.obj i).map ((t.eTruncLTι i).app X) =
    (t.eTruncLTι i).app ((t.eTruncLT.obj i).obj X) := by
  induction i using WithBotTop.rec with simp [truncLT_map_truncLTι_app]

/-- The natural transformation `𝟭 C ⟶ t.eTruncGE.obj i` for all `i : EInt`. -/
/-
**CategoryTheory.Triangulated.TStructure.eTruncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGE : EInt ⥤ C ⥤ C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…

--- 原说明 ---
The natural transformation `𝟭 C ⟶ t.eTruncGE.obj i` for all `i : EInt`.
-/
noncomputable abbrev eTruncGEπ (i : EInt) : 𝟭 C ⟶ t.eTruncGE.obj i :=
  t.eTruncGE.map (homOfLE (bot_le))
/-
**CategoryTheory.Triangulated.TStructure.eTruncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGE : EInt ⥤ C ⥤ C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
-/
@[simp] lemma eTruncGEπ_bot : t.eTruncGEπ ⊥ = 𝟙 _ := rfl
/-
**CategoryTheory.Triangulated.TStructure.eTruncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGE : EInt ⥤ C ⥤ C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
-/
@[simp] lemma eTruncGEπ_coe (n : ℤ) : t.eTruncGEπ n = t.truncGEπ n := rfl
/-
**CategoryTheory.Triangulated.TStructure.eTruncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGE : EInt ⥤ C ⥤ C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
-/
@[simp] lemma eTruncGEπ_top : t.eTruncGEπ ⊤ = 0 := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.eTruncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGE : EInt ⥤ C ⥤ C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
-/
lemma eTruncGEπ_naturality (i : EInt) {X Y : C} (f : X ⟶ Y) :
    (t.eTruncGEπ i).app X ≫ (t.eTruncGE.obj i).map f = f ≫ (t.eTruncGEπ i).app Y :=
  ((t.eTruncGEπ i).naturality f).symm
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (t.eTruncGEπ ⊥) := by
  dsimp [eTruncGEπ]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.eTruncGE** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGE : EInt ⥤ C ⥤ C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
-/
lemma eTruncGEπ_app_eTruncGE_map_app {i j : EInt} (f : i ⟶ j) (X : C) :
    (t.eTruncGEπ i).app X ≫ (t.eTruncGE.map f).app X = (t.eTruncGEπ j).app X := by
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Triangulated.TStructure.eTruncGE_obj_map_eTruncGE** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eTruncGE_obj_map_eTruncGEπ_app (i : EInt) (X : C) :
    (t.eTruncGE.obj i).map ((t.eTruncGEπ i).app X) =
    (t.eTruncGEπ i).app ((t.eTruncGE.obj i).obj X) := by
  induction i using WithBotTop.rec with simp [truncGE_map_truncGEπ_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLT_obj_map_eTruncLT** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eTruncLT_obj_map_eTruncLTι_app_eTruncLT_map_app
    {i j : EInt} (f : i ⟶ j) (X : C) :
    (t.eTruncLT.obj i).map ((t.eTruncLTι j).app X) ≫ (t.eTruncLT.map f).app X =
      (t.eTruncLTι i).app ((t.eTruncLT.obj j).obj X) := by
  dsimp [eTruncLTι]
  rw [show homOfLE le_top = f ≫ homOfLE le_top by rfl]
  induction j using WithBotTop.rec with simp [truncLT_map_truncLTι_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The (distinguished) triangles given by the natural transformations
`t.eTruncLT.obj i ⟶ 𝟭 C ⟶ t.eTruncGE.obj i ⟶ ...` for all `i : EInt`. -/
@[simps!]
/-
**CategoryTheory.Triangulated.TStructure.eTriangleLTGE** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTriangleLTGE : EInt ⥤ C ⥤ Triangle C where obj i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (distinguished) triangles given by the natural transformations
`t.eTruncLT.obj i ⟶ 𝟭 C ⟶ t.eTruncGE.obj i ⟶ ...` for all `i : EInt`.
-/
noncomputable def eTriangleLTGE : EInt ⥤ C ⥤ Triangle C where
  obj i := Triangle.functorMk (t.eTruncLTι i) (t.eTruncGEπ i) (t.eTruncGEδLT.app i)
  map f := Triangle.functorHomMk _ _ (t.eTruncLT.map f) (𝟙 _) (t.eTruncGE.map f)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.eTriangleLTGE_distinguished** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTriangleLTGE_distinguished (i : EInt) (X : C) : (t.eTriangleLTGE.obj i).o
bj X in distTriang _
参数：i : EInt；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.distinguished_iff_of_isZero₁`：di
stinguished_iff_of_isZero₁ (T : Triangle C) (h : IsZero T.obj₁) : T in distTrian
g _ ↔ IsIso T.mor₂
· 使用定理 `CategoryTheory.Functor.zero_obj`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D]   
[inst_2 : CategoryThe…
· 使用引理 `CategoryTheory.Triangulated.TStructure.triangleLTGE_distinguished`：trian
gleLTGE_distinguished (n : Int) (X : C) : (t.triangleLTGE n).obj X in distTriang
 C
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.distinguished_iff_of_isZero₃`：di
stinguished_iff_of_isZero₃ (T : Triangle C) (h : IsZero T.obj₃) : T in distTrian
g _ ↔ IsIso T.mor₁
-/
lemma eTriangleLTGE_distinguished (i : EInt) (X : C) :
    (t.eTriangleLTGE.obj i).obj X ∈ distTriang _ := by
  induction i using WithBotTop.rec with
  | bot =>
    rw [Triangle.distinguished_iff_of_isZero₁ _ (Functor.zero_obj X)]
    dsimp
    infer_instance
  | coe n => exact t.triangleLTGE_distinguished n X
  | top =>
    rw [Triangle.distinguished_iff_of_isZero₃ _ (Functor.zero_obj X)]
    dsimp
    infer_instance
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) [t.IsLE X n] (i : EInt) :
    t.IsLE ((t.eTruncLT.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => exact isLE_of_isZero _ (by simp) _
  | coe _ => dsimp; infer_instance
  | top => dsimp; infer_instance
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) [t.IsGE X n] (i : EInt) :
    t.IsGE ((t.eTruncGE.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => dsimp; infer_instance
  | coe _ => dsimp; infer_instance
  | top => exact isGE_of_isZero _ (by simp) _
/-
**CategoryTheory.Triangulated.TStructure.isGE_eTruncGE_obj_obj** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isGE_eTruncGE_obj_obj (n : Int) (i : EInt) (h : n <= i) (X : C) : t.IsGE (
(t.eTruncGE.obj i).obj X) n
参数：n : Int；i : EInt；h : n <= i；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_of_ge`：isGE_of_ge (X : C) (p
 q : Int) (hpq : p <= q
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsGEObjTruncGE`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_of_isZero`：isGE_of_isZero {X
 : C} (hX : IsZero X) (n : Int) : t.IsGE X n
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.zero_obj`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D]   
[inst_2 : CategoryThe…
-/
lemma isGE_eTruncGE_obj_obj (n : ℤ) (i : EInt) (h : n ≤ i) (X : C) :
    t.IsGE ((t.eTruncGE.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => simp at h
  | coe i =>
    dsimp
    exact t.isGE_of_ge _ _ _ (by simpa using h)
  | top => exact t.isGE_of_isZero (Functor.zero_obj _) _
/-
**CategoryTheory.Triangulated.TStructure.isLE_eTruncLT_obj_obj** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isLE_eTruncLT_obj_obj (n : Int) (i : EInt) (h : i <= (n + 1 :)) (X : C) : 
t.IsLE (((t.eTruncLT.obj i)).obj X) n
参数：n : Int；i : EInt；h : i <= (n + 1 :)；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.isLE_of_isZero`：isLE_of_isZero {X
 : C} (hX : IsZero X) (n : Int) : t.IsLE X n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
· 使用引理 `CategoryTheory.Triangulated.TStructure.isLE_of_le`：isLE_of_le (X : C) (p
 q : Int) (hpq : p <= q
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsLEObjTruncLTHSubIntOfNat`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma isLE_eTruncLT_obj_obj (n : ℤ) (i : EInt) (h : i ≤ (n + 1 :)) (X : C) :
    t.IsLE (((t.eTruncLT.obj i)).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => exact t.isLE_of_isZero (by simp) _
  | coe i =>
    simp only [WithBotTop.coe_le_coe] at h
    dsimp
    exact t.isLE_of_le _ (i - 1) n (by lia)
  | top => simp at h
/-
**CategoryTheory.Triangulated.TStructure.isZero_eTruncLT_obj_obj** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isZero_eTruncLT_obj_obj (X : C) (n : Int) [t.IsGE X n] (j : EInt) (hj : j 
<= n) : IsZero ((t.eTruncLT.obj j).obj X)
参数：X : C；n : Int；j : EInt；hj : j <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_of_ge`：isGE_of_ge (X : C) (p
 q : Int) (hpq : p <= q
· 使用引理 `CategoryTheory.Triangulated.TStructure.isZero_truncLT_obj_of_isGE`：isZer
o_truncLT_obj_of_isGE (n : Int) (X : C) [t.IsGE X n] : IsZero ((t.truncLT n).obj
 X)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma isZero_eTruncLT_obj_obj (X : C) (n : ℤ) [t.IsGE X n] (j : EInt) (hj : j ≤ n) :
    IsZero ((t.eTruncLT.obj j).obj X) := by
  induction j using WithBotTop.rec with
  | bot => simp
  | coe j =>
    have := t.isGE_of_ge X j n (by simpa using hj)
    exact t.isZero_truncLT_obj_of_isGE _ _
  | top => simp at hj
/-
**CategoryTheory.Triangulated.TStructure.isZero_eTruncGE_obj_obj** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isZero_eTruncGE_obj_obj (X : C) (n : Int) [t.IsLE X n] (j : EInt) (hj : n 
< j) : IsZero ((t.eTruncGE.obj j).obj X)
参数：X : C；n : Int；j : EInt；hj : n < j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.isLE_of_le`：isLE_of_le (X : C) (p
 q : Int) (hpq : p <= q
· 使用引理 `CategoryTheory.Triangulated.TStructure.isZero_truncGE_obj_of_isLE`：isZer
o_truncGE_obj_of_isLE (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (X : C) [t.IsLE X n₀] : Is
Zero ((t.truncGE n₁).obj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
-/
lemma isZero_eTruncGE_obj_obj (X : C) (n : ℤ) [t.IsLE X n] (j : EInt) (hj : n < j) :
    IsZero ((t.eTruncGE.obj j).obj X) := by
  induction j using WithBotTop.rec with
  | bot => simp at hj
  | coe j =>
    simp only [WithBotTop.coe_lt_coe] at hj
    have := t.isLE_of_le X n (j - 1) (by lia)
    exact t.isZero_truncGE_obj_of_isLE (j - 1) j (by lia) _
  | top => simp

section

variable [IsTriangulated C]

/-
**CategoryTheory.Triangulated.TStructure.isIso_eTruncGE_obj_map_truncGE** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_eTruncGE_obj_map_truncGEπ_app (a b : EInt) (h : a ≤ b) (X : C) :
    IsIso ((t.eTruncGE.obj b).map ((t.eTruncGEπ a).app X)) := by
  induction b using WithBotTop.rec with
  | bot =>
    obtain rfl : a = ⊥ := by simpa using h
    infer_instance
  | coe b =>
    induction a using WithBotTop.rec with
    | bot => infer_instance
    | coe a => exact t.isIso_truncGE_map_truncGEπ_app b a (by simpa using h) X
    | top => simp at h
  | top => exact ⟨0, IsZero.eq_of_src (by simp) _ _, IsZero.eq_of_src (by simp) _ _⟩
/-
**CategoryTheory.Triangulated.TStructure.isIso_eTruncLT_obj_map_truncLT** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_eTruncLT_obj_map_truncLTπ_app (a b : EInt) (h : a ≤ b) (X : C) :
    IsIso ((t.eTruncLT.obj a).map ((t.eTruncLTι b).app X)) := by
  induction a using WithBotTop.rec with
  | bot => exact ⟨0, IsZero.eq_of_src (by simp) _ _, IsZero.eq_of_src (by simp) _ _⟩
  | coe a =>
    induction b using WithBotTop.rec with
    | bot => simp at h
    | coe b =>
      exact t.isIso_truncLT_map_truncLTι_app a b (by simpa using h) X
    | top => dsimp; infer_instance
  | top =>
    obtain rfl : b = ⊤ := by simpa using h
    infer_instance
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : EInt) (X : C) : IsIso ((t.eTruncLT.obj a).map ((t.eTruncLTι a).app X)) :=
  isIso_eTruncLT_obj_map_truncLTπ_app t a a (by rfl) X
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : EInt) (X : C) : IsIso ((t.eTruncLTι a).app ((t.eTruncLT.obj a).obj X)) := by
  rw [← eTruncLT_obj_map_eTruncLTι_app]
  infer_instance
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) [t.IsGE X n] (i : EInt) :
    t.IsGE ((t.eTruncLT.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => exact isGE_of_isZero _ (by simp) _
  | coe _ => dsimp; infer_instance
  | top => dsimp; infer_instance
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) [t.IsLE X n] (i : EInt) :
    t.IsLE ((t.eTruncGE.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => dsimp; infer_instance
  | coe _ => dsimp; infer_instance
  | top => exact isLE_of_isZero _ (by simp) _

/-- The natural transformation `t.eTruncGE.obj b ⟶ t.eTruncGE.obj a ⋙ t.eTruncGE.obj b`
for all `a` and `b` in `EInt`. -/
@[simps!]
/-
**CategoryTheory.Triangulated.TStructure.eTruncGEToGEGE** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGEToGEGE (a b : EInt) : t.eTruncGE.obj b ⟶ t.eTruncGE.obj a ⋙ t.eTru
ncGE.obj b
参数：a b : EInt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `t.eTruncGE.obj b ⟶ t.eTruncGE.obj a ⋙ t.eTruncGE.obj
 b`
for all `a` and `b` in `EInt`.
-/
noncomputable def eTruncGEToGEGE (a b : EInt) :
    t.eTruncGE.obj b ⟶ t.eTruncGE.obj a ⋙ t.eTruncGE.obj b :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (t.eTruncGEπ a) _
/-
**CategoryTheory.Triangulated.TStructure.isIso_eTruncGEIsoGEGE** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isIso_eTruncGEIsoGEGE (a b : EInt) (hab : a <= b) : IsIso (t.eTruncGEToGEG
E a b)
参数：a b : EInt；hab : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.isIso_iff_isIso_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncGEToGEGE_app`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pread
ditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用引理 `CategoryTheory.Triangulated.TStructure.isIso_eTruncGE_obj_map_truncGEπ_a
pp`：isIso_eTruncGE_obj_map_truncGEπ_app (a b : EInt) (h : a <= b) (X : C) : IsIs
o ((t.eTruncGE.obj b).map ((t.eTruncGEπ a).app X))
-/
lemma isIso_eTruncGEIsoGEGE (a b : EInt) (hab : a ≤ b) :
    IsIso (t.eTruncGEToGEGE a b) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro
  simp only [eTruncGEToGEGE_app]
  exact t.isIso_eTruncGE_obj_map_truncGEπ_app _ _ hab _

section

variable (a b : EInt) (hab : a ≤ b)

/-- The natural isomorphism `t.eTruncGE.obj b ≅ t.eTruncGE.obj a ⋙ t.eTruncGE.obj b`
when `a` and `b` in `EInt` satisfy `a ≤ b`. -/
@[simps! hom]
/-
**CategoryTheory.Triangulated.TStructure.eTruncGEIsoGEGE** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGEIsoGEGE : t.eTruncGE.obj b ≅ t.eTruncGE.obj a ⋙ t.eTruncGE.obj b
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.isIso_eTruncGEIsoGEGE`：isIso_eTru
ncGEIsoGEGE (a b : EInt) (hab : a <= b) : IsIso (t.eTruncGEToGEGE a b)

--- 原说明 ---
The natural isomorphism `t.eTruncGE.obj b ≅ t.eTruncGE.obj a ⋙ t.eTruncGE.obj b`
when `a` and `b` in `EInt` satisfy `a ≤ b`.
-/
noncomputable def eTruncGEIsoGEGE :
    t.eTruncGE.obj b ≅ t.eTruncGE.obj a ⋙ t.eTruncGE.obj b :=
  haveI := t.isIso_eTruncGEIsoGEGE a b hab
  asIso (t.eTruncGEToGEGE a b)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.eTruncGEIsoGEGE_hom_inv_id_app** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGEIsoGEGE_hom_inv_id_app (X : C) : (t.eTruncGE.obj b).map ((t.eTrunc
GEπ a).app X) ≫ (t.eTruncGEIsoGEGE a b hab).inv.app X = 𝟙 _
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncGEIsoGEGE_hom`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Prea
dditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncGEToGEGE_app`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pread
ditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
-/
lemma eTruncGEIsoGEGE_hom_inv_id_app (X : C) :
    (t.eTruncGE.obj b).map ((t.eTruncGEπ a).app X) ≫ (t.eTruncGEIsoGEGE a b hab).inv.app X =
      𝟙 _ := by
  simpa using! (t.eTruncGEIsoGEGE a b hab).hom_inv_id_app X

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.eTruncGEIsoGEGE_inv_hom_id_app** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncGEIsoGEGE_inv_hom_id_app (X : C) : (t.eTruncGEIsoGEGE a b hab).inv.a
pp X ≫ (t.eTruncGE.obj b).map ((t.eTruncGEπ a).app X) = 𝟙 _
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncGEIsoGEGE_hom`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Prea
dditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncGEToGEGE_app`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pread
ditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
-/
lemma eTruncGEIsoGEGE_inv_hom_id_app (X : C) :
    (t.eTruncGEIsoGEGE a b hab).inv.app X ≫ (t.eTruncGE.obj b).map ((t.eTruncGEπ a).app X) =
      𝟙 _ := by
  simpa using! (t.eTruncGEIsoGEGE a b hab).inv_hom_id_app X

end

/-- The natural transformation `t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ⟶ t.eTruncLT.obj b`
for all `a` and `b` in `EInt`. -/
@[simps!]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLTLTToLT** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLTLTToLT (a b : EInt) : t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ⟶ t.eTru
ncLT.obj b
参数：a b : EInt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ⟶ t.eTruncLT.obj
 b`
for all `a` and `b` in `EInt`.
-/
noncomputable def eTruncLTLTToLT (a b : EInt) :
    t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ⟶ t.eTruncLT.obj b :=
  Functor.whiskerRight (t.eTruncLTι a) _ ≫ (Functor.leftUnitor _).hom
/-
**CategoryTheory.Triangulated.TStructure.isIso_eTruncLTLTIsoLT** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isIso_eTruncLTLTIsoLT (a b : EInt) (hab : b <= a) : IsIso (t.eTruncLTLTToL
T a b)
参数：a b : EInt；hab : b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.isIso_iff_isIso_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncLTLTToLT_app`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pread
ditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用引理 `CategoryTheory.Triangulated.TStructure.isIso_eTruncLT_obj_map_truncLTπ_a
pp`：isIso_eTruncLT_obj_map_truncLTπ_app (a b : EInt) (h : a <= b) (X : C) : IsIs
o ((t.eTruncLT.obj a).map ((t.eTruncLTι b).app X))
-/
lemma isIso_eTruncLTLTIsoLT (a b : EInt) (hab : b ≤ a) :
    IsIso (t.eTruncLTLTToLT a b) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro
  simp only [eTruncLTLTToLT_app]
  exact t.isIso_eTruncLT_obj_map_truncLTπ_app _ _ hab _

section

variable (a b : EInt) (hab : b ≤ a)

/-- The natural isomorphism `t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ⟶ t.eTruncLT.obj b`
when `a` and `b` in `EInt` satisfy `b ≤ a`. -/
@[simps! hom]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLTLTIsoLT** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLTLTIsoLT : t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ≅ t.eTruncLT.obj b
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.isIso_eTruncLTLTIsoLT`：isIso_eTru
ncLTLTIsoLT (a b : EInt) (hab : b <= a) : IsIso (t.eTruncLTLTToLT a b)

--- 原说明 ---
The natural isomorphism `t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ⟶ t.eTruncLT.obj b`
when `a` and `b` in `EInt` satisfy `b ≤ a`.
-/
noncomputable def eTruncLTLTIsoLT :
    t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ≅ t.eTruncLT.obj b :=
  haveI := t.isIso_eTruncLTLTIsoLT a b hab
  asIso (t.eTruncLTLTToLT a b)

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLTLTIsoLT_hom_inv_id_app** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLTLTIsoLT_hom_inv_id_app (X : C) : (t.eTruncLT.obj b).map ((t.eTrunc
LTι a).app X) ≫ (t.eTruncLTLTIsoLT a b hab).inv.app X = 𝟙 _
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncLTLTToLT_app`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pread
ditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
-/
lemma eTruncLTLTIsoLT_hom_inv_id_app (X : C) :
    (t.eTruncLT.obj b).map ((t.eTruncLTι a).app X) ≫
      (t.eTruncLTLTIsoLT a b hab).inv.app X = 𝟙 _ := by
  simpa using (t.eTruncLTLTIsoLT a b hab).hom_inv_id_app X

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLTLTIsoLT_inv_hom_id_app** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLTLTIsoLT_inv_hom_id_app (X : C) : (t.eTruncLTLTIsoLT a b hab).inv.a
pp X ≫ (t.eTruncLT.obj b).map ((t.eTruncLTι a).app X) = 𝟙 _
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncLTLTIsoLT_hom`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Prea
dditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncLTLTToLT_app`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pread
ditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
-/
lemma eTruncLTLTIsoLT_inv_hom_id_app (X : C) :
    (t.eTruncLTLTIsoLT a b hab).inv.app X ≫
    (t.eTruncLT.obj b).map ((t.eTruncLTι a).app X) = 𝟙 _ := by
  simpa using (t.eTruncLTLTIsoLT a b hab).inv_hom_id_app X

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLTLTIsoLT_inv_hom_id_app_eTruncLT
_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLTLTIsoLT_inv_hom_id_app_eTruncLT_obj (X : C) : (t.eTruncLTLTIsoLT a
 b hab).inv.app ((t.eTruncLT.obj a).obj X) ≫ (t.eTruncLT.obj b).map ((t.eTruncLT
.obj a).map ((t.eTruncLTι a).app X)) = 𝟙 _
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Triangulated.TStructure.eTruncLT_obj_map_eTruncLTι_app`：e
TruncLT_obj_map_eTruncLTι_app (i : EInt) (X : C) : (t.eTruncLT.obj i).map ((t.eT
runcLTι i).app X) = (t.eTruncLTι i).app ((t.eTruncLT.obj i)…
· 使用引理 `CategoryTheory.Triangulated.TStructure.eTruncLTLTIsoLT_inv_hom_id_app`：e
TruncLTLTIsoLT_inv_hom_id_app (X : C) : (t.eTruncLTLTIsoLT a b hab).inv.app X ≫ 
(t.eTruncLT.obj b).map ((t.eTruncLTι a).app X) = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eTruncLTLTIsoLT_inv_hom_id_app_eTruncLT_obj (X : C) :
    (t.eTruncLTLTIsoLT a b hab).inv.app ((t.eTruncLT.obj a).obj X) ≫
      (t.eTruncLT.obj b).map ((t.eTruncLT.obj a).map ((t.eTruncLTι a).app X)) = 𝟙 _ := by
  simp [eTruncLT_obj_map_eTruncLTι_app]

end


section

variable (a b : EInt)

/-- The natural transformation from
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b` to
`t.eTruncGE.obj a ⋙ t.eTruncLT.obj b`. (This is an isomorphism.) -/
@[simps!]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLTGELTSelfToLTGE** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLTGELTSelfToLTGE : t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.
obj b ⟶ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation from
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b` to
`t.eTruncGE.obj a ⋙ t.eTruncLT.obj b`. (This is an isomorphism.)
-/
noncomputable def eTruncLTGELTSelfToLTGE :
    t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b ⟶
      t.eTruncGE.obj a ⋙ t.eTruncLT.obj b :=
  Functor.whiskerRight (t.eTruncLTι b) _ ≫ (Functor.leftUnitor _).hom

/-- The natural transformation from
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b` to
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a`. (This is an isomorphism.) -/
@[simps!]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLTGELTSelfToGELT** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLTGELTSelfToGELT : t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.
obj b ⟶ t.eTruncLT.obj b ⋙ t.eTruncGE.obj a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation from
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b` to
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a`. (This is an isomorphism.)
-/
noncomputable def eTruncLTGELTSelfToGELT :
    t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b ⟶
      t.eTruncLT.obj b ⋙ t.eTruncGE.obj a :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerLeft _ (t.eTruncLTι b) ≫
    (Functor.rightUnitor _).hom

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (t.eTruncLTGELTSelfToLTGE a b) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  induction b using WithBotTop.rec with
  | bot => simp [isIsoZero_iff_source_target_isZero]
  | coe b =>
    induction a using WithBotTop.rec with
    | bot => simpa using inferInstanceAs (IsIso ((t.truncLT b).map ((t.truncLTι b).app X)))
    | coe a =>
      simp only [eTruncLT_obj_coe, eTruncGE_obj_coe, eTruncLTGELTSelfToLTGE_app,
        eTruncLT_map_eq_truncLTι]
      infer_instance
    | top =>
      simp only [eTruncLT_obj_coe, eTruncGE_obj_top, Functor.comp_obj, eTruncLTGELTSelfToLTGE_app,
        eTruncLT_map_eq_truncLTι, zero_map, Functor.map_zero, isIsoZero_iff_source_target_isZero]
      constructor
      all_goals exact Functor.map_isZero _ (Functor.zero_obj _)
  | top => simpa using inferInstanceAs (IsIso (𝟙 _))

variable (b : EInt) (X : C)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (t.eTruncLTGELTSelfToGELT a b) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  induction a using WithBotTop.rec with
  | bot => simpa using inferInstanceAs (IsIso ((t.eTruncLTι b).app ((t.eTruncLT.obj b).obj X)))
  | coe a =>
    induction b using WithBotTop.rec with
    | bot => simpa [isIsoZero_iff_source_target_isZero] using
        (t.eTruncGE.obj a).map_isZero (Functor.zero_obj _)
    | coe b =>
      simp only [eTruncLT_obj_coe, eTruncGE_obj_coe, eTruncLTGELTSelfToGELT_app,
        eTruncLT_map_eq_truncLTι]
      infer_instance
    | top => simpa using inferInstanceAs (IsIso (𝟙 _))
  | top =>
    exact ⟨0, ((t.eTruncLT.obj b).map_isZero (by simp)).eq_of_src _ _,
      IsZero.eq_of_src (by simp) _ _⟩

end

/-- The commutation natural isomorphism
`t.eTruncGE.obj a ⋙ t.eTruncLT.obj b ≅ t.eTruncLT.obj b ⋙ t.eTruncGE.obj a`
for all `a` and `b` in `EInt`. -/
/-
**CategoryTheory.Triangulated.TStructure.eTruncLTGEIsoGELT** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLTGEIsoGELT (a b : EInt) : t.eTruncGE.obj a ⋙ t.eTruncLT.obj b ≅ t.e
TruncLT.obj b ⋙ t.eTruncGE.obj a
参数：a b : EInt。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsIsoFunctorETruncLTGELTSelfT
oLTGE`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : 
CategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsIsoFunctorETruncLTGELTSelfT
oGELT`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : 
CategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…

--- 原说明 ---
The commutation natural isomorphism
`t.eTruncGE.obj a ⋙ t.eTruncLT.obj b ≅ t.eTruncLT.obj b ⋙ t.eTruncGE.obj a`
for all `a` and `b` in `EInt`.
-/
noncomputable def eTruncLTGEIsoGELT (a b : EInt) :
    t.eTruncGE.obj a ⋙ t.eTruncLT.obj b ≅ t.eTruncLT.obj b ⋙ t.eTruncGE.obj a :=
  (asIso (t.eTruncLTGELTSelfToLTGE a b)).symm ≪≫ asIso (t.eTruncLTGELTSelfToGELT a b)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLTGEIsoGELT_hom_naturality** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLTGEIsoGELT_hom_naturality (a b : EInt) {X Y : C} (f : X ⟶ Y) : (t.e
TruncLT.obj b).map ((t.eTruncGE.obj a).map f) ≫ (t.eTruncLTGEIsoGELT a b).hom.ap
p Y = (t.eTruncLTGEIsoGELT a b).hom.app X ≫ (t.eTruncGE.obj a).map ((t.eTruncLT.
obj b).map f)
参数：a b : EInt；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma eTruncLTGEIsoGELT_hom_naturality (a b : EInt) {X Y : C} (f : X ⟶ Y) :
    (t.eTruncLT.obj b).map ((t.eTruncGE.obj a).map f) ≫ (t.eTruncLTGEIsoGELT a b).hom.app Y =
      (t.eTruncLTGEIsoGELT a b).hom.app X ≫ (t.eTruncGE.obj a).map ((t.eTruncLT.obj b).map f) :=
  (t.eTruncLTGEIsoGELT a b).hom.naturality f

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLTGEIsoGELT_hom_app_fac** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLTGEIsoGELT_hom_app_fac (a b : EInt) (X : C) : (t.eTruncLT.obj b).ma
p ((t.eTruncGE.obj a).map ((t.eTruncLTι b).app X)) ≫ (t.eTruncLTGEIsoGELT a b).h
om.app X = (t.eTruncLTι b).app ((t.eTruncGE.obj a).obj ((t.eTruncLT.obj b).obj X
))
参数：a b : EInt；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsIsoFunctorETruncLTGELTSelfT
oLTGE`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : 
CategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncLTGELTSelfToLTGE_app`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncLTGELTSelfToGELT_app`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eTruncLTGEIsoGELT_hom_app_fac (a b : EInt) (X : C) :
    (t.eTruncLT.obj b).map ((t.eTruncGE.obj a).map ((t.eTruncLTι b).app X)) ≫
      (t.eTruncLTGEIsoGELT a b).hom.app X =
    (t.eTruncLTι b).app ((t.eTruncGE.obj a).obj ((t.eTruncLT.obj b).obj X)) := by
  simp [eTruncLTGEIsoGELT]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLTGEIsoGELT_hom_app_fac'** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLTGEIsoGELT_hom_app_fac' (a b : EInt) (X : C) : (t.eTruncLTGEIsoGELT
 a b).hom.app X ≫ (t.eTruncGE.obj a).map ((t.eTruncLTι b).app X) = (t.eTruncLTι 
b).app ((t.eTruncGE.obj a).obj X)
参数：a b : EInt；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsIsoFunctorETruncLTGELTSelfT
oLTGE`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : 
CategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncLTGELTSelfToLTGE_app`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncLTGELTSelfToGELT_app`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eTruncLTGEIsoGELT_hom_app_fac' (a b : EInt) (X : C) :
    (t.eTruncLTGEIsoGELT a b).hom.app X ≫ (t.eTruncGE.obj a).map ((t.eTruncLTι b).app X) =
      (t.eTruncLTι b).app ((t.eTruncGE.obj a).obj X) := by
  simp [eTruncLTGEIsoGELT]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open ComposableArrows in
@[reassoc]
/-
**CategoryTheory.Triangulated.TStructure.eTruncLTGEIsoGELT_naturality_app** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：eTruncLTGEIsoGELT_naturality_app (a b : EInt) (hab : a <= b) (a' b' : EInt
) (hab' : a' <= b') (φ : mk₁ (homOfLE hab) ⟶ mk₁ (homOfLE hab')) (X : C) : (t.eT
runcLT.map (φ.app 1)).app ((t.eTruncGE.obj a).obj X) ≫ (t.eTruncLT.obj b').map (
(t.eTruncGE.map (φ.app 0)).app X) ≫ (t.eTruncLTGEIsoGELT a' b').hom.app X = (t.e
TruncLTGEIsoGELT a b).hom.app X ≫ (t.eTruncGE.map (φ.app 0)).app _ ≫ (t.eTruncGE
.obj a').map ((t.eTruncLT.map (φ.app 1)).app X)
参数：a b : EInt；hab : a <= b；a' b' : EInt；hab' : a' <= b'；φ : mk₁ (homOfLE hab) ⟶ 
mk₁ (homOfLE hab')；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsIsoFunctorETruncLTGELTSelfT
oLTGE`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : 
CategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncLTGELTSelfToLTGE_app`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncLTGEIsoGELT_hom_app_fac_ass
oc`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Cat
egoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Triangulated.TStructure.eTruncLT_map_app_eTruncLTι_app`：e
TruncLT_map_app_eTruncLTι_app {i j : EInt} (f : i ⟶ j) (X : C) : (t.eTruncLT.map
 f).app X ≫ (t.eTruncLTι j).app X = (t.eTruncLTι i).app X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Triangulated.TStructure.eTruncLTGEIsoGELT_hom_app_fac`：eT
runcLTGEIsoGELT_hom_app_fac (a b : EInt) (X : C) : (t.eTruncLT.obj b).map ((t.eT
runcGE.obj a).map ((t.eTruncLTι b).app X)) ≫ (t.eTruncLTGE…
· 使用定理 `CategoryTheory.Triangulated.TStructure.eTruncLT_map_app_eTruncLTι_app_as
soc`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eTruncLTGEIsoGELT_naturality_app (a b : EInt) (hab : a ≤ b)
    (a' b' : EInt) (hab' : a' ≤ b') (φ : mk₁ (homOfLE hab) ⟶ mk₁ (homOfLE hab')) (X : C) :
      (t.eTruncLT.map (φ.app 1)).app ((t.eTruncGE.obj a).obj X) ≫
        (t.eTruncLT.obj b').map ((t.eTruncGE.map (φ.app 0)).app X) ≫
        (t.eTruncLTGEIsoGELT a' b').hom.app X =
    (t.eTruncLTGEIsoGELT a b).hom.app X ≫ (t.eTruncGE.map (φ.app 0)).app _ ≫
      (t.eTruncGE.obj a').map ((t.eTruncLT.map (φ.app 1)).app X) := by
  dsimp
  rw [← cancel_epi ((t.eTruncLTGELTSelfToLTGE a b).app X), eTruncLTGELTSelfToLTGE_app,
    eTruncLTGEIsoGELT_hom_app_fac_assoc, NatTrans.naturality_assoc, ← Functor.map_comp_assoc,
    NatTrans.naturality, Functor.map_comp_assoc, ← t.eTruncLT_map_app_eTruncLTι_app (φ.app 1) X]
  simp [↓Functor.map_comp, t.eTruncLTGEIsoGELT_hom_app_fac]

end

end TStructure

end Triangulated

end CategoryTheory

