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

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C Int]
  [forall (n : Int), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `eTruncLT` / `eTruncLT` 的定义

English:
definition eTruncLT
  signature: : EInt ⥤ C ⥤ C where
  body: WithBotTop.rec 0 t.truncLT (𝟭 C)
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

中文:
定义 eTruncLT
  签名: : E整数 ⥤ C ⥤ C where
  定义体: WithBotTop.rec 0 t.truncLT (𝟭 C)
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

Depends on / 依赖: WithBotTop, WithBotTop.rec, t.truncLT, truncLT
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
/--
lemma `eTruncLT_obj_top` / 引理 `eTruncLT_obj_top`

English:
lemma eTruncLT_obj_top
  statement: t.eTruncLT.obj ⊤ = 𝟭 _
  proof: rfl

@[simp]

中文:
引理 eTruncLT_obj_top
  结论: t.eTruncLT.obj ⊤ = 𝟭 _
  证明: rfl

@[simp]
-/
lemma eTruncLT_obj_top : t.eTruncLT.obj ⊤ = 𝟭 _ := rfl

@[simp]
/--
lemma `eTruncLT_obj_bot` / 引理 `eTruncLT_obj_bot`

English:
lemma eTruncLT_obj_bot
  statement: t.eTruncLT.obj ⊥ = 0
  proof: rfl

@[simp]

中文:
引理 eTruncLT_obj_bot
  结论: t.eTruncLT.obj ⊥ = 0
  证明: rfl

@[simp]
-/
lemma eTruncLT_obj_bot : t.eTruncLT.obj ⊥ = 0 := rfl

@[simp]
/--
lemma `eTruncLT_obj_coe` / 引理 `eTruncLT_obj_coe`

English:
lemma eTruncLT_obj_coe
  given: (n : Int)
  statement: t.eTruncLT.obj n = t.truncLT n
  proof: rfl

@[simp]

中文:
引理 eTruncLT_obj_coe
  条件: (n : 整数)
  结论: t.eTruncLT.obj n = t.truncLT n
  证明: rfl

@[simp]
-/
lemma eTruncLT_obj_coe (n : Int) : t.eTruncLT.obj n = t.truncLT n := rfl

@[simp]
/--
lemma `eTruncLT_map_eq_truncLTι` / 引理 `eTruncLT_map_eq_truncLTι`

English:
lemma eTruncLT_map_eq_truncLTι
  given: (n : Int)
  proof: rfl

中文:
引理 eTruncLT_map_eq_truncLTι
  条件: (n : 整数)
  证明: rfl
-/
lemma eTruncLT_map_eq_truncLTι (n : Int) :
    t.eTruncLT.map (homOfLE (show (n : EInt) <= ⊤ by simp)) = t.truncLTι n := rfl

instance (i : EInt) : (t.eTruncLT.obj i).Additive := by
  induction i using WithBotTop.rec
  all_goals dsimp; infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `eTruncGE` / `eTruncGE` 的定义

English:
definition eTruncGE
  signature: : EInt ⥤ C ⥤ C where
  body: WithBotTop.rec (𝟭 C) t.truncGE 0
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

中文:
定义 eTruncGE
  签名: : E整数 ⥤ C ⥤ C where
  定义体: WithBotTop.rec (𝟭 C) t.truncGE 0
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

Depends on / 依赖: WithBotTop, WithBotTop.rec, t.truncGE, truncGE
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
/--
lemma `eTruncGE_obj_bot` / 引理 `eTruncGE_obj_bot`

English:
lemma eTruncGE_obj_bot
  proof: rfl

@[simp]

中文:
引理 eTruncGE_obj_bot
  证明: rfl

@[simp]
-/
lemma eTruncGE_obj_bot :
    t.eTruncGE.obj ⊥ = 𝟭 _ := rfl

@[simp]
/--
lemma `eTruncGE_obj_top` / 引理 `eTruncGE_obj_top`

English:
lemma eTruncGE_obj_top
  proof: rfl

@[simp]

中文:
引理 eTruncGE_obj_top
  证明: rfl

@[simp]
-/
lemma eTruncGE_obj_top :
    t.eTruncGE.obj ⊤ = 0 := rfl

@[simp]
/--
lemma `eTruncGE_obj_coe` / 引理 `eTruncGE_obj_coe`

English:
lemma eTruncGE_obj_coe
  given: (n : Int)
  statement: t.eTruncGE.obj n = t.truncGE n
  proof: rfl

中文:
引理 eTruncGE_obj_coe
  条件: (n : 整数)
  结论: t.eTruncGE.obj n = t.truncGE n
  证明: rfl
-/
lemma eTruncGE_obj_coe (n : Int) : t.eTruncGE.obj n = t.truncGE n := rfl

instance (i : EInt) : (t.eTruncGE.obj i).Additive := by
  induction i using WithBotTop.rec
  all_goals dsimp; infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `eTruncGEδLT` / `eTruncGEδLT` 的定义

English:
definition eTruncGEδLT
  signature: :
  body: WithBotTop.rec 0 t.truncGEδLT 0
  naturality {a b} hab := by
    replace hab := leOfHom hab
    induction a using WithBotTop.rec; rotate_right
    · apply (isZero_zero _).eq_of_src
    all_goals
      induction b using WithBotTop.rec <;> simp at hab <;>
        dsimp [eTruncGE, eTruncLT] <;>
        simp [t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE]

@[simp]

中文:
定义 eTruncGEδLT
  签名: :
  定义体: WithBotTop.rec 0 t.truncGEδLT 0
  naturality {a b} hab := by
    replace hab := leOfHom hab
    induction a using WithBotTop.rec; rotate_right
    · apply (isZero_zero _).eq_of_src
    all_goals
      induction b using WithBotTop.rec <;> simp at hab <;>
        dsimp [eTruncGE, eTruncLT] <;>
        simp [t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE]

@[simp]

Depends on / 依赖: WithBotTop, WithBotTop.rec, t.truncGE
-/
noncomputable def eTruncGEδLT :
    t.eTruncGE ⟶ t.eTruncLT ⋙ ((Functor.whiskeringRight ..).obj (shiftFunctor C (1 : Int))) where
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
/--
lemma `eTruncGEδLT_coe` / 引理 `eTruncGEδLT_coe`

English:
lemma eTruncGEδLT_coe
  given: (n : Int)
  proof: rfl

中文:
引理 eTruncGEδLT_coe
  条件: (n : 整数)
  证明: rfl
-/
lemma eTruncGEδLT_coe (n : Int) :
    t.eTruncGEδLT.app n = t.truncGEδLT n := rfl

/--
Definition of `eTruncLTι` / `eTruncLTι` 的定义

English:
abbreviation eTruncLTι
  signature: (i : EInt)
  body: t.eTruncLT.map (homOfLE (le_top))

中文:
缩写 eTruncLTι
  签名: (i : E整数)
  定义体: t.eTruncLT.map (homOfLE (le_top))

Depends on / 依赖: eTruncLT, homOfLE, le_top, t.eTruncLT.map
-/
noncomputable abbrev eTruncLTι (i : EInt) : t.eTruncLT.obj i ⟶ 𝟭 _ :=
  t.eTruncLT.map (homOfLE (le_top))

/--
lemma `eTruncLT_ι_bot` / 引理 `eTruncLT_ι_bot`

English:
lemma eTruncLT_ι_bot
  statement: t.eTruncLTι ⊥ = 0
  proof: rfl

中文:
引理 eTruncLT_ι_bot
  结论: t.eTruncLTι ⊥ = 0
  证明: rfl
-/
@[simp] lemma eTruncLT_ι_bot : t.eTruncLTι ⊥ = 0 := rfl
/--
lemma `eTruncLT_ι_coe` / 引理 `eTruncLT_ι_coe`

English:
lemma eTruncLT_ι_coe
  given: (n : Int)
  statement: t.eTruncLTι n = t.truncLTι n
  proof: rfl

中文:
引理 eTruncLT_ι_coe
  条件: (n : 整数)
  结论: t.eTruncLTι n = t.truncLTι n
  证明: rfl
-/
@[simp] lemma eTruncLT_ι_coe (n : Int) : t.eTruncLTι n = t.truncLTι n := rfl
/--
lemma `eTruncLT_ι_top` / 引理 `eTruncLT_ι_top`

English:
lemma eTruncLT_ι_top
  statement: t.eTruncLTι ⊤ = 𝟙 _
  proof: rfl

@[reassoc]

中文:
引理 eTruncLT_ι_top
  结论: t.eTruncLTι ⊤ = 𝟙 _
  证明: rfl

@[reassoc]
-/
@[simp] lemma eTruncLT_ι_top : t.eTruncLTι ⊤ = 𝟙 _ := rfl

@[reassoc]
/--
lemma `eTruncLTι_naturality` / 引理 `eTruncLTι_naturality`

English:
lemma eTruncLTι_naturality
  given: (i : EInt) {X Y : C} (f : X ⟶ Y)
  proof: (t.eTruncLTι i).naturality f

中文:
引理 eTruncLTι_naturality
  条件: (i : E整数) {X Y : C} (f : X ⟶ Y)
  证明: (t.eTruncLTι i).naturality f

Depends on / 依赖: naturality, t.eTruncLT
-/
lemma eTruncLTι_naturality (i : EInt) {X Y : C} (f : X ⟶ Y) :
    (t.eTruncLT.obj i).map f ≫ (t.eTruncLTι i).app Y = (t.eTruncLTι i).app X ≫ f :=
  (t.eTruncLTι i).naturality f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (t.eTruncLTι ⊤)
  body: by
  dsimp [eTruncLTι]
  infer_instance

中文:
实例 :
  签名: 是同构 (t.eTruncLTι ⊤)
  定义体: by
  dsimp [eTruncLTι]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : IsIso (t.eTruncLTι ⊤) := by
  dsimp [eTruncLTι]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `eTruncLT_map_app_eTruncLTι_app` / 引理 `eTruncLT_map_app_eTruncLTι_app`

English:
lemma eTruncLT_map_app_eTruncLTι_app
  given: {i j : EInt} (f : i ⟶ j) (X : C)
  proof: by
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rfl

中文:
引理 eTruncLT_map_app_eTruncLTι_app
  条件: {i j : E整数} (f : i ⟶ j) (X : C)
  证明: by
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rfl

Depends on / 依赖: Functor, Functor.map_comp, NatTrans, NatTrans.comp_app, comp_app, map_comp
-/
lemma eTruncLT_map_app_eTruncLTι_app {i j : EInt} (f : i ⟶ j) (X : C) :
    (t.eTruncLT.map f).app X ≫ (t.eTruncLTι j).app X = (t.eTruncLTι i).app X := by
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `eTruncLT_obj_map_eTruncLTι_app` / 引理 `eTruncLT_obj_map_eTruncLTι_app`

English:
lemma eTruncLT_obj_map_eTruncLTι_app
  given: (i : EInt) (X : C)
  proof: by
  induction i using WithBotTop.rec with simp [truncLT_map_truncLTι_app]

中文:
引理 eTruncLT_obj_map_eTruncLTι_app
  条件: (i : E整数) (X : C)
  证明: by
  induction i using WithBotTop.rec with simp [truncLT_map_truncLTι_app]

Depends on / 依赖: WithBotTop, WithBotTop.rec
-/
lemma eTruncLT_obj_map_eTruncLTι_app (i : EInt) (X : C) :
    (t.eTruncLT.obj i).map ((t.eTruncLTι i).app X) =
    (t.eTruncLTι i).app ((t.eTruncLT.obj i).obj X) := by
  induction i using WithBotTop.rec with simp [truncLT_map_truncLTι_app]

/--
Definition of `eTruncGEπ` / `eTruncGEπ` 的定义

English:
abbreviation eTruncGEπ
  signature: (i : EInt)
  body: t.eTruncGE.map (homOfLE (bot_le))

中文:
缩写 eTruncGEπ
  签名: (i : E整数)
  定义体: t.eTruncGE.map (homOfLE (bot_le))

Depends on / 依赖: bot_le, eTruncGE, homOfLE, t.eTruncGE.map
-/
noncomputable abbrev eTruncGEπ (i : EInt) : 𝟭 C ⟶ t.eTruncGE.obj i :=
  t.eTruncGE.map (homOfLE (bot_le))

/--
lemma `eTruncGEπ_bot` / 引理 `eTruncGEπ_bot`

English:
lemma eTruncGEπ_bot
  statement: t.eTruncGEπ ⊥ = 𝟙 _
  proof: rfl

中文:
引理 eTruncGEπ_bot
  结论: t.eTruncGEπ ⊥ = 𝟙 _
  证明: rfl
-/
@[simp] lemma eTruncGEπ_bot : t.eTruncGEπ ⊥ = 𝟙 _ := rfl
/--
lemma `eTruncGEπ_coe` / 引理 `eTruncGEπ_coe`

English:
lemma eTruncGEπ_coe
  given: (n : Int)
  statement: t.eTruncGEπ n = t.truncGEπ n
  proof: rfl

中文:
引理 eTruncGEπ_coe
  条件: (n : 整数)
  结论: t.eTruncGEπ n = t.truncGEπ n
  证明: rfl
-/
@[simp] lemma eTruncGEπ_coe (n : Int) : t.eTruncGEπ n = t.truncGEπ n := rfl
/--
lemma `eTruncGEπ_top` / 引理 `eTruncGEπ_top`

English:
lemma eTruncGEπ_top
  statement: t.eTruncGEπ ⊤ = 0
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 eTruncGEπ_top
  结论: t.eTruncGEπ ⊤ = 0
  证明: rfl

@[reassoc (attr := simp)]
-/
@[simp] lemma eTruncGEπ_top : t.eTruncGEπ ⊤ = 0 := rfl

@[reassoc (attr := simp)]
/--
lemma `eTruncGEπ_naturality` / 引理 `eTruncGEπ_naturality`

English:
lemma eTruncGEπ_naturality
  given: (i : EInt) {X Y : C} (f : X ⟶ Y)
  proof: ((t.eTruncGEπ i).naturality f).symm

中文:
引理 eTruncGEπ_naturality
  条件: (i : E整数) {X Y : C} (f : X ⟶ Y)
  证明: ((t.eTruncGEπ i).naturality f).symm

Depends on / 依赖: naturality, t.eTruncGE
-/
lemma eTruncGEπ_naturality (i : EInt) {X Y : C} (f : X ⟶ Y) :
    (t.eTruncGEπ i).app X ≫ (t.eTruncGE.obj i).map f = f ≫ (t.eTruncGEπ i).app Y :=
  ((t.eTruncGEπ i).naturality f).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (t.eTruncGEπ ⊥)
  body: by
  dsimp [eTruncGEπ]
  infer_instance

中文:
实例 :
  签名: 是同构 (t.eTruncGEπ ⊥)
  定义体: by
  dsimp [eTruncGEπ]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : IsIso (t.eTruncGEπ ⊥) := by
  dsimp [eTruncGEπ]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `eTruncGEπ_app_eTruncGE_map_app` / 引理 `eTruncGEπ_app_eTruncGE_map_app`

English:
lemma eTruncGEπ_app_eTruncGE_map_app
  given: {i j : EInt} (f : i ⟶ j) (X : C)
  proof: by
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rfl

中文:
引理 eTruncGEπ_app_eTruncGE_map_app
  条件: {i j : E整数} (f : i ⟶ j) (X : C)
  证明: by
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rfl

Depends on / 依赖: Functor, Functor.map_comp, NatTrans, NatTrans.comp_app, comp_app, map_comp
-/
lemma eTruncGEπ_app_eTruncGE_map_app {i j : EInt} (f : i ⟶ j) (X : C) :
    (t.eTruncGEπ i).app X ≫ (t.eTruncGE.map f).app X = (t.eTruncGEπ j).app X := by
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `eTruncGE_obj_map_eTruncGEπ_app` / 引理 `eTruncGE_obj_map_eTruncGEπ_app`

English:
lemma eTruncGE_obj_map_eTruncGEπ_app
  given: (i : EInt) (X : C)
  proof: by
  induction i using WithBotTop.rec with simp [truncGE_map_truncGEπ_app]

中文:
引理 eTruncGE_obj_map_eTruncGEπ_app
  条件: (i : E整数) (X : C)
  证明: by
  induction i using WithBotTop.rec with simp [truncGE_map_truncGEπ_app]

Depends on / 依赖: WithBotTop, WithBotTop.rec
-/
lemma eTruncGE_obj_map_eTruncGEπ_app (i : EInt) (X : C) :
    (t.eTruncGE.obj i).map ((t.eTruncGEπ i).app X) =
    (t.eTruncGEπ i).app ((t.eTruncGE.obj i).obj X) := by
  induction i using WithBotTop.rec with simp [truncGE_map_truncGEπ_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `eTruncLT_obj_map_eTruncLTι_app_eTruncLT_map_app` / 引理 `eTruncLT_obj_map_eTruncLTι_app_eTruncLT_map_app`

English:
lemma eTruncLT_obj_map_eTruncLTι_app_eTruncLT_map_app
  proof: by
  dsimp [eTruncLTι]
  rw [show homOfLE le_top = f ≫ homOfLE le_top by rfl]
  induction j using WithBotTop.rec with simp [truncLT_map_truncLTι_app]

中文:
引理 eTruncLT_obj_map_eTruncLTι_app_eTruncLT_map_app
  证明: by
  dsimp [eTruncLTι]
  rw [show homOfLE le_top = f ≫ homOfLE le_top by rfl]
  induction j using WithBotTop.rec with simp [truncLT_map_truncLTι_app]

Depends on / 依赖: WithBotTop, WithBotTop.rec, homOfLE, le_top
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
/--
Definition of `eTriangleLTGE` / `eTriangleLTGE` 的定义

English:
definition eTriangleLTGE
  signature: : EInt ⥤ C ⥤ Triangle C where
  body: Triangle.functorMk (t.eTruncLTι i) (t.eTruncGEπ i) (t.eTruncGEδLT.app i)
  map f := Triangle.functorHomMk _ _ (t.eTruncLT.map f) (𝟙 _) (t.eTruncGE.map f)

中文:
定义 eTriangleLTGE
  签名: : E整数 ⥤ C ⥤ Triangle C where
  定义体: Triangle.functorMk (t.eTruncLTι i) (t.eTruncGEπ i) (t.eTruncGEδLT.app i)
  map f := Triangle.functorHomMk _ _ (t.eTruncLT.map f) (𝟙 _) (t.eTruncGE.map f)

Depends on / 依赖: LT.app, Triangle, Triangle.functorMk, functorMk, t.eTruncGE, t.eTruncLT
-/
noncomputable def eTriangleLTGE : EInt ⥤ C ⥤ Triangle C where
  obj i := Triangle.functorMk (t.eTruncLTι i) (t.eTruncGEπ i) (t.eTruncGEδLT.app i)
  map f := Triangle.functorHomMk _ _ (t.eTruncLT.map f) (𝟙 _) (t.eTruncGE.map f)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `eTriangleLTGE_distinguished` / 引理 `eTriangleLTGE_distinguished`

English:
lemma eTriangleLTGE_distinguished
  given: (i : EInt) (X : C)
  proof: by
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

中文:
引理 eTriangleLTGE_distinguished
  条件: (i : E整数) (X : C)
  证明: by
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

Depends on / 依赖: Functor, Functor.zero_obj, Triangle, Triangle.distinguished_iff_of_isZero, WithBotTop, WithBotTop.rec, infer_instance, t.triangleLTGE_distinguished, triangleLTGE_distinguished, zero_obj
-/
lemma eTriangleLTGE_distinguished (i : EInt) (X : C) :
    (t.eTriangleLTGE.obj i).obj X in distTriang _ := by
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

instance (X : C) (n : Int) [t.IsLE X n] (i : EInt) :
    t.IsLE ((t.eTruncLT.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => exact isLE_of_isZero _ (by simp) _
  | coe _ => dsimp; infer_instance
  | top => dsimp; infer_instance

instance (X : C) (n : Int) [t.IsGE X n] (i : EInt) :
    t.IsGE ((t.eTruncGE.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => dsimp; infer_instance
  | coe _ => dsimp; infer_instance
  | top => exact isGE_of_isZero _ (by simp) _

/--
lemma `isGE_eTruncGE_obj_obj` / 引理 `isGE_eTruncGE_obj_obj`

English:
lemma isGE_eTruncGE_obj_obj
  given: (n : Int) (i : EInt) (h : n <= i) (X : C)
  proof: by
  induction i using WithBotTop.rec with
  | bot => simp at h
  | coe i =>
    dsimp
    exact t.isGE_of_ge _ _ _ (by simpa using h)
  | top => exact t.isGE_of_isZero (Functor.zero_obj _) _

中文:
引理 isGE_eTruncGE_obj_obj
  条件: (n : 整数) (i : E整数) (h : n <= i) (X : C)
  证明: by
  induction i using WithBotTop.rec with
  | bot => simp at h
  | coe i =>
    dsimp
    exact t.isGE_of_ge _ _ _ (by simpa using h)
  | top => exact t.isGE_of_isZero (Functor.zero_obj _) _

Depends on / 依赖: Functor, Functor.zero_obj, WithBotTop, WithBotTop.rec, isGE_of_ge, isGE_of_isZero, t.isGE_of_ge, t.isGE_of_isZero, zero_obj
-/
lemma isGE_eTruncGE_obj_obj (n : Int) (i : EInt) (h : n <= i) (X : C) :
    t.IsGE ((t.eTruncGE.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => simp at h
  | coe i =>
    dsimp
    exact t.isGE_of_ge _ _ _ (by simpa using h)
  | top => exact t.isGE_of_isZero (Functor.zero_obj _) _

/--
lemma `isLE_eTruncLT_obj_obj` / 引理 `isLE_eTruncLT_obj_obj`

English:
lemma isLE_eTruncLT_obj_obj
  given: (n : Int) (i : EInt) (h : i <= (n + 1 :)) (X : C)
  proof: by
  induction i using WithBotTop.rec with
  | bot => exact t.isLE_of_isZero (by simp) _
  | coe i =>
    simp only [WithBotTop.coe_le_coe] at h
    dsimp
    exact t.isLE_of_le _ (i - 1) n (by lia)
  | top => simp at h

中文:
引理 isLE_eTruncLT_obj_obj
  条件: (n : 整数) (i : E整数) (h : i <= (n + 1 :)) (X : C)
  证明: by
  induction i using WithBotTop.rec with
  | bot => exact t.isLE_of_isZero (by simp) _
  | coe i =>
    simp only [WithBotTop.coe_le_coe] at h
    dsimp
    exact t.isLE_of_le _ (i - 1) n (by lia)
  | top => simp at h

Depends on / 依赖: WithBotTop, WithBotTop.coe_le_coe, WithBotTop.rec, coe_le_coe, isLE_of_isZero, isLE_of_le, t.isLE_of_isZero, t.isLE_of_le
-/
lemma isLE_eTruncLT_obj_obj (n : Int) (i : EInt) (h : i <= (n + 1 :)) (X : C) :
    t.IsLE (((t.eTruncLT.obj i)).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => exact t.isLE_of_isZero (by simp) _
  | coe i =>
    simp only [WithBotTop.coe_le_coe] at h
    dsimp
    exact t.isLE_of_le _ (i - 1) n (by lia)
  | top => simp at h

/--
lemma `isZero_eTruncLT_obj_obj` / 引理 `isZero_eTruncLT_obj_obj`

English:
lemma isZero_eTruncLT_obj_obj
  given: (X : C) (n : Int) [t.IsGE X n] (j : EInt) (hj : j <= n)
  proof: by
  induction j using WithBotTop.rec with
  | bot => simp
  | coe j =>
    have := t.isGE_of_ge X j n (by simpa using hj)
    exact t.isZero_truncLT_obj_of_isGE _ _
  | top => simp at hj

中文:
引理 isZero_eTruncLT_obj_obj
  条件: (X : C) (n : 整数) [t.是GE X n] (j : E整数) (hj : j <= n)
  证明: by
  induction j using WithBotTop.rec with
  | bot => simp
  | coe j =>
    have := t.isGE_of_ge X j n (by simpa using hj)
    exact t.isZero_truncLT_obj_of_isGE _ _
  | top => simp at hj

Depends on / 依赖: WithBotTop, WithBotTop.rec, isGE_of_ge, isZero_truncLT_obj_of_isGE, t.isGE_of_ge, t.isZero_truncLT_obj_of_isGE
-/
lemma isZero_eTruncLT_obj_obj (X : C) (n : Int) [t.IsGE X n] (j : EInt) (hj : j <= n) :
    IsZero ((t.eTruncLT.obj j).obj X) := by
  induction j using WithBotTop.rec with
  | bot => simp
  | coe j =>
    have := t.isGE_of_ge X j n (by simpa using hj)
    exact t.isZero_truncLT_obj_of_isGE _ _
  | top => simp at hj

/--
lemma `isZero_eTruncGE_obj_obj` / 引理 `isZero_eTruncGE_obj_obj`

English:
lemma isZero_eTruncGE_obj_obj
  given: (X : C) (n : Int) [t.IsLE X n] (j : EInt) (hj : n < j)
  proof: by
  induction j using WithBotTop.rec with
  | bot => simp at hj
  | coe j =>
    simp only [WithBotTop.coe_lt_coe] at hj
    have := t.isLE_of_le X n (j - 1) (by lia)
    exact t.isZero_truncGE_obj_of_isLE (j - 1) j (by lia) _
  | top => simp

中文:
引理 isZero_eTruncGE_obj_obj
  条件: (X : C) (n : 整数) [t.是LE X n] (j : E整数) (hj : n < j)
  证明: by
  induction j using WithBotTop.rec with
  | bot => simp at hj
  | coe j =>
    simp only [WithBotTop.coe_lt_coe] at hj
    have := t.isLE_of_le X n (j - 1) (by lia)
    exact t.isZero_truncGE_obj_of_isLE (j - 1) j (by lia) _
  | top => simp

Depends on / 依赖: WithBotTop, WithBotTop.coe_lt_coe, WithBotTop.rec, coe_lt_coe, isLE_of_le, isZero_truncGE_obj_of_isLE, t.isLE_of_le, t.isZero_truncGE_obj_of_isLE
-/
lemma isZero_eTruncGE_obj_obj (X : C) (n : Int) [t.IsLE X n] (j : EInt) (hj : n < j) :
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

/--
lemma `isIso_eTruncGE_obj_map_truncGEπ_app` / 引理 `isIso_eTruncGE_obj_map_truncGEπ_app`

English:
lemma isIso_eTruncGE_obj_map_truncGEπ_app
  given: (a b : EInt) (h : a <= b) (X : C)
  proof: by
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

中文:
引理 isIso_eTruncGE_obj_map_truncGEπ_app
  条件: (a b : E整数) (h : a <= b) (X : C)
  证明: by
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

Depends on / 依赖: IsZero, IsZero.eq_of_src, WithBotTop, WithBotTop.rec, eq_of_src, infer_instance, t.isIso_truncGE_map_truncGE
-/
lemma isIso_eTruncGE_obj_map_truncGEπ_app (a b : EInt) (h : a <= b) (X : C) :
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

/--
lemma `isIso_eTruncLT_obj_map_truncLTπ_app` / 引理 `isIso_eTruncLT_obj_map_truncLTπ_app`

English:
lemma isIso_eTruncLT_obj_map_truncLTπ_app
  given: (a b : EInt) (h : a <= b) (X : C)
  proof: by
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

中文:
引理 isIso_eTruncLT_obj_map_truncLTπ_app
  条件: (a b : E整数) (h : a <= b) (X : C)
  证明: by
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

Depends on / 依赖: IsZero, IsZero.eq_of_src, WithBotTop, WithBotTop.rec, eq_of_src, infer_instance, t.isIso_truncLT_map_truncLT
-/
lemma isIso_eTruncLT_obj_map_truncLTπ_app (a b : EInt) (h : a <= b) (X : C) :
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

instance (a : EInt) (X : C) : IsIso ((t.eTruncLT.obj a).map ((t.eTruncLTι a).app X)) :=
  isIso_eTruncLT_obj_map_truncLTπ_app t a a (by rfl) X

instance (a : EInt) (X : C) : IsIso ((t.eTruncLTι a).app ((t.eTruncLT.obj a).obj X)) := by
  rw [← eTruncLT_obj_map_eTruncLTι_app]
  infer_instance

instance (X : C) (n : Int) [t.IsGE X n] (i : EInt) :
    t.IsGE ((t.eTruncLT.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => exact isGE_of_isZero _ (by simp) _
  | coe _ => dsimp; infer_instance
  | top => dsimp; infer_instance

instance (X : C) (n : Int) [t.IsLE X n] (i : EInt) :
    t.IsLE ((t.eTruncGE.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => dsimp; infer_instance
  | coe _ => dsimp; infer_instance
  | top => exact isLE_of_isZero _ (by simp) _

/-- The natural transformation `t.eTruncGE.obj b ⟶ t.eTruncGE.obj a ⋙ t.eTruncGE.obj b`
for all `a` and `b` in `EInt`. -/
@[simps!]
/--
Definition of `eTruncGEToGEGE` / `eTruncGEToGEGE` 的定义

English:
definition eTruncGEToGEGE
  signature: (a b : EInt)
  body: (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (t.eTruncGEπ a) _

中文:
定义 eTruncGEToGEGE
  签名: (a b : E整数)
  定义体: (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (t.eTruncGEπ a) _

Depends on / 依赖: Functor, Functor.leftUnitor, Functor.whiskerRight, leftUnitor, t.eTruncGE, whiskerRight
-/
noncomputable def eTruncGEToGEGE (a b : EInt) :
    t.eTruncGE.obj b ⟶ t.eTruncGE.obj a ⋙ t.eTruncGE.obj b :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (t.eTruncGEπ a) _

/--
lemma `isIso_eTruncGEIsoGEGE` / 引理 `isIso_eTruncGEIsoGEGE`

English:
lemma isIso_eTruncGEIsoGEGE
  given: (a b : EInt) (hab : a <= b)
  proof: by
  rw [NatTrans.isIso_iff_isIso_app]
  intro
  simp only [eTruncGEToGEGE_app]
  exact t.isIso_eTruncGE_obj_map_truncGEπ_app _ _ hab _

中文:
引理 isIso_eTruncGEIsoGEGE
  条件: (a b : E整数) (hab : a <= b)
  证明: by
  rw [NatTrans.isIso_iff_isIso_app]
  intro
  simp only [eTruncGEToGEGE_app]
  exact t.isIso_eTruncGE_obj_map_truncGEπ_app _ _ hab _

Depends on / 依赖: NatTrans, NatTrans.isIso_iff_isIso_app, eTruncGEToGEGE_app, isIso_iff_isIso_app, t.isIso_eTruncGE_obj_map_truncGE
-/
lemma isIso_eTruncGEIsoGEGE (a b : EInt) (hab : a <= b) :
    IsIso (t.eTruncGEToGEGE a b) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro
  simp only [eTruncGEToGEGE_app]
  exact t.isIso_eTruncGE_obj_map_truncGEπ_app _ _ hab _

section

variable (a b : EInt) (hab : a <= b)

/-- The natural isomorphism `t.eTruncGE.obj b ≅ t.eTruncGE.obj a ⋙ t.eTruncGE.obj b`
when `a` and `b` in `EInt` satisfy `a ≤ b`. -/
@[simps! hom]
/--
Definition of `eTruncGEIsoGEGE` / `eTruncGEIsoGEGE` 的定义

English:
definition eTruncGEIsoGEGE
  signature: :
  body: haveI := t.isIso_eTruncGEIsoGEGE a b hab
  asIso (t.eTruncGEToGEGE a b)

@[reassoc (attr := simp)]

中文:
定义 eTruncGEIsoGEGE
  签名: :
  定义体: haveI := t.isIso_eTruncGEIsoGEGE a b hab
  asIso (t.eTruncGEToGEGE a b)

@[reassoc (attr := simp)]

Depends on / 依赖: eTruncGEToGEGE, isIso_eTruncGEIsoGEGE, t.eTruncGEToGEGE, t.isIso_eTruncGEIsoGEGE
-/
noncomputable def eTruncGEIsoGEGE :
    t.eTruncGE.obj b ≅ t.eTruncGE.obj a ⋙ t.eTruncGE.obj b :=
  haveI := t.isIso_eTruncGEIsoGEGE a b hab
  asIso (t.eTruncGEToGEGE a b)

@[reassoc (attr := simp)]
/--
lemma `eTruncGEIsoGEGE_hom_inv_id_app` / 引理 `eTruncGEIsoGEGE_hom_inv_id_app`

English:
lemma eTruncGEIsoGEGE_hom_inv_id_app
  given: (X : C)
  proof: by
  simpa using! (t.eTruncGEIsoGEGE a b hab).hom_inv_id_app X

@[reassoc (attr := simp)]

中文:
引理 eTruncGEIsoGEGE_hom_inv_id_app
  条件: (X : C)
  证明: by
  simpa using! (t.eTruncGEIsoGEGE a b hab).hom_inv_id_app X

@[reassoc (attr := simp)]

Depends on / 依赖: eTruncGEIsoGEGE, hom_inv_id_app, t.eTruncGEIsoGEGE
-/
lemma eTruncGEIsoGEGE_hom_inv_id_app (X : C) :
    (t.eTruncGE.obj b).map ((t.eTruncGEπ a).app X) ≫ (t.eTruncGEIsoGEGE a b hab).inv.app X =
      𝟙 _ := by
  simpa using! (t.eTruncGEIsoGEGE a b hab).hom_inv_id_app X

@[reassoc (attr := simp)]
/--
lemma `eTruncGEIsoGEGE_inv_hom_id_app` / 引理 `eTruncGEIsoGEGE_inv_hom_id_app`

English:
lemma eTruncGEIsoGEGE_inv_hom_id_app
  given: (X : C)
  proof: by
  simpa using! (t.eTruncGEIsoGEGE a b hab).inv_hom_id_app X

中文:
引理 eTruncGEIsoGEGE_inv_hom_id_app
  条件: (X : C)
  证明: by
  simpa using! (t.eTruncGEIsoGEGE a b hab).inv_hom_id_app X

Depends on / 依赖: eTruncGEIsoGEGE, inv_hom_id_app, t.eTruncGEIsoGEGE
-/
lemma eTruncGEIsoGEGE_inv_hom_id_app (X : C) :
    (t.eTruncGEIsoGEGE a b hab).inv.app X ≫ (t.eTruncGE.obj b).map ((t.eTruncGEπ a).app X) =
      𝟙 _ := by
  simpa using! (t.eTruncGEIsoGEGE a b hab).inv_hom_id_app X

end

/-- The natural transformation `t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ⟶ t.eTruncLT.obj b`
for all `a` and `b` in `EInt`. -/
@[simps!]
/--
Definition of `eTruncLTLTToLT` / `eTruncLTLTToLT` 的定义

English:
definition eTruncLTLTToLT
  signature: (a b : EInt)
  body: Functor.whiskerRight (t.eTruncLTι a) _ ≫ (Functor.leftUnitor _).hom

中文:
定义 eTruncLTLTToLT
  签名: (a b : E整数)
  定义体: Functor.whiskerRight (t.eTruncLTι a) _ ≫ (Functor.leftUnitor _).hom

Depends on / 依赖: Functor, Functor.leftUnitor, Functor.whiskerRight, leftUnitor, t.eTruncLT, whiskerRight
-/
noncomputable def eTruncLTLTToLT (a b : EInt) :
    t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ⟶ t.eTruncLT.obj b :=
  Functor.whiskerRight (t.eTruncLTι a) _ ≫ (Functor.leftUnitor _).hom

/--
lemma `isIso_eTruncLTLTIsoLT` / 引理 `isIso_eTruncLTLTIsoLT`

English:
lemma isIso_eTruncLTLTIsoLT
  given: (a b : EInt) (hab : b <= a)
  proof: by
  rw [NatTrans.isIso_iff_isIso_app]
  intro
  simp only [eTruncLTLTToLT_app]
  exact t.isIso_eTruncLT_obj_map_truncLTπ_app _ _ hab _

中文:
引理 isIso_eTruncLTLTIsoLT
  条件: (a b : E整数) (hab : b <= a)
  证明: by
  rw [NatTrans.isIso_iff_isIso_app]
  intro
  simp only [eTruncLTLTToLT_app]
  exact t.isIso_eTruncLT_obj_map_truncLTπ_app _ _ hab _

Depends on / 依赖: NatTrans, NatTrans.isIso_iff_isIso_app, eTruncLTLTToLT_app, isIso_iff_isIso_app, t.isIso_eTruncLT_obj_map_truncLT
-/
lemma isIso_eTruncLTLTIsoLT (a b : EInt) (hab : b <= a) :
    IsIso (t.eTruncLTLTToLT a b) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro
  simp only [eTruncLTLTToLT_app]
  exact t.isIso_eTruncLT_obj_map_truncLTπ_app _ _ hab _

section

variable (a b : EInt) (hab : b <= a)

/-- The natural isomorphism `t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ⟶ t.eTruncLT.obj b`
when `a` and `b` in `EInt` satisfy `b ≤ a`. -/
@[simps! hom]
/--
Definition of `eTruncLTLTIsoLT` / `eTruncLTLTIsoLT` 的定义

English:
definition eTruncLTLTIsoLT
  signature: :
  body: haveI := t.isIso_eTruncLTLTIsoLT a b hab
  asIso (t.eTruncLTLTToLT a b)

中文:
定义 eTruncLTLTIsoLT
  签名: :
  定义体: haveI := t.isIso_eTruncLTLTIsoLT a b hab
  asIso (t.eTruncLTLTToLT a b)

Depends on / 依赖: eTruncLTLTToLT, isIso_eTruncLTLTIsoLT, t.eTruncLTLTToLT, t.isIso_eTruncLTLTIsoLT
-/
noncomputable def eTruncLTLTIsoLT :
    t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ≅ t.eTruncLT.obj b :=
  haveI := t.isIso_eTruncLTLTIsoLT a b hab
  asIso (t.eTruncLTLTToLT a b)

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `eTruncLTLTIsoLT_hom_inv_id_app` / 引理 `eTruncLTLTIsoLT_hom_inv_id_app`

English:
lemma eTruncLTLTIsoLT_hom_inv_id_app
  given: (X : C)
  proof: by
  simpa using (t.eTruncLTLTIsoLT a b hab).hom_inv_id_app X

@[reassoc (attr := simp)]

中文:
引理 eTruncLTLTIsoLT_hom_inv_id_app
  条件: (X : C)
  证明: by
  simpa using (t.eTruncLTLTIsoLT a b hab).hom_inv_id_app X

@[reassoc (attr := simp)]

Depends on / 依赖: eTruncLTLTIsoLT, hom_inv_id_app, t.eTruncLTLTIsoLT
-/
lemma eTruncLTLTIsoLT_hom_inv_id_app (X : C) :
    (t.eTruncLT.obj b).map ((t.eTruncLTι a).app X) ≫
      (t.eTruncLTLTIsoLT a b hab).inv.app X = 𝟙 _ := by
  simpa using (t.eTruncLTLTIsoLT a b hab).hom_inv_id_app X

@[reassoc (attr := simp)]
/--
lemma `eTruncLTLTIsoLT_inv_hom_id_app` / 引理 `eTruncLTLTIsoLT_inv_hom_id_app`

English:
lemma eTruncLTLTIsoLT_inv_hom_id_app
  given: (X : C)
  proof: by
  simpa using (t.eTruncLTLTIsoLT a b hab).inv_hom_id_app X

@[reassoc (attr := simp)]

中文:
引理 eTruncLTLTIsoLT_inv_hom_id_app
  条件: (X : C)
  证明: by
  simpa using (t.eTruncLTLTIsoLT a b hab).inv_hom_id_app X

@[reassoc (attr := simp)]

Depends on / 依赖: eTruncLTLTIsoLT, inv_hom_id_app, t.eTruncLTLTIsoLT
-/
lemma eTruncLTLTIsoLT_inv_hom_id_app (X : C) :
    (t.eTruncLTLTIsoLT a b hab).inv.app X ≫
    (t.eTruncLT.obj b).map ((t.eTruncLTι a).app X) = 𝟙 _ := by
  simpa using (t.eTruncLTLTIsoLT a b hab).inv_hom_id_app X

@[reassoc (attr := simp)]
/--
lemma `eTruncLTLTIsoLT_inv_hom_id_app_eTruncLT_obj` / 引理 `eTruncLTLTIsoLT_inv_hom_id_app_eTruncLT_obj`

English:
lemma eTruncLTLTIsoLT_inv_hom_id_app_eTruncLT_obj
  given: (X : C)
  proof: by
  simp [eTruncLT_obj_map_eTruncLTι_app]

中文:
引理 eTruncLTLTIsoLT_inv_hom_id_app_eTruncLT_obj
  条件: (X : C)
  证明: by
  simp [eTruncLT_obj_map_eTruncLTι_app]
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
/--
Definition of `eTruncLTGELTSelfToLTGE` / `eTruncLTGELTSelfToLTGE` 的定义

English:
definition eTruncLTGELTSelfToLTGE
  signature: :
  body: Functor.whiskerRight (t.eTruncLTι b) _ ≫ (Functor.leftUnitor _).hom

中文:
定义 eTruncLTGELTSelfToLTGE
  签名: :
  定义体: Functor.whiskerRight (t.eTruncLTι b) _ ≫ (Functor.leftUnitor _).hom

Depends on / 依赖: Functor, Functor.leftUnitor, Functor.whiskerRight, leftUnitor, t.eTruncLT, whiskerRight
-/
noncomputable def eTruncLTGELTSelfToLTGE :
    t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b ⟶
      t.eTruncGE.obj a ⋙ t.eTruncLT.obj b :=
  Functor.whiskerRight (t.eTruncLTι b) _ ≫ (Functor.leftUnitor _).hom

/-- The natural transformation from
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b` to
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a`. (This is an isomorphism.) -/
@[simps!]
/--
Definition of `eTruncLTGELTSelfToGELT` / `eTruncLTGELTSelfToGELT` 的定义

English:
definition eTruncLTGELTSelfToGELT
  signature: :
  body: (Functor.associator _ _ _).inv ≫ Functor.whiskerLeft _ (t.eTruncLTι b) ≫
    (Functor.rightUnitor _).hom

中文:
定义 eTruncLTGELTSelfToGELT
  签名: :
  定义体: (Functor.associator _ _ _).inv ≫ Functor.whiskerLeft _ (t.eTruncLTι b) ≫
    (Functor.rightUnitor _).hom

Depends on / 依赖: Functor, Functor.associator, Functor.rightUnitor, Functor.whiskerLeft, associator, rightUnitor, t.eTruncLT, whiskerLeft
-/
noncomputable def eTruncLTGELTSelfToGELT :
    t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b ⟶
      t.eTruncLT.obj b ⋙ t.eTruncGE.obj a :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerLeft _ (t.eTruncLTι b) ≫
    (Functor.rightUnitor _).hom

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (t.eTruncLTGELTSelfToLTGE a b)
  body: by
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

中文:
实例 :
  签名: 是同构 (t.eTruncLTGELTSelfToLTGE a b)
  定义体: by
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

Depends on / 依赖: Functor, Functor.comp_obj, NatTrans, NatTrans.isIso_iff_isIso_app, WithBotTop, WithBotTop.rec, comp_obj, eTruncGE_obj_coe, eTruncGE_obj_top, eTruncLTGELTSelfToLTGE_app, eTruncLT_obj_coe, infer_instance, isIsoZero_iff_source_target_isZero, isIso_iff_isIso_app, t.truncLT, truncLT
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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (t.eTruncLTGELTSelfToGELT a b)
  body: by
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

中文:
实例 :
  签名: 是同构 (t.eTruncLTGELTSelfToGELT a b)
  定义体: by
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

Depends on / 依赖: Functor, Functor.zero_obj, NatTrans, NatTrans.isIso_iff_isIso_app, WithBotTop, WithBotTop.rec, eTruncGE, eTruncGE_obj_coe, eTruncLT, eTruncLTGELTSelfToGELT_app, eTruncLT_obj_coe, infer_instance, isIsoZero_iff_source_target_isZero, isIso_iff_isIso_app, map_isZero, t.eTruncGE.obj, t.eTruncLT, t.eTruncLT.obj, zero_obj
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

/--
Definition of `eTruncLTGEIsoGELT` / `eTruncLTGEIsoGELT` 的定义

English:
definition eTruncLTGEIsoGELT
  signature: (a b : EInt)
  body: (asIso (t.eTruncLTGELTSelfToLTGE a b)).symm ≪≫ asIso (t.eTruncLTGELTSelfToGELT a b)

@[reassoc (attr := simp)]

中文:
定义 eTruncLTGEIsoGELT
  签名: (a b : E整数)
  定义体: (asIso (t.eTruncLTGELTSelfToLTGE a b)).symm ≪≫ asIso (t.eTruncLTGELTSelfToGELT a b)

@[reassoc (attr := simp)]

Depends on / 依赖: eTruncLTGELTSelfToGELT, eTruncLTGELTSelfToLTGE, t.eTruncLTGELTSelfToGELT, t.eTruncLTGELTSelfToLTGE
-/
noncomputable def eTruncLTGEIsoGELT (a b : EInt) :
    t.eTruncGE.obj a ⋙ t.eTruncLT.obj b ≅ t.eTruncLT.obj b ⋙ t.eTruncGE.obj a :=
  (asIso (t.eTruncLTGELTSelfToLTGE a b)).symm ≪≫ asIso (t.eTruncLTGELTSelfToGELT a b)

@[reassoc (attr := simp)]
/--
lemma `eTruncLTGEIsoGELT_hom_naturality` / 引理 `eTruncLTGEIsoGELT_hom_naturality`

English:
lemma eTruncLTGEIsoGELT_hom_naturality
  given: (a b : EInt) {X Y : C} (f : X ⟶ Y)
  proof: (t.eTruncLTGEIsoGELT a b).hom.naturality f

中文:
引理 eTruncLTGEIsoGELT_hom_naturality
  条件: (a b : E整数) {X Y : C} (f : X ⟶ Y)
  证明: (t.eTruncLTGEIsoGELT a b).hom.naturality f

Depends on / 依赖: eTruncLTGEIsoGELT, hom.naturality, naturality, t.eTruncLTGEIsoGELT
-/
lemma eTruncLTGEIsoGELT_hom_naturality (a b : EInt) {X Y : C} (f : X ⟶ Y) :
    (t.eTruncLT.obj b).map ((t.eTruncGE.obj a).map f) ≫ (t.eTruncLTGEIsoGELT a b).hom.app Y =
      (t.eTruncLTGEIsoGELT a b).hom.app X ≫ (t.eTruncGE.obj a).map ((t.eTruncLT.obj b).map f) :=
  (t.eTruncLTGEIsoGELT a b).hom.naturality f

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `eTruncLTGEIsoGELT_hom_app_fac` / 引理 `eTruncLTGEIsoGELT_hom_app_fac`

English:
lemma eTruncLTGEIsoGELT_hom_app_fac
  given: (a b : EInt) (X : C)
  proof: by
  simp [eTruncLTGEIsoGELT]

@[reassoc (attr := simp)]

中文:
引理 eTruncLTGEIsoGELT_hom_app_fac
  条件: (a b : E整数) (X : C)
  证明: by
  simp [eTruncLTGEIsoGELT]

@[reassoc (attr := simp)]

Depends on / 依赖: eTruncLTGEIsoGELT
-/
lemma eTruncLTGEIsoGELT_hom_app_fac (a b : EInt) (X : C) :
    (t.eTruncLT.obj b).map ((t.eTruncGE.obj a).map ((t.eTruncLTι b).app X)) ≫
      (t.eTruncLTGEIsoGELT a b).hom.app X =
    (t.eTruncLTι b).app ((t.eTruncGE.obj a).obj ((t.eTruncLT.obj b).obj X)) := by
  simp [eTruncLTGEIsoGELT]

@[reassoc (attr := simp)]
/--
lemma `eTruncLTGEIsoGELT_hom_app_fac'` / 引理 `eTruncLTGEIsoGELT_hom_app_fac'`

English:
lemma eTruncLTGEIsoGELT_hom_app_fac'
  given: (a b : EInt) (X : C)
  proof: by
  simp [eTruncLTGEIsoGELT]

中文:
引理 eTruncLTGEIsoGELT_hom_app_fac'
  条件: (a b : E整数) (X : C)
  证明: by
  simp [eTruncLTGEIsoGELT]

Depends on / 依赖: eTruncLTGEIsoGELT
-/
lemma eTruncLTGEIsoGELT_hom_app_fac' (a b : EInt) (X : C) :
    (t.eTruncLTGEIsoGELT a b).hom.app X ≫ (t.eTruncGE.obj a).map ((t.eTruncLTι b).app X) =
      (t.eTruncLTι b).app ((t.eTruncGE.obj a).obj X) := by
  simp [eTruncLTGEIsoGELT]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open ComposableArrows in
@[reassoc]
/--
lemma `eTruncLTGEIsoGELT_naturality_app` / 引理 `eTruncLTGEIsoGELT_naturality_app`

English:
lemma eTruncLTGEIsoGELT_naturality_app
  statement: (a b : EInt) (hab : a <= b)
  proof: by
  dsimp
  rw [← cancel_epi ((t.eTruncLTGELTSelfToLTGE a b).app X)]; rw [eTruncLTGELTSelfToLTGE_app]; rw [eTruncLTGEIsoGELT_hom_app_fac_assoc]; rw [NatTrans.naturality_assoc]; rw [← Functor.map_comp_assoc]; rw [NatTrans.naturality]; rw [Functor.map_comp_assoc]; rw [← t.eTruncLT_map_app_eTruncLTι_app (φ.app 1) X]
  simp [↓Functor.map_comp, t.eTruncLTGEIsoGELT_hom_app_fac]

中文:
引理 eTruncLTGEIsoGELT_naturality_app
  结论: (a b : E整数) (hab : a <= b)
  证明: by
  dsimp
  rw [← cancel_epi ((t.eTruncLTGELTSelfToLTGE a b).app X)]; rw [eTruncLTGELTSelfToLTGE_app]; rw [eTruncLTGEIsoGELT_hom_app_fac_assoc]; rw [NatTrans.naturality_assoc]; rw [← Functor.map_comp_assoc]; rw [NatTrans.naturality]; rw [Functor.map_comp_assoc]; rw [← t.eTruncLT_map_app_eTruncLTι_app (φ.app 1) X]
  simp [↓Functor.map_comp, t.eTruncLTGEIsoGELT_hom_app_fac]

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_comp_assoc, NatTrans, NatTrans.naturality, NatTrans.naturality_assoc, cancel_epi, eTruncLTGEIsoGELT_hom_app_fac, eTruncLTGEIsoGELT_hom_app_fac_assoc, eTruncLTGELTSelfToLTGE, eTruncLTGELTSelfToLTGE_app, map_comp, map_comp_assoc, naturality, naturality_assoc, t.eTruncLTGEIsoGELT_hom_app_fac, t.eTruncLTGELTSelfToLTGE, t.eTruncLT_map_app_eTruncLT
-/
lemma eTruncLTGEIsoGELT_naturality_app (a b : EInt) (hab : a <= b)
    (a' b' : EInt) (hab' : a' <= b') (φ : mk₁ (homOfLE hab) ⟶ mk₁ (homOfLE hab')) (X : C) :
      (t.eTruncLT.map (φ.app 1)).app ((t.eTruncGE.obj a).obj X) ≫
        (t.eTruncLT.obj b').map ((t.eTruncGE.map (φ.app 0)).app X) ≫
        (t.eTruncLTGEIsoGELT a' b').hom.app X =
    (t.eTruncLTGEIsoGELT a b).hom.app X ≫ (t.eTruncGE.map (φ.app 0)).app _ ≫
      (t.eTruncGE.obj a').map ((t.eTruncLT.map (φ.app 1)).app X) := by
  dsimp
  rw [← cancel_epi ((t.eTruncLTGELTSelfToLTGE a b).app X)]; rw [eTruncLTGELTSelfToLTGE_app]; rw [eTruncLTGEIsoGELT_hom_app_fac_assoc]; rw [NatTrans.naturality_assoc]; rw [← Functor.map_comp_assoc]; rw [NatTrans.naturality]; rw [Functor.map_comp_assoc]; rw [← t.eTruncLT_map_app_eTruncLTι_app (φ.app 1) X]
  simp [↓Functor.map_comp, t.eTruncLTGEIsoGELT_hom_app_fac]

end

end TStructure

end Triangulated

end CategoryTheory
