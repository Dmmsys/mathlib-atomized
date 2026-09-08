/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Binary biproducts

We introduce the notion of binary biproducts.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

For results about biproducts in preadditive categories see
`CategoryTheory.Preadditive.Biproducts`.

In a category with zero morphisms, we model the (binary) biproduct of `P Q : C`
using a `BinaryBicone`, which has a cone point `X`,
and morphisms `fst : X ⟶ P`, `snd : X ⟶ Q`, `inl : P ⟶ X` and `inr : X ⟶ Q`,
such that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`.
Such a `BinaryBicone` is a biproduct if the cone is a limit cone, and the cocone is a colimit
cocone.

-/

@[expose] public section

noncomputable section

universe w w' v u

open CategoryTheory Functor Opposite

namespace CategoryTheory.Limits

variable {J : Type w}
universe uC' uC uD' uD
variable {C : Type uC} [Category.{uC'} C] [HasZeroMorphisms C]
variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

/-- A binary bicone for a pair of objects `P Q : C` consists of the cone point `X`,
maps from `X` to both `P` and `Q`, and maps from both `P` and `Q` to `X`,
so that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q` -/
/-
**CategoryTheory.Limits.BinaryBicone** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：BinaryBicone (P Q : C) where pt : C fst : pt ⟶ P snd : pt ⟶ Q inl : P ⟶ pt
 inr : Q ⟶ pt inl_fst : inl ≫ fst = 𝟙 P
参数：P Q : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary bicone for a pair of objects `P Q : C` consists of the cone point `X`,
maps from `X` to both `P` and `Q`, and maps from both `P` and `Q` to `X`,
so that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 
Q`
-/
structure BinaryBicone (P Q : C) where
  pt : C
  fst : pt ⟶ P
  snd : pt ⟶ Q
  inl : P ⟶ pt
  inr : Q ⟶ pt
  inl_fst : inl ≫ fst = 𝟙 P := by aesop
  inl_snd : inl ≫ snd = 0 := by aesop
  inr_fst : inr ≫ fst = 0 := by aesop
  inr_snd : inr ≫ snd = 𝟙 Q := by aesop

attribute [inherit_doc BinaryBicone] BinaryBicone.pt BinaryBicone.fst BinaryBicone.snd
  BinaryBicone.inl BinaryBicone.inr BinaryBicone.inl_fst BinaryBicone.inl_snd
  BinaryBicone.inr_fst BinaryBicone.inr_snd

attribute [reassoc (attr := simp)]
  BinaryBicone.inl_fst BinaryBicone.inl_snd BinaryBicone.inr_fst BinaryBicone.inr_snd

/-- A binary bicone morphism between two binary bicones for the same diagram is a morphism of the
binary bicone points which commutes with the cone and cocone legs. -/
/-
**CategoryTheory.Limits.BinaryBiconeMorphism** 是 Mathlib 中的一个结构，位于命名空间 `Category
Theory.Limits`。
形式化陈述：BinaryBiconeMorphism {P Q : C} (A B : BinaryBicone P Q) where /-- A morphi
sm between the two vertex objects of the bicones -/ hom : A.pt ⟶ B.pt /-- The tr
iangle consisting of the two natural transformations and `hom` commutes -/ wfst 
: hom ≫ B.fst = A.fst
参数：A B : BinaryBicone P Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary bicone morphism between two binary bicones for the same diagram is a mo
rphism of the
binary bicone points which commutes with the cone and cocone legs.
-/
structure BinaryBiconeMorphism {P Q : C} (A B : BinaryBicone P Q) where
  /-- A morphism between the two vertex objects of the bicones -/
  hom : A.pt ⟶ B.pt
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wfst : hom ≫ B.fst = A.fst := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wsnd : hom ≫ B.snd = A.snd := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  winl : A.inl ≫ hom = B.inl := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  winr : A.inr ≫ hom = B.inr := by cat_disch

attribute [reassoc (attr := simp)] BinaryBiconeMorphism.wfst BinaryBiconeMorphism.wsnd
attribute [reassoc (attr := simp)] BinaryBiconeMorphism.winl BinaryBiconeMorphism.winr

/-- The category of binary bicones on a given diagram. -/
@[simps]
/-
**CategoryTheory.Limits.BinaryBicone.category** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {P Q : C} → CategoryTheor
y.Category.{uC', max uC uC'} (CategoryTheory.Limits.BinaryBicone P Q)
参数：CategoryTheory.Limits.BinaryBicone P Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of binary bicones on a given diagram.
-/
instance BinaryBicone.category {P Q : C} : Category (BinaryBicone P Q) where
  Hom A B := BinaryBiconeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

/-- We do not want `simps` automatically generate the lemma for simplifying the `Hom` field of
-- a category. So we need to write the `ext` lemma in terms of the categorical morphism, rather than
the underlying structure. -/
@[ext]
/-
**CategoryTheory.Limits.BinaryBiconeMorphism.ext** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.BinaryBiconeMorphism`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {P Q : C} {c c' : CategoryTheory.Limits
.BinaryBicone P Q} (f g : c ⟶ c'), f.hom = g.hom → f = g
参数：f g : c ⟶ c'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
We do not want `simps` automatically generate the lemma for simplifying the `Hom
` field of
-- a category. So we need to write the `ext` lemma in terms of the categorical m
orphism, rather than
the underlying structure.
-/
theorem BinaryBiconeMorphism.ext {P Q : C} {c c' : BinaryBicone P Q}
    (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

namespace BinaryBicones

/-- To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps. -/
@[aesop apply safe (rule_sets := [CategoryTheory]), simps]
/-
**CategoryTheory.Limits.BinaryBicones.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.BinaryBicones`。
形式化陈述：ext {P Q : C} {c c' : BinaryBicone P Q} (φ : c.pt ≅ c'.pt) (winl : c.inl ≫
 φ.hom = c'.inl
参数：φ : c.pt ≅ c'.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps.
-/
def ext {P Q : C} {c c' : BinaryBicone P Q} (φ : c.pt ≅ c'.pt)
    (winl : c.inl ≫ φ.hom = c'.inl := by cat_disch)
    (winr : c.inr ≫ φ.hom = c'.inr := by cat_disch)
    (wfst : φ.hom ≫ c'.fst = c.fst := by cat_disch)
    (wsnd : φ.hom ≫ c'.snd = c.snd := by cat_disch) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      wfst := φ.inv_comp_eq.mpr wfst.symm
      wsnd := φ.inv_comp_eq.mpr wsnd.symm
      winl := φ.comp_inv_eq.mpr winl.symm
      winr := φ.comp_inv_eq.mpr winr.symm }

variable (P Q : C) (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]

/-- A functor `F : C ⥤ D` sends binary bicones for `P` and `Q`
to binary bicones for `G.obj P` and `G.obj Q` functorially. -/
@[simps]
/-
**CategoryTheory.Limits.BinaryBicones.functoriality** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.BinaryBicones`。
形式化陈述：functoriality : BinaryBicone P Q ⥤ BinaryBicone (F.obj P) (F.obj Q) where 
obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` sends binary bicones for `P` and `Q`
to binary bicones for `G.obj P` and `G.obj Q` functorially.
-/
def functoriality : BinaryBicone P Q ⥤ BinaryBicone (F.obj P) (F.obj Q) where
  obj A :=
    { pt := F.obj A.pt
      fst := F.map A.fst
      snd := F.map A.snd
      inl := F.map A.inl
      inr := F.map A.inr
      inl_fst := by rw [← F.map_comp, A.inl_fst, F.map_id]
      inl_snd := by rw [← F.map_comp, A.inl_snd, F.map_zero]
      inr_fst := by rw [← F.map_comp, A.inr_fst, F.map_zero]
      inr_snd := by rw [← F.map_comp, A.inr_snd, F.map_id] }
  map f :=
    { hom := F.map f.hom
      wfst := by simp [-BinaryBiconeMorphism.wfst, ← f.wfst]
      wsnd := by simp [-BinaryBiconeMorphism.wsnd, ← f.wsnd]
      winl := by simp [-BinaryBiconeMorphism.winl, ← f.winl]
      winr := by simp [-BinaryBiconeMorphism.winr, ← f.winr] }

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.BinaryBicones.functoriality_full** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Limits.BinaryBicones`。
形式化陈述：functoriality_full [F.Full] [F.Faithful] : (functoriality P Q F).Full wher
e map_surjective t
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicones.functoriality_obj_fst`：∀ {C : Type u
C} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {D : Type uD} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.BinaryBiconeMorphism.wfst`：∀ {C : Type uC} [inst :
 CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {P Q : C} {A B : Category…
· 使用定理 `CategoryTheory.Limits.BinaryBicones.functoriality_obj_snd`：∀ {C : Type u
C} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {D : Type uD} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.BinaryBiconeMorphism.wsnd`：∀ {C : Type uC} [inst :
 CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {P Q : C} {A B : Category…
· 使用定理 `CategoryTheory.Limits.BinaryBicones.functoriality_obj_inl`：∀ {C : Type u
C} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {D : Type uD} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.BinaryBiconeMorphism.winl`：∀ {C : Type uC} [inst :
 CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {P Q : C} {A B : Category…
· 使用定理 `CategoryTheory.Limits.BinaryBicones.functoriality_obj_inr`：∀ {C : Type u
C} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {D : Type uD} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.BinaryBiconeMorphism.winr`：∀ {C : Type uC} [inst :
 CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {P Q : C} {A B : Category…
· 使用定理 `CategoryTheory.Limits.BinaryBiconeMorphism.ext`：∀ {C : Type uC} [inst : 
CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {P Q : C} {c c' : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.BinaryBicones.functoriality_map_hom`：∀ {C : Type u
C} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {D : Type uD} [inst_2 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance functoriality_full [F.Full] [F.Faithful] : (functoriality P Q F).Full where
  map_surjective t :=
   ⟨{ hom := F.preimage t.hom
      winl := F.map_injective (by simpa using! t.winl)
      winr := F.map_injective (by simpa using! t.winr)
      wfst := F.map_injective (by simpa using! t.wfst)
      wsnd := F.map_injective (by simpa using! t.wsnd) }, by cat_disch⟩
/-
**CategoryTheory.Limits.BinaryBicones.functoriality_faithful** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.Limits.BinaryBicones`。
形式化陈述：functoriality_faithful [F.Faithful] : (functoriality P Q F).Faithful where
 map_injective {_X} {_Y} f g h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryBiconeMorphism.ext`：∀ {C : Type uC} [inst : 
CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {P Q : C} {c c' : Categor…
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
instance functoriality_faithful [F.Faithful] : (functoriality P Q F).Faithful where
  map_injective {_X} {_Y} f g h :=
    BinaryBiconeMorphism.ext f g <| F.map_injective <| congr_arg BinaryBiconeMorphism.hom h

end BinaryBicones

namespace BinaryBicone

variable {P P' Q Q' : C}

/-- Extract the cone from a binary bicone. -/
/-
**CategoryTheory.Limits.BinaryBicone.toCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.BinaryBicone`。
形式化陈述：toCone (c : BinaryBicone P Q) : Cone (pair P Q)
参数：c : BinaryBicone P Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the cone from a binary bicone.
-/
def toCone (c : BinaryBicone P Q) : Cone (pair P Q) :=
  BinaryFan.mk c.fst c.snd

@[simp]
/-
**CategoryTheory.Limits.BinaryBicone.toCone_pt** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.BinaryBicone`。
形式化陈述：toCone_pt (c : BinaryBicone P Q) : c.toCone.pt = c.pt
参数：c : BinaryBicone P Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCone_pt (c : BinaryBicone P Q) : c.toCone.pt = c.pt := rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryBicone.toCone_** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.BinaryBicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCone_π_app_left (c : BinaryBicone P Q) : c.toCone.π.app ⟨WalkingPair.left⟩ = c.fst :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryBicone.toCone_** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.BinaryBicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCone_π_app_right (c : BinaryBicone P Q) : c.toCone.π.app ⟨WalkingPair.right⟩ = c.snd :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryBicone.binary_fan_fst_toCone** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：binary_fan_fst_toCone (c : BinaryBicone P Q) : BinaryFan.fst c.toCone = c.
fst
参数：c : BinaryBicone P Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem binary_fan_fst_toCone (c : BinaryBicone P Q) : BinaryFan.fst c.toCone = c.fst := rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryBicone.binary_fan_snd_toCone** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：binary_fan_snd_toCone (c : BinaryBicone P Q) : BinaryFan.snd c.toCone = c.
snd
参数：c : BinaryBicone P Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem binary_fan_snd_toCone (c : BinaryBicone P Q) : BinaryFan.snd c.toCone = c.snd := rfl

/-- Extract the cocone from a binary bicone. -/
/-
**CategoryTheory.Limits.BinaryBicone.toCocone** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.BinaryBicone`。
形式化陈述：toCocone (c : BinaryBicone P Q) : Cocone (pair P Q)
参数：c : BinaryBicone P Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the cocone from a binary bicone.
-/
def toCocone (c : BinaryBicone P Q) : Cocone (pair P Q) := BinaryCofan.mk c.inl c.inr

@[simp]
/-
**CategoryTheory.Limits.BinaryBicone.toCocone_pt** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.BinaryBicone`。
形式化陈述：toCocone_pt (c : BinaryBicone P Q) : c.toCocone.pt = c.pt
参数：c : BinaryBicone P Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCocone_pt (c : BinaryBicone P Q) : c.toCocone.pt = c.pt := rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryBicone.toCocone_** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.BinaryBicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCocone_ι_app_left (c : BinaryBicone P Q) : c.toCocone.ι.app ⟨WalkingPair.left⟩ = c.inl :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryBicone.toCocone_** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.BinaryBicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCocone_ι_app_right (c : BinaryBicone P Q) :
    c.toCocone.ι.app ⟨WalkingPair.right⟩ = c.inr := rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryBicone.binary_cofan_inl_toCocone** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：binary_cofan_inl_toCocone (c : BinaryBicone P Q) : BinaryCofan.inl c.toCoc
one = c.inl
参数：c : BinaryBicone P Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem binary_cofan_inl_toCocone (c : BinaryBicone P Q) : BinaryCofan.inl c.toCocone = c.inl :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryBicone.binary_cofan_inr_toCocone** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：binary_cofan_inr_toCocone (c : BinaryBicone P Q) : BinaryCofan.inr c.toCoc
one = c.inr
参数：c : BinaryBicone P Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem binary_cofan_inr_toCocone (c : BinaryBicone P Q) : BinaryCofan.inr c.toCocone = c.inr :=
  rfl

/-- The retract of a binary bicone `c` given by `c.inl` and `c.fst`. -/
/-
**CategoryTheory.Limits.BinaryBicone.retract_left** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.BinaryBicone`。
形式化陈述：retract_left (c : BinaryBicone P Q) : Retract P c.pt where i
参数：c : BinaryBicone P Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The retract of a binary bicone `c` given by `c.inl` and `c.fst`.
-/
def retract_left (c : BinaryBicone P Q) : Retract P c.pt where
  i := c.inl
  r := c.fst

/-- The retract of a binary bicone `c` given by `c.inr` and `c.snd`. -/
/-
**CategoryTheory.Limits.BinaryBicone.retract_right** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.BinaryBicone`。
形式化陈述：retract_right (c : BinaryBicone P Q) : Retract Q c.pt where i
参数：c : BinaryBicone P Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The retract of a binary bicone `c` given by `c.inr` and `c.snd`.
-/
def retract_right (c : BinaryBicone P Q) : Retract Q c.pt where
  i := c.inr
  r := c.snd
/-
**CategoryTheory.Limits.BinaryBicone.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Limits.BinaryBicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (c : BinaryBicone P Q) : IsSplitMono c.inl := c.retract_left.instIsSplitMonoI
/-
**CategoryTheory.Limits.BinaryBicone.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Limits.BinaryBicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (c : BinaryBicone P Q) : IsSplitMono c.inr := c.retract_right.instIsSplitMonoI
/-
**CategoryTheory.Limits.BinaryBicone.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Limits.BinaryBicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (c : BinaryBicone P Q) : IsSplitEpi c.fst := c.retract_left.instIsSplitEpiR
/-
**CategoryTheory.Limits.BinaryBicone.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Limits.BinaryBicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (c : BinaryBicone P Q) : IsSplitEpi c.snd := c.retract_right.instIsSplitEpiR

set_option backward.isDefEq.respectTransparency false in
/-- Convert a `BinaryBicone` into a `Bicone` over a pair. -/
@[simps]
/-
**CategoryTheory.Limits.BinaryBicone.toBiconeFunctor** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.BinaryBicone`。
形式化陈述：toBiconeFunctor {X Y : C} : BinaryBicone X Y ⥤ Bicone (pairFunction X Y) w
here obj b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a `BinaryBicone` into a `Bicone` over a pair.
-/
def toBiconeFunctor {X Y : C} : BinaryBicone X Y ⥤ Bicone (pairFunction X Y) where
  obj b :=
    { pt := b.pt
      π := fun j => WalkingPair.casesOn j b.fst b.snd
      ι := fun j => WalkingPair.casesOn j b.inl b.inr
      ι_π := fun j j' => by
        rcases j with ⟨⟩ <;> rcases j' with ⟨⟩ <;> simp }
  map f := {
    hom := f.hom
    wπ := fun i => WalkingPair.casesOn i f.wfst f.wsnd
    wι := fun i => WalkingPair.casesOn i f.winl f.winr }

/-- A shorthand for `toBiconeFunctor.obj` -/
/-
**CategoryTheory.Limits.BinaryBicone.toBicone** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Limits.BinaryBicone`。
形式化陈述：toBicone {X Y : C} (b : BinaryBicone X Y) : Bicone (pairFunction X Y)
参数：b : BinaryBicone X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A shorthand for `toBiconeFunctor.obj`
-/
abbrev toBicone {X Y : C} (b : BinaryBicone X Y) : Bicone (pairFunction X Y) :=
  toBiconeFunctor.obj b

set_option backward.defeqAttrib.useBackward true in
/-- A binary bicone is a limit cone if and only if the corresponding bicone is a limit cone. -/
/-
**CategoryTheory.Limits.BinaryBicone.toBiconeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.BinaryBicone`。
形式化陈述：toBiconeIsLimit {X Y : C} (b : BinaryBicone X Y) : IsLimit b.toBicone.toCo
ne ≃ IsLimit b.toCone
参数：b : BinaryBicone X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary bicone is a limit cone if and only if the corresponding bicone is a lim
it cone.
-/
def toBiconeIsLimit {X Y : C} (b : BinaryBicone X Y) :
    IsLimit b.toBicone.toCone ≃ IsLimit b.toCone :=
  IsLimit.equivIsoLimit <| Cone.ext (Iso.refl _) fun ⟨as⟩ => by cases as <;> simp

set_option backward.defeqAttrib.useBackward true in
/-- A binary bicone is a colimit cocone if and only if the corresponding bicone is a colimit
cocone. -/
/-
**CategoryTheory.Limits.BinaryBicone.toBiconeIsColimit** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：toBiconeIsColimit {X Y : C} (b : BinaryBicone X Y) : IsColimit b.toBicone.
toCocone ≃ IsColimit b.toCocone
参数：b : BinaryBicone X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary bicone is a colimit cocone if and only if the corresponding bicone is a
 colimit
cocone.
-/
def toBiconeIsColimit {X Y : C} (b : BinaryBicone X Y) :
    IsColimit b.toBicone.toCocone ≃ IsColimit b.toCocone :=
  IsColimit.equivIsoColimit <| Cocone.ext (Iso.refl _) fun ⟨as⟩ => by cases as <;> simp

/-- Transport a binary bicone via isomorphisms. -/
@[simps]
/-
**CategoryTheory.Limits.BinaryBicone.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.BinaryBicone`。
形式化陈述：ofIso (b : BinaryBicone P Q) (eP : P ≅ P') (eQ : Q ≅ Q') : BinaryBicone P'
 Q' where pt
参数：b : BinaryBicone P Q；eP : P ≅ P'；eQ : Q ≅ Q'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a binary bicone via isomorphisms.
-/
def ofIso (b : BinaryBicone P Q) (eP : P ≅ P') (eQ : Q ≅ Q') :
    BinaryBicone P' Q' where
  pt := b.pt
  fst := b.fst ≫ eP.hom
  snd := b.snd ≫ eQ.hom
  inl := eP.inv ≫ b.inl
  inr := eQ.inv ≫ b.inr

attribute [local simp←] op_comp in
/-- The opposite of a binary bicone. -/
@[simps]
/-
**CategoryTheory.Limits.BinaryBicone.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.BinaryBicone`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {P Q : C} →         Categ
oryTheory.Limits.BinaryBicone P Q → CategoryTheory.Limits.BinaryBicone (Opposite
.op P) (Opposite.op Q)
参数：Opposite.op P；Opposite.op Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a binary bicone.
-/
protected def op (b : BinaryBicone P Q) :
    BinaryBicone (op P) (op Q) where
  pt := Opposite.op b.pt
  fst := b.inl.op
  snd := b.inr.op
  inl := b.fst.op
  inr := b.snd.op

end BinaryBicone

namespace Bicone

set_option backward.isDefEq.respectTransparency false in
/-- Convert a `Bicone` over a function on `WalkingPair` to a BinaryBicone. -/
@[simps]
/-
**CategoryTheory.Limits.Bicone.toBinaryBiconeFunctor** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.Bicone`。
形式化陈述：toBinaryBiconeFunctor {X Y : C} : Bicone (pairFunction X Y) ⥤ BinaryBicone
 X Y where obj b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a `Bicone` over a function on `WalkingPair` to a BinaryBicone.
-/
def toBinaryBiconeFunctor {X Y : C} : Bicone (pairFunction X Y) ⥤ BinaryBicone X Y where
  obj b :=
    { pt := b.pt
      fst := b.π WalkingPair.left
      snd := b.π WalkingPair.right
      inl := b.ι WalkingPair.left
      inr := b.ι WalkingPair.right
      inl_fst := by simp
      inr_fst := by simp
      inl_snd := by simp
      inr_snd := by simp }
  map f :=
    { hom := f.hom }

/-- A shorthand for `toBinaryBiconeFunctor.obj` -/
/-
**CategoryTheory.Limits.Bicone.toBinaryBicone** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Limits.Bicone`。
形式化陈述：toBinaryBicone {X Y : C} (b : Bicone (pairFunction X Y)) : BinaryBicone X 
Y
参数：b : Bicone (pairFunction X Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A shorthand for `toBinaryBiconeFunctor.obj`
-/
abbrev toBinaryBicone {X Y : C} (b : Bicone (pairFunction X Y)) : BinaryBicone X Y :=
  toBinaryBiconeFunctor.obj b

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A bicone over a pair is a limit cone if and only if the corresponding binary bicone is a limit
cone. -/
/-
**CategoryTheory.Limits.Bicone.toBinaryBiconeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.Bicone`。
形式化陈述：toBinaryBiconeIsLimit {X Y : C} (b : Bicone (pairFunction X Y)) : IsLimit 
b.toBinaryBicone.toCone ≃ IsLimit b.toCone
参数：b : Bicone (pairFunction X Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bicone over a pair is a limit cone if and only if the corresponding binary bic
one is a limit
cone.
-/
def toBinaryBiconeIsLimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    IsLimit b.toBinaryBicone.toCone ≃ IsLimit b.toCone :=
  IsLimit.equivIsoLimit <| Cone.ext (Iso.refl _) fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A bicone over a pair is a colimit cocone if and only if the corresponding binary bicone is a
colimit cocone. -/
/-
**CategoryTheory.Limits.Bicone.toBinaryBiconeIsColimit** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.Bicone`。
形式化陈述：toBinaryBiconeIsColimit {X Y : C} (b : Bicone (pairFunction X Y)) : IsColi
mit b.toBinaryBicone.toCocone ≃ IsColimit b.toCocone
参数：b : Bicone (pairFunction X Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bicone over a pair is a colimit cocone if and only if the corresponding binary
 bicone is a
colimit cocone.
-/
def toBinaryBiconeIsColimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    IsColimit b.toBinaryBicone.toCocone ≃ IsColimit b.toCocone :=
  IsColimit.equivIsoColimit <| Cocone.ext (Iso.refl _) fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

end Bicone

/-- Structure witnessing that a binary bicone is a limit cone and a limit cocone. -/
/-
**CategoryTheory.Limits.BinaryBicone.IsBilimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {P Q : C} → CategoryTheor
y.Limits.BinaryBicone P Q → Type (max uC uC')
参数：max uC uC'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure witnessing that a binary bicone is a limit cone and a limit cocone.
-/
structure BinaryBicone.IsBilimit {P Q : C} (b : BinaryBicone P Q) where
  isLimit : IsLimit b.toCone
  isColimit : IsColimit b.toCocone

attribute [inherit_doc BinaryBicone.IsBilimit] BinaryBicone.IsBilimit.isLimit
  BinaryBicone.IsBilimit.isColimit

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If a binary bicone for `P` and `Q` is bilimit, then the binary bicone for `P'` and `Q'`
obtained using isomorphisms `P ≅ P'` and `Q ≅ Q'` is also bilimit. -/
/-
**CategoryTheory.Limits.BinaryBicone.IsBilimit.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.BinaryBicone.IsBilimit`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {P Q P' Q' : C} →        
 {b : CategoryTheory.Limits.BinaryBicone P Q} →           b.IsBilimit → (eP : P 
≅ P') → (eQ : Q ≅ Q') → (b.ofIso eP eQ).IsBilimit
参数：eP : P ≅ P'；eQ : Q ≅ Q'；b.ofIso eP eQ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a binary bicone for `P` and `Q` is bilimit, then the binary bicone for `P'` a
nd `Q'`
obtained using isomorphisms `P ≅ P'` and `Q ≅ Q'` is also bilimit.
-/
def BinaryBicone.IsBilimit.ofIso {P Q P' Q' : C} {b : BinaryBicone P Q} (hb : b.IsBilimit)
    (eP : P ≅ P') (eQ : Q ≅ Q') :
    (b.ofIso eP eQ).IsBilimit where
  isLimit := by
    refine (IsLimit.equivOfNatIsoOfIso (mapPairIso eP eQ) _ _ ?_).1 hb.isLimit
    exact BinaryFan.ext (Iso.refl _) (by simp [BinaryFan.fst])
      (by simp [BinaryFan.snd])
  isColimit := by
    refine (IsColimit.equivOfNatIsoOfIso (mapPairIso eP eQ) _ _ ?_).1 hb.isColimit
    exact BinaryCofan.ext (Iso.refl _) (by simp [BinaryCofan.inl])
      (by simp [BinaryCofan.inr])

/-- The opposite of a bilimit binary bicone is bilimit. -/
/-
**CategoryTheory.Limits.BinaryBicone.IsBilimit.op** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.BinaryBicone.IsBilimit`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {P Q : C} → {b : Category
Theory.Limits.BinaryBicone P Q} → b.IsBilimit → b.op.IsBilimit
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a bilimit binary bicone is bilimit.
-/
protected def BinaryBicone.IsBilimit.op {P Q : C} {b : BinaryBicone P Q} (h : b.IsBilimit) :
    b.op.IsBilimit where
  isLimit := BinaryCofan.IsColimit.op h.isColimit
  isColimit := BinaryFan.IsLimit.op h.isLimit

/-- A binary bicone is a bilimit bicone if and only if the corresponding bicone is a bilimit. -/
/-
**CategoryTheory.Limits.BinaryBicone.toBiconeIsBilimit** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} → (b : Category
Theory.Limits.BinaryBicone X Y) → b.toBicone.IsBilimit ≃ b.IsBilimit
参数：b : CategoryTheory.Limits.BinaryBicone X Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A binary bicone is a bilimit bicone if and only if the corresponding bicone is a
 bilimit.
-/
def BinaryBicone.toBiconeIsBilimit {X Y : C} (b : BinaryBicone X Y) :
    b.toBicone.IsBilimit ≃ b.IsBilimit where
  toFun h := ⟨b.toBiconeIsLimit h.isLimit, b.toBiconeIsColimit h.isColimit⟩
  invFun h := ⟨b.toBiconeIsLimit.symm h.isLimit, b.toBiconeIsColimit.symm h.isColimit⟩
  left_inv := fun ⟨h, h'⟩ => by dsimp only; simp
  right_inv := fun ⟨h, h'⟩ => by dsimp only; simp

/-- A bicone over a pair is a bilimit bicone if and only if the corresponding binary bicone is a
bilimit. -/
/-
**CategoryTheory.Limits.Bicone.toBinaryBiconeIsBilimit** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.Bicone`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (b : 
CategoryTheory.Limits.Bicone (CategoryTheory.Limits.pairFunction X Y)) →        
   b.toBinaryBicone.IsBilimit ≃ b.IsBilimit
参数：b : CategoryTheory.Limits.Bicone (CategoryTheory.Limits.pairFunction X Y)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A bicone over a pair is a bilimit bicone if and only if the corresponding binary
 bicone is a
bilimit.
-/
def Bicone.toBinaryBiconeIsBilimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    b.toBinaryBicone.IsBilimit ≃ b.IsBilimit where
  toFun h := ⟨b.toBinaryBiconeIsLimit h.isLimit, b.toBinaryBiconeIsColimit h.isColimit⟩
  invFun h := ⟨b.toBinaryBiconeIsLimit.symm h.isLimit, b.toBinaryBiconeIsColimit.symm h.isColimit⟩
  left_inv := fun ⟨h, h'⟩ => by dsimp only; simp
  right_inv := fun ⟨h, h'⟩ => by dsimp only; simp

/-- A bicone over `P Q : C`, which is both a limit cone and a colimit cocone. -/
/-
**CategoryTheory.Limits.BinaryBiproductData** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] → [Category
Theory.Limits.HasZeroMorphisms C] → C → C → Type (max uC uC')
参数：max uC uC'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bicone over `P Q : C`, which is both a limit cone and a colimit cocone.
-/
structure BinaryBiproductData (P Q : C) where
  bicone : BinaryBicone P Q
  isBilimit : bicone.IsBilimit

initialize_simps_projections BinaryBiproductData (-isBilimit)

attribute [inherit_doc BinaryBiproductData] BinaryBiproductData.bicone
  BinaryBiproductData.isBilimit

/-- Transport a binary bicone data via isomorphisms. -/
@[simps]
/-
**CategoryTheory.Limits.BinaryBiproductData.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.BinaryBiproductData`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {P Q P' Q' : C} →        
 CategoryTheory.Limits.BinaryBiproductData P Q →           (P ≅ P') → (Q ≅ Q') →
 CategoryTheory.Limits.BinaryBiproductData P' Q'
参数：P ≅ P'；Q ≅ Q'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a binary bicone data via isomorphisms.
-/
def BinaryBiproductData.ofIso {P Q P' Q' : C} (d : BinaryBiproductData P Q)
    (eP : P ≅ P') (eQ : Q ≅ Q') :
    BinaryBiproductData P' Q' where
  bicone := d.bicone.ofIso eP eQ
  isBilimit := d.isBilimit.ofIso _ _

/-- The opposite of a binary biproduct data. -/
@[simps]
/-
**CategoryTheory.Limits.BinaryBiproductData.op** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.BinaryBiproductData`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {P Q : C} →         Categ
oryTheory.Limits.BinaryBiproductData P Q →           CategoryTheory.Limits.Binar
yBiproductData (Opposite.op P) (Opposite.op Q)
参数：Opposite.op P；Opposite.op Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a binary biproduct data.
-/
protected def BinaryBiproductData.op {P Q : C} (d : BinaryBiproductData P Q) :
    BinaryBiproductData (op P) (op Q) where
  bicone := d.bicone.op
  isBilimit := d.isBilimit.op

/-- `HasBinaryBiproduct P Q` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`. -/
/-
**CategoryTheory.Limits.HasBinaryBiproduct** 是 Mathlib 中的一个归纳类型，位于命名空间 `Category
Theory.Limits`。
形式化陈述：{C : Type uC} → [inst : CategoryTheory.Category.{uC', uC} C] → [CategoryTh
eory.Limits.HasZeroMorphisms C] → C → C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasBinaryBiproduct P Q` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`.
-/
class HasBinaryBiproduct (P Q : C) : Prop where mk' ::
  exists_binary_biproduct : Nonempty (BinaryBiproductData P Q)

attribute [inherit_doc HasBinaryBiproduct] HasBinaryBiproduct.exists_binary_biproduct
/-
**CategoryTheory.Limits.HasBinaryBiproduct.mk** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.HasBinaryBiproduct`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {P Q : C} (d : CategoryTheory.Limits.Bi
naryBiproductData P Q), CategoryTheory.Limits.HasBinaryBiproduct P Q
参数：d : CategoryTheory.Limits.BinaryBiproductData P Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasBinaryBiproduct.mk {P Q : C} (d : BinaryBiproductData P Q) : HasBinaryBiproduct P Q :=
  ⟨Nonempty.intro d⟩

/--
Use the axiom of choice to extract explicit `BinaryBiproductData F` from `HasBinaryBiproduct F`.
-/
/-
**CategoryTheory.Limits.getBinaryBiproductData** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：getBinaryBiproductData (P Q : C) [HasBinaryBiproduct P Q] : BinaryBiproduc
tData P Q
参数：P Q : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.exists_binary_biproduct`：∀ {C :
 Type uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C}   {P Q : C} [self : Categor…

--- 原说明 ---
Use the axiom of choice to extract explicit `BinaryBiproductData F` from `HasBin
aryBiproduct F`.
-/
def getBinaryBiproductData (P Q : C) [HasBinaryBiproduct P Q] : BinaryBiproductData P Q :=
  Classical.choice HasBinaryBiproduct.exists_binary_biproduct

/-- A bicone for `P Q` which is both a limit cone and a colimit cocone. -/
/-
**CategoryTheory.Limits.BinaryBiproduct.bicone** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.BinaryBiproduct`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (P Q : C) → [CategoryTheo
ry.Limits.HasBinaryBiproduct P Q] → CategoryTheory.Limits.BinaryBicone P Q
参数：P Q : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bicone for `P Q` which is both a limit cone and a colimit cocone.
-/
def BinaryBiproduct.bicone (P Q : C) [HasBinaryBiproduct P Q] : BinaryBicone P Q :=
  (getBinaryBiproductData P Q).bicone

/-- `BinaryBiproduct.bicone P Q` is a limit bicone. -/
/-
**CategoryTheory.Limits.BinaryBiproduct.isBilimit** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.BinaryBiproduct`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (P Q : C) →         [inst
_2 : CategoryTheory.Limits.HasBinaryBiproduct P Q] →           (CategoryTheory.L
imits.BinaryBiproduct.bicone P Q).IsBilimit
参数：P Q : C；CategoryTheory.Limits.BinaryBiproduct.bicone P Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BinaryBiproduct.bicone P Q` is a limit bicone.
-/
def BinaryBiproduct.isBilimit (P Q : C) [HasBinaryBiproduct P Q] :
    (BinaryBiproduct.bicone P Q).IsBilimit :=
  (getBinaryBiproductData P Q).isBilimit

/-- `BinaryBiproduct.bicone P Q` is a limit cone. -/
/-
**CategoryTheory.Limits.BinaryBiproduct.isLimit** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.BinaryBiproduct`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (P Q : C) →         [inst
_2 : CategoryTheory.Limits.HasBinaryBiproduct P Q] →           CategoryTheory.Li
mits.IsLimit (CategoryTheory.Limits.BinaryBiproduct.bicone P Q).toCone
参数：P Q : C；CategoryTheory.Limits.BinaryBiproduct.bicone P Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BinaryBiproduct.bicone P Q` is a limit cone.
-/
def BinaryBiproduct.isLimit (P Q : C) [HasBinaryBiproduct P Q] :
    IsLimit (BinaryBiproduct.bicone P Q).toCone :=
  (getBinaryBiproductData P Q).isBilimit.isLimit

/-- `BinaryBiproduct.bicone P Q` is a colimit cocone. -/
/-
**CategoryTheory.Limits.BinaryBiproduct.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.BinaryBiproduct`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (P Q : C) →         [inst
_2 : CategoryTheory.Limits.HasBinaryBiproduct P Q] →           CategoryTheory.Li
mits.IsColimit (CategoryTheory.Limits.BinaryBiproduct.bicone P Q).toCocone
参数：P Q : C；CategoryTheory.Limits.BinaryBiproduct.bicone P Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BinaryBiproduct.bicone P Q` is a colimit cocone.
-/
def BinaryBiproduct.isColimit (P Q : C) [HasBinaryBiproduct P Q] :
    IsColimit (BinaryBiproduct.bicone P Q).toCocone :=
  (getBinaryBiproductData P Q).isBilimit.isColimit
/-
**CategoryTheory.Limits.hasBinaryBiproduct_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：hasBinaryBiproduct_of_iso {P Q P' Q' : C} [HasBinaryBiproduct P Q] (eP : P
 ≅ P') (eQ : Q ≅ Q') : HasBinaryBiproduct P' Q' where exists_binary_biproduct
参数：eP : P ≅ P'；eQ : Q ≅ Q'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasBinaryBiproduct_of_iso {P Q P' Q' : C} [HasBinaryBiproduct P Q]
    (eP : P ≅ P') (eQ : Q ≅ Q') :
    HasBinaryBiproduct P' Q' where
  exists_binary_biproduct := ⟨(getBinaryBiproductData P Q).ofIso eP eQ⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P Q : C} [HasBinaryBiproduct P Q] :
    HasBinaryBiproduct (op P) (op Q) where
  exists_binary_biproduct := ⟨(getBinaryBiproductData P Q).op⟩

section

variable (C)

/-- `HasBinaryBiproducts C` represents the existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`, for every `P Q : C`. -/
/-
**CategoryTheory.Limits.HasBinaryBiproducts** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：(C : Type uC) → [inst : CategoryTheory.Category.{uC', uC} C] → [CategoryTh
eory.Limits.HasZeroMorphisms C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasBinaryBiproducts C` represents the existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`, for every `P Q :
 C`.
-/
class HasBinaryBiproducts : Prop where
  has_binary_biproduct : ∀ P Q : C, HasBinaryBiproduct P Q

attribute [instance 100] HasBinaryBiproducts.has_binary_biproduct

/-- A category with finite biproducts has binary biproducts.

This is not an instance as typically in concrete categories there will be
an alternative construction with nicer definitional properties. -/
/-
**CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasBinaryBiproducts_of_finite_biproducts [HasFiniteBiproducts C] : HasBina
ryBiproducts C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.mk`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {P Q : C} (d : CategoryTh…
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A category with finite biproducts has binary biproducts.

This is not an instance as typically in concrete categories there will be
an alternative construction with nicer definitional properties.
-/
theorem hasBinaryBiproducts_of_finite_biproducts [HasFiniteBiproducts C] : HasBinaryBiproducts C :=
  { has_binary_biproduct := fun P Q =>
      HasBinaryBiproduct.mk
        { bicone := (biproduct.bicone (pairFunction P Q)).toBinaryBicone
          isBilimit := (Bicone.toBinaryBiconeIsBilimit _).symm (biproduct.isBilimit _) } }
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasBinaryBiproducts C] : HasBinaryBiproducts Cᵒᵖ where
  has_binary_biproduct X Y :=
    inferInstanceAs (HasBinaryBiproduct (op X.unop) (op Y.unop))

end

variable {P Q : C}

/-
**CategoryTheory.Limits.HasBinaryBiproduct.hasLimit_pair** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.HasBinaryBiproduct`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {P Q : C} [CategoryTheory.Limits.HasBin
aryBiproduct P Q],   CategoryTheory.Limits.HasLimit (CategoryTheory.Limits.pair 
P Q)
参数：CategoryTheory.Limits.pair P Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance HasBinaryBiproduct.hasLimit_pair [HasBinaryBiproduct P Q] : HasLimit (pair P Q) :=
  HasLimit.mk ⟨_, BinaryBiproduct.isLimit P Q⟩
/-
**CategoryTheory.Limits.HasBinaryBiproduct.hasColimit_pair** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.HasBinaryBiproduct`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {P Q : C} [CategoryTheory.Limits.HasBin
aryBiproduct P Q],   CategoryTheory.Limits.HasColimit (CategoryTheory.Limits.pai
r P Q)
参数：CategoryTheory.Limits.pair P Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance HasBinaryBiproduct.hasColimit_pair [HasBinaryBiproduct P Q] : HasColimit (pair P Q) :=
  HasColimit.mk ⟨_, BinaryBiproduct.isColimit P Q⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasBinaryProducts_of_hasBinaryBiproducts [HasBinaryBiproducts C] :
    HasBinaryProducts C where
  has_limit F := hasLimit_of_iso (diagramIsoPair F).symm
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasBinaryCoproducts_of_hasBinaryBiproducts [HasBinaryBiproducts C] :
    HasBinaryCoproducts C where
  has_colimit F := hasColimit_of_iso (diagramIsoPair F)

/-- The isomorphism between the specified binary product and the specified binary coproduct for
a pair for a binary biproduct. -/
/-
**CategoryTheory.Limits.biprodIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：biprodIso (X Y : C) [HasBinaryBiproduct X Y] : Limits.prod X Y ≅ Limits.co
prod X Y
参数：X Y : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.hasLimit_pair`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.hasColimit_pair`：∀ {C : Type uC
} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {P Q : C} [CategoryTheory…

--- 原说明 ---
The isomorphism between the specified binary product and the specified binary co
product for
a pair for a binary biproduct.
-/
def biprodIso (X Y : C) [HasBinaryBiproduct X Y] : Limits.prod X Y ≅ Limits.coprod X Y :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (BinaryBiproduct.isLimit X Y)).trans <|
    IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)

/-- An arbitrary choice of biproduct of a pair of objects. -/
/-
**CategoryTheory.Limits.biprod** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：biprod (X Y : C) [HasBinaryBiproduct X Y]
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary choice of biproduct of a pair of objects.
-/
abbrev biprod (X Y : C) [HasBinaryBiproduct X Y] :=
  (BinaryBiproduct.bicone X Y).pt

@[inherit_doc biprod]
notation:20 X " ⊞ " Y:20 => biprod X Y

/-- The projection onto the first summand of a binary biproduct. -/
/-
**CategoryTheory.Limits.biprod.fst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} → [inst_2 : Cat
egoryTheory.Limits.HasBinaryBiproduct X Y] → X ⊞ Y ⟶ X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection onto the first summand of a binary biproduct.
-/
abbrev biprod.fst {X Y : C} [HasBinaryBiproduct X Y] : X ⊞ Y ⟶ X :=
  (BinaryBiproduct.bicone X Y).fst

/-- The projection onto the second summand of a binary biproduct. -/
/-
**CategoryTheory.Limits.biprod.snd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} → [inst_2 : Cat
egoryTheory.Limits.HasBinaryBiproduct X Y] → X ⊞ Y ⟶ Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection onto the second summand of a binary biproduct.
-/
abbrev biprod.snd {X Y : C} [HasBinaryBiproduct X Y] : X ⊞ Y ⟶ Y :=
  (BinaryBiproduct.bicone X Y).snd

/-- The inclusion into the first summand of a binary biproduct. -/
/-
**CategoryTheory.Limits.biprod.inl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} → [inst_2 : Cat
egoryTheory.Limits.HasBinaryBiproduct X Y] → X ⟶ X ⊞ Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion into the first summand of a binary biproduct.
-/
abbrev biprod.inl {X Y : C} [HasBinaryBiproduct X Y] : X ⟶ X ⊞ Y :=
  (BinaryBiproduct.bicone X Y).inl

/-- The inclusion into the second summand of a binary biproduct. -/
/-
**CategoryTheory.Limits.biprod.inr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} → [inst_2 : Cat
egoryTheory.Limits.HasBinaryBiproduct X Y] → Y ⟶ X ⊞ Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion into the second summand of a binary biproduct.
-/
abbrev biprod.inr {X Y : C} [HasBinaryBiproduct X Y] : Y ⟶ X ⊞ Y :=
  (BinaryBiproduct.bicone X Y).inr

section

variable {X Y : C} [HasBinaryBiproduct X Y]

/-
**CategoryTheory.Limits.BinaryBiproduct.bicone_fst** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.BinaryBiproduct`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   (CategoryTheory.Limits.BinaryBiproduct.bicone X Y)
.fst = CategoryTheory.Limits.biprod.fst
参数：CategoryTheory.Limits.BinaryBiproduct.bicone X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem BinaryBiproduct.bicone_fst : (BinaryBiproduct.bicone X Y).fst = biprod.fst := rfl
/-
**CategoryTheory.Limits.BinaryBiproduct.bicone_snd** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.BinaryBiproduct`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   (CategoryTheory.Limits.BinaryBiproduct.bicone X Y)
.snd = CategoryTheory.Limits.biprod.snd
参数：CategoryTheory.Limits.BinaryBiproduct.bicone X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem BinaryBiproduct.bicone_snd : (BinaryBiproduct.bicone X Y).snd = biprod.snd := rfl
/-
**CategoryTheory.Limits.BinaryBiproduct.bicone_inl** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.BinaryBiproduct`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   (CategoryTheory.Limits.BinaryBiproduct.bicone X Y)
.inl = CategoryTheory.Limits.biprod.inl
参数：CategoryTheory.Limits.BinaryBiproduct.bicone X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem BinaryBiproduct.bicone_inl : (BinaryBiproduct.bicone X Y).inl = biprod.inl := rfl
/-
**CategoryTheory.Limits.BinaryBiproduct.bicone_inr** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.BinaryBiproduct`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   (CategoryTheory.Limits.BinaryBiproduct.bicone X Y)
.inr = CategoryTheory.Limits.biprod.inr
参数：CategoryTheory.Limits.BinaryBiproduct.bicone X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem BinaryBiproduct.bicone_inr : (BinaryBiproduct.bicone X Y).inr = biprod.inr := rfl

end

@[reassoc]
/-
**CategoryTheory.Limits.biprod.inl_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   CategoryTheory.CategoryStruct.comp CategoryTheory.
Limits.biprod.inl CategoryTheory.Limits.biprod.fst =     CategoryTheory.Category
Struct.id X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
theorem biprod.inl_fst {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 𝟙 X :=
  (BinaryBiproduct.bicone X Y).inl_fst

@[reassoc]
/-
**CategoryTheory.Limits.biprod.inl_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   CategoryTheory.CategoryStruct.comp CategoryTheory.
Limits.biprod.inl CategoryTheory.Limits.biprod.snd = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
theorem biprod.inl_snd {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 0 :=
  (BinaryBiproduct.bicone X Y).inl_snd

@[reassoc]
/-
**CategoryTheory.Limits.biprod.inr_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   CategoryTheory.CategoryStruct.comp CategoryTheory.
Limits.biprod.inr CategoryTheory.Limits.biprod.fst = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
theorem biprod.inr_fst {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 0 :=
  (BinaryBiproduct.bicone X Y).inr_fst

@[reassoc]
/-
**CategoryTheory.Limits.biprod.inr_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   CategoryTheory.CategoryStruct.comp CategoryTheory.
Limits.biprod.inr CategoryTheory.Limits.biprod.snd =     CategoryTheory.Category
Struct.id Y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
theorem biprod.inr_snd {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 𝟙 Y :=
  (BinaryBiproduct.bicone X Y).inr_snd

/-- Given a pair of maps into the summands of a binary biproduct,
we obtain a map into the binary biproduct. -/
/-
**CategoryTheory.Limits.biprod.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {W X Y : C} → [inst_2 : C
ategoryTheory.Limits.HasBinaryBiproduct X Y] → (W ⟶ X) → (W ⟶ Y) → (W ⟶ X ⊞ Y)
参数：W ⟶ X；W ⟶ Y；W ⟶ X ⊞ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a pair of maps into the summands of a binary biproduct,
we obtain a map into the binary biproduct.
-/
abbrev biprod.lift {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⊞ Y :=
  BinaryFan.IsLimit.lift (BinaryBiproduct.isLimit X Y) f g

/-- Given a pair of maps out of the summands of a binary biproduct,
we obtain a map out of the binary biproduct. -/
/-
**CategoryTheory.Limits.biprod.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {W X Y : C} → [inst_2 : C
ategoryTheory.Limits.HasBinaryBiproduct X Y] → (X ⟶ W) → (Y ⟶ W) → (X ⊞ Y ⟶ W)
参数：X ⟶ W；Y ⟶ W；X ⊞ Y ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a pair of maps out of the summands of a binary biproduct,
we obtain a map out of the binary biproduct.
-/
abbrev biprod.desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) : X ⊞ Y ⟶ W :=
  BinaryCofan.IsColimit.desc (BinaryBiproduct.isColimit X Y) f g

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.lift_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y : C} [inst_2 : CategoryTheory.Li
mits.HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y),   CategoryTheory.CategoryS
truct.comp (CategoryTheory.Limits.biprod.lift f g) CategoryTheory.Limits.biprod.
fst = f
参数：f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits.biprod.lift f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
theorem biprod.lift_fst {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.fst = f :=
  (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.lift_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y : C} [inst_2 : CategoryTheory.Li
mits.HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y),   CategoryTheory.CategoryS
truct.comp (CategoryTheory.Limits.biprod.lift f g) CategoryTheory.Limits.biprod.
snd = g
参数：f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits.biprod.lift f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
theorem biprod.lift_snd {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.snd = g :=
  (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.right⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.inl_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y : C} [inst_2 : CategoryTheory.Li
mits.HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W),   CategoryTheory.CategoryS
truct.comp CategoryTheory.Limits.biprod.inl (CategoryTheory.Limits.biprod.desc f
 g) = f
参数：f : X ⟶ W；g : Y ⟶ W；CategoryTheory.Limits.biprod.desc f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
theorem biprod.inl_desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inl ≫ biprod.desc f g = f :=
  (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.inr_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y : C} [inst_2 : CategoryTheory.Li
mits.HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W),   CategoryTheory.CategoryS
truct.comp CategoryTheory.Limits.biprod.inr (CategoryTheory.Limits.biprod.desc f
 g) = g
参数：f : X ⟶ W；g : Y ⟶ W；CategoryTheory.Limits.biprod.desc f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
theorem biprod.inr_desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inr ≫ biprod.desc f g = g :=
  (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.right⟩
/-
**CategoryTheory.Limits.biprod.mono_lift_of_mono_left** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y : C} [inst_2 : CategoryTheory.Li
mits.HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) [CategoryTheory.Mono f],   
CategoryTheory.Mono (CategoryTheory.Limits.biprod.lift f g)
参数：f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits.biprod.lift f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
instance biprod.mono_lift_of_mono_left {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (biprod.lift f g) :=
  mono_of_mono_fac <| biprod.lift_fst _ _
/-
**CategoryTheory.Limits.biprod.mono_lift_of_mono_right** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y : C} [inst_2 : CategoryTheory.Li
mits.HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) [CategoryTheory.Mono g],   
CategoryTheory.Mono (CategoryTheory.Limits.biprod.lift f g)
参数：f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits.biprod.lift f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
instance biprod.mono_lift_of_mono_right {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (biprod.lift f g) :=
  mono_of_mono_fac <| biprod.lift_snd _ _
/-
**CategoryTheory.Limits.biprod.epi_desc_of_epi_left** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y : C} [inst_2 : CategoryTheory.Li
mits.HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) [CategoryTheory.Epi f],   C
ategoryTheory.Epi (CategoryTheory.Limits.biprod.desc f g)
参数：f : X ⟶ W；g : Y ⟶ W；CategoryTheory.Limits.biprod.desc f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
instance biprod.epi_desc_of_epi_left {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi f] : Epi (biprod.desc f g) :=
  epi_of_epi_fac <| biprod.inl_desc _ _
/-
**CategoryTheory.Limits.biprod.epi_desc_of_epi_right** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y : C} [inst_2 : CategoryTheory.Li
mits.HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) [CategoryTheory.Epi g],   C
ategoryTheory.Epi (CategoryTheory.Limits.biprod.desc f g)
参数：f : X ⟶ W；g : Y ⟶ W；CategoryTheory.Limits.biprod.desc f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
instance biprod.epi_desc_of_epi_right {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi g] : Epi (biprod.desc f g) :=
  epi_of_epi_fac <| biprod.inr_desc _ _

/-- Given a pair of maps between the summands of a pair of binary biproducts,
we obtain a map between the binary biproducts. -/
/-
**CategoryTheory.Limits.biprod.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {W X Y Z : C} →         [
inst_2 : CategoryTheory.Limits.HasBinaryBiproduct W X] →           [inst_3 : Cat
egoryTheory.Limits.HasBinaryBiproduct Y Z] → (W ⟶ Y) → (X ⟶ Z) → (W ⊞ X ⟶ Y ⊞ Z)
参数：W ⟶ Y；X ⟶ Z；W ⊞ X ⟶ Y ⊞ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a pair of maps between the summands of a pair of binary biproducts,
we obtain a map between the binary biproducts.
-/
abbrev biprod.map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
  IsLimit.map (BinaryBiproduct.bicone W X).toCone (BinaryBiproduct.isLimit Y Z)
    (@mapPair _ _ (pair W X) (pair Y Z) f g)

/-- An alternative to `biprod.map` constructed via colimits.
This construction only exists in order to show it is equal to `biprod.map`. -/
/-
**CategoryTheory.Limits.biprod.map'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {W X Y Z : C} →         [
inst_2 : CategoryTheory.Limits.HasBinaryBiproduct W X] →           [inst_3 : Cat
egoryTheory.Limits.HasBinaryBiproduct Y Z] → (W ⟶ Y) → (X ⟶ Z) → (W ⊞ X ⟶ Y ⊞ Z)
参数：W ⟶ Y；X ⟶ Z；W ⊞ X ⟶ Y ⊞ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative to `biprod.map` constructed via colimits.
This construction only exists in order to show it is equal to `biprod.map`.
-/
abbrev biprod.map' {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
  IsColimit.map (BinaryBiproduct.isColimit W X) (BinaryBiproduct.bicone Y Z).toCocone
    (@mapPair _ _ (pair W X) (pair Y Z) f g)

@[ext]
/-
**CategoryTheory.Limits.biprod.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y Z : C} [inst_2 : CategoryTheory.Li
mits.HasBinaryBiproduct X Y] (f g : Z ⟶ X ⊞ Y),   CategoryTheory.CategoryStruct.
comp f CategoryTheory.Limits.biprod.fst =       CategoryTheory.CategoryStruct.co
mp g CategoryTheory.Limits.biprod.fst →     CategoryTheory.CategoryStruct.comp f
 CategoryTheory.Limits.biprod.snd =         CategoryTheory.CategoryStruct.comp g
 CategoryTheory.Limits.biprod.snd →       f = g
参数：f g : Z ⟶ X ⊞ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryFan.IsLimit.hom_ext`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.BinaryF
an X Y}   (h : CategoryTheory.Limits.…
-/
theorem biprod.hom_ext {X Y Z : C} [HasBinaryBiproduct X Y] (f g : Z ⟶ X ⊞ Y)
    (h₀ : f ≫ biprod.fst = g ≫ biprod.fst) (h₁ : f ≫ biprod.snd = g ≫ biprod.snd) : f = g :=
  BinaryFan.IsLimit.hom_ext (BinaryBiproduct.isLimit X Y) h₀ h₁

@[ext]
/-
**CategoryTheory.Limits.biprod.hom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y Z : C} [inst_2 : CategoryTheory.Li
mits.HasBinaryBiproduct X Y] (f g : X ⊞ Y ⟶ Z),   CategoryTheory.CategoryStruct.
comp CategoryTheory.Limits.biprod.inl f =       CategoryTheory.CategoryStruct.co
mp CategoryTheory.Limits.biprod.inl g →     CategoryTheory.CategoryStruct.comp C
ategoryTheory.Limits.biprod.inr f =         CategoryTheory.CategoryStruct.comp C
ategoryTheory.Limits.biprod.inr g →       f = g
参数：f g : X ⊞ Y ⟶ Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryCofan.IsColimit.hom_ext`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Bin
aryCofan X Y}   (h : CategoryTheory.Limit…
-/
theorem biprod.hom_ext' {X Y Z : C} [HasBinaryBiproduct X Y] (f g : X ⊞ Y ⟶ Z)
    (h₀ : biprod.inl ≫ f = biprod.inl ≫ g) (h₁ : biprod.inr ≫ f = biprod.inr ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (BinaryBiproduct.isColimit X Y) h₀ h₁

/-- The canonical isomorphism between the chosen biproduct and the chosen product. -/
/-
**CategoryTheory.Limits.biprod.isoProd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (X Y : C) → [inst_2 : Cat
egoryTheory.Limits.HasBinaryBiproduct X Y] → X ⊞ Y ≅ X ⨯ Y
参数：X Y : C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.hasLimit_pair`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…

--- 原说明 ---
The canonical isomorphism between the chosen biproduct and the chosen product.
-/
def biprod.isoProd (X Y : C) [HasBinaryBiproduct X Y] : X ⊞ Y ≅ X ⨯ Y :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit X Y) (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.biprod.isoProd_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   (CategoryTheory.Limits.biprod.isoProd X Y).hom =  
   CategoryTheory.Limits.prod.lift CategoryTheory.Limits.biprod.fst CategoryTheo
ry.Limits.biprod.snd
参数：CategoryTheory.Limits.biprod.isoProd X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.hasLimit_pair`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
theorem biprod.isoProd_hom {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoProd X Y).hom = prod.lift biprod.fst biprod.snd := by
      ext <;> simp [biprod.isoProd]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.biprod.isoProd_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   (CategoryTheory.Limits.biprod.isoProd X Y).inv =  
   CategoryTheory.Limits.biprod.lift CategoryTheory.Limits.prod.fst CategoryTheo
ry.Limits.prod.snd
参数：CategoryTheory.Limits.biprod.isoProd X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.hasLimit_pair`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.biprod.isoProd_hom`：∀ {C : Type uC} [inst : Catego
ryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
theorem biprod.isoProd_inv {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoProd X Y).inv = biprod.lift prod.fst prod.snd := by
  ext <;> simp [Iso.inv_comp_eq]

/-- The canonical isomorphism between the chosen biproduct and the chosen coproduct. -/
/-
**CategoryTheory.Limits.biprod.isoCoprod** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (X Y : C) → [inst_2 : Cat
egoryTheory.Limits.HasBinaryBiproduct X Y] → X ⊞ Y ≅ X ⨿ Y
参数：X Y : C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.hasColimit_pair`：∀ {C : Type uC
} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {P Q : C} [CategoryTheory…

--- 原说明 ---
The canonical isomorphism between the chosen biproduct and the chosen coproduct.
-/
def biprod.isoCoprod (X Y : C) [HasBinaryBiproduct X Y] : X ⊞ Y ≅ X ⨿ Y :=
  IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.biprod.isoCoprod_inv** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   (CategoryTheory.Limits.biprod.isoCoprod X Y).inv =
     CategoryTheory.Limits.coprod.desc CategoryTheory.Limits.biprod.inl Category
Theory.Limits.biprod.inr
参数：CategoryTheory.Limits.biprod.isoCoprod X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.hasColimit_pair`：∀ {C : Type uC
} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {P Q : C} [CategoryTheory…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.colimit.comp_coconePointUniqueUpToIso_inv`：∀ {J : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Cate
goryTheory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
theorem biprod.isoCoprod_inv {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoCoprod X Y).inv = coprod.desc biprod.inl biprod.inr := by
  ext <;> simp [biprod.isoCoprod]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.biprod_isoCoprod_hom** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：biprod_isoCoprod_hom {X Y : C} [HasBinaryBiproduct X Y] : (biprod.isoCopro
d X Y).hom = biprod.desc coprod.inl coprod.inr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.hasColimit_pair`：∀ {C : Type uC
} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {P Q : C} [CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.isoCoprod_inv`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
theorem biprod_isoCoprod_hom {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoCoprod X Y).hom = biprod.desc coprod.inl coprod.inr := by
  ext <;> simp [← Iso.eq_comp_inv]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.biprod.map_eq_map'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y Z : C} [inst_2 : CategoryTheory.
Limits.HasBinaryBiproduct W X]   [inst_3 : CategoryTheory.Limits.HasBinaryBiprod
uct Y Z] (f : W ⟶ Y) (g : X ⟶ Z),   CategoryTheory.Limits.biprod.map f g = Categ
oryTheory.Limits.biprod.map' f g
参数：f : W ⟶ Y；g : X ⟶ Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsLimit.map_π`：map_π {F G : J ⥤ C} (c : Cone F) {d
 : Cone G} (hd : IsLimit d) (α : F ⟶ G) (j : J) : hd.map c α ≫ d.π.app j = c.π.a
pp j ≫ α.app j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.IsColimit.ι_map`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, 
u₃} C]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
theorem biprod.map_eq_map' {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z]
    (f : W ⟶ Y) (g : X ⟶ Z) : biprod.map f g = biprod.map' f g := by
  ext
  · simp only [mapPair_left, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_left, ←
      BinaryBicone.toCocone_ι_app_left]
    simp
  · simp only [mapPair_left, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_right, ←
      BinaryBicone.toCocone_ι_app_left]
    simp
  · simp only [mapPair_right, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_left, ←
      BinaryBicone.toCocone_ι_app_right]
    simp
  · simp only [mapPair_right, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_right, ←
      BinaryBicone.toCocone_ι_app_right]
    simp
/-
**CategoryTheory.Limits.biprod.inl_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   CategoryTheory.IsSplitMono CategoryTheory.Limits.b
iprod.inl
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitMono.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {X Y : C} {f : Y ⟶ X} (se : CategoryTheory.SplitMono f),   C
ategoryTheory.IsSpli…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance biprod.inl_mono {X Y : C} [HasBinaryBiproduct X Y] :
    IsSplitMono (biprod.inl : X ⟶ X ⊞ Y) :=
  IsSplitMono.mk' { retraction := biprod.fst }
/-
**CategoryTheory.Limits.biprod.inr_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   CategoryTheory.IsSplitMono CategoryTheory.Limits.b
iprod.inr
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitMono.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {X Y : C} {f : Y ⟶ X} (se : CategoryTheory.SplitMono f),   C
ategoryTheory.IsSpli…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance biprod.inr_mono {X Y : C} [HasBinaryBiproduct X Y] :
    IsSplitMono (biprod.inr : Y ⟶ X ⊞ Y) :=
  IsSplitMono.mk' { retraction := biprod.snd }
/-
**CategoryTheory.Limits.biprod.fst_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   CategoryTheory.IsSplitEpi CategoryTheory.Limits.bi
prod.fst
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitEpi.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (se : CategoryTheory.SplitEpi f),   Cat
egoryTheory.IsSplit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance biprod.fst_epi {X Y : C} [HasBinaryBiproduct X Y] : IsSplitEpi (biprod.fst : X ⊞ Y ⟶ X) :=
  IsSplitEpi.mk' { section_ := biprod.inl }
/-
**CategoryTheory.Limits.biprod.snd_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   CategoryTheory.IsSplitEpi CategoryTheory.Limits.bi
prod.snd
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitEpi.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (se : CategoryTheory.SplitEpi f),   Cat
egoryTheory.IsSplit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance biprod.snd_epi {X Y : C} [HasBinaryBiproduct X Y] : IsSplitEpi (biprod.snd : X ⊞ Y ⟶ Y) :=
  IsSplitEpi.mk' { section_ := biprod.inr }

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.map_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y Z : C} [inst_2 : CategoryTheory.
Limits.HasBinaryBiproduct W X]   [inst_3 : CategoryTheory.Limits.HasBinaryBiprod
uct Y Z] (f : W ⟶ Y) (g : X ⟶ Z),   CategoryTheory.CategoryStruct.comp (Category
Theory.Limits.biprod.map f g) CategoryTheory.Limits.biprod.fst =     CategoryThe
ory.CategoryStruct.comp CategoryTheory.Limits.biprod.fst f
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.biprod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.map_π`：map_π {F G : J ⥤ C} (c : Cone F) {d
 : Cone G} (hd : IsLimit d) (α : F ⟶ G) (j : J) : hd.map c α ≫ d.π.app j = c.π.a
pp j ≫ α.app j
-/
theorem biprod.map_fst {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.map f g ≫ biprod.fst = biprod.fst ≫ f :=
  IsLimit.map_π _ _ _ (⟨WalkingPair.left⟩ : Discrete WalkingPair)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.map_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y Z : C} [inst_2 : CategoryTheory.
Limits.HasBinaryBiproduct W X]   [inst_3 : CategoryTheory.Limits.HasBinaryBiprod
uct Y Z] (f : W ⟶ Y) (g : X ⟶ Z),   CategoryTheory.CategoryStruct.comp (Category
Theory.Limits.biprod.map f g) CategoryTheory.Limits.biprod.snd =     CategoryThe
ory.CategoryStruct.comp CategoryTheory.Limits.biprod.snd g
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.biprod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.map_π`：map_π {F G : J ⥤ C} (c : Cone F) {d
 : Cone G} (hd : IsLimit d) (α : F ⟶ G) (j : J) : hd.map c α ≫ d.π.app j = c.π.a
pp j ≫ α.app j
-/
theorem biprod.map_snd {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.map f g ≫ biprod.snd = biprod.snd ≫ g :=
  IsLimit.map_π _ _ _ (⟨WalkingPair.right⟩ : Discrete WalkingPair)

-- Because `biprod.map` is defined in terms of `lim` rather than `colim`,
-- we need to provide additional `simp` lemmas.
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.inl_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y Z : C} [inst_2 : CategoryTheory.
Limits.HasBinaryBiproduct W X]   [inst_3 : CategoryTheory.Limits.HasBinaryBiprod
uct Y Z] (f : W ⟶ Y) (g : X ⟶ Z),   CategoryTheory.CategoryStruct.comp CategoryT
heory.Limits.biprod.inl (CategoryTheory.Limits.biprod.map f g) =     CategoryThe
ory.CategoryStruct.comp f CategoryTheory.Limits.biprod.inl
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.biprod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.map_eq_map'`：∀ {C : Type uC} [inst : Catego
ryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.IsColimit.ι_map`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, 
u₃} C]   {F G : CategoryThe…
-/
theorem biprod.inl_map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.inl ≫ biprod.map f g = f ≫ biprod.inl := by
  rw [biprod.map_eq_map']
  exact IsColimit.ι_map (BinaryBiproduct.isColimit W X) _ _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.inr_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y Z : C} [inst_2 : CategoryTheory.
Limits.HasBinaryBiproduct W X]   [inst_3 : CategoryTheory.Limits.HasBinaryBiprod
uct Y Z] (f : W ⟶ Y) (g : X ⟶ Z),   CategoryTheory.CategoryStruct.comp CategoryT
heory.Limits.biprod.inr (CategoryTheory.Limits.biprod.map f g) =     CategoryThe
ory.CategoryStruct.comp g CategoryTheory.Limits.biprod.inr
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.biprod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.map_eq_map'`：∀ {C : Type uC} [inst : Catego
ryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.IsColimit.ι_map`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, 
u₃} C]   {F G : CategoryThe…
-/
theorem biprod.inr_map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.inr ≫ biprod.map f g = g ≫ biprod.inr := by
  rw [biprod.map_eq_map']
  exact IsColimit.ι_map (BinaryBiproduct.isColimit W X) _ _ ⟨WalkingPair.right⟩

/-- Given a pair of isomorphisms between the summands of a pair of binary biproducts,
we obtain an isomorphism between the binary biproducts. -/
@[simps]
/-
**CategoryTheory.Limits.biprod.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {W X Y Z : C} →         [
inst_2 : CategoryTheory.Limits.HasBinaryBiproduct W X] →           [inst_3 : Cat
egoryTheory.Limits.HasBinaryBiproduct Y Z] → (W ≅ Y) → (X ≅ Z) → (W ⊞ X ≅ Y ⊞ Z)
参数：W ≅ Y；X ≅ Z；W ⊞ X ≅ Y ⊞ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a pair of isomorphisms between the summands of a pair of binary biproducts
,
we obtain an isomorphism between the binary biproducts.
-/
def biprod.mapIso {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⊞ X ≅ Y ⊞ Z where
  hom := biprod.map f.hom g.hom
  inv := biprod.map f.inv g.inv

/-- Auxiliary lemma for `biprod.uniqueUpToIso`. -/
/-
**CategoryTheory.Limits.biprod.conePointUniqueUpToIso_hom** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   (X Y : C) [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y] {b : CategoryTheory.Limits.BinaryBicone X Y}   (hb : 
b.IsBilimit),   (hb.isLimit.conePointUniqueUpToIso (CategoryTheory.Limits.Binary
Biproduct.isLimit X Y)).hom =     CategoryTheory.Limits.biprod.lift b.fst b.snd
参数：X Y : C；hb : b.IsBilimit；hb.isLimit.conePointUniqueUpToIso (CategoryTheory.Li
mits.BinaryBiproduct.isLimit X Y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for `biprod.uniqueUpToIso`.
-/
theorem biprod.conePointUniqueUpToIso_hom (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)).hom =
      biprod.lift b.fst b.snd := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary lemma for `biprod.uniqueUpToIso`. -/
/-
**CategoryTheory.Limits.biprod.conePointUniqueUpToIso_inv** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   (X Y : C) [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y] {b : CategoryTheory.Limits.BinaryBicone X Y}   (hb : 
b.IsBilimit),   (hb.isLimit.conePointUniqueUpToIso (CategoryTheory.Limits.Binary
Biproduct.isLimit X Y)).inv =     CategoryTheory.Limits.biprod.desc b.inl b.inr
参数：X Y : C；hb : b.IsBilimit；hb.isLimit.conePointUniqueUpToIso (CategoryTheory.Li
mits.BinaryBiproduct.isLimit X Y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…

--- 原说明 ---
Auxiliary lemma for `biprod.uniqueUpToIso`.
-/
theorem biprod.conePointUniqueUpToIso_inv (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)).inv =
      biprod.desc b.inl b.inr := by
  refine biprod.hom_ext' _ _ (hb.isLimit.hom_ext fun j => ?_) (hb.isLimit.hom_ext fun j => ?_)
  all_goals
    simp only [Category.assoc, IsLimit.conePointUniqueUpToIso_inv_comp]
    rcases j with ⟨⟨⟩⟩
  all_goals simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Binary biproducts are unique up to isomorphism. This already follows because bilimits are
limits, but in the case of biproducts we can give an isomorphism with particularly nice
definitional properties, namely that `biprod.lift b.fst b.snd` and `biprod.desc b.inl b.inr`
are inverses of each other. -/
@[simps]
/-
**CategoryTheory.Limits.biprod.uniqueUpToIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (X Y : C) →         [inst
_2 : CategoryTheory.Limits.HasBinaryBiproduct X Y] →           {b : CategoryTheo
ry.Limits.BinaryBicone X Y} → b.IsBilimit → (b.pt ≅ X ⊞ Y)
参数：X Y : C；b.pt ≅ X ⊞ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Binary biproducts are unique up to isomorphism. This already follows because bil
imits are
limits, but in the case of biproducts we can give an isomorphism with particular
ly nice
definitional properties, namely that `biprod.lift b.fst b.snd` and `biprod.desc 
b.inl b.inr`
are inverses of each other.
-/
def biprod.uniqueUpToIso (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) : b.pt ≅ X ⊞ Y where
  hom := biprod.lift b.fst b.snd
  inv := biprod.desc b.inl b.inr
  hom_inv_id := by
    rw [← biprod.conePointUniqueUpToIso_hom X Y hb, ←
      biprod.conePointUniqueUpToIso_inv X Y hb, Iso.hom_inv_id]
  inv_hom_id := by
    rw [← biprod.conePointUniqueUpToIso_hom X Y hb, ←
      biprod.conePointUniqueUpToIso_inv X Y hb, Iso.inv_hom_id]

-- There are three further variations,
-- about `IsIso biprod.inr`, `IsIso biprod.fst` and `IsIso biprod.snd`,
-- but any one suffices to prove `indecomposable_of_simple`
-- and they are likely not separately useful.
/-
**CategoryTheory.Limits.biprod.isIso_inl_iff_id_eq_fst_comp_inl** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   (X Y : C) [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct X Y],   CategoryTheory.IsIso CategoryTheory.Limits.biprod.
inl ↔     CategoryTheory.CategoryStruct.id (X ⊞ Y) =       CategoryTheory.Catego
ryStruct.comp CategoryTheory.Limits.biprod.fst CategoryTheory.Limits.biprod.inl
参数：X Y : C；X ⊞ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Limits.biprod.inl_fst`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem biprod.isIso_inl_iff_id_eq_fst_comp_inl (X Y : C) [HasBinaryBiproduct X Y] :
    IsIso (biprod.inl : X ⟶ X ⊞ Y) ↔ 𝟙 (X ⊞ Y) = biprod.fst ≫ biprod.inl := by
  constructor
  · intro h
    have := (cancel_epi (inv biprod.inl : X ⊞ Y ⟶ X)).2 <| @biprod.inl_fst _ _ _ X Y _
    rw [IsIso.inv_hom_id_assoc, Category.comp_id] at this
    rw [this, IsIso.inv_hom_id]
  · intro h
    exact ⟨⟨biprod.fst, biprod.inl_fst, h.symm⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.biprod.map_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [
CategoryTheory.Epi f] [CategoryTheory.Epi g]   [inst_4 : CategoryTheory.Limits.H
asBinaryBiproduct W X] [inst_5 : CategoryTheory.Limits.HasBinaryBiproduct Y Z], 
  CategoryTheory.Epi (CategoryTheory.Limits.biprod.map f g)
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.biprod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.hasColimit_pair`：∀ {C : Type uC
} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {P Q : C} [CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biprod_isoCoprod_hom`：biprod_isoCoprod_hom {X Y : 
C} [HasBinaryBiproduct X Y] : (biprod.isoCoprod X Y).hom = biprod.desc coprod.in
l coprod.inr
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.biprod.isoCoprod_inv`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.biprod.inl_map`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.biprod.inr_map`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.coprod.map_epi`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)   [CategoryTh
eory.Epi f] [CategoryTheor…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance biprod.map_epi {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
    [Epi g] [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] : Epi (biprod.map f g) := by
  rw [show biprod.map f g =
    (biprod.isoCoprod _ _).hom ≫ coprod.map f g ≫ (biprod.isoCoprod _ _).inv by aesop]
  infer_instance
/-
**CategoryTheory.Limits.prod.map_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.prod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [
CategoryTheory.Epi f] [CategoryTheory.Epi g]   [inst_4 : CategoryTheory.Limits.H
asBinaryBiproduct W X] [inst_5 : CategoryTheory.Limits.HasBinaryBiproduct Y Z], 
  CategoryTheory.Epi (CategoryTheory.Limits.prod.map f g)
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.hasLimit_pair`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biprod.isoProd_inv`：∀ {C : Type uC} [inst : Catego
ryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.biprod.isoProd_hom`：∀ {C : Type uC} [inst : Catego
ryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.biprod.map_fst`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.biprod.map_snd`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.lift_fst_comp_snd_comp`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Lim
its.HasBinaryProduct W Y] [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.biprod.map_epi`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} (f : W ⟶ Y)…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance prod.map_epi {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
    [Epi g] [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] : Epi (prod.map f g) := by
  rw [show prod.map f g = (biprod.isoProd _ _).inv ≫ biprod.map f g ≫
    (biprod.isoProd _ _).hom by simp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.biprod.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [
CategoryTheory.Mono f] [CategoryTheory.Mono g]   [inst_4 : CategoryTheory.Limits
.HasBinaryBiproduct W X] [inst_5 : CategoryTheory.Limits.HasBinaryBiproduct Y Z]
,   CategoryTheory.Mono (CategoryTheory.Limits.biprod.map f g)
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.biprod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.hasLimit_pair`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biprod.isoProd_hom`：∀ {C : Type uC} [inst : Catego
ryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.biprod.isoProd_inv`：∀ {C : Type uC} [inst : Catego
ryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.prod.lift_map_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Ha
sBinaryProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.biprod.inl_map`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.biprod.inr_map`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
（共 35 条，此处仅展示前 30 条）
-/
instance biprod.map_mono {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
    [Mono g] [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] : Mono (biprod.map f g) := by
  rw [show biprod.map f g = (biprod.isoProd _ _).hom ≫ prod.map f g ≫
    (biprod.isoProd _ _).inv by aesop]
  infer_instance
/-
**CategoryTheory.Limits.coprod.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.coprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [
CategoryTheory.Mono f] [CategoryTheory.Mono g]   [inst_4 : CategoryTheory.Limits
.HasBinaryBiproduct W X] [inst_5 : CategoryTheory.Limits.HasBinaryBiproduct Y Z]
,   CategoryTheory.Mono (CategoryTheory.Limits.coprod.map f g)
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.coprod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.hasColimit_pair`：∀ {C : Type uC
} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {P Q : C} [CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biprod.isoCoprod_inv`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.biprod_isoCoprod_hom`：biprod_isoCoprod_hom {X Y : 
C} [HasBinaryBiproduct X Y] : (biprod.isoCoprod X Y).hom = biprod.desc coprod.in
l coprod.inr
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.Limits.biprod.inl_map_assoc`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.inr_map_assoc`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp_inl_comp_inr`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.L
imits.HasBinaryCoproduct W Y] [inst_2 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.biprod.map_mono`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y Z : C} (f : W ⟶ Y)…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance coprod.map_mono {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
    [Mono g] [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] : Mono (coprod.map f g) := by
  rw [show coprod.map f g = (biprod.isoCoprod _ _).inv ≫ biprod.map f g ≫
    (biprod.isoCoprod _ _).hom by simp]
  infer_instance

section BiprodKernel

section BinaryBicone

variable {X Y : C} (c : BinaryBicone X Y)

/-- A kernel fork for the kernel of `BinaryBicone.fst`. It consists of the morphism
`BinaryBicone.inr`. -/
/-
**CategoryTheory.Limits.BinaryBicone.fstKernelFork** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} → (c : Category
Theory.Limits.BinaryBicone X Y) → CategoryTheory.Limits.KernelFork c.fst
参数：c : CategoryTheory.Limits.BinaryBicone X Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…

--- 原说明 ---
A kernel fork for the kernel of `BinaryBicone.fst`. It consists of the morphism
`BinaryBicone.inr`.
-/
def BinaryBicone.fstKernelFork : KernelFork c.fst :=
  KernelFork.ofι c.inr c.inr_fst

@[simp]
/-
**CategoryTheory.Limits.BinaryBicone.fstKernelFork_** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BinaryBicone.fstKernelFork_ι : (BinaryBicone.fstKernelFork c).ι = c.inr := rfl

/-- A kernel fork for the kernel of `BinaryBicone.snd`. It consists of the morphism
`BinaryBicone.inl`. -/
/-
**CategoryTheory.Limits.BinaryBicone.sndKernelFork** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} → (c : Category
Theory.Limits.BinaryBicone X Y) → CategoryTheory.Limits.KernelFork c.snd
参数：c : CategoryTheory.Limits.BinaryBicone X Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…

--- 原说明 ---
A kernel fork for the kernel of `BinaryBicone.snd`. It consists of the morphism
`BinaryBicone.inl`.
-/
def BinaryBicone.sndKernelFork : KernelFork c.snd :=
  KernelFork.ofι c.inl c.inl_snd

@[simp]
/-
**CategoryTheory.Limits.BinaryBicone.sndKernelFork_** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BinaryBicone.sndKernelFork_ι : (BinaryBicone.sndKernelFork c).ι = c.inl := rfl

/-- A cokernel cofork for the cokernel of `BinaryBicone.inl`. It consists of the morphism
`BinaryBicone.snd`. -/
/-
**CategoryTheory.Limits.BinaryBicone.inlCokernelCofork** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} → (c : Category
Theory.Limits.BinaryBicone X Y) → CategoryTheory.Limits.CokernelCofork c.inl
参数：c : CategoryTheory.Limits.BinaryBicone X Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…

--- 原说明 ---
A cokernel cofork for the cokernel of `BinaryBicone.inl`. It consists of the mor
phism
`BinaryBicone.snd`.
-/
def BinaryBicone.inlCokernelCofork : CokernelCofork c.inl :=
  CokernelCofork.ofπ c.snd c.inl_snd

@[simp]
/-
**CategoryTheory.Limits.BinaryBicone.inlCokernelCofork_** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BinaryBicone.inlCokernelCofork_π : (BinaryBicone.inlCokernelCofork c).π = c.snd := rfl

/-- A cokernel cofork for the cokernel of `BinaryBicone.inr`. It consists of the morphism
`BinaryBicone.fst`. -/
/-
**CategoryTheory.Limits.BinaryBicone.inrCokernelCofork** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} → (c : Category
Theory.Limits.BinaryBicone X Y) → CategoryTheory.Limits.CokernelCofork c.inr
参数：c : CategoryTheory.Limits.BinaryBicone X Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…

--- 原说明 ---
A cokernel cofork for the cokernel of `BinaryBicone.inr`. It consists of the mor
phism
`BinaryBicone.fst`.
-/
def BinaryBicone.inrCokernelCofork : CokernelCofork c.inr :=
  CokernelCofork.ofπ c.fst c.inr_fst

@[simp]
/-
**CategoryTheory.Limits.BinaryBicone.inrCokernelCofork_** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BinaryBicone.inrCokernelCofork_π : (BinaryBicone.inrCokernelCofork c).π = c.fst := rfl

variable {c}

set_option backward.isDefEq.respectTransparency false in
/-- The fork defined in `BinaryBicone.fstKernelFork` is indeed a kernel. -/
/-
**CategoryTheory.Limits.BinaryBicone.isLimitFstKernelFork** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         {c : 
CategoryTheory.Limits.BinaryBicone X Y} →           CategoryTheory.Limits.IsLimi
t c.toCone → CategoryTheory.Limits.IsLimit c.fstKernelFork
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fork defined in `BinaryBicone.fstKernelFork` is indeed a kernel.
-/
def BinaryBicone.isLimitFstKernelFork (i : IsLimit c.toCone) : IsLimit c.fstKernelFork :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ c.snd, by apply BinaryFan.IsLimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The fork defined in `BinaryBicone.sndKernelFork` is indeed a kernel. -/
/-
**CategoryTheory.Limits.BinaryBicone.isLimitSndKernelFork** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         {c : 
CategoryTheory.Limits.BinaryBicone X Y} →           CategoryTheory.Limits.IsLimi
t c.toCone → CategoryTheory.Limits.IsLimit c.sndKernelFork
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fork defined in `BinaryBicone.sndKernelFork` is indeed a kernel.
-/
def BinaryBicone.isLimitSndKernelFork (i : IsLimit c.toCone) : IsLimit c.sndKernelFork :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ c.fst, by apply BinaryFan.IsLimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The cofork defined in `BinaryBicone.inlCokernelCofork` is indeed a cokernel. -/
/-
**CategoryTheory.Limits.BinaryBicone.isColimitInlCokernelCofork** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         {c : 
CategoryTheory.Limits.BinaryBicone X Y} →           CategoryTheory.Limits.IsColi
mit c.toCocone → CategoryTheory.Limits.IsColimit c.inlCokernelCofork
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofork defined in `BinaryBicone.inlCokernelCofork` is indeed a cokernel.
-/
def BinaryBicone.isColimitInlCokernelCofork (i : IsColimit c.toCocone) :
    IsColimit c.inlCokernelCofork :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨c.inr ≫ s.π, by apply BinaryCofan.IsColimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The cofork defined in `BinaryBicone.inrCokernelCofork` is indeed a cokernel. -/
/-
**CategoryTheory.Limits.BinaryBicone.isColimitInrCokernelCofork** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         {c : 
CategoryTheory.Limits.BinaryBicone X Y} →           CategoryTheory.Limits.IsColi
mit c.toCocone → CategoryTheory.Limits.IsColimit c.inrCokernelCofork
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofork defined in `BinaryBicone.inrCokernelCofork` is indeed a cokernel.
-/
def BinaryBicone.isColimitInrCokernelCofork (i : IsColimit c.toCocone) :
    IsColimit c.inrCokernelCofork :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨c.inl ≫ s.π, by apply BinaryCofan.IsColimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

end BinaryBicone

section HasBinaryBiproduct

variable (X Y : C) [HasBinaryBiproduct X Y]

/-- A kernel fork for the kernel of `biprod.fst`. It consists of the
morphism `biprod.inr`. -/
/-
**CategoryTheory.Limits.biprod.fstKernelFork** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (X Y : C) →         [inst
_2 : CategoryTheory.Limits.HasBinaryBiproduct X Y] →           CategoryTheory.Li
mits.KernelFork CategoryTheory.Limits.biprod.fst
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A kernel fork for the kernel of `biprod.fst`. It consists of the
morphism `biprod.inr`.
-/
def biprod.fstKernelFork : KernelFork (biprod.fst : X ⊞ Y ⟶ X) :=
  BinaryBicone.fstKernelFork _

@[simp]
/-
**CategoryTheory.Limits.biprod.fstKernelFork_** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biprod.fstKernelFork_ι : Fork.ι (biprod.fstKernelFork X Y) = (biprod.inr : Y ⟶ X ⊞ Y) :=
  rfl

/-- The fork `biprod.fstKernelFork` is indeed a limit. -/
/-
**CategoryTheory.Limits.biprod.isKernelFstKernelFork** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (X Y : C) →         [inst
_2 : CategoryTheory.Limits.HasBinaryBiproduct X Y] →           CategoryTheory.Li
mits.IsLimit (CategoryTheory.Limits.biprod.fstKernelFork X Y)
参数：X Y : C；CategoryTheory.Limits.biprod.fstKernelFork X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fork `biprod.fstKernelFork` is indeed a limit.
-/
def biprod.isKernelFstKernelFork : IsLimit (biprod.fstKernelFork X Y) :=
  BinaryBicone.isLimitFstKernelFork (BinaryBiproduct.isLimit _ _)

/-- A kernel fork for the kernel of `biprod.snd`. It consists of the
morphism `biprod.inl`. -/
/-
**CategoryTheory.Limits.biprod.sndKernelFork** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (X Y : C) →         [inst
_2 : CategoryTheory.Limits.HasBinaryBiproduct X Y] →           CategoryTheory.Li
mits.KernelFork CategoryTheory.Limits.biprod.snd
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A kernel fork for the kernel of `biprod.snd`. It consists of the
morphism `biprod.inl`.
-/
def biprod.sndKernelFork : KernelFork (biprod.snd : X ⊞ Y ⟶ Y) :=
  BinaryBicone.sndKernelFork _

@[simp]
/-
**CategoryTheory.Limits.biprod.sndKernelFork_** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biprod.sndKernelFork_ι : Fork.ι (biprod.sndKernelFork X Y) = (biprod.inl : X ⟶ X ⊞ Y) :=
  rfl

/-- The fork `biprod.sndKernelFork` is indeed a limit. -/
/-
**CategoryTheory.Limits.biprod.isKernelSndKernelFork** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (X Y : C) →         [inst
_2 : CategoryTheory.Limits.HasBinaryBiproduct X Y] →           CategoryTheory.Li
mits.IsLimit (CategoryTheory.Limits.biprod.sndKernelFork X Y)
参数：X Y : C；CategoryTheory.Limits.biprod.sndKernelFork X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fork `biprod.sndKernelFork` is indeed a limit.
-/
def biprod.isKernelSndKernelFork : IsLimit (biprod.sndKernelFork X Y) :=
  BinaryBicone.isLimitSndKernelFork (BinaryBiproduct.isLimit _ _)

/-- A cokernel cofork for the cokernel of `biprod.inl`. It consists of the
morphism `biprod.snd`. -/
/-
**CategoryTheory.Limits.biprod.inlCokernelCofork** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (X Y : C) →         [inst
_2 : CategoryTheory.Limits.HasBinaryBiproduct X Y] →           CategoryTheory.Li
mits.CokernelCofork CategoryTheory.Limits.biprod.inl
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cokernel cofork for the cokernel of `biprod.inl`. It consists of the
morphism `biprod.snd`.
-/
def biprod.inlCokernelCofork : CokernelCofork (biprod.inl : X ⟶ X ⊞ Y) :=
  BinaryBicone.inlCokernelCofork _

@[simp]
/-
**CategoryTheory.Limits.biprod.inlCokernelCofork_** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biprod.inlCokernelCofork_π : Cofork.π (biprod.inlCokernelCofork X Y) = biprod.snd :=
  rfl

/-- The cofork `biprod.inlCokernelFork` is indeed a colimit. -/
/-
**CategoryTheory.Limits.biprod.isCokernelInlCokernelFork** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (X Y : C) →         [inst
_2 : CategoryTheory.Limits.HasBinaryBiproduct X Y] →           CategoryTheory.Li
mits.IsColimit (CategoryTheory.Limits.biprod.inlCokernelCofork X Y)
参数：X Y : C；CategoryTheory.Limits.biprod.inlCokernelCofork X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofork `biprod.inlCokernelFork` is indeed a colimit.
-/
def biprod.isCokernelInlCokernelFork : IsColimit (biprod.inlCokernelCofork X Y) :=
  BinaryBicone.isColimitInlCokernelCofork (BinaryBiproduct.isColimit _ _)

/-- A cokernel cofork for the cokernel of `biprod.inr`. It consists of the
morphism `biprod.fst`. -/
/-
**CategoryTheory.Limits.biprod.inrCokernelCofork** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (X Y : C) →         [inst
_2 : CategoryTheory.Limits.HasBinaryBiproduct X Y] →           CategoryTheory.Li
mits.CokernelCofork CategoryTheory.Limits.biprod.inr
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cokernel cofork for the cokernel of `biprod.inr`. It consists of the
morphism `biprod.fst`.
-/
def biprod.inrCokernelCofork : CokernelCofork (biprod.inr : Y ⟶ X ⊞ Y) :=
  BinaryBicone.inrCokernelCofork _

@[simp]
/-
**CategoryTheory.Limits.biprod.inrCokernelCofork_** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biprod.inrCokernelCofork_π : Cofork.π (biprod.inrCokernelCofork X Y) = biprod.fst :=
  rfl

/-- The cofork `biprod.inrCokernelFork` is indeed a colimit. -/
/-
**CategoryTheory.Limits.biprod.isCokernelInrCokernelFork** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (X Y : C) →         [inst
_2 : CategoryTheory.Limits.HasBinaryBiproduct X Y] →           CategoryTheory.Li
mits.IsColimit (CategoryTheory.Limits.biprod.inrCokernelCofork X Y)
参数：X Y : C；CategoryTheory.Limits.biprod.inrCokernelCofork X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofork `biprod.inrCokernelFork` is indeed a colimit.
-/
def biprod.isCokernelInrCokernelFork : IsColimit (biprod.inrCokernelCofork X Y) :=
  BinaryBicone.isColimitInrCokernelCofork (BinaryBiproduct.isColimit _ _)

section

variable (P Q) [HasBinaryBiproduct P Q]

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism `op (P ⊞ Q) ≅ op P ⊞ op Q`. -/
/-
**CategoryTheory.Limits.biprod.opIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       (P Q : C) →         [inst
_2 : CategoryTheory.Limits.HasBinaryBiproduct P Q] → Opposite.op (P ⊞ Q) ≅ Oppos
ite.op P ⊞ Opposite.op Q
参数：P Q : C；P ⊞ Q。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasBinaryBiproductOppositeOp`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…

--- 原说明 ---
The isomorphism `op (P ⊞ Q) ≅ op P ⊞ op Q`.
-/
def biprod.opIso : op (P ⊞ Q) ≅ op P ⊞ op Q :=
  biprod.uniqueUpToIso _ _ (getBinaryBiproductData P Q).op.isBilimit

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.opIso_hom_fst** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   (P Q : C) [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct P Q],   CategoryTheory.CategoryStruct.comp (CategoryTheory
.Limits.biprod.opIso P Q).hom CategoryTheory.Limits.biprod.fst =     CategoryThe
ory.Limits.biprod.inl.op
参数：P Q : C；CategoryTheory.Limits.biprod.opIso P Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.instHasBinaryBiproductOppositeOp`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…
-/
lemma biprod.opIso_hom_fst : (opIso P Q).hom ≫ fst = inl.op := lift_fst _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.opIso_hom_snd** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   (P Q : C) [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct P Q],   CategoryTheory.CategoryStruct.comp (CategoryTheory
.Limits.biprod.opIso P Q).hom CategoryTheory.Limits.biprod.snd =     CategoryThe
ory.Limits.biprod.inr.op
参数：P Q : C；CategoryTheory.Limits.biprod.opIso P Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.instHasBinaryBiproductOppositeOp`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…
-/
lemma biprod.opIso_hom_snd : (opIso P Q).hom ≫ snd = inr.op := lift_snd _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.inl_opIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   (P Q : C) [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct P Q],   CategoryTheory.CategoryStruct.comp CategoryTheory.
Limits.biprod.inl (CategoryTheory.Limits.biprod.opIso P Q).inv =     CategoryThe
ory.Limits.biprod.fst.op
参数：P Q : C；CategoryTheory.Limits.biprod.opIso P Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.instHasBinaryBiproductOppositeOp`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…
-/
lemma biprod.inl_opIso_inv : inl ≫ (opIso P Q).inv = fst.op := inl_desc _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.inr_opIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   (P Q : C) [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct P Q],   CategoryTheory.CategoryStruct.comp CategoryTheory.
Limits.biprod.inr (CategoryTheory.Limits.biprod.opIso P Q).inv =     CategoryThe
ory.Limits.biprod.snd.op
参数：P Q : C；CategoryTheory.Limits.biprod.opIso P Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.instHasBinaryBiproductOppositeOp`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…
-/
lemma biprod.inr_opIso_inv : inr ≫ (opIso P Q).inv = snd.op := inr_desc _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.fst_op_opIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   (P Q : C) [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct P Q],   CategoryTheory.CategoryStruct.comp CategoryTheory.
Limits.biprod.fst.op (CategoryTheory.Limits.biprod.opIso P Q).hom =     Category
Theory.Limits.biprod.inl
参数：P Q : C；CategoryTheory.Limits.biprod.opIso P Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.instHasBinaryBiproductOppositeOp`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.opIso_hom_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   (P Q : C) [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.opIso_hom_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   (P Q : C) [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
lemma biprod.fst_op_opIso_hom : fst.op ≫ (opIso P Q).hom = inl := by
  ext <;> simp [← op_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.snd_op_opIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   (P Q : C) [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct P Q],   CategoryTheory.CategoryStruct.comp CategoryTheory.
Limits.biprod.snd.op (CategoryTheory.Limits.biprod.opIso P Q).hom =     Category
Theory.Limits.biprod.inr
参数：P Q : C；CategoryTheory.Limits.biprod.opIso P Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.instHasBinaryBiproductOppositeOp`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.opIso_hom_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   (P Q : C) [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.opIso_hom_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   (P Q : C) [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
lemma biprod.snd_op_opIso_hom : snd.op ≫ (opIso P Q).hom = inr := by
  ext <;> simp [← op_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.opIso_inv_inl_op** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   (P Q : C) [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct P Q],   CategoryTheory.CategoryStruct.comp (CategoryTheory
.Limits.biprod.opIso P Q).inv CategoryTheory.Limits.biprod.inl.op =     Category
Theory.Limits.biprod.fst
参数：P Q : C；CategoryTheory.Limits.biprod.opIso P Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.instHasBinaryBiproductOppositeOp`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.inl_opIso_inv_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   (P Q : C) [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.inr_opIso_inv_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   (P Q : C) [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
lemma biprod.opIso_inv_inl_op : (opIso P Q).inv ≫ inl.op = fst := by
  ext <;> simp [← op_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.opIso_inv_inr_op** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   (P Q : C) [inst_2 : CategoryTheory.Limi
ts.HasBinaryBiproduct P Q],   CategoryTheory.CategoryStruct.comp (CategoryTheory
.Limits.biprod.opIso P Q).inv CategoryTheory.Limits.biprod.inr.op =     Category
Theory.Limits.biprod.snd
参数：P Q : C；CategoryTheory.Limits.biprod.opIso P Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.instHasBinaryBiproductOppositeOp`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.inl_opIso_inv_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   (P Q : C) [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.inr_opIso_inv_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   (P Q : C) [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
lemma biprod.opIso_inv_inr_op : (opIso P Q).inv ≫ inr.op = snd := by
  ext <;> simp [← op_comp]

end

end HasBinaryBiproduct

variable {X Y : C} [HasBinaryBiproduct X Y]

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasKernel (biprod.fst : X ⊞ Y ⟶ X) :=
  HasLimit.mk ⟨_, biprod.isKernelFstKernelFork X Y⟩

/-- The kernel of `biprod.fst : X ⊞ Y ⟶ X` is `Y`. -/
@[simps!]
/-
**CategoryTheory.Limits.kernelBiprodFstIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：kernelBiprodFstIso : kernel (biprod.fst : X ⊞ Y ⟶ X) ≅ Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasKernelFst`：∀ {C : Type uC} [inst : Category
Theory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
   {X Y : C} [inst_2 : Categ…

--- 原说明 ---
The kernel of `biprod.fst : X ⊞ Y ⟶ X` is `Y`.
-/
def kernelBiprodFstIso : kernel (biprod.fst : X ⊞ Y ⟶ X) ≅ Y :=
  limit.isoLimitCone ⟨_, biprod.isKernelFstKernelFork X Y⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasKernel (biprod.snd : X ⊞ Y ⟶ Y) :=
  HasLimit.mk ⟨_, biprod.isKernelSndKernelFork X Y⟩

/-- The kernel of `biprod.snd : X ⊞ Y ⟶ Y` is `X`. -/
@[simps!]
/-
**CategoryTheory.Limits.kernelBiprodSndIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：kernelBiprodSndIso : kernel (biprod.snd : X ⊞ Y ⟶ Y) ≅ X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasKernelSnd`：∀ {C : Type uC} [inst : Category
Theory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
   {X Y : C} [inst_2 : Categ…

--- 原说明 ---
The kernel of `biprod.snd : X ⊞ Y ⟶ Y` is `X`.
-/
def kernelBiprodSndIso : kernel (biprod.snd : X ⊞ Y ⟶ Y) ≅ X :=
  limit.isoLimitCone ⟨_, biprod.isKernelSndKernelFork X Y⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasCokernel (biprod.inl : X ⟶ X ⊞ Y) :=
  HasColimit.mk ⟨_, biprod.isCokernelInlCokernelFork X Y⟩

/-- The cokernel of `biprod.inl : X ⟶ X ⊞ Y` is `Y`. -/
@[simps!]
/-
**CategoryTheory.Limits.cokernelBiprodInlIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：cokernelBiprodInlIso : cokernel (biprod.inl : X ⟶ X ⊞ Y) ≅ Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasCokernelInl`：∀ {C : Type uC} [inst : Catego
ryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {X Y : C} [inst_2 : Categ…

--- 原说明 ---
The cokernel of `biprod.inl : X ⟶ X ⊞ Y` is `Y`.
-/
def cokernelBiprodInlIso : cokernel (biprod.inl : X ⟶ X ⊞ Y) ≅ Y :=
  colimit.isoColimitCocone ⟨_, biprod.isCokernelInlCokernelFork X Y⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasCokernel (biprod.inr : Y ⟶ X ⊞ Y) :=
  HasColimit.mk ⟨_, biprod.isCokernelInrCokernelFork X Y⟩

/-- The cokernel of `biprod.inr : Y ⟶ X ⊞ Y` is `X`. -/
@[simps!]
/-
**CategoryTheory.Limits.cokernelBiprodInrIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：cokernelBiprodInrIso : cokernel (biprod.inr : Y ⟶ X ⊞ Y) ≅ X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasCokernelInr`：∀ {C : Type uC} [inst : Catego
ryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {X Y : C} [inst_2 : Categ…

--- 原说明 ---
The cokernel of `biprod.inr : Y ⟶ X ⊞ Y` is `X`.
-/
def cokernelBiprodInrIso : cokernel (biprod.inr : Y ⟶ X ⊞ Y) ≅ X :=
  colimit.isoColimitCocone ⟨_, biprod.isCokernelInrCokernelFork X Y⟩

end BiprodKernel

section IsZero

/-- If `Y` is a zero object, `X ≅ X ⊞ Y` for any `X`. -/
@[simps!]
/-
**CategoryTheory.Limits.isoBiprodZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：isoBiprodZero {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero Y) : X ≅ X ⊞
 Y where hom
参数：hY : IsZero Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Y` is a zero object, `X ≅ X ⊞ Y` for any `X`.
-/
def isoBiprodZero {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero Y) : X ≅ X ⊞ Y where
  hom := biprod.inl
  inv := biprod.fst
  inv_hom_id := by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inl_fst, Category.comp_id, Category.id_comp, biprod.inl_snd,
        comp_zero]
    apply hY.eq_of_tgt

/-- If `X` is a zero object, `Y ≅ X ⊞ Y` for any `Y`. -/
@[simps]
/-
**CategoryTheory.Limits.isoZeroBiprod** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：isoZeroBiprod {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero X) : Y ≅ X ⊞
 Y where hom
参数：hY : IsZero X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is a zero object, `Y ≅ X ⊞ Y` for any `Y`.
-/
def isoZeroBiprod {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero X) : Y ≅ X ⊞ Y where
  hom := biprod.inr
  inv := biprod.snd
  inv_hom_id := by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inr_snd, Category.comp_id, Category.id_comp, biprod.inr_fst,
        comp_zero]
    apply hY.eq_of_tgt

@[simp]
/-
**CategoryTheory.Limits.biprod_isZero_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：biprod_isZero_iff (A B : C) [HasBinaryBiproduct A B] : IsZero (biprod A B)
 ↔ IsZero A ∧ IsZero B
参数：A B : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
-/
lemma biprod_isZero_iff (A B : C) [HasBinaryBiproduct A B] :
    IsZero (biprod A B) ↔ IsZero A ∧ IsZero B := by
  constructor
  · intro h
    simp only [IsZero.iff_id_eq_zero] at h ⊢
    simp only [show 𝟙 A = biprod.inl ≫ 𝟙 (A ⊞ B) ≫ biprod.fst by simp,
      show 𝟙 B = biprod.inr ≫ 𝟙 (A ⊞ B) ≫ biprod.snd by simp, h, zero_comp, comp_zero,
      and_self]
  · rintro ⟨hA, hB⟩
    rw [IsZero.iff_id_eq_zero]
    apply biprod.hom_ext
    · apply hA.eq_of_tgt
    · apply hB.eq_of_tgt

end IsZero

section

variable [HasBinaryBiproducts C]

/-- The braiding isomorphism which swaps a binary biproduct. -/
@[simps]
/-
**CategoryTheory.Limits.biprod.braiding** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       [inst_2 : CategoryTheory.
Limits.HasBinaryBiproducts C] → (P Q : C) → P ⊞ Q ≅ Q ⊞ P
参数：P Q : C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…

--- 原说明 ---
The braiding isomorphism which swaps a binary biproduct.
-/
def biprod.braiding (P Q : C) : P ⊞ Q ≅ Q ⊞ P where
  hom := biprod.lift biprod.snd biprod.fst
  inv := biprod.lift biprod.snd biprod.fst

/-- An alternative formula for the braiding isomorphism which swaps a binary biproduct,
using the fact that the biproduct is a coproduct. -/
@[simps]
/-
**CategoryTheory.Limits.biprod.braiding'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       [inst_2 : CategoryTheory.
Limits.HasBinaryBiproducts C] → (P Q : C) → P ⊞ Q ≅ Q ⊞ P
参数：P Q : C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…

--- 原说明 ---
An alternative formula for the braiding isomorphism which swaps a binary biprodu
ct,
using the fact that the biproduct is a coproduct.
-/
def biprod.braiding' (P Q : C) : P ⊞ Q ≅ Q ⊞ P where
  hom := biprod.desc biprod.inr biprod.inl
  inv := biprod.desc biprod.inr biprod.inl
/-
**CategoryTheory.Limits.biprod.braiding'_eq_braiding** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limits.HasBina
ryBiproducts C] {P Q : C},   CategoryTheory.Limits.biprod.braiding' P Q = Catego
ryTheory.Limits.biprod.braiding P Q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.biprod.braiding'_hom`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.biprod.braiding_hom`：∀ {C : Type uC} [inst : Categ
oryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
theorem biprod.braiding'_eq_braiding {P Q : C} : biprod.braiding' P Q = biprod.braiding P Q := by
  cat_disch

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
/-
**CategoryTheory.Limits.biprod.braid_natural** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limits.HasBina
ryBiproducts C] {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W),   CategoryTheory.Category
Struct.comp (CategoryTheory.Limits.biprod.map f g)       (CategoryTheory.Limits.
biprod.braiding Y W).hom =     CategoryTheory.CategoryStruct.comp (CategoryTheor
y.Limits.biprod.braiding X Z).hom       (CategoryTheory.Limits.biprod.map g f)
参数：f : X ⟶ Y；g : Z ⟶ W；CategoryTheory.Limits.biprod.map f g；CategoryTheory.Limit
s.biprod.braiding Y W；CategoryTheory.Limits.biprod.braiding X Z；CategoryTheory.L
imits.biprod.map g f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.braiding_hom`：∀ {C : Type uC} [inst : Categ
oryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   [inst_2 : CategoryTheory.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.biprod.inl_map_assoc`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.biprod.map_fst`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.biprod.map_snd`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.biprod.inr_map_assoc`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…

--- 原说明 ---
The braiding isomorphism can be passed through a map by swapping the order.
-/
theorem biprod.braid_natural {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    biprod.map f g ≫ (biprod.braiding _ _).hom = (biprod.braiding _ _).hom ≫ biprod.map g f := by
  cat_disch

@[reassoc]
/-
**CategoryTheory.Limits.biprod.braiding_map_braiding** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limits.HasBina
ryBiproducts C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z),   CategoryTheory.Category
Struct.comp (CategoryTheory.Limits.biprod.braiding X W).hom       (CategoryTheor
y.CategoryStruct.comp (CategoryTheory.Limits.biprod.map f g)         (CategoryTh
eory.Limits.biprod.braiding Y Z).hom) =     CategoryTheory.Limits.biprod.map g f
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.biprod.braiding X W；CategoryTheory.
CategoryStruct.comp (CategoryTheory.Limits.biprod.map f g)         (CategoryTheo
ry.Limits.biprod.braiding Y Z).hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biprod.braiding_hom`：∀ {C : Type uC} [inst : Categ
oryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.map_snd`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.biprod.inl_map`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.map_fst`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.biprod.inr_map`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
theorem biprod.braiding_map_braiding {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) :
    (biprod.braiding X W).hom ≫ biprod.map f g ≫ (biprod.braiding Y Z).hom = biprod.map g f := by
  cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.symmetry'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limits.HasBina
ryBiproducts C] (P Q : C),   CategoryTheory.CategoryStruct.comp       (CategoryT
heory.Limits.biprod.lift CategoryTheory.Limits.biprod.snd CategoryTheory.Limits.
biprod.fst)       (CategoryTheory.Limits.biprod.lift CategoryTheory.Limits.bipro
d.snd CategoryTheory.Limits.biprod.fst) =     CategoryTheory.CategoryStruct.id (
P ⊞ Q)
参数：P Q : C；CategoryTheory.Limits.biprod.lift CategoryTheory.Limits.biprod.snd Ca
tegoryTheory.Limits.biprod.fst；CategoryTheory.Limits.biprod.lift CategoryTheory.
Limits.biprod.snd CategoryTheory.Limits.biprod.fst；P ⊞ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
theorem biprod.symmetry' (P Q : C) :
    biprod.lift biprod.snd biprod.fst ≫ biprod.lift biprod.snd biprod.fst = 𝟙 (P ⊞ Q) := by
  cat_disch

/-- The braiding isomorphism is symmetric. -/
@[reassoc]
/-
**CategoryTheory.Limits.biprod.symmetry** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limits.HasBina
ryBiproducts C] (P Q : C),   CategoryTheory.CategoryStruct.comp (CategoryTheory.
Limits.biprod.braiding P Q).hom       (CategoryTheory.Limits.biprod.braiding Q P
).hom =     CategoryTheory.CategoryStruct.id (P ⊞ Q)
参数：P Q : C；CategoryTheory.Limits.biprod.braiding P Q；CategoryTheory.Limits.bipro
d.braiding Q P；P ⊞ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biprod.braiding_hom`：∀ {C : Type uC} [inst : Categ
oryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.biprod.symmetry'`：∀ {C : Type uC} [inst : Category
Theory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
   [inst_2 : CategoryTheory.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The braiding isomorphism is symmetric.
-/
theorem biprod.symmetry (P Q : C) :
    (biprod.braiding P Q).hom ≫ (biprod.braiding Q P).hom = 𝟙 _ := by simp

/-- The associator isomorphism which associates a binary biproduct. -/
@[simps]
/-
**CategoryTheory.Limits.biprod.associator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.biprod`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{uC', uC} C] →     [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       [inst_2 : CategoryTheory.
Limits.HasBinaryBiproducts C] → (P Q R : C) → (P ⊞ Q) ⊞ R ≅ P ⊞ Q ⊞ R
参数：P Q R : C；P ⊞ Q。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…

--- 原说明 ---
The associator isomorphism which associates a binary biproduct.
-/
def biprod.associator (P Q R : C) : (P ⊞ Q) ⊞ R ≅ P ⊞ (Q ⊞ R) where
  hom := biprod.lift (biprod.fst ≫ biprod.fst) (biprod.lift (biprod.fst ≫ biprod.snd) biprod.snd)
  inv := biprod.lift (biprod.lift biprod.fst (biprod.snd ≫ biprod.fst)) (biprod.snd ≫ biprod.snd)

/-- The associator isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
/-
**CategoryTheory.Limits.biprod.associator_natural** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limits.HasBina
ryBiproducts C] {U V W X Y Z : C} (f : U ⟶ X) (g : V ⟶ Y) (h : W ⟶ Z),   Categor
yTheory.CategoryStruct.comp (CategoryTheory.Limits.biprod.map (CategoryTheory.Li
mits.biprod.map f g) h)       (CategoryTheory.Limits.biprod.associator X Y Z).ho
m =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.biprod.associa
tor U V W).hom       (CategoryTheory.Limits.biprod.map f (CategoryTheory.Limits.
biprod.map g h))
参数：f : U ⟶ X；g : V ⟶ Y；h : W ⟶ Z；CategoryTheory.Limits.biprod.map (CategoryTheor
y.Limits.biprod.map f g) h；CategoryTheory.Limits.biprod.associator X Y Z；Categor
yTheory.Limits.biprod.associator U V W；CategoryTheory.Limits.biprod.map f (Categ
oryTheory.Limits.biprod.map g h)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.associator_hom`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   [inst_2 : CategoryTheory.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.biprod.inl_map_assoc`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.biprod.map_fst`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.biprod.map_snd`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.biprod.inr_map_assoc`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…

--- 原说明 ---
The associator isomorphism can be passed through a map by swapping the order.
-/
theorem biprod.associator_natural {U V W X Y Z : C} (f : U ⟶ X) (g : V ⟶ Y) (h : W ⟶ Z) :
    biprod.map (biprod.map f g) h ≫ (biprod.associator _ _ _).hom
      = (biprod.associator _ _ _).hom ≫ biprod.map f (biprod.map g h) := by
  cat_disch

/-- The associator isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
/-
**CategoryTheory.Limits.biprod.associator_inv_natural** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limits.HasBina
ryBiproducts C] {U V W X Y Z : C} (f : U ⟶ X) (g : V ⟶ Y) (h : W ⟶ Z),   Categor
yTheory.CategoryStruct.comp (CategoryTheory.Limits.biprod.map f (CategoryTheory.
Limits.biprod.map g h))       (CategoryTheory.Limits.biprod.associator X Y Z).in
v =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.biprod.associa
tor U V W).inv       (CategoryTheory.Limits.biprod.map (CategoryTheory.Limits.bi
prod.map f g) h)
参数：f : U ⟶ X；g : V ⟶ Y；h : W ⟶ Z；CategoryTheory.Limits.biprod.map f (CategoryThe
ory.Limits.biprod.map g h)；CategoryTheory.Limits.biprod.associator X Y Z；Categor
yTheory.Limits.biprod.associator U V W；CategoryTheory.Limits.biprod.map (Categor
yTheory.Limits.biprod.map f g) h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.associator_inv`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   [inst_2 : CategoryTheory.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.biprod.inl_map_assoc`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.biprod.map_fst`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.biprod.map_snd`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.inr_map_assoc`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…

--- 原说明 ---
The associator isomorphism can be passed through a map by swapping the order.
-/
theorem biprod.associator_inv_natural {U V W X Y Z : C} (f : U ⟶ X) (g : V ⟶ Y) (h : W ⟶ Z) :
    biprod.map f (biprod.map g h) ≫ (biprod.associator _ _ _).inv
      = (biprod.associator _ _ _).inv ≫ biprod.map (biprod.map f g) h := by
  cat_disch

end

end Limits

open CategoryTheory.Limits

section

-- TODO:
-- If someone is interested, they could provide the constructions:
--   HasBinaryBiproducts ↔ HasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- An object is indecomposable if it cannot be written as the biproduct of two nonzero objects. -/
/-
**CategoryTheory.Indecomposable** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] → [CategoryTheory.Limits.HasBinaryBip
roducts C] → C → Prop
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…

--- 原说明 ---
An object is indecomposable if it cannot be written as the biproduct of two nonz
ero objects.
-/
def Indecomposable (X : C) : Prop :=
  ¬IsZero X ∧ ∀ Y Z, (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z

/-- If
```
(f 0)
(0 g)
```
is invertible, then `f` is invertible.
-/
/-
**CategoryTheory.isIso_left_of_isIso_biprod_map** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limits.HasBinaryBi
products C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)   [CategoryTheory.IsIso (Categ
oryTheory.Limits.biprod.map f g)], CategoryTheory.IsIso f
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.biprod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.inl_map_assoc`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Limits.biprod.map_fst`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…

--- 原说明 ---
If
```
(f 0)
(0 g)
```
is invertible, then `f` is invertible.
-/
theorem isIso_left_of_isIso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
    [IsIso (biprod.map f g)] : IsIso f :=
  ⟨⟨biprod.inl ≫ inv (biprod.map f g) ≫ biprod.fst,
      ⟨by
        have t := congrArg (fun p : W ⊞ X ⟶ W ⊞ X => biprod.inl ≫ p ≫ biprod.fst)
          (IsIso.hom_inv_id (biprod.map f g))
        simp only [Category.id_comp, Category.assoc, biprod.inl_map_assoc] at t
        simp [t], by
        have t := congrArg (fun p : Y ⊞ Z ⟶ Y ⊞ Z => biprod.inl ≫ p ≫ biprod.fst)
          (IsIso.inv_hom_id (biprod.map f g))
        simp only [Category.id_comp, Category.assoc, biprod.map_fst] at t
        simp only [Category.assoc]
        simp [t]⟩⟩⟩

/-- If
```
(f 0)
(0 g)
```
is invertible, then `g` is invertible.
-/
/-
**CategoryTheory.isIso_right_of_isIso_biprod_map** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limits.HasBinaryBi
products C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)   [CategoryTheory.IsIso (Categ
oryTheory.Limits.biprod.map f g)], CategoryTheory.IsIso g
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.biprod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.isIso_left_of_isIso_biprod_map`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.biprod.braiding_map_braiding`：∀ {C : Type uC} [ins
t : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
If
```
(f 0)
(0 g)
```
is invertible, then `g` is invertible.
-/
theorem isIso_right_of_isIso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
    [IsIso (biprod.map f g)] : IsIso g :=
  letI : IsIso (biprod.map g f) := by
    rw [← biprod.braiding_map_braiding]
    infer_instance
  isIso_left_of_isIso_biprod_map g f

end

end CategoryTheory

