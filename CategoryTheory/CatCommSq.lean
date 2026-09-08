/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-!
# 2-commutative squares of functors

Similarly to `Mathlib/CategoryTheory/CommSq.lean`, which defines the notion of commutative squares,
this file introduces the notion of 2-commutative squares of functors.

If `T : C₁ ⥤ C₂`, `L : C₁ ⥤ C₃`, `R : C₂ ⥤ C₄`, `B : C₃ ⥤ C₄` are functors,
then `[CatCommSq T L R B]` contains the datum of an isomorphism `T ⋙ R ≅ L ⋙ B`.

Future work: using this notion in the development of the localization of categories
(e.g. localization of adjunctions).

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Category* C₅] [Category* C₆]

/-- `CatCommSq T L R B` expresses that there is a 2-commutative square of functors, where
the functors `T`, `L`, `R` and `B` are respectively the left, top, right and bottom functors
of the square. -/
@[ext]
/-
**CategoryTheory.CatCommSq** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C₁ : Type u_1} →   {C₂ : Type u_2} →     {C₃ : Type u_3} →       {C₄ : Ty
pe u_4} →         [inst : CategoryTheory.Category.{v_1, u_1} C₁] →           [in
st_1 : CategoryTheory.Category.{v_2, u_2} C₂] →             [inst_2 : CategoryTh
eory.Category.{v_3, u_3} C₃] →               [inst_3 : CategoryTheory.Category.{
v_4, u_4} C₄] →                 CategoryTheory.Functor C₁ C₂ →                  
 CategoryTheory.Functor C₁ C₃ →                     CategoryTheory.Functor C₂ C₄
 → CategoryTheory.Functor C₃ C₄ → Type (max u_1 v_4)
参数：max u_1 v_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CatCommSq T L R B` expresses that there is a 2-commutative square of functors, 
where
the functors `T`, `L`, `R` and `B` are respectively the left, top, right and bot
tom functors
of the square.
-/
class CatCommSq (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄) where
  /-- Assuming `[CatCommSq T L R B]`, `iso T L R B` is the isomorphism `T ⋙ R ≅ L ⋙ B`
  given by the 2-commutative square. -/
  iso (T) (L) (R) (B) : T ⋙ R ≅ L ⋙ B

variable (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

namespace CatCommSq

/-- The vertical identity `CatCommSq` -/
@[instance_reducible, simps!]
/-
**CategoryTheory.CatCommSq.vId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CatComm
Sq`。
形式化陈述：vId : CatCommSq T (𝟭 C₁) (𝟭 C₂) T where iso
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vertical identity `CatCommSq`
-/
def vId : CatCommSq T (𝟭 C₁) (𝟭 C₂) T where
  iso := Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

/-- The horizontal identity `CatCommSq` -/
@[simps!, instance_reducible]
/-
**CategoryTheory.CatCommSq.hId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CatComm
Sq`。
形式化陈述：hId : CatCommSq (𝟭 C₁) L L (𝟭 C₃) where iso
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The horizontal identity `CatCommSq`
-/
def hId : CatCommSq (𝟭 C₁) L L (𝟭 C₃) where
  iso := Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm

@[reassoc (attr := simp)]
/-
**CategoryTheory.CatCommSq.iso_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.CatCommSq`。
形式化陈述：iso_hom_naturality [h : CatCommSq T L R B] {x y : C₁} (f : x ⟶ y) : R.map 
(T.map f) ≫ (iso T L R B).hom.app y = (iso T L R B).hom.app x ≫ B.map (L.map f)
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma iso_hom_naturality [h : CatCommSq T L R B] {x y : C₁} (f : x ⟶ y) :
    R.map (T.map f) ≫ (iso T L R B).hom.app y = (iso T L R B).hom.app x ≫ B.map (L.map f) :=
  (iso T L R B).hom.naturality f

@[reassoc (attr := simp)]
/-
**CategoryTheory.CatCommSq.iso_inv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.CatCommSq`。
形式化陈述：iso_inv_naturality [h : CatCommSq T L R B] {x y : C₁} (f : x ⟶ y) : B.map 
(L.map f) ≫ (iso T L R B).inv.app y = (iso T L R B).inv.app x ≫ R.map (T.map f)
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma iso_inv_naturality [h : CatCommSq T L R B] {x y : C₁} (f : x ⟶ y) :
    B.map (L.map f) ≫ (iso T L R B).inv.app y = (iso T L R B).inv.app x ≫ R.map (T.map f) :=
  (iso T L R B).inv.naturality f

/-- Horizontal composition of 2-commutative squares -/
@[simps!, instance_reducible]
/-
**CategoryTheory.CatCommSq.hComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CatCo
mmSq`。
形式化陈述：hComp (T₁ : C₁ ⥤ C₂) (T₂ : C₂ ⥤ C₃) (V₁ : C₁ ⥤ C₄) (V₂ : C₂ ⥤ C₅) (V₃ : C₃
 ⥤ C₆) (B₁ : C₄ ⥤ C₅) (B₂ : C₅ ⥤ C₆) [CatCommSq T₁ V₁ V₂ B₁] [CatCommSq T₂ V₂ V₃
 B₂] : CatCommSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) where iso
参数：T₁ : C₁ ⥤ C₂；T₂ : C₂ ⥤ C₃；V₁ : C₁ ⥤ C₄；V₂ : C₂ ⥤ C₅；V₃ : C₃ ⥤ C₆；B₁ : C₄ ⥤ C₅
；B₂ : C₅ ⥤ C₆。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Horizontal composition of 2-commutative squares
-/
def hComp (T₁ : C₁ ⥤ C₂) (T₂ : C₂ ⥤ C₃) (V₁ : C₁ ⥤ C₄) (V₂ : C₂ ⥤ C₅) (V₃ : C₃ ⥤ C₆)
    (B₁ : C₄ ⥤ C₅) (B₂ : C₅ ⥤ C₆) [CatCommSq T₁ V₁ V₂ B₁] [CatCommSq T₂ V₂ V₃ B₂] :
    CatCommSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) where
  iso := associator _ _ _ ≪≫ isoWhiskerLeft T₁ (iso T₂ V₂ V₃ B₂) ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight (iso T₁ V₁ V₂ B₁) B₂ ≪≫
    associator _ _ _

/-- A variant of `hComp` where both squares can be explicitly provided. -/
/-
**CategoryTheory.CatCommSq.hComp'** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Ca
tCommSq`。
形式化陈述：hComp' {T₁ : C₁ ⥤ C₂} {T₂ : C₂ ⥤ C₃} {V₁ : C₁ ⥤ C₄} {V₂ : C₂ ⥤ C₅} {V₃ : C
₃ ⥤ C₆} {B₁ : C₄ ⥤ C₅} {B₂ : C₅ ⥤ C₆} (S₁ : CatCommSq T₁ V₁ V₂ B₁) (S₂ : CatComm
Sq T₂ V₂ V₃ B₂) : CatCommSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂)
参数：S₁ : CatCommSq T₁ V₁ V₂ B₁；S₂ : CatCommSq T₂ V₂ V₃ B₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `hComp` where both squares can be explicitly provided.
-/
abbrev hComp' {T₁ : C₁ ⥤ C₂} {T₂ : C₂ ⥤ C₃} {V₁ : C₁ ⥤ C₄} {V₂ : C₂ ⥤ C₅} {V₃ : C₃ ⥤ C₆}
    {B₁ : C₄ ⥤ C₅} {B₂ : C₅ ⥤ C₆} (S₁ : CatCommSq T₁ V₁ V₂ B₁) (S₂ : CatCommSq T₂ V₂ V₃ B₂) :
    CatCommSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) :=
  letI := S₁
  letI := S₂
  hComp _ _ _ V₂ _ _ _

/-- Vertical composition of 2-commutative squares -/
@[simps!, instance_reducible]
/-
**CategoryTheory.CatCommSq.vComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CatCo
mmSq`。
形式化陈述：vComp (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃) (H₁ : C₁ ⥤ C₄) (H₂ : C₂ ⥤ C₅) (H₃ : C₃
 ⥤ C₆) (R₁ : C₄ ⥤ C₅) (R₂ : C₅ ⥤ C₆) [CatCommSq H₁ L₁ R₁ H₂] [CatCommSq H₂ L₂ R₂
 H₃] : CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ where iso
参数：L₁ : C₁ ⥤ C₂；L₂ : C₂ ⥤ C₃；H₁ : C₁ ⥤ C₄；H₂ : C₂ ⥤ C₅；H₃ : C₃ ⥤ C₆；R₁ : C₄ ⥤ C₅
；R₂ : C₅ ⥤ C₆。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vertical composition of 2-commutative squares
-/
def vComp (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃) (H₁ : C₁ ⥤ C₄) (H₂ : C₂ ⥤ C₅) (H₃ : C₃ ⥤ C₆)
    (R₁ : C₄ ⥤ C₅) (R₂ : C₅ ⥤ C₆) [CatCommSq H₁ L₁ R₁ H₂] [CatCommSq H₂ L₂ R₂ H₃] :
    CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ where
  iso := (associator _ _ _).symm ≪≫ isoWhiskerRight (iso H₁ L₁ R₁ H₂) R₂ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft L₁ (iso H₂ L₂ R₂ H₃) ≪≫
      (associator _ _ _).symm

/-- A variant of `vComp` where both squares can be explicitly provided. -/
/-
**CategoryTheory.CatCommSq.vComp'** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Ca
tCommSq`。
形式化陈述：vComp' {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {H₁ : C₁ ⥤ C₄} {H₂ : C₂ ⥤ C₅} {H₃ : C
₃ ⥤ C₆} {R₁ : C₄ ⥤ C₅} {R₂ : C₅ ⥤ C₆} (S₁ : CatCommSq H₁ L₁ R₁ H₂) (S₂ : CatComm
Sq H₂ L₂ R₂ H₃) : CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃
参数：S₁ : CatCommSq H₁ L₁ R₁ H₂；S₂ : CatCommSq H₂ L₂ R₂ H₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `vComp` where both squares can be explicitly provided.
-/
abbrev vComp' {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {H₁ : C₁ ⥤ C₄} {H₂ : C₂ ⥤ C₅} {H₃ : C₃ ⥤ C₆}
    {R₁ : C₄ ⥤ C₅} {R₂ : C₅ ⥤ C₆} (S₁ : CatCommSq H₁ L₁ R₁ H₂) (S₂ : CatCommSq H₂ L₂ R₂ H₃) :
    CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ :=
  letI := S₁
  letI := S₂
  vComp _ _ _ H₂ _ _ _

section

variable (T : C₁ ≌ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ≌ C₄)

/-- Horizontal inverse of a 2-commutative square -/
@[simps!, instance_reducible]
/-
**CategoryTheory.CatCommSq.hInv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CatCom
mSq`。
形式化陈述：hInv (_ : CatCommSq T.functor L R B.functor) : CatCommSq T.inverse R L B.i
nverse where iso
参数：_ : CatCommSq T.functor L R B.functor。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Horizontal inverse of a 2-commutative square
-/
def hInv (_ : CatCommSq T.functor L R B.functor) : CatCommSq T.inverse R L B.inverse where
  iso := isoWhiskerLeft _ (L.rightUnitor.symm ≪≫ isoWhiskerLeft L B.unitIso ≪≫
      (associator _ _ _).symm ≪≫
      isoWhiskerRight (iso T.functor L R B.functor).symm B.inverse ≪≫
      associator _ _ _) ≪≫ (associator _ _ _).symm ≪≫
      isoWhiskerRight T.counitIso _ ≪≫ leftUnitor _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CatCommSq.hInv_hInv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
atCommSq`。
形式化陈述：hInv_hInv (h : CatCommSq T.functor L R B.functor) : hInv T.symm R L B.symm
 (hInv T L R B h) = h
参数：h : CatCommSq T.functor L R B.functor。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CatCommSq.ext`：∀ {C₁ : Type u_1} {C₂ : Type u_2} {C₃ : Ty
pe u_3} {C₄ : Type u_4} {inst : CategoryTheory.Category.{v_1, u_1} C₁}   {inst_1
 : CategoryTheory.…
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.CatCommSq.hInv_iso_hom_app`：∀ {C₁ : Type u_1} {C₂ : Type 
u_2} {C₃ : Type u_3} {C₄ : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} 
C₁]   [inst_1 : CategoryTheory.…
· 使用定理 `CategoryTheory.CatCommSq.hInv_iso_inv_app`：∀ {C₁ : Type u_1} {C₂ : Type 
u_2} {C₃ : Type u_3} {C₄ : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} 
C₁]   [inst_1 : CategoryTheory.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Equivalence.counitInv_app_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (e : C ≌ D) (X : C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Equivalence.fun_inv_map`：fun_inv_map (e : C ≌ D) (X Y : D
) (f : X ⟶ Y) : e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitI
nv.app Y
· 使用定理 `CategoryTheory.Equivalence.counitInv_functor_comp`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   (e : C ≌ D) (X : C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hInv_hInv (h : CatCommSq T.functor L R B.functor) :
    hInv T.symm R L B.symm (hInv T L R B h) = h := by
  ext X
  rw [← cancel_mono (B.functor.map (L.map (T.unitIso.hom.app X)))]
  rw [← Functor.comp_map]
  erw [← h.iso.hom.naturality (T.unitIso.hom.app X)]
  rw [hInv_iso_hom_app]
  simp only [Equivalence.symm_functor]
  rw [hInv_iso_inv_app]
  dsimp
  simp only [Functor.comp_obj, assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Equivalence.counitInv_app_functor, Functor.map_id]
  simp only [Functor.map_comp, Equivalence.fun_inv_map, assoc,
    Equivalence.counitInv_functor_comp, comp_id, Iso.inv_hom_id_app_assoc]

/-- In a square of categories, when the top and bottom functors are part
of equivalence of categories, it is equivalent to show 2-commutativity for
the functors of these equivalences or for their inverses. -/
/-
**CategoryTheory.CatCommSq.hInvEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.C
atCommSq`。
形式化陈述：hInvEquiv : CatCommSq T.functor L R B.functor ≃ CatCommSq T.inverse R L B.
inverse where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CatCommSq.hInv_hInv`：hInv_hInv (h : CatCommSq T.functor L
 R B.functor) : hInv T.symm R L B.symm (hInv T L R B h) = h

--- 原说明 ---
In a square of categories, when the top and bottom functors are part
of equivalence of categories, it is equivalent to show 2-commutativity for
the functors of these equivalences or for their inverses.
-/
def hInvEquiv : CatCommSq T.functor L R B.functor ≃ CatCommSq T.inverse R L B.inverse where
  toFun := hInv T L R B
  invFun := hInv T.symm R L B.symm
  left_inv := hInv_hInv T L R B
  right_inv := hInv_hInv T.symm R L B.symm

end

section

variable (T : C₁ ⥤ C₂) (L : C₁ ≌ C₃) (R : C₂ ≌ C₄) (B : C₃ ⥤ C₄)

/-- Vertical inverse of a 2-commutative square -/
@[simps!, instance_reducible]
/-
**CategoryTheory.CatCommSq.vInv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CatCom
mSq`。
形式化陈述：vInv (_ : CatCommSq T L.functor R.functor B) : CatCommSq B L.inverse R.inv
erse T where iso
参数：_ : CatCommSq T L.functor R.functor B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vertical inverse of a 2-commutative square
-/
def vInv (_ : CatCommSq T L.functor R.functor B) : CatCommSq B L.inverse R.inverse T where
  iso := isoWhiskerRight (B.leftUnitor.symm ≪≫ isoWhiskerRight L.counitIso.symm B ≪≫
      associator _ _ _ ≪≫
      isoWhiskerLeft L.inverse (iso T L.functor R.functor B).symm) R.inverse ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (associator _ _ _) ≪≫
      (associator _ _ _).symm ≪≫ isoWhiskerLeft _ R.unitIso.symm ≪≫
      rightUnitor _

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.CatCommSq.vInv_vInv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
atCommSq`。
形式化陈述：vInv_vInv (h : CatCommSq T L.functor R.functor B) : vInv B L.symm R.symm T
 (vInv T L R B h) = h
参数：h : CatCommSq T L.functor R.functor B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CatCommSq.ext`：∀ {C₁ : Type u_1} {C₂ : Type u_2} {C₃ : Ty
pe u_3} {C₄ : Type u_4} {inst : CategoryTheory.Category.{v_1, u_1} C₁}   {inst_1
 : CategoryTheory.…
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CatCommSq.vInv_iso_hom_app`：∀ {C₁ : Type u_1} {C₂ : Type 
u_2} {C₃ : Type u_3} {C₄ : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} 
C₁]   [inst_1 : CategoryTheory.…
· 使用定理 `CategoryTheory.CatCommSq.vInv_iso_inv_app`：∀ {C₁ : Type u_1} {C₂ : Type 
u_2} {C₃ : Type u_3} {C₄ : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} 
C₁]   [inst_1 : CategoryTheory.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Equivalence.fun_inv_map`：fun_inv_map (e : C ≌ D) (X Y : D
) (f : X ⟶ Y) : e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitI
nv.app Y
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Equivalence.counit_app_functor`：counit_app_functor (e : C
 ≌ D) (X : C) : e.counit.app (e.functor.obj X) = e.functor.map (e.unitInv.app X)
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.NatTrans.id_app`：id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ 
F).app X = 𝟙 (F.obj X)
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Equivalence.functor_unit_comp_assoc`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   (e : C ≌ D) (X : C…
· 使用引理 `CategoryTheory.CatCommSq.iso_hom_naturality`：iso_hom_naturality [h : Cat
CommSq T L R B] {x y : C₁} (f : x ⟶ y) : R.map (T.map f) ≫ (iso T L R B).hom.app
 y = (iso T L R B).hom.app x ≫ B.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma vInv_vInv (h : CatCommSq T L.functor R.functor B) :
    vInv B L.symm R.symm T (vInv T L R B h) = h := by
  ext X
  rw [vInv_iso_hom_app]
  dsimp
  rw [vInv_iso_inv_app]
  rw [← cancel_mono (B.map (L.functor.map (NatTrans.app L.unitIso.hom X)))]
  rw [← Functor.comp_map]
  dsimp
  simp only [Functor.map_comp, Equivalence.fun_inv_map, Functor.comp_obj,
    Functor.id_obj, assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, comp_id]
  rw [← B.map_comp, L.counit_app_functor, ← L.functor.map_comp, ← NatTrans.comp_app,
    Iso.inv_hom_id, NatTrans.id_app, L.functor.map_id]
  simp

/-- In a square of categories, when the left and right functors are part
of equivalence of categories, it is equivalent to show 2-commutativity for
the functors of these equivalences or for their inverses. -/
/-
**CategoryTheory.CatCommSq.vInvEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.C
atCommSq`。
形式化陈述：vInvEquiv : CatCommSq T L.functor R.functor B ≃ CatCommSq B L.inverse R.in
verse T where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CatCommSq.vInv_vInv`：vInv_vInv (h : CatCommSq T L.functor
 R.functor B) : vInv B L.symm R.symm T (vInv T L R B h) = h

--- 原说明 ---
In a square of categories, when the left and right functors are part
of equivalence of categories, it is equivalent to show 2-commutativity for
the functors of these equivalences or for their inverses.
-/
def vInvEquiv : CatCommSq T L.functor R.functor B ≃ CatCommSq B L.inverse R.inverse T where
  toFun := vInv T L R B
  invFun := vInv B L.symm R.symm T
  left_inv := vInv_vInv T L R B
  right_inv := vInv_vInv B L.symm R.symm T

end

end CatCommSq

end CategoryTheory

