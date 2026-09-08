/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Kan extensions

The basic definitions for Kan extensions of functors are introduced in this file. Part of API
is parallel to the definitions for bicategories (see `CategoryTheory.Bicategory.Kan.IsKan`).
(The bicategory API cannot be used directly here because it would not allow the universe
polymorphism which is necessary for some applications.)

Given a natural transformation `α : L ⋙ F' ⟶ F`, we define the property
`F'.IsRightKanExtension α` which expresses that `(F', α)` is a right Kan
extension of `F` along `L`, i.e. that it is a terminal object in a
category `RightExtension L F` of costructured arrows. The condition
`F'.IsLeftKanExtension α` for `α : F ⟶ L ⋙ F'` is defined similarly.

We also introduce typeclasses `HasRightKanExtension L F` and `HasLeftKanExtension L F`
which assert the existence of a right or left Kan extension, and chosen Kan extensions
are obtained as `leftKanExtension L F` and `rightKanExtension L F`.

## References
* https://ncatlab.org/nlab/show/Kan+extension

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C C' H D D' : Type*}
  [Category* C] [Category* C'] [Category* H] [Category* D] [Category* D']

/-- Given two functors `L : C ⥤ D` and `F : C ⥤ H`, this is the category of functors
`F' : D ⥤ H` equipped with a natural transformation `L ⋙ F' ⟶ F`. -/
/-
**CategoryTheory.Functor.RightExtension** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：RightExtension (L : C ⥤ D) (F : C ⥤ H)
参数：L : C ⥤ D；F : C ⥤ H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two functors `L : C ⥤ D` and `F : C ⥤ H`, this is the category of functors
`F' : D ⥤ H` equipped with a natural transformation `L ⋙ F' ⟶ F`.
-/
abbrev RightExtension (L : C ⥤ D) (F : C ⥤ H) :=
  CostructuredArrow ((whiskeringLeft C D H).obj L) F

/-- Given two functors `L : C ⥤ D` and `F : C ⥤ H`, this is the category of functors
`F' : D ⥤ H` equipped with a natural transformation `F ⟶ L ⋙ F'`. -/
/-
**CategoryTheory.Functor.LeftExtension** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：LeftExtension (L : C ⥤ D) (F : C ⥤ H)
参数：L : C ⥤ D；F : C ⥤ H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two functors `L : C ⥤ D` and `F : C ⥤ H`, this is the category of functors
`F' : D ⥤ H` equipped with a natural transformation `F ⟶ L ⋙ F'`.
-/
abbrev LeftExtension (L : C ⥤ D) (F : C ⥤ H) :=
  StructuredArrow F ((whiskeringLeft C D H).obj L)

/-- Constructor for objects of the category `Functor.RightExtension L F`. -/
@[simps!]
/-
**CategoryTheory.Functor.RightExtension.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor.RightExtension`。
形式化陈述：{C : Type u_1} →   {H : Type u_3} →     {D : Type u_4} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_3, u_3} H] →           [inst_2 : CategoryTheory.Category.{v_4, u_4} D] →      
       (F' : CategoryTheory.Functor D H) →               {L : CategoryTheory.Fun
ctor C D} → {F : CategoryTheory.Functor C H} → (L.comp F' ⟶ F) → L.RightExtensio
n F
参数：F' : CategoryTheory.Functor D H；L.comp F' ⟶ F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for objects of the category `Functor.RightExtension L F`.
-/
def RightExtension.mk (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F) :
    RightExtension L F :=
  CostructuredArrow.mk α

/-- Constructor for objects of the category `Functor.LeftExtension L F`. -/
@[simps!]
/-
**CategoryTheory.Functor.LeftExtension.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor.LeftExtension`。
形式化陈述：{C : Type u_1} →   {H : Type u_3} →     {D : Type u_4} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_3, u_3} H] →           [inst_2 : CategoryTheory.Category.{v_4, u_4} D] →      
       (F' : CategoryTheory.Functor D H) →               {L : CategoryTheory.Fun
ctor C D} → {F : CategoryTheory.Functor C H} → (F ⟶ L.comp F') → L.LeftExtension
 F
参数：F' : CategoryTheory.Functor D H；F ⟶ L.comp F'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for objects of the category `Functor.LeftExtension L F`.
-/
def LeftExtension.mk (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') :
    LeftExtension L F :=
  StructuredArrow.mk α

section

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F)

/-- Given `α : L ⋙ F' ⟶ F`, the property `F'.IsRightKanExtension α` asserts that
`(F', α)` is a terminal object in the category `RightExtension L F`, i.e. that `(F', α)`
is a right Kan extension of `F` along `L`. -/
/-
**CategoryTheory.Functor.IsRightKanExtension** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：{C : Type u_1} →   {H : Type u_3} →     {D : Type u_4} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_3, u_3} H] →           [inst_2 : CategoryTheory.Category.{v_4, u_4} D] →      
       (F' : CategoryTheory.Functor D H) →               {L : CategoryTheory.Fun
ctor C D} → {F : CategoryTheory.Functor C H} → (L.comp F' ⟶ F) → Prop
参数：F' : CategoryTheory.Functor D H；L.comp F' ⟶ F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `α : L ⋙ F' ⟶ F`, the property `F'.IsRightKanExtension α` asserts that
`(F', α)` is a terminal object in the category `RightExtension L F`, i.e. that `
(F', α)`
is a right Kan extension of `F` along `L`.
-/
class IsRightKanExtension : Prop where
  nonempty_isUniversal : Nonempty (RightExtension.mk F' α).IsUniversal

variable [F'.IsRightKanExtension α]

/-- If `(F', α)` is a right Kan extension of `F` along `L`, then `(F', α)` is a terminal object
in the category `RightExtension L F`. -/
/-
**CategoryTheory.Functor.isUniversalOfIsRightKanExtension** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：isUniversalOfIsRightKanExtension : (RightExtension.mk F' α).IsUniversal
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsRightKanExtension.nonempty_isUniversal`：∀ {C : 
Type u_1} {H : Type u_3} {D : Type u_4} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_3} …

--- 原说明 ---
If `(F', α)` is a right Kan extension of `F` along `L`, then `(F', α)` is a term
inal object
in the category `RightExtension L F`.
-/
noncomputable def isUniversalOfIsRightKanExtension : (RightExtension.mk F' α).IsUniversal :=
  IsRightKanExtension.nonempty_isUniversal.some

/-- If `(F', α)` is a right Kan extension of `F` along `L` and `β : L ⋙ G ⟶ F` is
a natural transformation, this is the induced morphism `G ⟶ F'`. -/
/-
**CategoryTheory.Functor.liftOfIsRightKanExtension** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：liftOfIsRightKanExtension (G : D ⥤ H) (β : L ⋙ G ⟶ F) : G ⟶ F'
参数：G : D ⥤ H；β : L ⋙ G ⟶ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `(F', α)` is a right Kan extension of `F` along `L` and `β : L ⋙ G ⟶ F` is
a natural transformation, this is the induced morphism `G ⟶ F'`.
-/
noncomputable def liftOfIsRightKanExtension (G : D ⥤ H) (β : L ⋙ G ⟶ F) : G ⟶ F' :=
  (F'.isUniversalOfIsRightKanExtension α).lift (RightExtension.mk G β)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.liftOfIsRightKanExtension_fac** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：liftOfIsRightKanExtension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) : whiskerLeft L 
(F'.liftOfIsRightKanExtension α G β) ≫ α = β
参数：G : D ⥤ H；β : L ⋙ G ⟶ F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.IsUniversal.fac`：fac (h : IsUniversal f
) (g : CostructuredArrow S T) : S.map (h.lift g) ≫ f.hom = g.hom
-/
lemma liftOfIsRightKanExtension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) :
    whiskerLeft L (F'.liftOfIsRightKanExtension α G β) ≫ α = β :=
  (F'.isUniversalOfIsRightKanExtension α).fac (RightExtension.mk G β)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.liftOfIsRightKanExtension_fac_app** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：liftOfIsRightKanExtension_fac_app (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C) : (F
'.liftOfIsRightKanExtension α G β).app (L.obj X) ≫ α.app X = β.app X
参数：G : D ⥤ H；β : L ⋙ G ⟶ F；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.Functor.liftOfIsRightKanExtension_fac`：liftOfIsRightKanEx
tension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) : whiskerLeft L (F'.liftOfIsRightKanExte
nsion α G β) ≫ α = β
-/
lemma liftOfIsRightKanExtension_fac_app (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C) :
    (F'.liftOfIsRightKanExtension α G β).app (L.obj X) ≫ α.app X = β.app X :=
  NatTrans.congr_app (F'.liftOfIsRightKanExtension_fac α G β) X
/-
**CategoryTheory.Functor.hom_ext_of_isRightKanExtension** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：hom_ext_of_isRightKanExtension {G : D ⥤ H} (γ₁ γ₂ : G ⟶ F') (hγ : whiskerL
eft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂
参数：γ₁ γ₂ : G ⟶ F'；hγ : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.IsUniversal.hom_ext`：hom_ext (h : IsUni
versal f) {c : C} {η η' : c ⟶ f.left} (w : S.map η ≫ f.hom = S.map η' ≫ f.hom) :
 η = η'
-/
lemma hom_ext_of_isRightKanExtension {G : D ⥤ H} (γ₁ γ₂ : G ⟶ F')
    (hγ : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂ :=
  (F'.isUniversalOfIsRightKanExtension α).hom_ext hγ

/-- If `(F', α)` is a right Kan extension of `F` along `L`, then this
is the induced bijection `(G ⟶ F') ≃ (L ⋙ G ⟶ F)` for all `G`. -/
@[simps!]
/-
**CategoryTheory.Functor.homEquivOfIsRightKanExtension** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：homEquivOfIsRightKanExtension (G : D ⥤ H) : (G ⟶ F') ≃ (L ⋙ G ⟶ F) where t
oFun β
参数：G : D ⥤ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `(F', α)` is a right Kan extension of `F` along `L`, then this
is the induced bijection `(G ⟶ F') ≃ (L ⋙ G ⟶ F)` for all `G`.
-/
noncomputable def homEquivOfIsRightKanExtension (G : D ⥤ H) :
    (G ⟶ F') ≃ (L ⋙ G ⟶ F) where
  toFun β := whiskerLeft _ β ≫ α
  invFun β := liftOfIsRightKanExtension _ α _ β
  left_inv β := Functor.hom_ext_of_isRightKanExtension _ α _ _ (by simp)
  right_inv := by cat_disch
/-
**CategoryTheory.Functor.isRightKanExtension_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：isRightKanExtension_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F 
: C ⥤ H} (α : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : whiskerLeft L e.hom ≫ α' = 
α) [F'.IsRightKanExtension α] : F''.IsRightKanExtension α' where nonempty_isUniv
ersal
参数：e : F' ≅ F''；α : L ⋙ F' ⟶ F；α' : L ⋙ F'' ⟶ F；comm : whiskerLeft L e.hom ≫ α' 
= α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isRightKanExtension_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H}
    (α : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : whiskerLeft L e.hom ≫ α' = α)
    [F'.IsRightKanExtension α] : F''.IsRightKanExtension α' where
  nonempty_isUniversal := ⟨IsTerminal.ofIso (F'.isUniversalOfIsRightKanExtension α)
    (CostructuredArrow.isoMk e comm)⟩
/-
**CategoryTheory.Functor.isRightKanExtension_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：isRightKanExtension_iff_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D}
 {F : C ⥤ H} (α : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : whiskerLeft L e.hom ≫ α
' = α) : F'.IsRightKanExtension α ↔ F''.IsRightKanExtension α'
参数：e : F' ≅ F''；α : L ⋙ F' ⟶ F；α' : L ⋙ F'' ⟶ F；comm : whiskerLeft L e.hom ≫ α' 
= α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isRightKanExtension_of_iso`：isRightKanExtension_o
f_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F) (
α' : L ⋙ F'' ⟶ F) (comm : whiskerLeft L…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.whiskerLeft_comp_assoc`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Iso.symm_hom`：symm_hom (α : X ≅ Y) : α.symm.hom = α.inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Functor.whiskerLeft_id'`：whiskerLeft_id' (F : C ⥤ D) {G :
 D ⥤ E} : whiskerLeft F (𝟙 G) = 𝟙 (F.comp G)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma isRightKanExtension_iff_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H}
    (α : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : whiskerLeft L e.hom ≫ α' = α) :
    F'.IsRightKanExtension α ↔ F''.IsRightKanExtension α' := by
  constructor
  · intro
    exact isRightKanExtension_of_iso e α α' comm
  · intro
    refine isRightKanExtension_of_iso e.symm α' α ?_
    rw [← comm, ← whiskerLeft_comp_assoc, Iso.symm_hom, e.inv_hom_id, whiskerLeft_id', id_comp]

/-- Right Kan extensions of isomorphic functors are isomorphic. -/
@[simps]
/-
**CategoryTheory.Functor.rightKanExtensionUniqueOfIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：rightKanExtensionUniqueOfIso {G : C ⥤ H} (i : F ≅ G) (G' : D ⥤ H) (β : L ⋙
 G' ⟶ G) [G'.IsRightKanExtension β] : F' ≅ G' where hom
参数：i : F ≅ G；G' : D ⥤ H；β : L ⋙ G' ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right Kan extensions of isomorphic functors are isomorphic.
-/
noncomputable def rightKanExtensionUniqueOfIso {G : C ⥤ H} (i : F ≅ G) (G' : D ⥤ H)
    (β : L ⋙ G' ⟶ G) [G'.IsRightKanExtension β] : F' ≅ G' where
  hom := liftOfIsRightKanExtension _ β F' (α ≫ i.hom)
  inv := liftOfIsRightKanExtension _ α G' (β ≫ i.inv)
  hom_inv_id := F'.hom_ext_of_isRightKanExtension α _ _ (by simp)
  inv_hom_id := G'.hom_ext_of_isRightKanExtension β _ _ (by simp)

/-- Two right Kan extensions are (canonically) isomorphic. -/
@[simps!]
/-
**CategoryTheory.Functor.rightKanExtensionUnique** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：rightKanExtensionUnique (F'' : D ⥤ H) (α' : L ⋙ F'' ⟶ F) [F''.IsRightKanEx
tension α'] : F' ≅ F''
参数：F'' : D ⥤ H；α' : L ⋙ F'' ⟶ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two right Kan extensions are (canonically) isomorphic.
-/
noncomputable def rightKanExtensionUnique
    (F'' : D ⥤ H) (α' : L ⋙ F'' ⟶ F) [F''.IsRightKanExtension α'] : F' ≅ F'' :=
  rightKanExtensionUniqueOfIso F' α (Iso.refl _) F'' α'
/-
**CategoryTheory.Functor.isRightKanExtension_iff_isIso** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：isRightKanExtension_iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F'' ⟶ F') {L
 : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : whiskerLeft L 
φ ≫ α = α') [F'.IsRightKanExtension α] : F''.IsRightKanExtension α' ↔ IsIso φ
参数：φ : F'' ⟶ F'；α : L ⋙ F' ⟶ F；α' : L ⋙ F'' ⟶ F；comm : whiskerLeft L φ ≫ α = α'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isRightKanExtension`：hom_ext_of_isRigh
tKanExtension {G : D ⥤ H} (γ₁ γ₂ : G ⟶ F') (hγ : whiskerLeft L γ₁ ≫ α = whiskerL
eft L γ₂ ≫ α) : γ₁ = γ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.rightKanExtensionUnique_hom`：∀ {C : Type u_1} {H 
: Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.liftOfIsRightKanExtension_fac`：liftOfIsRightKanEx
tension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) : whiskerLeft L (F'.liftOfIsRightKanExte
nsion α G β) ≫ α = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `CategoryTheory.Functor.isRightKanExtension_iff_of_iso`：isRightKanExtensi
on_iff_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F
' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : whiskerLe…
-/
lemma isRightKanExtension_iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F'' ⟶ F')
    {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F)
    (comm : whiskerLeft L φ ≫ α = α') [F'.IsRightKanExtension α] :
    F''.IsRightKanExtension α' ↔ IsIso φ := by
  constructor
  · intro
    rw [F'.hom_ext_of_isRightKanExtension α φ (rightKanExtensionUnique _ α' _ α).hom
      (by simp [comm])]
    infer_instance
  · intro
    rw [isRightKanExtension_iff_of_iso (asIso φ) α' α comm]
    infer_instance
end

section

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F')

/-- Given `α : F ⟶ L ⋙ F'`, the property `F'.IsLeftKanExtension α` asserts that
`(F', α)` is an initial object in the category `LeftExtension L F`, i.e. that `(F', α)`
is a left Kan extension of `F` along `L`. -/
/-
**CategoryTheory.Functor.IsLeftKanExtension** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：{C : Type u_1} →   {H : Type u_3} →     {D : Type u_4} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_3, u_3} H] →           [inst_2 : CategoryTheory.Category.{v_4, u_4} D] →      
       (F' : CategoryTheory.Functor D H) →               {L : CategoryTheory.Fun
ctor C D} → {F : CategoryTheory.Functor C H} → (F ⟶ L.comp F') → Prop
参数：F' : CategoryTheory.Functor D H；F ⟶ L.comp F'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `α : F ⟶ L ⋙ F'`, the property `F'.IsLeftKanExtension α` asserts that
`(F', α)` is an initial object in the category `LeftExtension L F`, i.e. that `(
F', α)`
is a left Kan extension of `F` along `L`.
-/
class IsLeftKanExtension : Prop where
  nonempty_isUniversal : Nonempty (LeftExtension.mk F' α).IsUniversal

variable [F'.IsLeftKanExtension α]

/-- If `(F', α)` is a left Kan extension of `F` along `L`, then `(F', α)` is an initial object
in the category `LeftExtension L F`. -/
/-
**CategoryTheory.Functor.isUniversalOfIsLeftKanExtension** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：isUniversalOfIsLeftKanExtension : (LeftExtension.mk F' α).IsUniversal
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLeftKanExtension.nonempty_isUniversal`：∀ {C : T
ype u_1} {H : Type u_3} {D : Type u_4} {inst : CategoryTheory.Category.{v_1, u_1
} C}   {inst_1 : CategoryTheory.Category.{v_3, u_3} …

--- 原说明 ---
If `(F', α)` is a left Kan extension of `F` along `L`, then `(F', α)` is an init
ial object
in the category `LeftExtension L F`.
-/
noncomputable def isUniversalOfIsLeftKanExtension : (LeftExtension.mk F' α).IsUniversal :=
  IsLeftKanExtension.nonempty_isUniversal.some

/-- If `(F', α)` is a left Kan extension of `F` along `L` and `β : F ⟶ L ⋙ G` is
a natural transformation, this is the induced morphism `F' ⟶ G`. -/
/-
**CategoryTheory.Functor.descOfIsLeftKanExtension** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：descOfIsLeftKanExtension (G : D ⥤ H) (β : F ⟶ L ⋙ G) : F' ⟶ G
参数：G : D ⥤ H；β : F ⟶ L ⋙ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `(F', α)` is a left Kan extension of `F` along `L` and `β : F ⟶ L ⋙ G` is
a natural transformation, this is the induced morphism `F' ⟶ G`.
-/
noncomputable def descOfIsLeftKanExtension (G : D ⥤ H) (β : F ⟶ L ⋙ G) : F' ⟶ G :=
  (F'.isUniversalOfIsLeftKanExtension α).desc (LeftExtension.mk G β)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.descOfIsLeftKanExtension_fac** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：descOfIsLeftKanExtension_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft
 L (F'.descOfIsLeftKanExtension α G β) = β
参数：G : D ⥤ H；β : F ⟶ L ⋙ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.IsUniversal.fac`：fac (h : IsUniversal f) 
(g : StructuredArrow S T) : f.hom ≫ T.map (h.desc g) = g.hom
-/
lemma descOfIsLeftKanExtension_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    α ≫ whiskerLeft L (F'.descOfIsLeftKanExtension α G β) = β :=
  (F'.isUniversalOfIsLeftKanExtension α).fac (LeftExtension.mk G β)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.descOfIsLeftKanExtension_fac_app** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：descOfIsLeftKanExtension_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) : α.a
pp X ≫ (F'.descOfIsLeftKanExtension α G β).app (L.obj X) = β.app X
参数：G : D ⥤ H；β : F ⟶ L ⋙ G；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac`：descOfIsLeftKanExte
nsion_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (F'.descOfIsLeftKanExt
ension α G β) = β
-/
lemma descOfIsLeftKanExtension_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) :
    α.app X ≫ (F'.descOfIsLeftKanExtension α G β).app (L.obj X) = β.app X :=
  NatTrans.congr_app (F'.descOfIsLeftKanExtension_fac α G β) X
/-
**CategoryTheory.Functor.hom_ext_of_isLeftKanExtension** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：hom_ext_of_isLeftKanExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whisk
erLeft L γ₁ = α ≫ whiskerLeft L γ₂) : γ₁ = γ₂
参数：γ₁ γ₂ : F' ⟶ G；hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiskerLeft L γ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.IsUniversal.hom_ext`：hom_ext (h : IsUnive
rsal f) {c : C} {η η' : f.right ⟶ c} (w : f.hom ≫ T.map η = f.hom ≫ T.map η') : 
η = η'
-/
lemma hom_ext_of_isLeftKanExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G)
    (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiskerLeft L γ₂) : γ₁ = γ₂ :=
  (F'.isUniversalOfIsLeftKanExtension α).hom_ext hγ

/-- If `(F', α)` is a left Kan extension of `F` along `L`, then this
is the induced bijection `(F' ⟶ G) ≃ (F ⟶ L ⋙ G)` for all `G`. -/
@[simps!]
/-
**CategoryTheory.Functor.homEquivOfIsLeftKanExtension** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：homEquivOfIsLeftKanExtension (G : D ⥤ H) : (F' ⟶ G) ≃ (F ⟶ L ⋙ G) where to
Fun β
参数：G : D ⥤ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `(F', α)` is a left Kan extension of `F` along `L`, then this
is the induced bijection `(F' ⟶ G) ≃ (F ⟶ L ⋙ G)` for all `G`.
-/
noncomputable def homEquivOfIsLeftKanExtension (G : D ⥤ H) :
    (F' ⟶ G) ≃ (F ⟶ L ⋙ G) where
  toFun β := α ≫ whiskerLeft _ β
  invFun β := descOfIsLeftKanExtension _ α _ β
  left_inv β := Functor.hom_ext_of_isLeftKanExtension _ α _ _ (by simp)
  right_inv := by cat_disch
/-
**CategoryTheory.Functor.isLeftKanExtension_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：isLeftKanExtension_of_iso {F' : D ⥤ H} {F'' : D ⥤ H} (e : F' ≅ F'') {L : C
 ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'') (comm : α ≫ whiskerLeft L 
e.hom = α') [F'.IsLeftKanExtension α] : F''.IsLeftKanExtension α' where nonempty
_isUniversal
参数：e : F' ≅ F''；α : F ⟶ L ⋙ F'；α' : F ⟶ L ⋙ F''；comm : α ≫ whiskerLeft L e.hom =
 α'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isLeftKanExtension_of_iso {F' : D ⥤ H} {F'' : D ⥤ H} (e : F' ≅ F'')
    {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'')
    (comm : α ≫ whiskerLeft L e.hom = α') [F'.IsLeftKanExtension α] :
    F''.IsLeftKanExtension α' where
  nonempty_isUniversal := ⟨IsInitial.ofIso (F'.isUniversalOfIsLeftKanExtension α)
    (StructuredArrow.isoMk e comm)⟩
/-
**CategoryTheory.Functor.isLeftKanExtension_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：isLeftKanExtension_iff_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} 
{F : C ⥤ H} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'') (comm : α ≫ whiskerLeft L e.hom 
= α') : F'.IsLeftKanExtension α ↔ F''.IsLeftKanExtension α'
参数：e : F' ≅ F''；α : F ⟶ L ⋙ F'；α' : F ⟶ L ⋙ F''；comm : α ≫ whiskerLeft L e.hom =
 α'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isLeftKanExtension_of_iso`：isLeftKanExtension_of_
iso {F' : D ⥤ H} {F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L
 ⋙ F') (α' : F ⟶ L ⋙ F'') (comm : α ≫ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.whiskerLeft_comp`：whiskerLeft_comp (F : C ⥤ D) {G
 H K : D ⥤ E} (α : G ⟶ H) (β : H ⟶ K) : whiskerLeft F (α ≫ β) = whiskerLeft F α 
≫ whiskerLeft F β
· 使用定理 `CategoryTheory.Iso.symm_hom`：symm_hom (α : X ≅ Y) : α.symm.hom = α.inv
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Functor.whiskerLeft_id'`：whiskerLeft_id' (F : C ⥤ D) {G :
 D ⥤ E} : whiskerLeft F (𝟙 G) = 𝟙 (F.comp G)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma isLeftKanExtension_iff_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'')
    {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'')
    (comm : α ≫ whiskerLeft L e.hom = α') :
    F'.IsLeftKanExtension α ↔ F''.IsLeftKanExtension α' := by
  constructor
  · intro
    exact isLeftKanExtension_of_iso e α α' comm
  · intro
    refine isLeftKanExtension_of_iso e.symm α' α ?_
    rw [← comm, assoc, ← whiskerLeft_comp, Iso.symm_hom, e.hom_inv_id, whiskerLeft_id', comp_id]

/-- Left Kan extensions of isomorphic functors are isomorphic. -/
@[simps]
/-
**CategoryTheory.Functor.leftKanExtensionUniqueOfIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：leftKanExtensionUniqueOfIso {G : C ⥤ H} (i : F ≅ G) (G' : D ⥤ H) (β : G ⟶ 
L ⋙ G') [G'.IsLeftKanExtension β] : F' ≅ G' where hom
参数：i : F ≅ G；G' : D ⥤ H；β : G ⟶ L ⋙ G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left Kan extensions of isomorphic functors are isomorphic.
-/
noncomputable def leftKanExtensionUniqueOfIso {G : C ⥤ H} (i : F ≅ G) (G' : D ⥤ H)
    (β : G ⟶ L ⋙ G') [G'.IsLeftKanExtension β] : F' ≅ G' where
  hom := descOfIsLeftKanExtension _ α G' (i.hom ≫ β)
  inv := descOfIsLeftKanExtension _ β F' (i.inv ≫ α)
  hom_inv_id := F'.hom_ext_of_isLeftKanExtension α _ _ (by simp)
  inv_hom_id := G'.hom_ext_of_isLeftKanExtension β _ _ (by simp)

/-- Two left Kan extensions are (canonically) isomorphic. -/
@[simps!]
/-
**CategoryTheory.Functor.leftKanExtensionUnique** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：leftKanExtensionUnique (F'' : D ⥤ H) (α' : F ⟶ L ⋙ F'') [F''.IsLeftKanExte
nsion α'] : F' ≅ F''
参数：F'' : D ⥤ H；α' : F ⟶ L ⋙ F''。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two left Kan extensions are (canonically) isomorphic.
-/
noncomputable def leftKanExtensionUnique
    (F'' : D ⥤ H) (α' : F ⟶ L ⋙ F'') [F''.IsLeftKanExtension α'] : F' ≅ F'' :=
  leftKanExtensionUniqueOfIso F' α (Iso.refl _) F'' α'
/-
**CategoryTheory.Functor.isLeftKanExtension_iff_isIso** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：isLeftKanExtension_iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F' ⟶ F'') {L 
: C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'') (comm : α ≫ whiskerLeft
 L φ = α') [F'.IsLeftKanExtension α] : F''.IsLeftKanExtension α' ↔ IsIso φ
参数：φ : F' ⟶ F''；α : F ⟶ L ⋙ F'；α' : F ⟶ L ⋙ F''；comm : α ≫ whiskerLeft L φ = α'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.leftKanExtensionUnique_hom`：∀ {C : Type u_1} {H :
 Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac`：descOfIsLeftKanExte
nsion_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (F'.descOfIsLeftKanExt
ension α G β) = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `CategoryTheory.Functor.isLeftKanExtension_of_iso`：isLeftKanExtension_of_
iso {F' : D ⥤ H} {F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L
 ⋙ F') (α' : F ⟶ L ⋙ F'') (comm : α ≫ …
-/
lemma isLeftKanExtension_iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F' ⟶ F'')
    {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'')
    (comm : α ≫ whiskerLeft L φ = α') [F'.IsLeftKanExtension α] :
    F''.IsLeftKanExtension α' ↔ IsIso φ := by
  constructor
  · intro
    rw [F'.hom_ext_of_isLeftKanExtension α φ (leftKanExtensionUnique _ α _ α').hom
      (by simp [comm])]
    infer_instance
  · intro
    exact isLeftKanExtension_of_iso (asIso φ) α α' comm

end

/-- This property `HasRightKanExtension L F` holds when the functor `F` has a right
Kan extension along `L`. -/
/-
**CategoryTheory.Functor.HasRightKanExtension** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：HasRightKanExtension (L : C ⥤ D) (F : C ⥤ H)
参数：L : C ⥤ D；F : C ⥤ H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This property `HasRightKanExtension L F` holds when the functor `F` has a right
Kan extension along `L`.
-/
abbrev HasRightKanExtension (L : C ⥤ D) (F : C ⥤ H) := HasTerminal (RightExtension L F)
/-
**CategoryTheory.Functor.HasRightKanExtension.mk** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Functor.HasRightKanExtension`。
形式化陈述：∀ {C : Type u_1} {H : Type u_3} {D : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} H] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} D]   (F' : CategoryTheory.Functor D H) {L : Ca
tegoryTheory.Functor C D} {F : CategoryTheory.Functor C H}   (α : L.comp F' ⟶ F)
 [F'.IsRightKanExtension α], L.HasRightKanExtension F
参数：F' : CategoryTheory.Functor D H；α : L.comp F' ⟶ F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.hasTerminal`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsTerminal 
X),   CategoryTheory.Limits.HasTer…
-/
lemma HasRightKanExtension.mk (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F)
    [F'.IsRightKanExtension α] : HasRightKanExtension L F :=
  (F'.isUniversalOfIsRightKanExtension α).hasTerminal

/-- This property `HasLeftKanExtension L F` holds when the functor `F` has a left
Kan extension along `L`. -/
/-
**CategoryTheory.Functor.HasLeftKanExtension** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：HasLeftKanExtension (L : C ⥤ D) (F : C ⥤ H)
参数：L : C ⥤ D；F : C ⥤ H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This property `HasLeftKanExtension L F` holds when the functor `F` has a left
Kan extension along `L`.
-/
abbrev HasLeftKanExtension (L : C ⥤ D) (F : C ⥤ H) := HasInitial (LeftExtension L F)
/-
**CategoryTheory.Functor.HasLeftKanExtension.mk** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Functor.HasLeftKanExtension`。
形式化陈述：∀ {C : Type u_1} {H : Type u_3} {D : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} H] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} D]   (F' : CategoryTheory.Functor D H) {L : Ca
tegoryTheory.Functor C D} {F : CategoryTheory.Functor C H}   (α : F ⟶ L.comp F')
 [F'.IsLeftKanExtension α], L.HasLeftKanExtension F
参数：F' : CategoryTheory.Functor D H；α : F ⟶ L.comp F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.hasInitial`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsInitial X),
   CategoryTheory.Limits.HasInit…
-/
lemma HasLeftKanExtension.mk (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F')
    [F'.IsLeftKanExtension α] : HasLeftKanExtension L F :=
  (F'.isUniversalOfIsLeftKanExtension α).hasInitial

section

variable (L : C ⥤ D) (F : C ⥤ H) [HasRightKanExtension L F]

/-- A chosen right Kan extension when `[HasRightKanExtension L F]` holds. -/
/-
**CategoryTheory.Functor.rightKanExtension** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：rightKanExtension : D ⥤ H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A chosen right Kan extension when `[HasRightKanExtension L F]` holds.
-/
noncomputable def rightKanExtension : D ⥤ H := (⊤_ _ : RightExtension L F).left

/-- The counit of the chosen right Kan extension `rightKanExtension L F`. -/
/-
**CategoryTheory.Functor.rightKanExtensionCounit** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：rightKanExtensionCounit : L ⋙ rightKanExtension L F ⟶ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit of the chosen right Kan extension `rightKanExtension L F`.
-/
noncomputable def rightKanExtensionCounit : L ⋙ rightKanExtension L F ⟶ F :=
  (⊤_ _ : RightExtension L F).hom
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (L.rightKanExtension F).IsRightKanExtension (L.rightKanExtensionCounit F) where
  nonempty_isUniversal := ⟨terminalIsTerminal⟩

@[ext]
/-
**CategoryTheory.Functor.rightKanExtension_hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：rightKanExtension_hom_ext {G : D ⥤ H} (γ₁ γ₂ : G ⟶ rightKanExtension L F) 
(hγ : whiskerLeft L γ₁ ≫ rightKanExtensionCounit L F = whiskerLeft L γ₂ ≫ rightK
anExtensionCounit L F) : γ₁ = γ₂
参数：γ₁ γ₂ : G ⟶ rightKanExtension L F；hγ : whiskerLeft L γ₁ ≫ rightKanExtensionCo
unit L F = whiskerLeft L γ₂ ≫ rightKanExtensionCounit L F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isRightKanExtension`：hom_ext_of_isRigh
tKanExtension {G : D ⥤ H} (γ₁ γ₂ : G ⟶ F') (hγ : whiskerLeft L γ₁ ≫ α = whiskerL
eft L γ₂ ≫ α) : γ₁ = γ₂
· 使用定理 `CategoryTheory.Functor.instIsRightKanExtensionRightKanExtensionRightKanE
xtensionCounit`：∀ {C : Type u_1} {H : Type u_3} {D : Type u_4} [inst : CategoryT
heory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} …
-/
lemma rightKanExtension_hom_ext {G : D ⥤ H} (γ₁ γ₂ : G ⟶ rightKanExtension L F)
    (hγ : whiskerLeft L γ₁ ≫ rightKanExtensionCounit L F =
      whiskerLeft L γ₂ ≫ rightKanExtensionCounit L F) :
    γ₁ = γ₂ :=
  hom_ext_of_isRightKanExtension _ _ _ _ hγ

end

section

variable (L : C ⥤ D) (F : C ⥤ H) [HasLeftKanExtension L F]

/-- A chosen left Kan extension when `[HasLeftKanExtension L F]` holds. -/
/-
**CategoryTheory.Functor.leftKanExtension** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：leftKanExtension : D ⥤ H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A chosen left Kan extension when `[HasLeftKanExtension L F]` holds.
-/
noncomputable def leftKanExtension : D ⥤ H := (⊥_ _ : LeftExtension L F).right

/-- The unit of the chosen left Kan extension `leftKanExtension L F`. -/
/-
**CategoryTheory.Functor.leftKanExtensionUnit** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：leftKanExtensionUnit : F ⟶ L ⋙ leftKanExtension L F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit of the chosen left Kan extension `leftKanExtension L F`.
-/
noncomputable def leftKanExtensionUnit : F ⟶ L ⋙ leftKanExtension L F :=
  (⊥_ _ : LeftExtension L F).hom
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (L.leftKanExtension F).IsLeftKanExtension (L.leftKanExtensionUnit F) where
  nonempty_isUniversal := ⟨initialIsInitial⟩

@[ext]
/-
**CategoryTheory.Functor.leftKanExtension_hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：leftKanExtension_hom_ext {G : D ⥤ H} (γ₁ γ₂ : leftKanExtension L F ⟶ G) (h
γ : leftKanExtensionUnit L F ≫ whiskerLeft L γ₁ = leftKanExtensionUnit L F ≫ whi
skerLeft L γ₂) : γ₁ = γ₂
参数：γ₁ γ₂ : leftKanExtension L F ⟶ G；hγ : leftKanExtensionUnit L F ≫ whiskerLeft 
L γ₁ = leftKanExtensionUnit L F ≫ whiskerLeft L γ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionLeftKanExtensionLeftKanExte
nsionUnit`：∀ {C : Type u_1} {H : Type u_3} {D : Type u_4} [inst : CategoryTheory
.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} …
-/
lemma leftKanExtension_hom_ext {G : D ⥤ H} (γ₁ γ₂ : leftKanExtension L F ⟶ G)
    (hγ : leftKanExtensionUnit L F ≫ whiskerLeft L γ₁ =
      leftKanExtensionUnit L F ≫ whiskerLeft L γ₂) : γ₁ = γ₂ :=
  hom_ext_of_isLeftKanExtension _ _ _ _ hγ

end

section

variable {L : C ⥤ D} {L' : C ⥤ D'} (G : D ⥤ D')

/-- The functor `LeftExtension L' F ⥤ LeftExtension L F`
induced by a natural transformation `L' ⟶ L ⋙ G'`. -/
@[simps!, implicit_reducible]
/-
**CategoryTheory.Functor.LeftExtension.postcomp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `LeftExtension L' F ⥤ LeftExtension L F`
induced by a natural transformation `L' ⟶ L ⋙ G'`.
-/
def LeftExtension.postcomp₁ (f : L' ⟶ L ⋙ G) (F : C ⥤ H) :
    LeftExtension L' F ⥤ LeftExtension L F :=
  StructuredArrow.map₂ (F := (whiskeringLeft D D' H).obj G) (G := 𝟭 _) (𝟙 _)
    ((whiskeringLeft C D' H).map f)

/-- The functor `RightExtension L' F ⥤ RightExtension L F`
induced by a natural transformation `L ⋙ G ⟶ L'`. -/
@[simps!, implicit_reducible]
/-
**CategoryTheory.Functor.RightExtension.postcomp** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `RightExtension L' F ⥤ RightExtension L F`
induced by a natural transformation `L ⋙ G ⟶ L'`.
-/
def RightExtension.postcomp₁ (f : L ⋙ G ⟶ L') (F : C ⥤ H) :
    RightExtension L' F ⥤ RightExtension L F :=
  CostructuredArrow.map₂ (F := (whiskeringLeft D D' H).obj G) (G := 𝟭 _)
    ((whiskeringLeft C D' H).map f) (𝟙 _)

variable [IsEquivalence G]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (f : L' ⟶ L ⋙ G) [IsIso f] (F : C ⥤ H) :
    IsEquivalence (LeftExtension.postcomp₁ G f F) := by
  apply StructuredArrow.isEquivalenceMap₂

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (f : L ⋙ G ⟶ L') [IsIso f] (F : C ⥤ H) :
    IsEquivalence (RightExtension.postcomp₁ G f F) := by
  apply CostructuredArrow.isEquivalenceMap₂

variable {G} in
/-
**CategoryTheory.Functor.hasLeftExtension_iff_postcomp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasLeftExtension_iff_postcomp₁ (e : L ⋙ G ≅ L') (F : C ⥤ H) :
    HasLeftKanExtension L' F ↔ HasLeftKanExtension L F :=
  (LeftExtension.postcomp₁ G e.inv F).asEquivalence.hasInitial_iff

variable {G} in
/-
**CategoryTheory.Functor.hasRightExtension_iff_postcomp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasRightExtension_iff_postcomp₁ (e : L ⋙ G ≅ L') (F : C ⥤ H) :
    HasRightKanExtension L' F ↔ HasRightKanExtension L F :=
  (RightExtension.postcomp₁ G e.hom F).asEquivalence.hasTerminal_iff

variable (e : L ⋙ G ≅ L') (F : C ⥤ H)

/-- Given an isomorphism `e : L ⋙ G ≅ L'`, a left extension of `F` along `L'` is universal
iff the corresponding left extension of `L` along `L` is. -/
/-
**CategoryTheory.Functor.LeftExtension.isUniversalPostcomp** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an isomorphism `e : L ⋙ G ≅ L'`, a left extension of `F` along `L'` is uni
versal
iff the corresponding left extension of `L` along `L` is.
-/
noncomputable def LeftExtension.isUniversalPostcomp₁Equiv (ex : LeftExtension L' F) :
    ex.IsUniversal ≃ ((LeftExtension.postcomp₁ G e.inv F).obj ex).IsUniversal := by
  apply IsInitial.isInitialIffObj (LeftExtension.postcomp₁ G e.inv F)

/-- Given an isomorphism `e : L ⋙ G ≅ L'`, a right extension of `F` along `L'` is universal
iff the corresponding right extension of `L` along `L` is. -/
/-
**CategoryTheory.Functor.RightExtension.isUniversalPostcomp** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an isomorphism `e : L ⋙ G ≅ L'`, a right extension of `F` along `L'` is un
iversal
iff the corresponding right extension of `L` along `L` is.
-/
noncomputable def RightExtension.isUniversalPostcomp₁Equiv (ex : RightExtension L' F) :
    ex.IsUniversal ≃ ((RightExtension.postcomp₁ G e.hom F).obj ex).IsUniversal := by
  apply IsTerminal.isTerminalIffObj (RightExtension.postcomp₁ G e.hom F)

variable {F F'}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.isLeftKanExtension_iff_postcomp** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isLeftKanExtension_iff_postcomp₁ (α : F ⟶ L' ⋙ F') :
    F'.IsLeftKanExtension α ↔ (G ⋙ F').IsLeftKanExtension
      (α ≫ whiskerRight e.inv _ ≫ (associator _ _ _).hom) := by
  let eq : (LeftExtension.mk _ α).IsUniversal ≃
      (LeftExtension.mk _
        (α ≫ whiskerRight e.inv _ ≫ (associator _ _ _).hom)).IsUniversal :=
    (LeftExtension.isUniversalPostcomp₁Equiv G e F _).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨eq (isUniversalOfIsLeftKanExtension _ _)⟩⟩
  · exact fun _ => ⟨⟨eq.symm (isUniversalOfIsLeftKanExtension _ _)⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.isRightKanExtension_iff_postcomp** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isRightKanExtension_iff_postcomp₁ (α : L' ⋙ F' ⟶ F) :
    F'.IsRightKanExtension α ↔ (G ⋙ F').IsRightKanExtension
      ((associator _ _ _).inv ≫ whiskerRight e.hom F' ≫ α) := by
  let eq : (RightExtension.mk _ α).IsUniversal ≃
    (RightExtension.mk _
      ((associator _ _ _).inv ≫ whiskerRight e.hom F' ≫ α)).IsUniversal :=
  (RightExtension.isUniversalPostcomp₁Equiv G e F _).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨eq (isUniversalOfIsRightKanExtension _ _)⟩⟩
  · exact fun _ => ⟨⟨eq.symm (isUniversalOfIsRightKanExtension _ _)⟩⟩

end

section

variable (L : C ⥤ D) (F : C ⥤ H) (G : H ⥤ D')

set_option backward.defeqAttrib.useBackward true in
/-- Given a left extension `E` of `F : C ⥤ H` along `L : C ⥤ D` and a functor `G : H ⥤ D'`,
`E.postcompose₂ G` is the extension of `F ⋙ G` along `L` obtained by whiskering by `G`
on the right. -/
@[simps!, implicit_reducible]
/-
**CategoryTheory.Functor.LeftExtension.postcompose** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a left extension `E` of `F : C ⥤ H` along `L : C ⥤ D` and a functor `G : H
 ⥤ D'`,
`E.postcompose₂ G` is the extension of `F ⋙ G` along `L` obtained by whiskering 
by `G`
on the right.
-/
def LeftExtension.postcompose₂ : LeftExtension L F ⥤ LeftExtension L (F ⋙ G) :=
  StructuredArrow.map₂
    (F := (whiskeringRight _ _ _).obj G)
    (G := (whiskeringRight _ _ _).obj G)
    (𝟙 _) ({ app _ := (associator _ _ _).hom })

set_option backward.defeqAttrib.useBackward true in
/-- Given a right extension `E` of `F : C ⥤ H` along `L : C ⥤ D` and a functor `G : H ⥤ D'`,
`E.postcompose₂ G` is the extension of `F ⋙ G` along `L` obtained by whiskering by `G`
on the right. -/
@[simps!, implicit_reducible]
/-
**CategoryTheory.Functor.RightExtension.postcompose** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a right extension `E` of `F : C ⥤ H` along `L : C ⥤ D` and a functor `G : 
H ⥤ D'`,
`E.postcompose₂ G` is the extension of `F ⋙ G` along `L` obtained by whiskering 
by `G`
on the right.
-/
def RightExtension.postcompose₂ : RightExtension L F ⥤ RightExtension L (F ⋙ G) :=
  CostructuredArrow.map₂
    (F := (whiskeringRight _ _ _).obj G)
    (G := (whiskeringRight _ _ _).obj G)
    ({ app _ := associator _ _ _ |>.inv }) (𝟙 _)

variable {L F} {F' : D ⥤ H}
set_option backward.isDefEq.respectTransparency.types false in
/-- An isomorphism to describe the action of `LeftExtension.postcompose₂` on terms of the form
`LeftExtension.mk _ α`. -/
@[simps!]
/-
**CategoryTheory.Functor.LeftExtension.postcompose** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism to describe the action of `LeftExtension.postcompose₂` on terms o
f the form
`LeftExtension.mk _ α`.
-/
def LeftExtension.postcompose₂ObjMkIso (α : F ⟶ L ⋙ F') :
    (LeftExtension.postcompose₂ L F G).obj (.mk F' α) ≅
    .mk (F' ⋙ G) <| whiskerRight α G ≫ (associator _ _ _).hom :=
  StructuredArrow.isoMk (.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An isomorphism to describe the action of `RightExtension.postcompose₂` on terms of the form
`RightExtension.mk _ α`. -/
@[simps!]
/-
**CategoryTheory.Functor.RightExtension.postcompose** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism to describe the action of `RightExtension.postcompose₂` on terms 
of the form
`RightExtension.mk _ α`.
-/
def RightExtension.postcompose₂ObjMkIso (α : L ⋙ F' ⟶ F) :
    (RightExtension.postcompose₂ L F G).obj (.mk F' α) ≅
    .mk (F' ⋙ G) <| (associator _ _ _).inv ≫ whiskerRight α G :=
  CostructuredArrow.isoMk (.refl _)

end

section

variable (L : C ⥤ D) (F : C ⥤ H) (F' : D ⥤ H) (G : C' ⥤ C)

/-- The functor `LeftExtension L F ⥤ LeftExtension (G ⋙ L) (G ⋙ F)`
obtained by precomposition. -/
@[simps!, implicit_reducible]
/-
**CategoryTheory.Functor.LeftExtension.precomp** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor.LeftExtension`。
形式化陈述：{C : Type u_1} →   {C' : Type u_2} →     {H : Type u_3} →       {D : Type 
u_4} →         [inst : CategoryTheory.Category.{v_1, u_1} C] →           [inst_1
 : CategoryTheory.Category.{v_2, u_2} C'] →             [inst_2 : CategoryTheory
.Category.{v_3, u_3} H] →               [inst_3 : CategoryTheory.Category.{v_4, 
u_4} D] →                 (L : CategoryTheory.Functor C D) →                   (
F : CategoryTheory.Functor C H) →                     (G : CategoryTheory.Functo
r C' C) →                       CategoryTheory.Functor (L.LeftExtension F) ((G.c
omp L).LeftExtension (G.comp F))
参数：L : CategoryTheory.Functor C D；F : CategoryTheory.Functor C H；G : CategoryThe
ory.Functor C' C；L.LeftExtension F；(G.comp L).LeftExtension (G.comp F)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `LeftExtension L F ⥤ LeftExtension (G ⋙ L) (G ⋙ F)`
obtained by precomposition.
-/
def LeftExtension.precomp : LeftExtension L F ⥤ LeftExtension (G ⋙ L) (G ⋙ F) :=
  StructuredArrow.map₂ (F := 𝟭 _) (G := (whiskeringLeft C' C H).obj G) (𝟙 _) (𝟙 _)

/-- The functor `RightExtension L F ⥤ RightExtension (G ⋙ L) (G ⋙ F)`
obtained by precomposition. -/
@[simps!, implicit_reducible]
/-
**CategoryTheory.Functor.RightExtension.precomp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor.RightExtension`。
形式化陈述：{C : Type u_1} →   {C' : Type u_2} →     {H : Type u_3} →       {D : Type 
u_4} →         [inst : CategoryTheory.Category.{v_1, u_1} C] →           [inst_1
 : CategoryTheory.Category.{v_2, u_2} C'] →             [inst_2 : CategoryTheory
.Category.{v_3, u_3} H] →               [inst_3 : CategoryTheory.Category.{v_4, 
u_4} D] →                 (L : CategoryTheory.Functor C D) →                   (
F : CategoryTheory.Functor C H) →                     (G : CategoryTheory.Functo
r C' C) →                       CategoryTheory.Functor (L.RightExtension F) ((G.
comp L).RightExtension (G.comp F))
参数：L : CategoryTheory.Functor C D；F : CategoryTheory.Functor C H；G : CategoryThe
ory.Functor C' C；L.RightExtension F；(G.comp L).RightExtension (G.comp F)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `RightExtension L F ⥤ RightExtension (G ⋙ L) (G ⋙ F)`
obtained by precomposition.
-/
def RightExtension.precomp : RightExtension L F ⥤ RightExtension (G ⋙ L) (G ⋙ F) :=
  CostructuredArrow.map₂ (F := 𝟭 _) (G := (whiskeringLeft C' C H).obj G) (𝟙 _) (𝟙 _)

variable [IsEquivalence G]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : IsEquivalence (LeftExtension.precomp L F G) := by
  apply StructuredArrow.isEquivalenceMap₂

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : IsEquivalence (RightExtension.precomp L F G) := by
  apply CostructuredArrow.isEquivalenceMap₂

/-- If `G` is an equivalence, then a left extension of `F` along `L` is universal iff
the corresponding left extension of `G ⋙ F` along `G ⋙ L` is. -/
/-
**CategoryTheory.Functor.LeftExtension.isUniversalPrecompEquiv** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：{C : Type u_1} →   {C' : Type u_2} →     {H : Type u_3} →       {D : Type 
u_4} →         [inst : CategoryTheory.Category.{v_1, u_1} C] →           [inst_1
 : CategoryTheory.Category.{v_2, u_2} C'] →             [inst_2 : CategoryTheory
.Category.{v_3, u_3} H] →               [inst_3 : CategoryTheory.Category.{v_4, 
u_4} D] →                 (L : CategoryTheory.Functor C D) →                   (
F : CategoryTheory.Functor C H) →                     (G : CategoryTheory.Functo
r C' C) →                       [G.IsEquivalence] →                         (e :
 L.LeftExtension F) →                           CategoryTheory.StructuredArrow.I
sUniversal e ≃                             CategoryTheory.StructuredArrow.IsUniv
ersal                               ((CategoryTheory.Functor.LeftExtension.preco
mp L F G).obj e)
参数：L : CategoryTheory.Functor C D；F : CategoryTheory.Functor C H；G : CategoryThe
ory.Functor C' C；e : L.LeftExtension F；(CategoryTheory.Functor.LeftExtension.pre
comp L F G).obj e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is an equivalence, then a left extension of `F` along `L` is universal if
f
the corresponding left extension of `G ⋙ F` along `G ⋙ L` is.
-/
noncomputable def LeftExtension.isUniversalPrecompEquiv (e : LeftExtension L F) :
    e.IsUniversal ≃ ((LeftExtension.precomp L F G).obj e).IsUniversal := by
  apply IsInitial.isInitialIffObj (LeftExtension.precomp L F G)

/-- If `G` is an equivalence, then a right extension of `F` along `L` is universal iff
the corresponding left extension of `G ⋙ F` along `G ⋙ L` is. -/
/-
**CategoryTheory.Functor.RightExtension.isUniversalPrecompEquiv** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Functor.RightExtension`。
形式化陈述：{C : Type u_1} →   {C' : Type u_2} →     {H : Type u_3} →       {D : Type 
u_4} →         [inst : CategoryTheory.Category.{v_1, u_1} C] →           [inst_1
 : CategoryTheory.Category.{v_2, u_2} C'] →             [inst_2 : CategoryTheory
.Category.{v_3, u_3} H] →               [inst_3 : CategoryTheory.Category.{v_4, 
u_4} D] →                 (L : CategoryTheory.Functor C D) →                   (
F : CategoryTheory.Functor C H) →                     (G : CategoryTheory.Functo
r C' C) →                       [G.IsEquivalence] →                         (e :
 L.RightExtension F) →                           CategoryTheory.CostructuredArro
w.IsUniversal e ≃                             CategoryTheory.CostructuredArrow.I
sUniversal                               ((CategoryTheory.Functor.RightExtension
.precomp L F G).obj e)
参数：L : CategoryTheory.Functor C D；F : CategoryTheory.Functor C H；G : CategoryThe
ory.Functor C' C；e : L.RightExtension F；(CategoryTheory.Functor.RightExtension.p
recomp L F G).obj e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is an equivalence, then a right extension of `F` along `L` is universal i
ff
the corresponding left extension of `G ⋙ F` along `G ⋙ L` is.
-/
noncomputable def RightExtension.isUniversalPrecompEquiv (e : RightExtension L F) :
    e.IsUniversal ≃ ((RightExtension.precomp L F G).obj e).IsUniversal := by
  apply IsTerminal.isTerminalIffObj (RightExtension.precomp L F G)

variable {F L}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.isLeftKanExtension_iff_precomp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：isLeftKanExtension_iff_precomp (α : F ⟶ L ⋙ F') : F'.IsLeftKanExtension α 
↔ F'.IsLeftKanExtension (whiskerLeft G α ≫ (associator _ _ _).inv)
参数：α : F ⟶ L ⋙ F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.LeftExtension.precomp_obj_hom_app`：∀ {C : Type u_
1} {C' : Type u_2} {H : Type u_3} {D : Type u_4} [inst : CategoryTheory.Category
.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cate…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma isLeftKanExtension_iff_precomp (α : F ⟶ L ⋙ F') :
    F'.IsLeftKanExtension α ↔ F'.IsLeftKanExtension
      (whiskerLeft G α ≫ (associator _ _ _).inv) := by
  let eq : (LeftExtension.mk _ α).IsUniversal ≃ (LeftExtension.mk _
      (whiskerLeft G α ≫ (associator _ _ _).inv)).IsUniversal :=
    (LeftExtension.isUniversalPrecompEquiv L F G _).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨eq (isUniversalOfIsLeftKanExtension _ _)⟩⟩
  · exact fun _ => ⟨⟨eq.symm (isUniversalOfIsLeftKanExtension _ _)⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.isRightKanExtension_iff_precomp** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：isRightKanExtension_iff_precomp (α : L ⋙ F' ⟶ F) : F'.IsRightKanExtension 
α ↔ F'.IsRightKanExtension ((associator _ _ _).hom ≫ whiskerLeft G α)
参数：α : L ⋙ F' ⟶ F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.RightExtension.precomp_obj_hom_app`：∀ {C : Type u
_1} {C' : Type u_2} {H : Type u_3} {D : Type u_4} [inst : CategoryTheory.Categor
y.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cate…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma isRightKanExtension_iff_precomp (α : L ⋙ F' ⟶ F) :
    F'.IsRightKanExtension α ↔
      F'.IsRightKanExtension ((associator _ _ _).hom ≫ whiskerLeft G α) := by
  let eq : (RightExtension.mk _ α).IsUniversal ≃ (RightExtension.mk _
      ((associator _ _ _).hom ≫ whiskerLeft G α)).IsUniversal :=
    (RightExtension.isUniversalPrecompEquiv L F G _).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨eq (isUniversalOfIsRightKanExtension _ _)⟩⟩
  · exact fun _ => ⟨⟨eq.symm (isUniversalOfIsRightKanExtension _ _)⟩⟩

end

section

variable {L L' : C ⥤ D} (iso₁ : L ≅ L') (F : C ⥤ H)

/-- The equivalence `RightExtension L F ≌ RightExtension L' F` induced by
a natural isomorphism `L ≅ L'`. -/
-- TODO: Should this be `@[simps!]` too?
/-
**CategoryTheory.Functor.rightExtensionEquivalenceOfIso** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def rightExtensionEquivalenceOfIso₁ : RightExtension L F ≌ RightExtension L' F :=
  CostructuredArrow.mapNatIso ((whiskeringLeft C D H).mapIso iso₁)

include iso₁ in
/-
**CategoryTheory.Functor.hasRightExtension_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasRightExtension_iff_of_iso₁ : HasRightKanExtension L F ↔ HasRightKanExtension L' F :=
  (rightExtensionEquivalenceOfIso₁ iso₁ F).hasTerminal_iff

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence `LeftExtension L F ≌ LeftExtension L' F` induced by
a natural isomorphism `L ≅ L'`. -/
@[simps!, implicit_reducible]
/-
**CategoryTheory.Functor.leftExtensionEquivalenceOfIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `LeftExtension L F ≌ LeftExtension L' F` induced by
a natural isomorphism `L ≅ L'`.
-/
def leftExtensionEquivalenceOfIso₁ : LeftExtension L F ≌ LeftExtension L' F :=
  StructuredArrow.mapNatIso ((whiskeringLeft C D H).mapIso iso₁)

include iso₁ in
/-
**CategoryTheory.Functor.hasLeftExtension_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasLeftExtension_iff_of_iso₁ : HasLeftKanExtension L F ↔ HasLeftKanExtension L' F :=
  (leftExtensionEquivalenceOfIso₁ iso₁ F).hasInitial_iff

end

section

variable (L : C ⥤ D) {F F' : C ⥤ H} (iso₂ : F ≅ F')

/-- The equivalence `RightExtension L F ≌ RightExtension L F'` induced by
a natural isomorphism `F ≅ F'`. -/
/-
**CategoryTheory.Functor.rightExtensionEquivalenceOfIso** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `RightExtension L F ≌ RightExtension L F'` induced by
a natural isomorphism `F ≅ F'`.
-/
def rightExtensionEquivalenceOfIso₂ : RightExtension L F ≌ RightExtension L F' :=
  CostructuredArrow.mapIso iso₂

include iso₂ in
/-
**CategoryTheory.Functor.hasRightExtension_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasRightExtension_iff_of_iso₂ : HasRightKanExtension L F ↔ HasRightKanExtension L F' :=
  (rightExtensionEquivalenceOfIso₂ L iso₂).hasTerminal_iff

/-- The equivalence `LeftExtension L F ≌ LeftExtension L F'` induced by
a natural isomorphism `F ≅ F'`. -/
/-
**CategoryTheory.Functor.leftExtensionEquivalenceOfIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `LeftExtension L F ≌ LeftExtension L F'` induced by
a natural isomorphism `F ≅ F'`.
-/
def leftExtensionEquivalenceOfIso₂ : LeftExtension L F ≌ LeftExtension L F' :=
  StructuredArrow.mapIso iso₂

include iso₂ in
/-
**CategoryTheory.Functor.hasLeftExtension_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasLeftExtension_iff_of_iso₂ : HasLeftKanExtension L F ↔ HasLeftKanExtension L F' :=
  (leftExtensionEquivalenceOfIso₂ L iso₂).hasInitial_iff

end

section

variable {L : C ⥤ D} {F₁ F₂ : C ⥤ H}

set_option backward.isDefEq.respectTransparency false in
/-- When two left extensions `α₁ : LeftExtension L F₁` and `α₂ : LeftExtension L F₂`
are essentially the same via an isomorphism of functors `F₁ ≅ F₂`,
then `α₁` is universal iff `α₂` is. -/
/-
**CategoryTheory.Functor.LeftExtension.isUniversalEquivOfIso** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When two left extensions `α₁ : LeftExtension L F₁` and `α₂ : LeftExtension L F₂`
are essentially the same via an isomorphism of functors `F₁ ≅ F₂`,
then `α₁` is universal iff `α₂` is.
-/
noncomputable def LeftExtension.isUniversalEquivOfIso₂
    (α₁ : LeftExtension L F₁) (α₂ : LeftExtension L F₂) (e : F₁ ≅ F₂)
    (e' : α₁.right ≅ α₂.right)
    (h : α₁.hom ≫ whiskerLeft L e'.hom = e.hom ≫ α₂.hom) :
    α₁.IsUniversal ≃ α₂.IsUniversal :=
  (IsInitial.isInitialIffObj (leftExtensionEquivalenceOfIso₂ L e).functor α₁).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk e'
      (by simp [leftExtensionEquivalenceOfIso₂, h])))
/-
**CategoryTheory.Functor.isLeftKanExtension_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：isLeftKanExtension_iff_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} 
{F : C ⥤ H} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'') (comm : α ≫ whiskerLeft L e.hom 
= α') : F'.IsLeftKanExtension α ↔ F''.IsLeftKanExtension α'
参数：e : F' ≅ F''；α : F ⟶ L ⋙ F'；α' : F ⟶ L ⋙ F''；comm : α ≫ whiskerLeft L e.hom =
 α'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isLeftKanExtension_of_iso`：isLeftKanExtension_of_
iso {F' : D ⥤ H} {F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L
 ⋙ F') (α' : F ⟶ L ⋙ F'') (comm : α ≫ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.whiskerLeft_comp`：whiskerLeft_comp (F : C ⥤ D) {G
 H K : D ⥤ E} (α : G ⟶ H) (β : H ⟶ K) : whiskerLeft F (α ≫ β) = whiskerLeft F α 
≫ whiskerLeft F β
· 使用定理 `CategoryTheory.Iso.symm_hom`：symm_hom (α : X ≅ Y) : α.symm.hom = α.inv
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Functor.whiskerLeft_id'`：whiskerLeft_id' (F : C ⥤ D) {G :
 D ⥤ E} : whiskerLeft F (𝟙 G) = 𝟙 (F.comp G)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma isLeftKanExtension_iff_of_iso₂ {F₁' F₂' : D ⥤ H} (α₁ : F₁ ⟶ L ⋙ F₁') (α₂ : F₂ ⟶ L ⋙ F₂')
    (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') (h : α₁ ≫ whiskerLeft L e'.hom = e.hom ≫ α₂) :
    F₁'.IsLeftKanExtension α₁ ↔ F₂'.IsLeftKanExtension α₂ := by
  let eq := LeftExtension.isUniversalEquivOfIso₂ (LeftExtension.mk _ α₁)
    (LeftExtension.mk _ α₂) e e' h
  constructor
  · exact fun _ => ⟨⟨eq.1 (isUniversalOfIsLeftKanExtension F₁' α₁)⟩⟩
  · exact fun _ => ⟨⟨eq.2 (isUniversalOfIsLeftKanExtension F₂' α₂)⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- When two right extensions `α₁ : RightExtension L F₁` and `α₂ : RightExtension L F₂`
are essentially the same via an isomorphism of functors `F₁ ≅ F₂`,
then `α₁` is universal iff `α₂` is. -/
/-
**CategoryTheory.Functor.RightExtension.isUniversalEquivOfIso** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When two right extensions `α₁ : RightExtension L F₁` and `α₂ : RightExtension L 
F₂`
are essentially the same via an isomorphism of functors `F₁ ≅ F₂`,
then `α₁` is universal iff `α₂` is.
-/
noncomputable def RightExtension.isUniversalEquivOfIso₂
    (α₁ : RightExtension L F₁) (α₂ : RightExtension L F₂) (e : F₁ ≅ F₂)
    (e' : α₁.left ≅ α₂.left)
    (h : whiskerLeft L e'.hom ≫ α₂.hom = α₁.hom ≫ e.hom) :
    α₁.IsUniversal ≃ α₂.IsUniversal :=
  (IsTerminal.isTerminalIffObj (rightExtensionEquivalenceOfIso₂ L e).functor α₁).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk e'
      (by simp [rightExtensionEquivalenceOfIso₂, h])))
/-
**CategoryTheory.Functor.isRightKanExtension_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：isRightKanExtension_iff_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D}
 {F : C ⥤ H} (α : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : whiskerLeft L e.hom ≫ α
' = α) : F'.IsRightKanExtension α ↔ F''.IsRightKanExtension α'
参数：e : F' ≅ F''；α : L ⋙ F' ⟶ F；α' : L ⋙ F'' ⟶ F；comm : whiskerLeft L e.hom ≫ α' 
= α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isRightKanExtension_of_iso`：isRightKanExtension_o
f_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F) (
α' : L ⋙ F'' ⟶ F) (comm : whiskerLeft L…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.whiskerLeft_comp_assoc`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Iso.symm_hom`：symm_hom (α : X ≅ Y) : α.symm.hom = α.inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Functor.whiskerLeft_id'`：whiskerLeft_id' (F : C ⥤ D) {G :
 D ⥤ E} : whiskerLeft F (𝟙 G) = 𝟙 (F.comp G)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma isRightKanExtension_iff_of_iso₂ {F₁' F₂' : D ⥤ H} (α₁ : L ⋙ F₁' ⟶ F₁) (α₂ : L ⋙ F₂' ⟶ F₂)
    (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') (h : whiskerLeft L e'.hom ≫ α₂ = α₁ ≫ e.hom) :
    F₁'.IsRightKanExtension α₁ ↔ F₂'.IsRightKanExtension α₂ := by
  let eq := RightExtension.isUniversalEquivOfIso₂ (RightExtension.mk _ α₁)
    (RightExtension.mk _ α₂) e e' h
  constructor
  · exact fun _ => ⟨⟨eq.1 (isUniversalOfIsRightKanExtension F₁' α₁)⟩⟩
  · exact fun _ => ⟨⟨eq.2 (isUniversalOfIsRightKanExtension F₂' α₂)⟩⟩

end

section transitivity

/-- A variant of `LeftExtension.precomp` where we precompose, and then
"whisker" the diagram by a given natural transformation `(α : F₀ ⟶ L ⋙ F₁)` -/
@[simps!]
/-
**CategoryTheory.Functor.LeftExtension.precomp** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor.LeftExtension`。
形式化陈述：{C : Type u_1} →   {C' : Type u_2} →     {H : Type u_3} →       {D : Type 
u_4} →         [inst : CategoryTheory.Category.{v_1, u_1} C] →           [inst_1
 : CategoryTheory.Category.{v_2, u_2} C'] →             [inst_2 : CategoryTheory
.Category.{v_3, u_3} H] →               [inst_3 : CategoryTheory.Category.{v_4, 
u_4} D] →                 (L : CategoryTheory.Functor C D) →                   (
F : CategoryTheory.Functor C H) →                     (G : CategoryTheory.Functo
r C' C) →                       CategoryTheory.Functor (L.LeftExtension F) ((G.c
omp L).LeftExtension (G.comp F))
参数：L : CategoryTheory.Functor C D；F : CategoryTheory.Functor C H；G : CategoryThe
ory.Functor C' C；L.LeftExtension F；(G.comp L).LeftExtension (G.comp F)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `LeftExtension.precomp` where we precompose, and then
"whisker" the diagram by a given natural transformation `(α : F₀ ⟶ L ⋙ F₁)`
-/
def LeftExtension.precomp₂
    {F₀ : C ⥤ H} {L : C ⥤ D} {F₁ : D ⥤ H} (L' : D ⥤ D') (α : F₀ ⟶ L ⋙ F₁) :
    L'.LeftExtension F₁ ⥤ (L ⋙ L').LeftExtension F₀ :=
  LeftExtension.precomp L' F₁ L ⋙ StructuredArrow.map α

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/
attribute [nolint simpNF] _root_.CategoryTheory.Functor.LeftExtension.precomp₂_map_left

variable
    {L : C ⥤ D} {L' : D ⥤ D'}
    {F₀ : C ⥤ H} {F₁ : D ⥤ H} {F₂ : D' ⥤ H}
    (α : F₀ ⟶ L ⋙ F₁)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If the right extension defined by `α : F₀ ⟶ L ⋙ F₁` is universal,
then for every `L' : D ⥤ D'`, `F₁ : D ⥤ H`, if an extension
`b : L'.LeftExtension F₁` is universal, so is the "pasted" extension
`(LeftExtension.precomp₂ L' α).obj b`. -/
/-
**CategoryTheory.Functor.LeftExtension.isUniversalPrecomp** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the right extension defined by `α : F₀ ⟶ L ⋙ F₁` is universal,
then for every `L' : D ⥤ D'`, `F₁ : D ⥤ H`, if an extension
`b : L'.LeftExtension F₁` is universal, so is the "pasted" extension
`(LeftExtension.precomp₂ L' α).obj b`.
-/
def LeftExtension.isUniversalPrecomp₂
    (hα : (LeftExtension.mk F₁ α).IsUniversal)
    {b : L'.LeftExtension F₁} (hb : b.IsUniversal) :
    ((LeftExtension.precomp₂ L' α).obj b).IsUniversal := by
  letI (y : (L ⋙ L').LeftExtension F₀) :
      Unique ((precomp₂ L' α).obj b ⟶ y) := by
    let u : L'.LeftExtension F₁ :=
      mk y.right <|
        hα.desc <| LeftExtension.mk _ <|
          y.hom ≫ (L.associator L' y.right).hom
    refine
      ⟨⟨StructuredArrow.homMk (hb.desc u) <| by
          ext x
          have hb_fac_app := congr_app (hb.fac u) (L.obj x)
          have hα_fac_app :=
            congr_app (hα.fac <| LeftExtension.mk _ <|
              y.hom ≫ (L.associator L' y.right).hom) x
          dsimp at hα_fac_app hb_fac_app
          simp [hb_fac_app, u, hα_fac_app]⟩, fun a => ?_⟩
    dsimp
    ext1
    apply hb.hom_ext
    apply hα.hom_ext
    ext t
    dsimp
    have a_w_t := congr_app a.w t
    have hb_fac_app := congr_app (hb.fac u) (L.obj t)
    have hα_fac_app :=
      congr_app
        (hα.fac <| LeftExtension.mk _ <|
          y.hom ≫ (L.associator L' y.right).hom) t
    dsimp at hb_fac_app hα_fac_app
    simp only [whiskeringLeft_obj_obj, comp_obj,
      precomp₂_obj_right, whiskeringLeft_obj_map, NatTrans.comp_app,
      precomp₂_obj_hom_app, whiskerLeft_app, assoc] at a_w_t
    simp [← a_w_t, hb_fac_app, u, hα_fac_app]
  apply IsInitial.ofUnique

set_option backward.isDefEq.respectTransparency.types false in
/-- If the left extension defined by `α : F₀ ⟶ L ⋙ F₁` is universal,
then for every `L' : D ⥤ D'`, `F₁ : D ⥤ H`, if an extension
`b : L'.LeftExtension F₁` is such that the "pasted" extension
`(LeftExtension.precomp₂ L' α).obj b` is universal, then `b` is itself
universal. -/
/-
**CategoryTheory.Functor.LeftExtension.isUniversalOfPrecomp** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the left extension defined by `α : F₀ ⟶ L ⋙ F₁` is universal,
then for every `L' : D ⥤ D'`, `F₁ : D ⥤ H`, if an extension
`b : L'.LeftExtension F₁` is such that the "pasted" extension
`(LeftExtension.precomp₂ L' α).obj b` is universal, then `b` is itself
universal.
-/
def LeftExtension.isUniversalOfPrecomp₂
    (hα : (LeftExtension.mk F₁ α).IsUniversal)
    {b : L'.LeftExtension F₁}
    (hb : ((LeftExtension.precomp₂ L' α).obj b).IsUniversal) :
    b.IsUniversal := by
  letI (y : L'.LeftExtension F₁) : Unique (b ⟶ y) := by
    let u : (LeftExtension.precomp₂ L' α).obj b ⟶
      (LeftExtension.precomp₂ L' α).obj y := hb.to _
    refine
      ⟨⟨StructuredArrow.homMk u.right <| by
          apply hα.hom_ext
          ext t
          have := congr_app u.w t
          dsimp at this
          simp only [precomp₂_obj_hom_app, assoc] at this
          simp [this]⟩, fun a => ?_⟩
    ext1
    apply hb.hom_ext
    ext t
    have := congr_app u.w t
    dsimp at this
    simp only [precomp₂_obj_hom_app, assoc] at this
    simp [this, ← a.w]
  apply IsInitial.ofUnique

/-- If the left extension defined by `α : F₀ ⟶ L ⋙ F₁` is universal,
then for every `L' : D ⥤ D'`, `F₁ : D ⥤ H`, an extension
`b : L'.LeftExtension F₁` is universal if and only if
`(LeftExtension.precomp₂ L' α).obj b` is universal. -/
/-
**CategoryTheory.Functor.LeftExtension.isUniversalPrecomp** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the left extension defined by `α : F₀ ⟶ L ⋙ F₁` is universal,
then for every `L' : D ⥤ D'`, `F₁ : D ⥤ H`, an extension
`b : L'.LeftExtension F₁` is universal if and only if
`(LeftExtension.precomp₂ L' α).obj b` is universal.
-/
def LeftExtension.isUniversalPrecomp₂Equiv
    (hα : (LeftExtension.mk F₁ α).IsUniversal)
    (b : L'.LeftExtension F₁) :
    b.IsUniversal ≃ ((LeftExtension.precomp₂ L' α).obj b).IsUniversal where
  toFun h := LeftExtension.isUniversalPrecomp₂ α hα h
  invFun h := LeftExtension.isUniversalOfPrecomp₂ α hα h
  left_inv x := by subsingleton
  right_inv x := by subsingleton


set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.isLeftKanExtension_iff_postcompose** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：isLeftKanExtension_iff_postcompose [F₁.IsLeftKanExtension α] {F₂ : D' ⥤ H}
 (L'' : C ⥤ D') (e : L ⋙ L' ≅ L'') (β : F₁ ⟶ L' ⋙ F₂) (γ : F₀ ⟶ L'' ⋙ F₂) (hγ : 
α ≫ whiskerLeft _ β ≫ (Functor.associator _ _ _).inv ≫ whiskerRight e.hom F₂ = γ
参数：L'' : C ⥤ D'；e : L ⋙ L' ≅ L''；β : F₁ ⟶ L' ⋙ F₂；γ : F₀ ⟶ L'' ⋙ F₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.CreatesColimit.toReflectsColimit`：∀ {C : Type u₁} {inst :
 CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.LeftExtension.precomp₂_obj_hom_app`：∀ {C : Type u
_1} {H : Type u_3} {D : Type u_4} {D' : Type u_5} [inst : CategoryTheory.Categor
y.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cate…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
theorem isLeftKanExtension_iff_postcompose [F₁.IsLeftKanExtension α]
    {F₂ : D' ⥤ H} (L'' : C ⥤ D') (e : L ⋙ L' ≅ L'') (β : F₁ ⟶ L' ⋙ F₂)
    (γ : F₀ ⟶ L'' ⋙ F₂)
    (hγ :
      α ≫ whiskerLeft _ β ≫
        (Functor.associator _ _ _).inv ≫ whiskerRight e.hom F₂ =
      γ := by aesop_cat) :
    F₂.IsLeftKanExtension β ↔ F₂.IsLeftKanExtension γ := by
  let Ψ := leftExtensionEquivalenceOfIso₁ e F₀
  obtain ⟨⟨hα⟩⟩ := (inferInstance : F₁.IsLeftKanExtension α)
  refine ⟨fun ⟨⟨h⟩⟩ => ⟨⟨?_⟩⟩, fun ⟨⟨h⟩⟩ => ⟨⟨?_⟩⟩⟩
  · apply IsInitial.isInitialIffObj Ψ.inverse _ |>.invFun
    haveI := LeftExtension.isUniversalPrecomp₂ α hα h
    let i :
        (LeftExtension.precomp₂ L' α).obj (LeftExtension.mk F₂ β) ≅
        Ψ.inverse.obj (LeftExtension.mk F₂ γ) :=
      StructuredArrow.isoMk (NatIso.ofComponents fun _ ↦ .refl _) <| by
        ext x
        simp [Ψ, ← congr_app hγ x, ← Functor.map_comp]
    exact IsInitial.ofIso this i
  · apply LeftExtension.isUniversalOfPrecomp₂ α hα
    apply IsInitial.isInitialIffObj Ψ.functor _ |>.invFun
    let i :
        (LeftExtension.mk F₂ γ) ≅
        Ψ.functor.obj <| (LeftExtension.precomp₂ L' α).obj <|
          LeftExtension.mk F₂ β :=
      StructuredArrow.isoMk (NatIso.ofComponents fun _ ↦ .refl _)
    exact IsInitial.ofIso h i

end transitivity

section Colimit

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') [F'.IsLeftKanExtension α]

/-- Construct a cocone for a left Kan extension `F' : D ⥤ H` of `F : C ⥤ H` along a functor
`L : C ⥤ D` given a cocone for `F`. -/
@[simps]
/-
**CategoryTheory.Functor.coconeOfIsLeftKanExtension** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：coconeOfIsLeftKanExtension (c : Cocone F) : Cocone F' where pt
参数：c : Cocone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a cocone for a left Kan extension `F' : D ⥤ H` of `F : C ⥤ H` along a 
functor
`L : C ⥤ D` given a cocone for `F`.
-/
noncomputable def coconeOfIsLeftKanExtension (c : Cocone F) : Cocone F' where
  pt := c.pt
  ι := F'.descOfIsLeftKanExtension α _ c.ι

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a colimit cocone for a functor `F : C ⥤ H` and `α : F ⟶ L ⋙ F'` is the unit of any
left Kan extension `F' : D ⥤ H` of `F` along `L : C ⥤ D`, then `coconeOfIsLeftKanExtension α c` is
a colimit cocone, too. -/
@[simps]
/-
**CategoryTheory.Functor.isColimitCoconeOfIsLeftKanExtension** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isColimitCoconeOfIsLeftKanExtension {c : Cocone F} (hc : IsColimit c) : Is
Colimit (F'.coconeOfIsLeftKanExtension α c) where desc s
参数：hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a colimit cocone for a functor `F : C ⥤ H` and `α : F ⟶ L ⋙ F'` is the
 unit of any
left Kan extension `F' : D ⥤ H` of `F` along `L : C ⥤ D`, then `coconeOfIsLeftKa
nExtension α c` is
a colimit cocone, too.
-/
noncomputable def isColimitCoconeOfIsLeftKanExtension {c : Cocone F} (hc : IsColimit c) :
    IsColimit (F'.coconeOfIsLeftKanExtension α c) where
  desc s := hc.desc (Cocone.mk _ (α ≫ whiskerLeft L s.ι))
  fac s := by
    have : F'.descOfIsLeftKanExtension α ((const D).obj c.pt) c.ι ≫
        (Functor.const _).map (hc.desc (Cocone.mk _ (α ≫ whiskerLeft L s.ι))) = s.ι :=
      F'.hom_ext_of_isLeftKanExtension α _ _ (by cat_disch)
    exact congr_app this
  uniq s m hm := hc.hom_ext (fun j ↦ by
    have := hm (L.obj j)
    nth_rw 1 [← F'.descOfIsLeftKanExtension_fac_app α ((const D).obj c.pt)]
    dsimp at this ⊢
    rw [assoc, this, IsColimit.fac, NatTrans.comp_app, whiskerLeft_app])

variable [HasColimit F] [HasColimit F']

/-- If `F' : D ⥤ H` is a left Kan extension of `F : C ⥤ H` along `L : C ⥤ D`, the colimit over `F'`
is isomorphic to the colimit over `F`. -/
/-
**CategoryTheory.Functor.colimitIsoOfIsLeftKanExtension** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：colimitIsoOfIsLeftKanExtension : colimit F' ≅ colimit F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F' : D ⥤ H` is a left Kan extension of `F : C ⥤ H` along `L : C ⥤ D`, the co
limit over `F'`
is isomorphic to the colimit over `F`.
-/
noncomputable def colimitIsoOfIsLeftKanExtension : colimit F' ≅ colimit F :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit F')
    (F'.isColimitCoconeOfIsLeftKanExtension α (colimit.isColimit F))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_colimitIsoOfIsLeftKanExtension_hom (i : C) :
    α.app i ≫ colimit.ι F' (L.obj i) ≫ (F'.colimitIsoOfIsLeftKanExtension α).hom =
      colimit.ι F i := by
  simp [colimitIsoOfIsLeftKanExtension]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_colimitIsoOfIsLeftKanExtension_inv (i : C) :
    colimit.ι F i ≫ (F'.colimitIsoOfIsLeftKanExtension α).inv =
    α.app i ≫ colimit.ι F' (L.obj i) := by
  rw [Iso.comp_inv_eq, assoc, ι_colimitIsoOfIsLeftKanExtension_hom]

end Colimit

section Limit

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F) [F'.IsRightKanExtension α]

/-- Construct a cone for a right Kan extension `F' : D ⥤ H` of `F : C ⥤ H` along a functor
`L : C ⥤ D` given a cone for `F`. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.Functor.coneOfIsRightKanExtension** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：coneOfIsRightKanExtension (c : Cone F) : Cone F' where pt
参数：c : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a cone for a right Kan extension `F' : D ⥤ H` of `F : C ⥤ H` along a f
unctor
`L : C ⥤ D` given a cone for `F`.
-/
noncomputable def coneOfIsRightKanExtension (c : Cone F) : Cone F' where
  pt := c.pt
  π := F'.liftOfIsRightKanExtension α _ c.π

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a limit cone for a functor `F : C ⥤ H` and `α : L ⋙ F' ⟶ F` is the counit of any
right Kan extension `F' : D ⥤ H` of `F` along `L : C ⥤ D`, then `coneOfIsRightKanExtension α c` is
a limit cone, too. -/
@[simps]
/-
**CategoryTheory.Functor.isLimitConeOfIsRightKanExtension** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：isLimitConeOfIsRightKanExtension {c : Cone F} (hc : IsLimit c) : IsLimit (
F'.coneOfIsRightKanExtension α c) where lift s
参数：hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a limit cone for a functor `F : C ⥤ H` and `α : L ⋙ F' ⟶ F` is the cou
nit of any
right Kan extension `F' : D ⥤ H` of `F` along `L : C ⥤ D`, then `coneOfIsRightKa
nExtension α c` is
a limit cone, too.
-/
noncomputable def isLimitConeOfIsRightKanExtension {c : Cone F} (hc : IsLimit c) :
    IsLimit (F'.coneOfIsRightKanExtension α c) where
  lift s := hc.lift (Cone.mk _ (whiskerLeft L s.π ≫ α))
  fac s := by
    have : (Functor.const _).map (hc.lift (Cone.mk _ (whiskerLeft L s.π ≫ α))) ≫
        F'.liftOfIsRightKanExtension α ((const D).obj c.pt) c.π = s.π :=
      F'.hom_ext_of_isRightKanExtension α _ _ (by cat_disch)
    exact congr_app this
  uniq s m hm := hc.hom_ext (fun j ↦ by
    have := hm (L.obj j)
    nth_rw 1 [← F'.liftOfIsRightKanExtension_fac_app α ((const D).obj c.pt)]
    dsimp at this ⊢
    rw [← assoc, this, IsLimit.fac, NatTrans.comp_app, whiskerLeft_app])

variable [HasLimit F] [HasLimit F']

/-- If `F' : D ⥤ H` is a right Kan extension of `F : C ⥤ H` along `L : C ⥤ D`, the limit over `F'`
is isomorphic to the limit over `F`. -/
/-
**CategoryTheory.Functor.limitIsoOfIsRightKanExtension** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：limitIsoOfIsRightKanExtension : limit F' ≅ limit F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F' : D ⥤ H` is a right Kan extension of `F : C ⥤ H` along `L : C ⥤ D`, the l
imit over `F'`
is isomorphic to the limit over `F`.
-/
noncomputable def limitIsoOfIsRightKanExtension : limit F' ≅ limit F :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit F')
    (F'.isLimitConeOfIsRightKanExtension α (limit.isLimit F))

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.limitIsoOfIsRightKanExtension_inv_** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limitIsoOfIsRightKanExtension_inv_π (i : C) :
    (F'.limitIsoOfIsRightKanExtension α).inv ≫ limit.π F' (L.obj i) ≫ α.app i = limit.π F i := by
  simp [limitIsoOfIsRightKanExtension]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.limitIsoOfIsRightKanExtension_hom_** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limitIsoOfIsRightKanExtension_hom_π (i : C) :
    (F'.limitIsoOfIsRightKanExtension α).hom ≫ limit.π F i = limit.π F' (L.obj i) ≫ α.app i := by
  rw [← Iso.eq_inv_comp, limitIsoOfIsRightKanExtension_inv_π]

end Limit

section

variable {L : C ≌ D} {F₀ : C ⥤ H} {F₁ : D ⥤ H}

variable (F₀) in
/-
**CategoryTheory.Functor.isLeftKanExtensionId** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：isLeftKanExtensionId : F₀.IsLeftKanExtension F₀.leftUnitor.inv where nonem
pty_isUniversal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instIsEquivalenceObjWhiskeringLeft`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance isLeftKanExtensionId : F₀.IsLeftKanExtension F₀.leftUnitor.inv where
  nonempty_isUniversal := ⟨StructuredArrow.mkIdInitial⟩

variable (F₀) in
/-
**CategoryTheory.Functor.isRightKanExtensionId** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：isRightKanExtensionId : F₀.IsRightKanExtension F₀.leftUnitor.hom where non
empty_isUniversal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instIsEquivalenceObjWhiskeringLeft`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance isRightKanExtensionId : F₀.IsRightKanExtension F₀.leftUnitor.hom where
  nonempty_isUniversal := ⟨CostructuredArrow.mkIdTerminal⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.isLeftKanExtensionAlongEquivalence** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：isLeftKanExtensionAlongEquivalence (α : F₀ ≅ L.functor ⋙ F₁) : F₁.IsLeftKa
nExtension α.hom
参数：α : F₀ ≅ L.functor ⋙ F₁。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.LeftExtension.postcomp₁_obj_hom_app`：∀ {C : Type 
u_1} {H : Type u_3} {D : Type u_4} {D' : Type u_5} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cate…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.StructuredArrow.hom_ext`：hom_ext {X Y : StructuredArrow S
 T} (f g : X ⟶ Y) (h : f.right = g.right) : f = g
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.StructuredArrow.Hom.w`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {S : D} {T : Categ…
-/
instance isLeftKanExtensionAlongEquivalence (α : F₀ ≅ L.functor ⋙ F₁) :
    F₁.IsLeftKanExtension α.hom := by
  refine ⟨⟨?_⟩⟩
  apply LeftExtension.isUniversalPostcomp₁Equiv
    (G := L.functor) L.functor.leftUnitor F₀ _ |>.invFun
  refine IsInitial.ofUniqueHom
    (fun y ↦ StructuredArrow.homMk <| α.inv ≫ y.hom ≫ y.right.leftUnitor.hom) ?_
  intro y m
  ext x
  simpa using α.inv.app x ≫= congr_app m.w x

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.isLeftKanExtensionAlongEquivalence'** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isLeftKanExtensionAlongEquivalence' (L : C ⥤ D) (α : F₀ ⟶ L ⋙ F₁) [IsEquiv
alence L] [IsIso α] : F₁.IsLeftKanExtension α
参数：L : C ⥤ D；α : F₀ ⟶ L ⋙ F₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isLeftKanExtensionAlongEquivalence' (L : C ⥤ D) (α : F₀ ⟶ L ⋙ F₁)
    [IsEquivalence L] [IsIso α] :
    F₁.IsLeftKanExtension α :=
  inferInstanceAs <|
    F₁.IsLeftKanExtension (asIso α : F₀ ≅ (asEquivalence L).functor ⋙ F₁).hom

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.isRightKanExtensionAlongEquivalence** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isRightKanExtensionAlongEquivalence (α : L.functor ⋙ F₁ ≅ F₀) : F₁.IsRight
KanExtension α.hom
参数：α : L.functor ⋙ F₁ ≅ F₀。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Functor.RightExtension.postcomp₁_obj_hom_app`：∀ {C : Type
 u_1} {H : Type u_3} {D : Type u_4} {D' : Type u_5} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cate…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.CostructuredArrow.hom_ext`：hom_ext {X Y : CostructuredArr
ow S T} (f g : X ⟶ Y) (h : f.left = g.left) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…
-/
instance isRightKanExtensionAlongEquivalence (α : L.functor ⋙ F₁ ≅ F₀) :
    F₁.IsRightKanExtension α.hom := by
  refine ⟨⟨?_⟩⟩
  apply RightExtension.isUniversalPostcomp₁Equiv
    (G := L.functor) L.functor.leftUnitor F₀ _ |>.invFun
  refine IsTerminal.ofUniqueHom
    (fun y ↦ CostructuredArrow.homMk <| y.left.leftUnitor.inv ≫ y.hom ≫ α.inv) ?_
  intro y m
  ext x
  simpa using congr_app m.w x =≫ α.inv.app x

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.isRightKanExtensionAlongEquivalence'** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isRightKanExtensionAlongEquivalence' (L : C ⥤ D) (α : L ⋙ F₁ ⟶ F₀) [IsEqui
valence L] [IsIso α] : F₁.IsRightKanExtension α
参数：L : C ⥤ D；α : L ⋙ F₁ ⟶ F₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isRightKanExtensionAlongEquivalence' (L : C ⥤ D) (α : L ⋙ F₁ ⟶ F₀)
    [IsEquivalence L] [IsIso α] :
    F₁.IsRightKanExtension α :=
  inferInstanceAs <|
    F₁.IsRightKanExtension (asIso α : (asEquivalence L).functor ⋙ F₁ ≅ F₀).hom

end

end Functor

end CategoryTheory

