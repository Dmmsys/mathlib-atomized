/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
public import Mathlib.CategoryTheory.Monoidal.Grp

/-!
# Yoneda embedding of `Grp C`

We show that group objects are exactly those whose yoneda presheaf is a presheaf of groups,
by constructing the yoneda embedding `Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{v}` and
showing that it is fully faithful and its (essential) image is the representable functors.
-/

@[expose] public section

assert_not_exists Field

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory
universe w v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {M G H X Y : C} [MonObj M] [GrpObj G] [GrpObj H]

variable (X) in
/-- If `X` represents a presheaf of monoids, then `X` is a monoid object. -/
@[to_additive (attr := instance_reducible)
/-- If `X` represents a presheaf of additive monoids, then `X` is an additive monoid object. -/]
/-
**CategoryTheory.GrpObj.ofRepresentableBy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.GrpObj`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] →       (X : C) →         (F : Cate
goryTheory.Functor Cᵒᵖ GrpCat) →           (F.comp (CategoryTheory.forget GrpCat
)).RepresentableBy X → CategoryTheory.GrpObj X
参数：X : C；F : CategoryTheory.Functor Cᵒᵖ GrpCat；F.comp (CategoryTheory.forget Grp
Cat)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def GrpObj.ofRepresentableBy (F : Cᵒᵖ ⥤ GrpCat.{w}) (α : (F ⋙ forget _).RepresentableBy X) :
    GrpObj X where
  __ := MonObj.ofRepresentableBy X (F ⋙ forget₂ GrpCat MonCat) α
  inv := α.homEquiv'.symm (α.homEquiv (𝟙 _))⁻¹
  left_inv := by
    change lift (α.homEquiv'.symm (α.homEquiv (𝟙 X))⁻¹) (𝟙 X) ≫
      α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X)) =
        toUnit X ≫ α.homEquiv'.symm 1
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul, map_one]
    simp only [← α.homEquiv'_comp, lift_fst, Equiv.apply_symm_apply, lift_snd]
    exact inv_mul_cancel (α.homEquiv (𝟙 X))
  right_inv := by
    change lift (𝟙 X) (α.homEquiv'.symm (α.homEquiv' (𝟙 X))⁻¹) ≫
      α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X)) =
        toUnit X ≫ α.homEquiv'.symm 1
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul, map_one]
    simp only [← α.homEquiv'_comp]
    simp

/-- If `G` is a group object, then `Hom(X, G)` has a group structure. -/
@[to_additive
/-- If `G` is an additive group object, then `Hom(X, G)` has an additive group structure. -/]
/-
**CategoryTheory.Hom.group** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Hom`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] → {G X : C} → [CategoryTheory.GrpOb
j G] → Group (X ⟶ G)
参数：X ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev Hom.group : Group (X ⟶ G) where
  inv f := f ≫ ι
  inv_mul_cancel f := calc
    lift (f ≫ ι) f ≫ μ
    _ = (f ≫ lift ι (𝟙 G)) ≫ μ := by simp
    _ = toUnit X ≫ η := by rw [Category.assoc]; simp

scoped[CategoryTheory.MonObj] attribute [instance] Hom.group
scoped[CategoryTheory.AddMonObj] attribute [instance] Hom.addGroup

@[to_additive]
/-
**CategoryTheory.Hom.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C] {G X : C}   [inst_2 : CategoryTheory.GrpObj
 G] (f : X ⟶ G), f⁻¹ = CategoryTheory.CategoryStruct.comp f CategoryTheory.GrpOb
j.inv
参数：f : X ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.inv_def (f : X ⟶ G) : f⁻¹ = f ≫ ι := rfl

variable (G) in
/-- If `G` is a group object, then `Hom(-, G)` is a presheaf of groups. -/
@[to_additive (attr := simps)
/-- If `G` is an additive group object, then `Hom(-, G)` is a presheaf of additive groups. -/]
/-
**CategoryTheory.yonedaGrpObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaGrpObj : Cᵒᵖ ⥤ GrpCat.{v} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def yonedaGrpObj : Cᵒᵖ ⥤ GrpCat.{v} where
  obj X := GrpCat.of (unop X ⟶ G)
  map φ := GrpCat.ofHom ((yonedaMonObj G).map φ).hom

variable (G) in
/-- If `G` is a monoid object, then `Hom(-, G)` as a presheaf of monoids is represented by `G`. -/
@[to_additive
/-- If `G` is an additive monoid object, then `Hom(-, G)` as a presheaf of additive monoids
is represented by `G`. -/]
/-
**CategoryTheory.yonedaGrpObjRepresentableBy** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：yonedaGrpObjRepresentableBy : (yonedaGrpObj G ⋙ forget _).RepresentableBy 
G
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def yonedaGrpObjRepresentableBy : (yonedaGrpObj G ⋙ forget _).RepresentableBy G :=
  Functor.representableByEquiv.symm (.refl _)

variable (G) in
@[to_additive]
/-
**CategoryTheory.GrpObj.ofRepresentableBy_yonedaGrpObjRepresentableBy** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.GrpObj`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C] (G : C)   [inst_2 : CategoryTheory.GrpObj G
],   CategoryTheory.GrpObj.ofRepresentableBy G (CategoryTheory.yonedaGrpObj G)  
     (CategoryTheory.yonedaGrpObjRepresentableBy G) =     inst_2
参数：G : C；CategoryTheory.yonedaGrpObj G；CategoryTheory.yonedaGrpObjRepresentableB
y G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrpObj.ext`：ext {X : C} (h₁ h₂ : GrpObj X) (H : h₁.toMonO
bj = h₂.toMonObj) : h₁ = h₂
· 使用定理 `CategoryTheory.MonObj.ext`：ext {X : C} (h₁ h₂ : MonObj X) (H : h₁.mul = 
h₂.mul) : h₁ = h₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst_snd`：lift_fst_snd {X Y
 : C} : lift (fst X Y) (snd X Y) = 𝟙 (X otimes Y)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma GrpObj.ofRepresentableBy_yonedaGrpObjRepresentableBy :
    ofRepresentableBy G _ (yonedaGrpObjRepresentableBy G) = ‹GrpObj G› := by
  ext; change lift (fst G G) (snd G G) ≫ μ = μ; rw [lift_fst_snd, Category.id_comp]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
variable (X) in
/-- If `X` represents a presheaf of groups `F`, then `Hom(-, X)` is isomorphic to `F` as
a presheaf of groups. -/
@[to_additive (attr := simps! hom inv)
/-- If `X` represents a presheaf of additive groups `F`, then `Hom(-, X)` is isomorphic to `F` as
a presheaf of additive groups. -/]
/-
**CategoryTheory.yonedaGrpObjIsoOfRepresentableBy** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory`。
形式化陈述：yonedaGrpObjIsoOfRepresentableBy (F : Cᵒᵖ ⥤ GrpCat.{v}) (α : (F ⋙ forget _
).RepresentableBy X) : letI
参数：F : Cᵒᵖ ⥤ GrpCat.{v}；α : (F ⋙ forget _).RepresentableBy X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def yonedaGrpObjIsoOfRepresentableBy (F : Cᵒᵖ ⥤ GrpCat.{v}) (α : (F ⋙ forget _).RepresentableBy X) :
    letI := GrpObj.ofRepresentableBy X F α
    yonedaGrpObj X ≅ F :=
  letI := GrpObj.ofRepresentableBy X F α
  NatIso.ofComponents (fun Y ↦ MulEquiv.toGrpIso
    { toEquiv := α.homEquiv
      map_mul' :=
  ((yonedaMonObjIsoOfRepresentableBy X (F ⋙ forget₂ GrpCat MonCat) α).hom.app Y).hom.map_mul })
      fun φ ↦ GrpCat.hom_ext <| MonoidHom.ext <| α.homEquiv_comp φ.unop

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The yoneda embedding of `Grp C` into presheaves of groups. -/
@[to_additive (attr := simps)
/-- The yoneda embedding of `AddGrp_C` into presheaves of additive groups. -/]
/-
**CategoryTheory.yonedaGrp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaGrp : Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{v} where obj G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def yonedaGrp : Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{v} where
  obj G := yonedaGrpObj G.X
  map {G H} ψ := { app Y := GrpCat.ofHom ((yonedaMon.map ψ.hom).app Y).hom }

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_additive (attr := reassoc)]
/-
**CategoryTheory.yonedaGrp_naturality** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`
。
形式化陈述：yonedaGrp_naturality (α : yonedaGrpObj G ⟶ yonedaGrpObj H) (f : X ⟶ Y) (g 
: Y ⟶ G) : α.app _ (f ≫ g) = f ≫ α.app _ g
参数：α : yonedaGrpObj G ⟶ yonedaGrpObj H；f : X ⟶ Y；g : Y ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma yonedaGrp_naturality (α : yonedaGrpObj G ⟶ yonedaGrpObj H) (f : X ⟶ Y) (g : Y ⟶ G) :
    α.app _ (f ≫ g) = f ≫ α.app _ g := congr($(α.naturality f.op) g)

/-- The yoneda embedding for `Grp C` is fully faithful. -/
@[to_additive
/-- The yoneda embedding for `AddGrp C` is fully faithful. -/]
/-
**CategoryTheory.yonedaGrpFullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：yonedaGrpFullyFaithful : yonedaGrp (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def yonedaGrpFullyFaithful : yonedaGrp (C := C).FullyFaithful where
  preimage {G H} α :=
    Grp.homMk' (yonedaMonFullyFaithful.preimage ((Functor.whiskerRight α (forget₂ GrpCat MonCat))))
  map_preimage {G H} α := by
    ext X : 3
    exact congr(($(yonedaMonFullyFaithful.map_preimage (X := G.toMon) (Y := H.toMon)
      (Functor.whiskerRight α (forget₂ GrpCat MonCat))).app X).hom)
  preimage_map f := by
    ext
    congr
    apply yonedaMonFullyFaithful.preimage_map

@[to_additive]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : yonedaGrp (C := C).Full := yonedaGrpFullyFaithful.full
@[to_additive]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : yonedaGrp (C := C).Faithful := yonedaGrpFullyFaithful.faithful

@[to_additive]
/-
**CategoryTheory.essImage_yonedaGrp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：essImage_yonedaGrp : yonedaGrp (C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma essImage_yonedaGrp :
    yonedaGrp (C := C).essImage = fun F ↦ (F ⋙ forget _).IsRepresentable := by
  ext F
  constructor
  · rintro ⟨G, ⟨α⟩⟩
    exact ⟨G.X, ⟨Functor.representableByEquiv.symm (Functor.isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    let := GrpObj.ofRepresentableBy X F e
    exact ⟨⟨X⟩, ⟨yonedaGrpObjIsoOfRepresentableBy X F e⟩⟩

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.GrpObj.inv_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrpOb
j`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   {G H X : C} [inst_2 : CategoryTheory.GrpO
bj G] [inst_3 : CategoryTheory.GrpObj H] (f : X ⟶ G) (g : G ⟶ H)   [CategoryTheo
ry.IsMonHom g], CategoryTheory.CategoryStruct.comp f⁻¹ g = (CategoryTheory.Categ
oryStruct.comp f g)⁻¹
参数：f : X ⟶ G；g : G ⟶ H；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GrpObj.inv_hom`：inv_hom [GrpObj A] [GrpObj B] (f : A ⟶ B)
 [IsMonHom f] : ι ≫ f = f ≫ ι
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma GrpObj.inv_comp (f : X ⟶ G) (g : G ⟶ H) [IsMonHom g] : f⁻¹ ≫ g = (f ≫ g)⁻¹ := by
  simp [Hom.inv_def]

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.GrpObj.div_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrpOb
j`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   {G H X : C} [inst_2 : CategoryTheory.GrpO
bj G] [inst_3 : CategoryTheory.GrpObj H] (f g : X ⟶ G) (h : G ⟶ H)   [CategoryTh
eory.IsMonHom h],   CategoryTheory.CategoryStruct.comp (f / g) h =     CategoryT
heory.CategoryStruct.comp f h / CategoryTheory.CategoryStruct.comp g h
参数：f g : X ⟶ G；h : G ⟶ H；f / g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_div`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (g h : α),   f (g / h) = f g / f h
-/
lemma GrpObj.div_comp (f g : X ⟶ G) (h : G ⟶ H) [IsMonHom h] :
    (f / g) ≫ h = (f ≫ h) / (g ≫ h) :=
  ((yonedaGrp.map (Grp.homMk (A := .mk G) (B := .mk H) h)).app (op X)).hom.map_div f g

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.GrpObj.zpow_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrpO
bj`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   {G H X : C} [inst_2 : CategoryTheory.GrpO
bj G] [inst_3 : CategoryTheory.GrpObj H] (f : X ⟶ G) (n : ℤ) (g : G ⟶ H)   [Cate
goryTheory.IsMonHom g], CategoryTheory.CategoryStruct.comp (f ^ n) g = CategoryT
heory.CategoryStruct.comp f g ^ n
参数：f : X ⟶ G；n : ℤ；g : G ⟶ H；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_zpow`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [in
st_1 : DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ),   f (g ^ n) = f g ^ n
-/
lemma GrpObj.zpow_comp (f : X ⟶ G) (n : ℤ) (g : G ⟶ H) [IsMonHom g] :
    (f ^ n) ≫ g = (f ≫ g) ^ n :=
  ((yonedaGrp.map (Grp.homMk (A := .mk G) (B := .mk H) g)).app (op X)).hom.map_zpow f n

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.GrpObj.comp_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrpOb
j`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   {G X Y : C} [inst_2 : CategoryTheory.GrpO
bj G] (f : X ⟶ Y) (g : Y ⟶ G),   CategoryTheory.CategoryStruct.comp f g⁻¹ = (Cat
egoryTheory.CategoryStruct.comp f g)⁻¹
参数：f : X ⟶ Y；g : Y ⟶ G；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
-/
lemma GrpObj.comp_inv (f : X ⟶ Y) (g : Y ⟶ G) : f ≫ g⁻¹ = (f ≫ g)⁻¹ :=
  ((yonedaGrp.obj ⟨G⟩).map f.op).hom.map_inv g

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.GrpObj.comp_div** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrpOb
j`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   {G X Y : C} [inst_2 : CategoryTheory.GrpO
bj G] (f : X ⟶ Y) (g h : Y ⟶ G),   CategoryTheory.CategoryStruct.comp f (g / h) 
=     CategoryTheory.CategoryStruct.comp f g / CategoryTheory.CategoryStruct.com
p f h
参数：f : X ⟶ Y；g h : Y ⟶ G；g / h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_div`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (g h : α),   f (g / h) = f g / f h
-/
lemma GrpObj.comp_div (f : X ⟶ Y) (g h : Y ⟶ G) : f ≫ (g / h) = f ≫ g / f ≫ h :=
  ((yonedaGrp.obj ⟨G⟩).map f.op).hom.map_div g h

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.GrpObj.comp_zpow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrpO
bj`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   {G X Y : C} [inst_2 : CategoryTheory.GrpO
bj G] (f : X ⟶ Y) (g : Y ⟶ G) (n : ℤ),   CategoryTheory.CategoryStruct.comp f (g
 ^ n) = CategoryTheory.CategoryStruct.comp f g ^ n
参数：f : X ⟶ Y；g : Y ⟶ G；n : ℤ；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `CategoryTheory.MonObj.comp_pow`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v, u_1} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {M 
X Y : C} [inst_2 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `CategoryTheory.GrpObj.comp_inv`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {G X Y 
: C} [inst_2 : Categ…
-/
lemma GrpObj.comp_zpow (f : X ⟶ Y) (g : Y ⟶ G) : ∀ n : ℤ, f ≫ g ^ n = (f ≫ g) ^ n
  | (n : ℕ) => by simp [comp_pow]
  | .negSucc n => by simp [comp_pow, comp_inv]

@[to_additive]
/-
**CategoryTheory.GrpObj.inv_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grp
Obj`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C] {G : C}   [inst_2 : CategoryTheory.GrpObj G
], CategoryTheory.GrpObj.inv = (CategoryTheory.CategoryStruct.id G)⁻¹
参数：CategoryTheory.CategoryStruct.id G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma GrpObj.inv_eq_inv : ι = (𝟙 G)⁻¹ := by simp [Hom.inv_def]

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.GrpObj.one_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrpObj
`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C] {G : C}   [inst_2 : CategoryTheory.GrpObj G
],   CategoryTheory.CategoryStruct.comp CategoryTheory.MonObj.one CategoryTheory
.GrpObj.inv = CategoryTheory.MonObj.one
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonObj.one_eq_one`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v, u_1} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   (
M : C) [inst_2 : Categ…
· 使用定理 `CategoryTheory.GrpObj.inv_eq_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C] {G : C}
   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.GrpObj.comp_inv`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {G X Y 
: C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma GrpObj.one_inv : η[G] ≫ ι = η := by simp [GrpObj.inv_eq_inv, GrpObj.comp_inv, one_eq_one]

open scoped _root_.CategoryTheory.Obj in
/-- If `G` is a group object and `F` is monoidal,
then `Hom(X, G) → Hom(F X, F G)` preserves inverses. -/
@[to_additive (attr := simp) /-- If `G` is an additive group object and `F` is monoidal,
then `Hom(X, G) → Hom(F X, F G)` preserves negation. -/]
/-
**CategoryTheory.Functor.map_inv'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   {D : Type u_1} [inst_2 : CategoryTheory.C
ategory.{v_1, u_1} D] [inst_3 : CategoryTheory.CartesianMonoidalCategory D]   (F
 : CategoryTheory.Functor C D) [inst_4 : F.Monoidal] {X G : C} (f : X ⟶ G) [inst
_5 : CategoryTheory.GrpObj G],   F.map f⁻¹ = (F.map f)⁻¹
参数：F : CategoryTheory.Functor C D；f : X ⟶ G；F.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_inv_iff_mul_eq_one`：eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_mul`：∀ {C : Type u_1} {D : Type u_2} [inst : 
CategoryTheory.Category.{v, u_1} C]   [inst_1 : CategoryTheory.CartesianMonoidal
Category C] [inst_2 …
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `CategoryTheory.Functor.map_one`：∀ {C : Type u_1} {D : Type u_2} [inst : 
CategoryTheory.Category.{v, u_1} C]   [inst_1 : CategoryTheory.CartesianMonoidal
Category C] [inst_2 …
-/
lemma Functor.map_inv' {D : Type*} [Category* D] [CartesianMonoidalCategory D] (F : C ⥤ D)
    [F.Monoidal] {X G : C} (f : X ⟶ G) [GrpObj G] :
    F.map (f⁻¹) = (F.map f)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← Functor.map_mul, inv_mul_cancel, Functor.map_one]

/-- Conjugation in `G` as a morphism. This is the map `(x, y) ↦ x * y * x⁻¹`,
see `CategoryTheory.GrpObj.lift_conj_eq_mul_mul_inv`. -/
@[to_additive
/-- Conjugation in `G` as a morphism. This is the map `(x, y) ↦ x + y + (-x)`,
see `CategoryTheory.AddGrpObj.lift_conj_eq_add_add_neg`. -/]
/-
**CategoryTheory.GrpObj.conj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GrpObj`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] →       (G : C) → [CategoryTheory.G
rpObj G] → CategoryTheory.MonoidalCategoryStruct.tensorObj G G ⟶ G
参数：G : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def GrpObj.conj (G : C) [GrpObj G] : G ⊗ G ⟶ G :=
  fst _ _ * snd _ _ * (fst _ _)⁻¹

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.GrpObj.lift_conj_eq_mul_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.GrpObj`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C] {X G : C}   [inst_2 : CategoryTheory.GrpObj
 G] (f₁ f₂ : X ⟶ G),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Cartes
ianMonoidalCategory.lift f₁ f₂)       (CategoryTheory.GrpObj.conj G) =     f₁ * 
f₂ * f₁⁻¹
参数：f₁ f₂ : X ⟶ G；CategoryTheory.CartesianMonoidalCategory.lift f₁ f₂；CategoryThe
ory.GrpObj.conj G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonObj.comp_mul`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v, u_1} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {M 
X Y : C} [inst_2 : C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `CategoryTheory.GrpObj.comp_inv`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {G X Y 
: C} [inst_2 : Categ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma GrpObj.lift_conj_eq_mul_mul_inv {X G : C} [GrpObj G] (f₁ f₂ : X ⟶ G) :
    lift f₁ f₂ ≫ conj G = f₁ * f₂ * f₁⁻¹ := by
  simp [conj, comp_mul, comp_inv]

/-- The commutator of `G` as a morphism. This is the map `(x, y) ↦ x * y * x⁻¹ * y⁻¹`,
see `CategoryTheory.GrpObj.lift_commutator_eq_mul_mul_inv_inv`.
This morphism is constant with value `1` if and only if `G` is commutative
(see `CategoryTheory.isCommMonObj_iff_commutator_eq_toUnit_η`). -/
@[to_additive
/-- The commutator of `G` as a morphism. This is the map `(x, y) ↦ x + y + (-x) + (-y)`,
see `CategoryTheory.AddGrpObj.lift_commutator_eq_add_add_neg_neg`.
This morphism is constant with value `0` if and only if `G` is commutative
(see `CategoryTheory.isCommAddMonObj_iff_commutator_eq_toAddUnit_η`). -/]
/-
**CategoryTheory.GrpObj.commutator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp
Obj`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] →       (G : C) → [CategoryTheory.G
rpObj G] → CategoryTheory.MonoidalCategoryStruct.tensorObj G G ⟶ G
参数：G : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def GrpObj.commutator (G : C) [GrpObj G] : G ⊗ G ⟶ G :=
  fst _ _ * snd _ _ * (fst _ _)⁻¹ * (snd _ _)⁻¹

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.GrpObj.lift_commutator_eq_mul_mul_inv_inv** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.GrpObj`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C] {X G : C}   [inst_2 : CategoryTheory.GrpObj
 G] (f₁ f₂ : X ⟶ G),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Cartes
ianMonoidalCategory.lift f₁ f₂)       (CategoryTheory.GrpObj.commutator G) =    
 f₁ * f₂ * f₁⁻¹ * f₂⁻¹
参数：f₁ f₂ : X ⟶ G；CategoryTheory.CartesianMonoidalCategory.lift f₁ f₂；CategoryThe
ory.GrpObj.commutator G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonObj.comp_mul`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v, u_1} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {M 
X Y : C} [inst_2 : C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `CategoryTheory.GrpObj.comp_inv`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {G X Y 
: C} [inst_2 : Categ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma GrpObj.lift_commutator_eq_mul_mul_inv_inv {X G : C} [GrpObj G] (f₁ f₂ : X ⟶ G) :
    lift f₁ f₂ ≫ commutator G = f₁ * f₂ * f₁⁻¹ * f₂⁻¹ := by
  simp [commutator, comp_mul, comp_inv]

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.GrpObj.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma GrpObj.η_whiskerRight_commutator : η ▷ G ≫ commutator G = toUnit _ ≫ η := by
  simp [commutator, comp_mul, comp_inv, one_eq_one]

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.GrpObj.whiskerLeft_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma GrpObj.whiskerLeft_η_commutator : G ◁ η ≫ commutator G = toUnit _ ≫ η := by
  simp [commutator, comp_mul, comp_inv, one_eq_one]

variable [BraidedCategory C]

@[to_additive]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCommMonObj G] : IsMonHom ι[G] where
  one_hom := by simp [one_eq_one, ← Hom.inv_def]
  mul_hom := by simp [GrpObj.mul_inv_rev]

attribute [local simp] Hom.inv_def in
@[to_additive]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCommMonObj G] {f : M ⟶ G} [IsMonHom f] : IsMonHom f⁻¹ where

namespace Grp
variable {G H : Grp C} [IsCommMonObj H.X]

@[to_additive]
/-
**CategoryTheory.Grp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonObj H where
  one := Grp.homMk η[H.toMon].hom
  mul := Grp.homMk μ[H.toMon].hom

@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.hom_one** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：hom_one (H : Grp C) [IsCommMonObj H.X] : η[H].hom.hom = η[H.X]
参数：H : Grp C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_one (H : Grp C) [IsCommMonObj H.X] : η[H].hom.hom = η[H.X] := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.hom_mul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：hom_mul (H : Grp C) [IsCommMonObj H.X] : μ[H].hom.hom = μ[H.X]
参数：H : Grp C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_mul (H : Grp C) [IsCommMonObj H.X] : μ[H].hom.hom = μ[H.X] := rfl

namespace Hom

@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.Hom.hom_one** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Grp.H
om`。
形式化陈述：hom_one : (1 : G ⟶ H).hom = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_one : (1 : G ⟶ H).hom = 1 := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.Hom.hom_mul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Grp.H
om`。
形式化陈述：hom_mul (f g : G ⟶ H) : (f * g).hom = f.hom * g.hom
参数：f g : G ⟶ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_mul (f g : G ⟶ H) : (f * g).hom = f.hom * g.hom := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.Hom.hom_pow** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Grp.H
om`。
形式化陈述：hom_pow (f : G ⟶ H) (n : Nat) : (f ^ n).hom = f.hom ^ n
参数：f : G ⟶ H；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma hom_pow (f : G ⟶ H) (n : ℕ) : (f ^ n).hom = f.hom ^ n := by
  induction n with
  | zero => simp
  | succ n hn => simp [pow_succ, hn]

end Hom

/-- A commutative group object is a group object in the category of group objects. -/
@[to_additive /-- A commutative additive group object is an additive group object in the category of
additive group objects. -/]
/-
**CategoryTheory.Grp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : GrpObj H where inv := Grp.homMk' { hom := ι[H.X] }

namespace Hom

@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.Hom.hom_hom_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.G
rp.Hom`。
形式化陈述：hom_hom_inv (f : G ⟶ H) : f⁻¹.hom.hom = f.hom.hom⁻¹
参数：f : G ⟶ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_hom_inv (f : G ⟶ H) : f⁻¹.hom.hom = f.hom.hom⁻¹ := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.Hom.hom_hom_div** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.G
rp.Hom`。
形式化陈述：hom_hom_div (f g : G ⟶ H) : (f / g).hom.hom = f.hom.hom / g.hom.hom
参数：f g : G ⟶ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_hom_div (f g : G ⟶ H) : (f / g).hom.hom = f.hom.hom / g.hom.hom := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Grp.Hom.hom_hom_zpow** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Grp.Hom`。
形式化陈述：hom_hom_zpow (f : G ⟶ H) (n : Int) : (f ^ n).hom.hom = f.hom.hom ^ n
参数：f : G ⟶ H；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `CategoryTheory.Grp.Hom.hom_pow`：hom_pow (f : G ⟶ H) (n : Nat) : (f ^ n).
hom = f.hom ^ n
· 使用引理 `CategoryTheory.Mon.Hom.hom_pow`：hom_pow (f : M ⟶ N) (n : Nat) : (f ^ n).
hom = f.hom ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
-/
lemma hom_hom_zpow (f : G ⟶ H) (n : ℤ) : (f ^ n).hom.hom = f.hom.hom ^ n := by
  cases n <;> simp

end Hom

attribute [local simp] mul_eq_mul comp_mul mul_comm mul_div_mul_comm in
/-- A commutative group object is a commutative group object in the category of group objects. -/
@[to_additive /-- A commutative additive group object is a commutative additive group object in the
category of additive group objects. -/]
/-
**CategoryTheory.Grp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCommMonObj H where

@[to_additive]
/-
**CategoryTheory.Grp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCommMonObj G.X] (f : G ⟶ H) : IsMonHom f where

end Grp

/-- If `G` is a commutative group object, then `Hom(X, G)` has a commutative group structure. -/
@[to_additive
/-- If `G` is a commutative additive group object, then `Hom(X, G)` has a commutative
additive group structure. -/]
/-
**CategoryTheory.Hom.commGroup** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Hom`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] →       {G X : C} →         [inst_2
 : CategoryTheory.GrpObj G] →           [inst_3 : CategoryTheory.BraidedCategory
 C] → [CategoryTheory.IsCommMonObj G] → CommGroup (X ⟶ G)
参数：X ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev Hom.commGroup [IsCommMonObj G] : CommGroup (X ⟶ G) where

scoped[CategoryTheory.MonObj] attribute [instance] Hom.commGroup
scoped[CategoryTheory.AddMonObj] attribute [instance] Hom.addCommGroup

section

@[to_additive]
/-
**CategoryTheory.GrpObj.conj_eq_snd_of_isCommMonObj** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.GrpObj`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C] {G : C}   [inst_2 : CategoryTheory.GrpObj G
] [inst_3 : CategoryTheory.BraidedCategory C] [CategoryTheory.IsCommMonObj G],  
 CategoryTheory.GrpObj.conj G = CategoryTheory.SemiCartesianMonoidalCategory.snd
 G G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_inv_cancel_comm`：mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma GrpObj.conj_eq_snd_of_isCommMonObj [IsCommMonObj G] : conj G = snd G G := by
  simp [conj]

open scoped IsMulCommutative in
/-- `G` is a commutative group object if and only if the commutator map `(x, y) ↦ x * y * x⁻¹ * y⁻¹`
is constant. -/
@[to_additive /-- `G` is a commutative additive group object if and only if the commutator map
`(x, y) ↦ x + y + (-x) + (-y)` is constant. -/]
/-
**CategoryTheory.isCommMonObj_iff_commutator_eq_toUnit_** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isCommMonObj_iff_commutator_eq_toUnit_η :
    IsCommMonObj G ↔ GrpObj.commutator G = toUnit _ ≫ η := by
  rw [isCommMonObj_iff_isMulCommutative]
  refine ⟨fun h ↦ ?_, fun heq X ↦ ⟨⟨fun f g ↦ ?_⟩⟩⟩
  · simp [GrpObj.commutator, one_eq_one]
  · simpa [one_eq_one, mul_inv_eq_iff_eq_mul] using congr(lift f g ≫ $heq)

end

end CategoryTheory

