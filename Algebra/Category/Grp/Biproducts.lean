/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# The category of abelian groups has finite biproducts
-/

@[expose] public section

open CategoryTheory Limits

universe w u

namespace AddCommGrpCat

-- As `AddCommGrpCat` is preadditive, and has all limits, it automatically has biproducts.
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasBinaryBiproducts AddCommGrpCat :=
  HasBinaryBiproducts.of_hasBinaryProducts
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasFiniteBiproducts AddCommGrpCat :=
  HasFiniteBiproducts.of_hasFiniteProducts

-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.
/-- Construct limit data for a binary product in `AddCommGrpCat`, using
`AddCommGrpCat.of (G × H)`.
-/
@[simps! cone_pt isLimit_lift]
/-
**AddCommGrpCat.binaryProductLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`
。
形式化陈述：binaryProductLimitCone (G H : AddCommGrpCat.{u}) : Limits.LimitCone (pair 
G H) where cone
参数：G H : AddCommGrpCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct limit data for a binary product in `AddCommGrpCat`, using
`AddCommGrpCat.of (G × H)`.
-/
def binaryProductLimitCone (G H : AddCommGrpCat.{u}) : Limits.LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (AddMonoidHom.fst G H)) (ofHom (AddMonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (AddMonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

@[simp]
/-
**AddCommGrpCat.binaryProductLimitCone_cone_** 是 Mathlib 中的一个定理，位于命名空间 `AddCommG
rpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem binaryProductLimitCone_cone_π_app_left (G H : AddCommGrpCat.{u}) :
    (binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.left⟩ = ofHom (AddMonoidHom.fst G H) :=
  rfl

@[simp]
/-
**AddCommGrpCat.binaryProductLimitCone_cone_** 是 Mathlib 中的一个定理，位于命名空间 `AddCommG
rpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem binaryProductLimitCone_cone_π_app_right (G H : AddCommGrpCat.{u}) :
    (binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.right⟩ = ofHom (AddMonoidHom.snd G H) :=
  rfl

/-- We verify that the biproduct in `AddCommGrpCat` is isomorphic to
the Cartesian product of the underlying types:
-/
/-
**AddCommGrpCat.biprodIsoProd** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：biprodIsoProd (G H : AddCommGrpCat.{u}) : (G ⊞ H : AddCommGrpCat) ≅ AddCom
mGrpCat.of (G × H)
参数：G H : AddCommGrpCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We verify that the biproduct in `AddCommGrpCat` is isomorphic to
the Cartesian product of the underlying types:
-/
noncomputable def biprodIsoProd (G H : AddCommGrpCat.{u}) :
    (G ⊞ H : AddCommGrpCat) ≅ AddCommGrpCat.of (G × H) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit G H) (binaryProductLimitCone G H).isLimit

@[simp, elementwise]
/-
**AddCommGrpCat.biprodIsoProd_inv_comp_fst** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrp
Cat`。
形式化陈述：biprodIsoProd_inv_comp_fst (G H : AddCommGrpCat.{u}) : (biprodIsoProd G H)
.inv ≫ biprod.fst = ofHom (AddMonoidHom.fst G H)
参数：G H : AddCommGrpCat.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
-/
theorem biprodIsoProd_inv_comp_fst (G H : AddCommGrpCat.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.fst = ofHom (AddMonoidHom.fst G H) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

@[simp, elementwise]
/-
**AddCommGrpCat.biprodIsoProd_inv_comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrp
Cat`。
形式化陈述：biprodIsoProd_inv_comp_snd (G H : AddCommGrpCat.{u}) : (biprodIsoProd G H)
.inv ≫ biprod.snd = ofHom (AddMonoidHom.snd G H)
参数：G H : AddCommGrpCat.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
-/
theorem biprodIsoProd_inv_comp_snd (G H : AddCommGrpCat.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.snd = ofHom (AddMonoidHom.snd G H) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

@[elementwise]
/-
**AddCommGrpCat.biprodIsoProd_inv_comp_desc** 是 Mathlib 中的一个引理，位于命名空间 `AddCommGr
pCat`。
形式化陈述：biprodIsoProd_inv_comp_desc {G H K : AddCommGrpCat.{u}} (f : G ⟶ K) (g : H
 ⟶ K) : (biprodIsoProd G H).inv ≫ biprod.desc f g = ofHom (AddMonoidHom.fst G H)
 ≫ f + ofHom (AddMonoidHom.snd G H) ≫ g
参数：f : G ⟶ K；g : H ⟶ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `AddCommGrpCat.instHasBinaryBiproducts`：CategoryTheory.Limits.HasBinaryBi
products AddCommGrpCat
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.desc_eq`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [inst
_2 : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma biprodIsoProd_inv_comp_desc {G H K : AddCommGrpCat.{u}} (f : G ⟶ K) (g : H ⟶ K) :
    (biprodIsoProd G H).inv ≫ biprod.desc f g =
      ofHom (AddMonoidHom.fst G H) ≫ f + ofHom (AddMonoidHom.snd G H) ≫ g := by
  simp [biprod.desc_eq, ← biprodIsoProd_inv_comp_fst, ← biprodIsoProd_inv_comp_snd]

namespace HasLimit

variable {J : Type w} (f : J → AddCommGrpCat.{max w u})

set_option backward.defeqAttrib.useBackward true in
/-- The map from an arbitrary cone over an indexed family of abelian groups
to the Cartesian product of those groups.
-/
@[simps!]
/-
**AddCommGrpCat.HasLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat.HasLimit`
。
形式化陈述：lift (s : Fan f) : s.pt ⟶ AddCommGrpCat.of (forall j, f j)
参数：s : Fan f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from an arbitrary cone over an indexed family of abelian groups
to the Cartesian product of those groups.
-/
def lift (s : Fan f) : s.pt ⟶ AddCommGrpCat.of (∀ j, f j) :=
  ofHom
  { toFun x j := s.π.app ⟨j⟩ x
    map_zero' := by
      simp only [Functor.const_obj_obj, map_zero]
      rfl
    map_add' x y := by
      simp only [Functor.const_obj_obj, map_add]
      rfl }

/-- Construct limit data for a product in `AddCommGrpCat`, using
`AddCommGrpCat.of (∀ j, F.obj j)`.
-/
@[simps]
/-
**AddCommGrpCat.HasLimit.productLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpC
at.HasLimit`。
形式化陈述：productLimitCone : Limits.LimitCone (Discrete.functor f) where cone
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct limit data for a product in `AddCommGrpCat`, using
`AddCommGrpCat.of (∀ j, F.obj j)`.
-/
def productLimitCone : Limits.LimitCone (Discrete.functor f) where
  cone :=
    { pt := AddCommGrpCat.of (∀ j, f j)
      π := Discrete.natTrans fun j => ofHom <| Pi.evalAddMonoidHom (fun j => f j) j.as }
  isLimit :=
    { lift := lift.{_, u} f
      fac := fun _ _ => rfl
      uniq := fun s m w => by
        ext x j
        exact CategoryTheory.congr_fun (w ⟨j⟩) x }

end HasLimit

open HasLimit

variable {J : Type} [Finite J]

/-- We verify that the biproduct we've just defined is isomorphic to the `AddCommGrpCat` structure
on the dependent function type.
-/
/-
**AddCommGrpCat.biproductIsoPi** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：biproductIsoPi (f : J -> AddCommGrpCat.{u}) : (⨁ f : AddCommGrpCat) ≅ AddC
ommGrpCat.of (forall j, f j)
参数：f : J -> AddCommGrpCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We verify that the biproduct we've just defined is isomorphic to the `AddCommGrp
Cat` structure
on the dependent function type.
-/
noncomputable def biproductIsoPi (f : J → AddCommGrpCat.{u}) :
    (⨁ f : AddCommGrpCat) ≅ AddCommGrpCat.of (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).isLimit

@[simp, elementwise]
/-
**AddCommGrpCat.biproductIsoPi_inv_comp_** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCa
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproductIsoPi_inv_comp_π (f : J → AddCommGrpCat.{u}) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = ofHom (Pi.evalAddMonoidHom (fun j => f j) j) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

end AddCommGrpCat

