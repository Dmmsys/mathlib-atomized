/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Functorial constructions of ideal sheaves

We define the pullback and pushforward of ideal sheaves in this file.

## Main definitions
- `AlgebraicGeometry.Scheme.IdealSheafData.comap`: The pullback of an ideal sheaf.
- `AlgebraicGeometry.Scheme.IdealSheafData.map`: The pushforward of an ideal sheaf.
- `AlgebraicGeometry.Scheme.IdealSheafData.map_gc`:
  The Galois connection between pullback and pushforward.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

namespace Scheme.IdealSheafData

/-- The pullback of an ideal sheaf. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.comap** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme.IdealSheafData`。
形式化陈述：comap (I : Y.IdealSheafData) (f : X ⟶ Y) : X.IdealSheafData
参数：I : Y.IdealSheafData；f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of an ideal sheaf.
-/
def comap (I : Y.IdealSheafData) (f : X ⟶ Y) : X.IdealSheafData :=
  (pullback.fst f I.subschemeι).ker

/-- The subscheme associated to the pullback ideal sheaf is isomorphic to the fibred product. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.comapIso** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：comapIso (I : Y.IdealSheafData) (f : X ⟶ Y) : (I.comap f).subscheme ≅ pull
back f I.subschemeι
参数：I : Y.IdealSheafData；f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subscheme associated to the pullback ideal sheaf is isomorphic to the fibred
 product.
-/
def comapIso (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).subscheme ≅ pullback f I.subschemeι :=
  (asIso (pullback.fst f I.subschemeι).toImage).symm

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.comapIso_inv_subscheme** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comapIso_inv_subschemeι (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comapIso f).inv ≫ (I.comap f).subschemeι = pullback.fst _ _ :=
  (pullback.fst f I.subschemeι).toImage_imageι

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_fst** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：comapIso_hom_fst (I : Y.IdealSheafData) (f : X ⟶ Y) : (I.comapIso f).hom ≫
 pullback.fst _ _ = (I.comap f).subschemeι
参数：I : Y.IdealSheafData；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.comapIso_inv_subschemeι`：comapIs
o_inv_subschemeι (I : Y.IdealSheafData) (f : X ⟶ Y) : (I.comapIso f).inv ≫ (I.co
map f).subschemeι = pullback.fst _ _
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma comapIso_hom_fst (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comapIso f).hom ≫ pullback.fst _ _ = (I.comap f).subschemeι := by
  rw [← comapIso_inv_subschemeι, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.comap_comp** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：comap_comp (I : Z.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z) : I.comap (f ≫ g
) = (I.comap g).comap f
参数：I : Z.IdealSheafData；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
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
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_fst`：comapIso_hom_f
st (I : Y.IdealSheafData) (f : X ⟶ Y) : (I.comapIso f).hom ≫ pullback.fst _ _ = 
(I.comap f).subschemeι
· 使用定理 `CategoryTheory.Limits.pullback.map_isIso`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [inst_1
 : CategoryTheory.Limits.HasPu…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.comap.eq_1`：∀ {X Y : AlgebraicGe
ometry.Scheme} (I : Y.IdealSheafData) (f : X ⟶ Y),   I.comap f = AlgebraicGeomet
ry.Scheme.Hom.ker (CategoryTheory.Limits…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso`：∀ {X Y Z : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [CategoryTheory.IsIso f],   AlgebraicGeomet
ry.Scheme.Hom.ker (CategoryTheory.Ca…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst`：pullbackRight
PullbackFstIso_hom_fst : (pullbackRightPullbackFstIso f g f').hom ≫ pullback.fst
 (f' ≫ f) g = pullback.fst f' (pullback.fst f g…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
-/
lemma comap_comp (I : Z.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z) :
    I.comap (f ≫ g) = (I.comap g).comap f := by
  let e : pullback f (I.comap g).subschemeι ≅ pullback (f ≫ g) I.subschemeι :=
    asIso (pullback.map _ _ _ _ (𝟙 _) (I.comapIso g).hom (𝟙 _) (by simp) (by simp)) ≪≫
      pullbackRightPullbackFstIso _ _ _
  rw [comap, comap, ← Scheme.Hom.ker_comp_of_isIso e.hom]
  simp [e]

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.comap_id** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：comap_id (I : Z.IdealSheafData) : I.comap (𝟙 _) = I
参数：I : Z.IdealSheafData。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.comap.eq_1`：∀ {X Y : AlgebraicGe
ometry.Scheme} (I : Y.IdealSheafData) (f : X ⟶ Y),   I.comap f = AlgebraicGeomet
ry.Scheme.Hom.ker (CategoryTheory.Limits…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso`：∀ {X Y Z : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [CategoryTheory.IsIso f],   AlgebraicGeomet
ry.Scheme.Hom.ker (CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Limits.hasPullback_of_left_iso`：hasPullback_of_left_iso :
 HasPullback f g
· 使用引理 `CategoryTheory.Limits.pullback_inv_snd_fst_of_left_isIso`：pullback_inv_s
nd_fst_of_left_isIso : inv (pullback.snd f g) ≫ pullback.fst f g = g ≫ inv f
· 使用定理 `CategoryTheory.IsIso.inv_id`：inv_id : inv (𝟙 X) = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`：ker_subschemeι :
 I.subschemeι.ker = I
-/
lemma comap_id (I : Z.IdealSheafData) :
    I.comap (𝟙 _) = I := by
  rw [comap, ← Scheme.Hom.ker_comp_of_isIso (inv (pullback.snd _ _)),
    pullback_inv_snd_fst_of_left_isIso, IsIso.inv_id, Category.comp_id, ker_subschemeι]

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support_comap** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：support_comap (I : Y.IdealSheafData) (f : X ⟶ Y) : (I.comap f).support = I
.support.preimage f.continuous
参数：I : Y.IdealSheafData；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Closeds.ext`：∀ {α : Type u_2} [inst : TopologicalSpace 
α] {s t : TopologicalSpace.Closeds α}, ↑s = ↑t → s = t
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.comap.eq_1`：∀ {X Y : AlgebraicGe
ometry.Scheme} (I : Y.IdealSheafData) (f : X ⟶ Y),   I.comap f = AlgebraicGeomet
ry.Scheme.Hom.ker (CategoryTheory.Limits…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.support_ker`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f],   ↑(AlgebraicGeometry.Schem
e.Hom.ker f).support = closure…
· 使用定理 `AlgebraicGeometry.instQuasiCompactFstScheme`：∀ {X Y Z : AlgebraicGeometr
y.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.QuasiCompact g],   Algebrai
cGeometry.QuasiCompact (CategoryT…
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.instQuasiCompactSubschemeι`：∀ {X
 : AlgebraicGeometry.Scheme} (I : X.IdealSheafData), AlgebraicGeometry.QuasiComp
act I.subschemeι
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.range_fst`：range_fst : Set.range (pull
back.fst f g) = f ⁻¹' Set.range g
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι`：range_subschem
eι : Set.range I.subschemeι = I.support
· 使用定理 `TopologicalSpace.Closeds.coe_preimage`：∀ {α : Type u_2} {β : Type u_3} [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   (s : TopologicalSpace
.Closeds β) {f : α → β} (hf…
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `TopologicalSpace.Closeds.isClosed`：isClosed (s : Closeds α) : IsClosed (
s : Set α)
-/
lemma support_comap (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).support = I.support.preimage f.continuous := by
  ext1
  rw [comap, Scheme.Hom.support_ker, Pullback.range_fst, range_subschemeι,
    TopologicalSpace.Closeds.coe_preimage, (I.support.isClosed.preimage f.continuous).closure_eq]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ker_fst_of_isClosedImmersion** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ker_fst_of_isClosedImmersion (i : Z ⟶ Y) (f : X ⟶ Y) [IsClosedImmersion i]
 : (pullback.fst f i).ker = i.ker.comap f
参数：i : Z ⟶ Y；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
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
· 使用定理 `AlgebraicGeometry.Scheme.Hom.toImage_imageι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Sch
eme.Hom.toImage f) (AlgebraicGeom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso`：∀ {X Y Z : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [CategoryTheory.IsIso f],   AlgebraicGeomet
ry.Scheme.Hom.ker (CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Limits.pullback.map_isIso`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [inst_1
 : CategoryTheory.Limits.HasPu…
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.instIsIsoSchemeToImage`：∀ {X Y : Alg
ebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f],   Ca
tegoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
lemma ker_fst_of_isClosedImmersion (i : Z ⟶ Y) (f : X ⟶ Y) [IsClosedImmersion i] :
    (pullback.fst f i).ker = i.ker.comap f := by
  delta IdealSheafData.comap
  rw [← Hom.ker_comp_of_isIso (pullback.map f i f i.imageι (𝟙 _) (i.toImage) (𝟙 _)
    (by simp) (by simp)), pullback.lift_fst, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- To show that the pullback of the closed immersion `iX` along `f` is the closed immersion
`iY`, it suffices to check that the preimage of `ker iY` under `f` is `ker iX`. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData._root_.AlgebraicGeometry.isPullback_of
_isClosedImmersion** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealShea
fData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To show that the pullback of the closed immersion `iX` along `f` is the closed i
mmersion
`iY`, it suffices to check that the preimage of `ker iY` under `f` is `ker iX`.
-/
lemma _root_.AlgebraicGeometry.isPullback_of_isClosedImmersion
    {ZX ZY X Y : Scheme} (iX : ZX ⟶ X) (iY : ZY ⟶ Y) (Zf : ZX ⟶ ZY) (f : X ⟶ Y)
    [IsClosedImmersion iX] [IsClosedImmersion iY]
    (h : iX ≫ f = Zf ≫ iY) (h' : iY.ker.comap f = iX.ker) : IsPullback iX Zf f iY := by
  suffices IsIso (pullback.lift _ _ h) by
    simpa using (IsPullback.of_vert_isIso (show CommSq iX (pullback.lift iX Zf h)
      (𝟙 X) (pullback.fst _ _) from ⟨by simp⟩)).paste_vert (IsPullback.of_hasPullback f iY)
  refine IsClosedImmersion.isIso_of_ker_eq iX (pullback.fst f iY) _ (by simp) ?_
  rw [ker_fst_of_isClosedImmersion, h']

/-- The pushforward of an ideal sheaf. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.map** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Scheme.IdealSheafData`。
形式化陈述：map (I : X.IdealSheafData) (f : X ⟶ Y) : Y.IdealSheafData
参数：I : X.IdealSheafData；f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushforward of an ideal sheaf.
-/
def map (I : X.IdealSheafData) (f : X ⟶ Y) : Y.IdealSheafData :=
  (I.subschemeι ≫ f).ker

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.le_map_iff_comap_le** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：le_map_iff_comap_le {I : X.IdealSheafData} {f : X ⟶ Y} {J : Y.IdealSheafDa
ta} : J <= I.map f ↔ J.comap f <= I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`：ker_subschemeι :
 I.subschemeι.ker = I
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.inclusion_subschemeι`：inclusion_
subschemeι {I J : IdealSheafData X} (h : I <= J) : inclusion h ≫ I.subschemeι = 
J.subschemeι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.toImage_imageι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Sch
eme.Hom.toImage f) (AlgebraicGeom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.le_ker_comp`：∀ {X Y Z : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) (g : Y.Hom Z),   g.ker ≤ AlgebraicGeometry.Scheme.Hom.ker (Ca
tegoryTheory.CategoryStruct.co…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_fst_assoc`：∀ {X Y :
 AlgebraicGeometry.Scheme} (I : Y.IdealSheafData) (f : X ⟶ Y) {Z : AlgebraicGeom
etry.Scheme} (h : X ⟶ Z),   CategoryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.inclusion_subschemeι_assoc`：∀ {X
 : AlgebraicGeometry.Scheme} {I J : X.IdealSheafData} (h : I ≤ J) {Z : Algebraic
Geometry.Scheme} (h_1 : X ⟶ Z),   CategoryTheory.Categor…
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.map.eq_1`：∀ {X Y : AlgebraicGeom
etry.Scheme} (I : X.IdealSheafData) (f : X ⟶ Y),   I.map f = AlgebraicGeometry.S
cheme.Hom.ker (CategoryTheory.Category…
-/
lemma le_map_iff_comap_le {I : X.IdealSheafData} {f : X ⟶ Y} {J : Y.IdealSheafData} :
    J ≤ I.map f ↔ J.comap f ≤ I := by
  constructor
  · intro H
    rw [← I.ker_subschemeι, ← pullback.lift_fst (f := f) (g := J.subschemeι) I.subschemeι
      ((I.subschemeι ≫ f).toImage ≫ inclusion H) (by simp)]
    exact Hom.le_ker_comp _ _
  · intro H
    have : (inclusion H ≫ (J.comapIso f).hom ≫ pullback.snd _ _) ≫ J.subschemeι =
        I.subschemeι ≫ f := by simp [← pullback.condition]
    rw [map, ← J.ker_subschemeι, ← this]
    exact Hom.le_ker_comp _ _

section gc

variable (I I₁ I₂ : X.IdealSheafData) (J J₁ J₂ : Y.IdealSheafData) (f : X ⟶ Y)

/-- Pushforward and pullback of ideal sheaves forms a Galois connection. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.map_gc** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme.IdealSheafData`。
形式化陈述：map_gc : GaloisConnection (comap · f) (map · f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.le_map_iff_comap_le`：le_map_iff_
comap_le {I : X.IdealSheafData} {f : X ⟶ Y} {J : Y.IdealSheafData} : J <= I.map 
f ↔ J.comap f <= I

--- 原说明 ---
Pushforward and pullback of ideal sheaves forms a Galois connection.
-/
lemma map_gc : GaloisConnection (comap · f) (map · f) := fun _ _ ↦ le_map_iff_comap_le.symm

section
set_option linter.style.whitespace false -- manual alignment is not recognised

/-
**AlgebraicGeometry.Scheme.IdealSheafData.map_mono** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：map_mono : Monotone (map · f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_gc`：map_gc : GaloisConnectio
n (comap · f) (map · f)
-/
lemma map_mono          : Monotone (map · f)                          := (map_gc f).monotone_u
/-
**AlgebraicGeometry.Scheme.IdealSheafData.comap_mono** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：comap_mono : Monotone (comap · f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_gc`：map_gc : GaloisConnectio
n (comap · f) (map · f)
-/
lemma comap_mono        : Monotone (comap · f)                        := (map_gc f).monotone_l
/-
**AlgebraicGeometry.Scheme.IdealSheafData.le_map_comap** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：le_map_comap : J <= (J.comap f).map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_gc`：map_gc : GaloisConnectio
n (comap · f) (map · f)
-/
lemma le_map_comap      : J ≤ (J.comap f).map f                       := (map_gc f).le_u_l J
/-
**AlgebraicGeometry.Scheme.IdealSheafData.comap_map_le** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：comap_map_le : (I.map f).comap f <= I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_gc`：map_gc : GaloisConnectio
n (comap · f) (map · f)
-/
lemma comap_map_le      : (I.map f).comap f ≤ I                       := (map_gc f).l_u_le I
/-
**AlgebraicGeometry.Scheme.IdealSheafData.map_top** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y), ⊤.map f = ⊤
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_gc`：map_gc : GaloisConnectio
n (comap · f) (map · f)
-/
@[simp] lemma map_top   : map ⊤ f = ⊤                                 := (map_gc f).u_top
/-
**AlgebraicGeometry.Scheme.IdealSheafData.comap_bot** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y), ⊥.comap f = ⊥
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_gc`：map_gc : GaloisConnectio
n (comap · f) (map · f)
-/
@[simp] lemma comap_bot : comap ⊥ f = ⊥                               := (map_gc f).l_bot
/-
**AlgebraicGeometry.Scheme.IdealSheafData.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (I₁ I₂ : X.IdealSheafData) (f : X ⟶ Y),
 (I₁ ⊓ I₂).map f = I₁.map f ⊓ I₂.map f
参数：I₁ I₂ : X.IdealSheafData；f : X ⟶ Y；I₁ ⊓ I₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_gc`：map_gc : GaloisConnectio
n (comap · f) (map · f)
-/
@[simp] lemma map_inf   : map (I₁ ⊓ I₂) f = map I₁ f ⊓ map I₂ f       := (map_gc f).u_inf
/-
**AlgebraicGeometry.Scheme.IdealSheafData.comap_sup** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (J₁ J₂ : Y.IdealSheafData) (f : X ⟶ Y),
 (J₁ ⊔ J₂).comap f = J₁.comap f ⊔ J₂.comap f
参数：J₁ J₂ : Y.IdealSheafData；f : X ⟶ Y；J₁ ⊔ J₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_gc`：map_gc : GaloisConnectio
n (comap · f) (map · f)
-/
@[simp] lemma comap_sup : comap (J₁ ⊔ J₂) f = comap J₁ f ⊔ comap J₂ f := (map_gc f).l_sup

end

end gc

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.map_bot** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：map_bot (f : X ⟶ Y) : map ⊥ f = f.ker
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso`：∀ {X Y Z : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [CategoryTheory.IsIso f],   AlgebraicGeomet
ry.Scheme.Hom.ker (CategoryTheory.Ca…
· 使用定理 `AlgebraicGeometry.Scheme.instIsIsoSubschemeιBotIdealSheafData`：∀ {X : Al
gebraicGeometry.Scheme}, CategoryTheory.IsIso ⊥.subschemeι
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_bot (f : X ⟶ Y) : map ⊥ f = f.ker := by
  simp [map, Scheme.Hom.ker_comp_of_isIso]

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.comap_top** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：comap_top (f : X ⟶ Y) : comap ⊤ f = ⊤
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.comap.eq_1`：∀ {X Y : AlgebraicGe
ometry.Scheme} (I : Y.IdealSheafData) (f : X ⟶ Y),   I.comap f = AlgebraicGeomet
ry.Scheme.Hom.ker (CategoryTheory.Limits…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_eq_top_iff_isEmpty`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X.Hom Y), f.ker = ⊤ ↔ IsEmpty ↥X
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.instIsEmptyCarrierCarrierCommRin
gCatSubschemeTop`：∀ {X : AlgebraicGeometry.Scheme}, IsEmpty ↥⊤.subscheme
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
-/
lemma comap_top (f : X ⟶ Y) : comap ⊤ f = ⊤ := by
  rw [comap, Hom.ker_eq_top_iff_isEmpty]
  exact Function.isEmpty (pullback.snd f _)

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：map_comp (I : X.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z) : I.map (f ≫ g) = 
(I.map f).map g
参数：I : X.IdealSheafData；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.le_map_iff_comap_le`：le_map_iff_
comap_le {I : X.IdealSheafData} {f : X ⟶ Y} {J : Y.IdealSheafData} : J <= I.map 
f ↔ J.comap f <= I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.comap_comp`：comap_comp (I : Z.Id
ealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z) : I.comap (f ≫ g) = (I.comap g).comap f
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.comap_map_le`：comap_map_le : (I.
map f).comap f <= I
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.comap_mono`：comap_mono : Monoton
e (comap · f)
-/
lemma map_comp (I : X.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z) :
    I.map (f ≫ g) = (I.map f).map g := by
  apply le_antisymm
  · rw [le_map_iff_comap_le, le_map_iff_comap_le, ← comap_comp]; exact comap_map_le _ _
  · rw [le_map_iff_comap_le, comap_comp]
    exact (comap_mono _ (comap_map_le _ _)).trans (comap_map_le _ _)

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.map_id** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme.IdealSheafData`。
形式化陈述：map_id (I : Z.IdealSheafData) : I.map (𝟙 _) = I
参数：I : Z.IdealSheafData。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`：ker_subschemeι :
 I.subschemeι.ker = I
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id (I : Z.IdealSheafData) :
    I.map (𝟙 _) = I := by
  simp [map]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.map_ker** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：map_ker (f : X ⟶ Y) (g : Y ⟶ Z) : f.ker.map g = (f ≫ g).ker
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_comp`：map_comp (I : X.IdealS
heafData) (f : X ⟶ Y) (g : Y ⟶ Z) : I.map (f ≫ g) = (I.map f).map g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_ker (f : X ⟶ Y) (g : Y ⟶ Z) : f.ker.map g = (f ≫ g).ker := by
  simp [← map_bot]
/-
**AlgebraicGeometry.Scheme.IdealSheafData._root_.AlgebraicGeometry.Scheme.Hom.ke
r_comp** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgebraicGeometry.Scheme.Hom.ker_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).ker = f.ker.map g := (map_ker f g).symm
/-
**AlgebraicGeometry.Scheme.IdealSheafData.map_vanishingIdeal** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：map_vanishingIdeal {X Y : Scheme} (f : X ⟶ Y) (Z : TopologicalSpace.Closed
s X) : (vanishingIdeal Z).map f = vanishingIdeal (.closure (f '' Z))
参数：f : X ⟶ Y；Z : TopologicalSpace.Closeds X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.map.eq_1`：∀ {X Y : AlgebraicGeom
etry.Scheme} (I : X.IdealSheafData) (f : X ⟶ Y),   I.map f = AlgebraicGeometry.S
cheme.Hom.ker (CategoryTheory.Category…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal
`：le_support_iff_le_vanishingIdeal {I : X.IdealSheafData} {Z : Closeds X} : Z <=
 I.support ↔ I <= vanishingIdeal Z
· 使用引理 `TopologicalSpace.Closeds.closure_le`：closure_le {s : Set α} {t : Closeds
 α} : .closure s <= t ↔ s subseteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_base`：comp_base {X Y Z : Scheme} (f : 
X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι`：range_subschem
eι : Set.range I.subschemeι = I.support
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal`：∀ {X
 : AlgebraicGeometry.Scheme} (Z : TopologicalSpace.Closeds ↥X),   ↑(AlgebraicGeo
metry.Scheme.IdealSheafData.vanishingIdeal Z).support = …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.range_subset_ker_support`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y), Set.range ⇑f ⊆ ↑(AlgebraicGeometry.Scheme.Hom.ker
 f).support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.support_comap`：support_comap (I 
: Y.IdealSheafData) (f : X ⟶ Y) : (I.comap f).support = I.support.preimage f.con
tinuous
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `TopologicalSpace.Closeds.coe_preimage`：∀ {α : Type u_2} {β : Type u_3} [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   (s : TopologicalSpace
.Closeds β) {f : α → β} (hf…
· 使用定理 `TopologicalSpace.Closeds.coe_closure`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (s : Set α), ↑(TopologicalSpace.Closeds.closure s) = closure s
-/
lemma map_vanishingIdeal {X Y : Scheme} (f : X ⟶ Y) (Z : TopologicalSpace.Closeds X) :
    (vanishingIdeal Z).map f = vanishingIdeal (.closure (f '' Z)) := by
  apply le_antisymm
  · rw [map, ← le_support_iff_le_vanishingIdeal, TopologicalSpace.Closeds.closure_le]
    refine .trans ?_ (Hom.range_subset_ker_support _)
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      range_subschemeι, coe_support_vanishingIdeal]
  · simp [le_map_iff_comap_le, ← le_support_iff_le_vanishingIdeal, ← Set.image_subset_iff,
      subset_closure, ← SetLike.coe_subset_coe]

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support_map** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：support_map (I : X.IdealSheafData) (f : X ⟶ Y) [QuasiCompact f] : (I.map f
).support = .closure (f '' I.support)
参数：I : X.IdealSheafData；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Closeds.ext`：∀ {α : Type u_2} [inst : TopologicalSpace 
α] {s t : TopologicalSpace.Closeds α}, ↑s = ↑t → s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.map.eq_1`：∀ {X Y : AlgebraicGeom
etry.Scheme} (I : X.IdealSheafData) (f : X ⟶ Y),   I.map f = AlgebraicGeometry.S
cheme.Hom.ker (CategoryTheory.Category…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.support_ker`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f],   ↑(AlgebraicGeometry.Schem
e.Hom.ker f).support = closure…
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.instQuasiCompactSubschemeι`：∀ {X
 : AlgebraicGeometry.Scheme} (I : X.IdealSheafData), AlgebraicGeometry.QuasiComp
act I.subschemeι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_base`：comp_base {X Y Z : Scheme} (f : 
X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι`：range_subschem
eι : Set.range I.subschemeι = I.support
· 使用定理 `TopologicalSpace.Closeds.coe_closure`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (s : Set α), ↑(TopologicalSpace.Closeds.closure s) = closure s
-/
lemma support_map (I : X.IdealSheafData) (f : X ⟶ Y) [QuasiCompact f] :
    (I.map f).support = .closure (f '' I.support) := by
  ext1
  rw [map, Scheme.Hom.support_ker, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, range_subschemeι, TopologicalSpace.Closeds.coe_closure]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_map** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ideal_map (I : X.IdealSheafData) (f : X ⟶ Y) [QuasiCompact f] (U : Y.affin
eOpens) (H : IsAffineOpen (f ⁻¹ᵁ U)) : (I.map f).ideal U = (I.ideal ⟨_, H⟩).coma
p (f.app U).hom
参数：I : X.IdealSheafData；f : X ⟶ Y；U : Y.affineOpens；H : IsAffineOpen (f ⁻¹ᵁ U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ker_coe_equiv`：ker_coe_equiv (f : R ≃+* S) : ker (f : R ->+* S) 
= ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_apply`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X.Hom Y) [AlgebraicGeometry.QuasiCompact f] (U : ↑Y.affineOpens),   f.ke
r.ideal U = RingHom.ker (Com…
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.instQuasiCompactSubschemeι`：∀ {X
 : AlgebraicGeometry.Scheme} (I : X.IdealSheafData), AlgebraicGeometry.QuasiComp
act I.subschemeι
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingHom.ker.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomCl
ass F R S] (…
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app`：subschemeι_app (
U : X.affineOpens) : I.subschemeι.app U = CommRingCat.ofHom (Ideal.Quotient.mk (
I.ideal U)) ≫ (I.subschemeObjIso U).inv
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ideal_map (I : X.IdealSheafData) (f : X ⟶ Y) [QuasiCompact f] (U : Y.affineOpens)
    (H : IsAffineOpen (f ⁻¹ᵁ U)) :
    (I.map f).ideal U = (I.ideal ⟨_, H⟩).comap (f.app U).hom := by
  have : RingHom.ker (I.subschemeObjIso ⟨_, H⟩).inv.hom = ⊥ :=
    RingHom.ker_coe_equiv (I.subschemeObjIso ⟨_, H⟩).symm.commRingCatIsoToRingEquiv
  simp [map, ← RingHom.comap_ker, subschemeι_app _ ⟨_, H⟩,
    this, ← RingHom.ker_eq_comap_bot]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_map_of_isAffineHom** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ideal_map_of_isAffineHom (I : X.IdealSheafData) (f : X ⟶ Y) [IsAffineHom f
] (U : Y.affineOpens) : (I.map f).ideal U = (I.ideal ⟨_, U.2.preimage f⟩).comap 
(f.app U).hom
参数：I : X.IdealSheafData；f : X ⟶ Y；U : Y.affineOpens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ideal_map`：ideal_map (I : X.Idea
lSheafData) (f : X ⟶ Y) [QuasiCompact f] (U : Y.affineOpens) (H : IsAffineOpen (
f ⁻¹ᵁ U)) : (I.map f).ideal U = (I.idea…
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfIsAffineHom`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffineHom f], AlgebraicGeometry.Qua
siCompact f
· 使用定理 `AlgebraicGeometry.IsAffineOpen.preimage`：∀ {X Y : AlgebraicGeometry.Sche
me} {U : Y.Opens},   AlgebraicGeometry.IsAffineOpen U →     ∀ (f : X ⟶ Y) [Algeb
raicGeometry.IsAffineHom f], …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma ideal_map_of_isAffineHom
    (I : X.IdealSheafData) (f : X ⟶ Y) [IsAffineHom f] (U : Y.affineOpens) :
    (I.map f).ideal U = (I.ideal ⟨_, U.2.preimage f⟩).comap (f.app U).hom :=
  ideal_map I f U (U.2.preimage f)
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion** 是 Mat
hlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ideal_comap_of_isOpenImmersion (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenI
mmersion f] (U : X.affineOpens) : (I.comap f).ideal U = (I.ideal ⟨f ''ᵁ U, U.2.i
mage_of_isOpenImmersion f⟩).comap (f.appIso U).inv.hom
参数：I : Y.IdealSheafData；f : X ⟶ Y；U : X.affineOpens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion`：image_of_isOpen
Immersion (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen (f ''ᵁ U)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion`：ker
_ideal_of_isPullback_of_isOpenImmersion {X Y U V : Scheme.{u}} (f : X ⟶ Y) (f' :
 U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) [IsOpenImmersion iV] [Q…
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.instQuasiCompactSubschemeι`：∀ {X
 : AlgebraicGeometry.Scheme} (I : X.IdealSheafData), AlgebraicGeometry.QuasiComp
act I.subschemeι
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`：ker_subschemeι :
 I.subschemeι.ker = I
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ideal_comap_of_isOpenImmersion
    (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] (U : X.affineOpens) :
    (I.comap f).ideal U = (I.ideal ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩).comap
      (f.appIso U).inv.hom := by
  refine (ker_ideal_of_isPullback_of_isOpenImmersion _ _ _ _
    (IsPullback.of_hasPullback f I.subschemeι) U).trans ?_
  simp

/-- If `J ≤ I.map f`, then `f` restricts to a map `I ⟶ J` between the closed subschemes. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：subschemeMap (I : X.IdealSheafData) (J : Y.IdealSheafData) (f : X ⟶ Y) (H 
: J <= I.map f) : I.subscheme ⟶ J.subscheme
参数：I : X.IdealSheafData；J : Y.IdealSheafData；f : X ⟶ Y；H : J <= I.map f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.instSubschemeι`：∀ {X : AlgebraicGeom
etry.Scheme} (I : X.IdealSheafData), AlgebraicGeometry.IsClosedImmersion I.subsc
hemeι

--- 原说明 ---
If `J ≤ I.map f`, then `f` restricts to a map `I ⟶ J` between the closed subsche
mes.
-/
def subschemeMap (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (f : X ⟶ Y) (H : J ≤ I.map f) : I.subscheme ⟶ J.subscheme :=
  IsClosedImmersion.lift J.subschemeι (I.subschemeι ≫ f) (by simpa using! H)

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap_subscheme** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subschemeMap_subschemeι (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (f : X ⟶ Y) (H : J ≤ I.map f) : subschemeMap I J f H ≫ J.subschemeι = I.subschemeι ≫ f :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_snd** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：comapIso_hom_snd (I : Y.IdealSheafData) (f : X ⟶ Y) : (I.comapIso f).hom ≫
 pullback.snd _ _ = subschemeMap _ _ f (I.le_map_comap f)
参数：I : Y.IdealSheafData；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.le_map_comap`：le_map_comap : J <
= (J.comap f).map f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.IsPreimmersion.instMonoScheme`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsPreimmersion f], CategoryTheory.Mon
o f
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.instIsPreimmersionSubschemeι`：∀ 
{X : AlgebraicGeometry.Scheme} (I : X.IdealSheafData), AlgebraicGeometry.IsPreim
mersion I.subschemeι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_fst_assoc`：∀ {X Y :
 AlgebraicGeometry.Scheme} (I : Y.IdealSheafData) (f : X ⟶ Y) {Z : AlgebraicGeom
etry.Scheme} (h : X ⟶ Z),   CategoryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap_subschemeι`：subsche
meMap_subschemeι (I : X.IdealSheafData) (J : Y.IdealSheafData) (f : X ⟶ Y) (H : 
J <= I.map f) : subschemeMap I J f H ≫ J.subschemeι =…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comapIso_hom_snd (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comapIso f).hom ≫ pullback.snd _ _ = subschemeMap _ _ f (I.le_map_comap f) := by
  rw [← cancel_mono I.subschemeι]
  simp [← pullback.condition]

end Scheme.IdealSheafData

end AlgebraicGeometry

