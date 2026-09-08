/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving binary products

Constructions to relate the notions of preserving binary products and reflecting binary products
to concrete binary fans.

In particular, we show that `ProdComparison G X Y` is an isomorphism iff `G` preserves
the product of `X` and `Y`.
-/

@[expose] public section


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)

namespace CategoryTheory.Limits

section

variable {P X Y Z : C} (f : P ⟶ X) (g : P ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
The map of a binary fan is a limit iff the fork consisting of the mapped morphisms is a limit. This
essentially lets us commute `BinaryFan.mk` with `Functor.mapCone`.
-/
/-
**CategoryTheory.Limits.isLimitMapConeBinaryFanEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：isLimitMapConeBinaryFanEquiv : IsLimit (G.mapCone (BinaryFan.mk f g)) ≃ Is
Limit (BinaryFan.mk (G.map f) (G.map g))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The map of a binary fan is a limit iff the fork consisting of the mapped morphis
ms is a limit. This
essentially lets us commute `BinaryFan.mk` with `Functor.mapCone`.
-/
def isLimitMapConeBinaryFanEquiv :
    IsLimit (G.mapCone (BinaryFan.mk f g)) ≃ IsLimit (BinaryFan.mk (G.map f) (G.map g)) :=
  (IsLimit.postcomposeHomEquiv (diagramIsoPair _) _).symm.trans
    (IsLimit.equivIsoLimit
      (Cone.ext (Iso.refl _)
        (by rintro (_ | _) <;> simp)))

/-- The property of preserving products expressed in terms of binary fans. -/
/-
**CategoryTheory.Limits.mapIsLimitOfPreservesOfIsLimit** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：mapIsLimitOfPreservesOfIsLimit [PreservesLimit (pair X Y) G] (l : IsLimit 
(BinaryFan.mk f g)) : IsLimit (BinaryFan.mk (G.map f) (G.map g))
参数：pair X Y；l : IsLimit (BinaryFan.mk f g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of preserving products expressed in terms of binary fans.
-/
def mapIsLimitOfPreservesOfIsLimit [PreservesLimit (pair X Y) G] (l : IsLimit (BinaryFan.mk f g)) :
    IsLimit (BinaryFan.mk (G.map f) (G.map g)) :=
  isLimitMapConeBinaryFanEquiv G f g (isLimitOfPreserves G l)

/-- The property of reflecting products expressed in terms of binary fans. -/
/-
**CategoryTheory.Limits.isLimitOfReflectsOfMapIsLimit** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：isLimitOfReflectsOfMapIsLimit [ReflectsLimit (pair X Y) G] (l : IsLimit (B
inaryFan.mk (G.map f) (G.map g))) : IsLimit (BinaryFan.mk f g)
参数：pair X Y；l : IsLimit (BinaryFan.mk (G.map f) (G.map g))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The property of reflecting products expressed in terms of binary fans.
-/
def isLimitOfReflectsOfMapIsLimit [ReflectsLimit (pair X Y) G]
    (l : IsLimit (BinaryFan.mk (G.map f) (G.map g))) : IsLimit (BinaryFan.mk f g) :=
  isLimitOfReflects G ((isLimitMapConeBinaryFanEquiv G f g).symm l)

variable (X Y)
variable [HasBinaryProduct X Y]

/-- If `G` preserves binary products and `C` has them, then the binary fan constructed of the mapped
morphisms of the binary product cone is a limit.
-/
/-
**CategoryTheory.Limits.isLimitOfHasBinaryProductOfPreservesLimit** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isLimitOfHasBinaryProductOfPreservesLimit [PreservesLimit (pair X Y) G] : 
IsLimit (BinaryFan.mk (G.map (Limits.prod.fst : X ⨯ Y ⟶ X)) (G.map Limits.prod.s
nd))
参数：pair X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves binary products and `C` has them, then the binary fan construct
ed of the mapped
morphisms of the binary product cone is a limit.
-/
def isLimitOfHasBinaryProductOfPreservesLimit [PreservesLimit (pair X Y) G] :
    IsLimit (BinaryFan.mk (G.map (Limits.prod.fst : X ⨯ Y ⟶ X)) (G.map Limits.prod.snd)) :=
  mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd X Y)
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PreservesLimit (pair X Y) G] :
    HasBinaryProduct (G.obj X) (G.obj Y) :=
  ⟨_, isLimitOfHasBinaryProductOfPreservesLimit G X Y⟩

variable [HasBinaryProduct (G.obj X) (G.obj Y)]

/-- If the product comparison map for `G` at `(X,Y)` is an isomorphism, then `G` preserves the
pair of `(X,Y)`.
-/
/-
**CategoryTheory.Limits.PreservesLimitPair.of_iso_prod_comparison** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits.PreservesLimitPair`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 (X Y : C) [inst_2 : CategoryTheory.Limits.HasBinaryProduct X Y]   [inst_3 : Cat
egoryTheory.Limits.HasBinaryProduct (G.obj X) (G.obj Y)]   [i : CategoryTheory.I
sIso (CategoryTheory.Limits.prodComparison G X Y)],   CategoryTheory.Limits.Pres
ervesLimit (CategoryTheory.Limits.pair X Y) G
参数：G : CategoryTheory.Functor C D；X Y : C；G.obj X；G.obj Y；CategoryTheory.Limits.
prodComparison G X Y；CategoryTheory.Limits.pair X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If the product comparison map for `G` at `(X,Y)` is an isomorphism, then `G` pre
serves the
pair of `(X,Y)`.
-/
lemma PreservesLimitPair.of_iso_prod_comparison [i : IsIso (prodComparison G X Y)] :
    PreservesLimit (pair X Y) G := by
  apply preservesLimit_of_preserves_limit_cone (prodIsProd X Y)
  apply (isLimitMapConeBinaryFanEquiv _ _ _).symm _
  refine @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (pair (G.obj X) (G.obj Y))) ?_
  apply i

variable [PreservesLimit (pair X Y) G]

/-- If `G` preserves the product of `(X,Y)`, then the product comparison map for `G` at `(X,Y)` is
an isomorphism.
-/
/-
**CategoryTheory.Limits.PreservesLimitPair.iso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.PreservesLimitPair`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           (X Y : C) →             [inst_2 : CategoryT
heory.Limits.HasBinaryProduct X Y] →               [inst_3 : CategoryTheory.Limi
ts.HasBinaryProduct (G.obj X) (G.obj Y)] →                 [CategoryTheory.Limit
s.PreservesLimit (CategoryTheory.Limits.pair X Y) G] →                   G.obj (
X ⨯ Y) ≅ G.obj X ⨯ G.obj Y
参数：G : CategoryTheory.Functor C D；X Y : C；G.obj X；G.obj Y；CategoryTheory.Limits.
pair X Y；X ⨯ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves the product of `(X,Y)`, then the product comparison map for `G`
 at `(X,Y)` is
an isomorphism.
-/
def PreservesLimitPair.iso : G.obj (X ⨯ Y) ≅ G.obj X ⨯ G.obj Y :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasBinaryProductOfPreservesLimit G X Y) (limit.isLimit _)

@[simp]
/-
**CategoryTheory.Limits.PreservesLimitPair.iso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.PreservesLimitPair`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 (X Y : C) [inst_2 : CategoryTheory.Limits.HasBinaryProduct X Y]   [inst_3 : Cat
egoryTheory.Limits.HasBinaryProduct (G.obj X) (G.obj Y)]   [inst_4 : CategoryThe
ory.Limits.PreservesLimit (CategoryTheory.Limits.pair X Y) G],   (CategoryTheory
.Limits.PreservesLimitPair.iso G X Y).hom = CategoryTheory.Limits.prodComparison
 G X Y
参数：G : CategoryTheory.Functor C D；X Y : C；G.obj X；G.obj Y；CategoryTheory.Limits.
pair X Y；CategoryTheory.Limits.PreservesLimitPair.iso G X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesLimitPair.iso_hom : (PreservesLimitPair.iso G X Y).hom = prodComparison G X Y :=
  rfl

@[simp, reassoc]
/-
**CategoryTheory.Limits.PreservesLimitPair.iso_inv_fst** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.PreservesLimitPair`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 (X Y : C) [inst_2 : CategoryTheory.Limits.HasBinaryProduct X Y]   [inst_3 : Cat
egoryTheory.Limits.HasBinaryProduct (G.obj X) (G.obj Y)]   [inst_4 : CategoryThe
ory.Limits.PreservesLimit (CategoryTheory.Limits.pair X Y) G],   CategoryTheory.
CategoryStruct.comp (CategoryTheory.Limits.PreservesLimitPair.iso G X Y).inv    
   (G.map CategoryTheory.Limits.prod.fst) =     CategoryTheory.Limits.prod.fst
参数：G : CategoryTheory.Functor C D；X Y : C；G.obj X；G.obj Y；CategoryTheory.Limits.
pair X Y；CategoryTheory.Limits.PreservesLimitPair.iso G X Y；G.map CategoryTheory
.Limits.prod.fst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.cancel_iso_hom_left`：cancel_iso_hom_left {X Y Z : C} 
(f : X ≅ Y) (g g' : Y ⟶ Z) : f.hom ≫ g = f.hom ≫ g' ↔ g = g'
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.prodComparison_fst`：prodComparison_fst : prodCompa
rison F A B ≫ prod.fst = F.map prod.fst
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesLimitPair.iso_inv_fst :
    (PreservesLimitPair.iso G X Y).inv ≫ G.map prod.fst = prod.fst := by
  rw [← Iso.cancel_iso_hom_left (PreservesLimitPair.iso G X Y), ← Category.assoc, Iso.hom_inv_id]
  simp

@[simp, reassoc]
/-
**CategoryTheory.Limits.PreservesLimitPair.iso_inv_snd** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.PreservesLimitPair`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 (X Y : C) [inst_2 : CategoryTheory.Limits.HasBinaryProduct X Y]   [inst_3 : Cat
egoryTheory.Limits.HasBinaryProduct (G.obj X) (G.obj Y)]   [inst_4 : CategoryThe
ory.Limits.PreservesLimit (CategoryTheory.Limits.pair X Y) G],   CategoryTheory.
CategoryStruct.comp (CategoryTheory.Limits.PreservesLimitPair.iso G X Y).inv    
   (G.map CategoryTheory.Limits.prod.snd) =     CategoryTheory.Limits.prod.snd
参数：G : CategoryTheory.Functor C D；X Y : C；G.obj X；G.obj Y；CategoryTheory.Limits.
pair X Y；CategoryTheory.Limits.PreservesLimitPair.iso G X Y；G.map CategoryTheory
.Limits.prod.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.cancel_iso_hom_left`：cancel_iso_hom_left {X Y Z : C} 
(f : X ≅ Y) (g g' : Y ⟶ Z) : f.hom ≫ g = f.hom ≫ g' ↔ g = g'
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.prodComparison_snd`：prodComparison_snd : prodCompa
rison F A B ≫ prod.snd = F.map prod.snd
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesLimitPair.iso_inv_snd :
    (PreservesLimitPair.iso G X Y).inv ≫ G.map prod.snd = prod.snd := by
  rw [← Iso.cancel_iso_hom_left (PreservesLimitPair.iso G X Y), ← Category.assoc, Iso.hom_inv_id]
  simp
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (prodComparison G X Y) := by
  rw [← PreservesLimitPair.iso_hom]
  infer_instance

/-- If the product comparison maps of `G` at every pair `(X,Y)` is an
isomorphism, then `G` preserves binary products. -/
/-
**CategoryTheory.Limits.preservesBinaryProducts_of_isIso_prodComparison** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBinaryProducts_of_isIso_prodComparison [HasBinaryProducts C] [Has
BinaryProducts D] [i : forall {X Y : C}, IsIso (prodComparison G X Y)] : Preserv
esLimitsOfShape (Discrete WalkingPair) G where preservesLimit
参数：prodComparison G X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitPair.of_iso_prod_comparison`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t

--- 原说明 ---
If the product comparison maps of `G` at every pair `(X,Y)` is an
isomorphism, then `G` preserves binary products.
-/
lemma preservesBinaryProducts_of_isIso_prodComparison
    [HasBinaryProducts C] [HasBinaryProducts D]
    [i : ∀ {X Y : C}, IsIso (prodComparison G X Y)] :
    PreservesLimitsOfShape (Discrete WalkingPair) G where
  preservesLimit := by
    intro K
    have : PreservesLimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) G :=
      PreservesLimitPair.of_iso_prod_comparison ..
    apply preservesLimit_of_iso_diagram G (diagramIsoPair K).symm

end

section

variable {P X Y Z : C} (f : X ⟶ P) (g : Y ⟶ P)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The map of a binary cofan is a colimit iff
the cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `BinaryCofan.mk` with `Functor.mapCocone`.
-/
/-
**CategoryTheory.Limits.isColimitMapCoconeBinaryCofanEquiv** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：isColimitMapCoconeBinaryCofanEquiv : IsColimit (Functor.mapCocone G (Binar
yCofan.mk f g)) ≃ IsColimit (BinaryCofan.mk (G.map f) (G.map g))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The map of a binary cofan is a colimit iff
the cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `BinaryCofan.mk` with `Functor.mapCocone`.
-/
def isColimitMapCoconeBinaryCofanEquiv :
    IsColimit (Functor.mapCocone G (BinaryCofan.mk f g))
    ≃ IsColimit (BinaryCofan.mk (G.map f) (G.map g)) :=
  (IsColimit.precomposeHomEquiv (diagramIsoPair _).symm _).symm.trans
    (IsColimit.equivIsoColimit
      (Cocone.ext (Iso.refl _)
        (by rintro (_ | _) <;> simp)))

/-- The property of preserving coproducts expressed in terms of binary cofans. -/
/-
**CategoryTheory.Limits.mapIsColimitOfPreservesOfIsColimit** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：mapIsColimitOfPreservesOfIsColimit [PreservesColimit (pair X Y) G] (l : Is
Colimit (BinaryCofan.mk f g)) : IsColimit (BinaryCofan.mk (G.map f) (G.map g))
参数：pair X Y；l : IsColimit (BinaryCofan.mk f g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of preserving coproducts expressed in terms of binary cofans.
-/
def mapIsColimitOfPreservesOfIsColimit [PreservesColimit (pair X Y) G]
    (l : IsColimit (BinaryCofan.mk f g)) : IsColimit (BinaryCofan.mk (G.map f) (G.map g)) :=
  isColimitMapCoconeBinaryCofanEquiv G f g (isColimitOfPreserves G l)

/-- The property of reflecting coproducts expressed in terms of binary cofans. -/
/-
**CategoryTheory.Limits.isColimitOfReflectsOfMapIsColimit** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：isColimitOfReflectsOfMapIsColimit [ReflectsColimit (pair X Y) G] (l : IsCo
limit (BinaryCofan.mk (G.map f) (G.map g))) : IsColimit (BinaryCofan.mk f g)
参数：pair X Y；l : IsColimit (BinaryCofan.mk (G.map f) (G.map g))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The property of reflecting coproducts expressed in terms of binary cofans.
-/
def isColimitOfReflectsOfMapIsColimit [ReflectsColimit (pair X Y) G]
    (l : IsColimit (BinaryCofan.mk (G.map f) (G.map g))) : IsColimit (BinaryCofan.mk f g) :=
  isColimitOfReflects G ((isColimitMapCoconeBinaryCofanEquiv G f g).symm l)

variable (X Y)
variable [HasBinaryCoproduct X Y]

/--
If `G` preserves binary coproducts and `C` has them, then the binary cofan constructed of the mapped
morphisms of the binary product cocone is a colimit.
-/
/-
**CategoryTheory.Limits.isColimitOfHasBinaryCoproductOfPreservesColimit** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isColimitOfHasBinaryCoproductOfPreservesColimit [PreservesColimit (pair X 
Y) G] : IsColimit (BinaryCofan.mk (G.map (Limits.coprod.inl : X ⟶ X ⨿ Y)) (G.map
 Limits.coprod.inr))
参数：pair X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves binary coproducts and `C` has them, then the binary cofan const
ructed of the mapped
morphisms of the binary product cocone is a colimit.
-/
def isColimitOfHasBinaryCoproductOfPreservesColimit [PreservesColimit (pair X Y) G] :
    IsColimit (BinaryCofan.mk (G.map (Limits.coprod.inl : X ⟶ X ⨿ Y)) (G.map Limits.coprod.inr)) :=
  mapIsColimitOfPreservesOfIsColimit G _ _ (coprodIsCoprod X Y)

variable [HasBinaryCoproduct (G.obj X) (G.obj Y)]

/-- If the coproduct comparison map for `G` at `(X,Y)` is an isomorphism, then `G` preserves the
pair of `(X,Y)`.
-/
/-
**CategoryTheory.Limits.PreservesColimitPair.of_iso_coprod_comparison** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.Limits.PreservesColimitPair`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 (X Y : C) [inst_2 : CategoryTheory.Limits.HasBinaryCoproduct X Y]   [inst_3 : C
ategoryTheory.Limits.HasBinaryCoproduct (G.obj X) (G.obj Y)]   [i : CategoryTheo
ry.IsIso (CategoryTheory.Limits.coprodComparison G X Y)],   CategoryTheory.Limit
s.PreservesColimit (CategoryTheory.Limits.pair X Y) G
参数：G : CategoryTheory.Functor C D；X Y : C；G.obj X；G.obj Y；CategoryTheory.Limits.
coprodComparison G X Y；CategoryTheory.Limits.pair X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If the coproduct comparison map for `G` at `(X,Y)` is an isomorphism, then `G` p
reserves the
pair of `(X,Y)`.
-/
lemma PreservesColimitPair.of_iso_coprod_comparison [i : IsIso (coprodComparison G X Y)] :
    PreservesColimit (pair X Y) G := by
  apply preservesColimit_of_preserves_colimit_cocone (coprodIsCoprod X Y)
  apply (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm _
  refine @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (pair (G.obj X) (G.obj Y))) ?_
  apply i

variable [PreservesColimit (pair X Y) G]

/--
If `G` preserves the coproduct of `(X,Y)`, then the coproduct comparison map for `G` at `(X,Y)` is
an isomorphism.
-/
/-
**CategoryTheory.Limits.PreservesColimitPair.iso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.PreservesColimitPair`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           (X Y : C) →             [inst_2 : CategoryT
heory.Limits.HasBinaryCoproduct X Y] →               [inst_3 : CategoryTheory.Li
mits.HasBinaryCoproduct (G.obj X) (G.obj Y)] →                 [CategoryTheory.L
imits.PreservesColimit (CategoryTheory.Limits.pair X Y) G] →                   G
.obj X ⨿ G.obj Y ≅ G.obj (X ⨿ Y)
参数：G : CategoryTheory.Functor C D；X Y : C；G.obj X；G.obj Y；CategoryTheory.Limits.
pair X Y；X ⨿ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves the coproduct of `(X,Y)`, then the coproduct comparison map for
 `G` at `(X,Y)` is
an isomorphism.
-/
def PreservesColimitPair.iso : G.obj X ⨿ G.obj Y ≅ G.obj (X ⨿ Y) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasBinaryCoproductOfPreservesColimit G X Y)

@[simp]
/-
**CategoryTheory.Limits.PreservesColimitPair.iso_hom** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.PreservesColimitPair`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 (X Y : C) [inst_2 : CategoryTheory.Limits.HasBinaryCoproduct X Y]   [inst_3 : C
ategoryTheory.Limits.HasBinaryCoproduct (G.obj X) (G.obj Y)]   [inst_4 : Categor
yTheory.Limits.PreservesColimit (CategoryTheory.Limits.pair X Y) G],   (Category
Theory.Limits.PreservesColimitPair.iso G X Y).hom = CategoryTheory.Limits.coprod
Comparison G X Y
参数：G : CategoryTheory.Functor C D；X Y : C；G.obj X；G.obj Y；CategoryTheory.Limits.
pair X Y；CategoryTheory.Limits.PreservesColimitPair.iso G X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesColimitPair.iso_hom :
    (PreservesColimitPair.iso G X Y).hom = coprodComparison G X Y := rfl
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (coprodComparison G X Y) := by
  rw [← PreservesColimitPair.iso_hom]
  infer_instance

/-- If the coproduct comparison maps of `G` at every pair `(X,Y)` is an
isomorphism, then `G` preserves binary coproducts. -/
/-
**CategoryTheory.Limits.preservesBinaryCoproducts_of_isIso_coprodComparison** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBinaryCoproducts_of_isIso_coprodComparison [HasBinaryCoproducts C
] [HasBinaryCoproducts D] [i : forall {X Y : C}, IsIso (coprodComparison G X Y)]
 : PreservesColimitsOfShape (Discrete WalkingPair) G where preservesColimit
参数：coprodComparison G X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitPair.of_iso_coprod_comparison`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 :
 CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…

--- 原说明 ---
If the coproduct comparison maps of `G` at every pair `(X,Y)` is an
isomorphism, then `G` preserves binary coproducts.
-/
lemma preservesBinaryCoproducts_of_isIso_coprodComparison
    [HasBinaryCoproducts C] [HasBinaryCoproducts D]
    [i : ∀ {X Y : C}, IsIso (coprodComparison G X Y)] :
    PreservesColimitsOfShape (Discrete WalkingPair) G where
  preservesColimit := by
    intro K
    have : PreservesColimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) G :=
      PreservesColimitPair.of_iso_coprod_comparison ..
    apply preservesColimit_of_iso_diagram G (diagramIsoPair K).symm

end

end CategoryTheory.Limits

