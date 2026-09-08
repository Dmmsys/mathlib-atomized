/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Products and coproducts in `C` and `Cᵒᵖ`

We construct products and coproducts in the opposite categories.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {J : Type u₂} [Category.{v₂} J]
variable (X : Type v₂)

/-- If `C` has products indexed by `X`, then `Cᵒᵖ` has coproducts indexed by `X`.
-/
/-
**CategoryTheory.Limits.hasCoproductsOfShape_opposite** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasCoproductsOfShape_opposite [HasProductsOfShape X C] : HasCoproductsOfSh
ape X Cᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C

--- 原说明 ---
If `C` has products indexed by `X`, then `Cᵒᵖ` has coproducts indexed by `X`.
-/
instance hasCoproductsOfShape_opposite [HasProductsOfShape X C] : HasCoproductsOfShape X Cᵒᵖ := by
  have : HasLimitsOfShape (Discrete X)ᵒᵖ C :=
    hasLimitsOfShape_of_equivalence (Discrete.opposite X).symm
  infer_instance
/-
**CategoryTheory.Limits.hasCoproductsOfShape_of_opposite** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：hasCoproductsOfShape_of_opposite [HasProductsOfShape X Cᵒᵖ] : HasCoproduct
sOfShape X C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasLimitsOfShape_op`：hasColi
mitsOfShape_of_hasLimitsOfShape_op [HasLimitsOfShape Jᵒᵖ Cᵒᵖ] : HasColimitsOfSha
pe J C
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
-/
theorem hasCoproductsOfShape_of_opposite [HasProductsOfShape X Cᵒᵖ] : HasCoproductsOfShape X C :=
  haveI : HasLimitsOfShape (Discrete X)ᵒᵖ Cᵒᵖ :=
    hasLimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasColimitsOfShape_of_hasLimitsOfShape_op

/-- If `C` has coproducts indexed by `X`, then `Cᵒᵖ` has products indexed by `X`.
-/
/-
**CategoryTheory.Limits.hasProductsOfShape_opposite** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasProductsOfShape_opposite [HasCoproductsOfShape X C] : HasProductsOfShap
e X Cᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_op_of_hasColimitsOfShape`：hasLimi
tsOfShape_op_of_hasColimitsOfShape [HasColimitsOfShape Jᵒᵖ C] : HasLimitsOfShape
 J Cᵒᵖ
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C

--- 原说明 ---
If `C` has coproducts indexed by `X`, then `Cᵒᵖ` has products indexed by `X`.
-/
instance hasProductsOfShape_opposite [HasCoproductsOfShape X C] : HasProductsOfShape X Cᵒᵖ :=
  haveI : HasColimitsOfShape (Discrete X)ᵒᵖ C :=
    hasColimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasLimitsOfShape_op_of_hasColimitsOfShape
/-
**CategoryTheory.Limits.hasProductsOfShape_of_opposite** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasProductsOfShape_of_opposite [HasCoproductsOfShape X Cᵒᵖ] : HasProductsO
fShape X C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasColimitsOfShape_op`：hasLimi
tsOfShape_of_hasColimitsOfShape_op [HasColimitsOfShape Jᵒᵖ Cᵒᵖ] : HasLimitsOfSha
pe J C
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
-/
theorem hasProductsOfShape_of_opposite [HasCoproductsOfShape X Cᵒᵖ] : HasProductsOfShape X C :=
  haveI : HasColimitsOfShape (Discrete X)ᵒᵖ Cᵒᵖ :=
    hasColimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasLimitsOfShape_of_hasColimitsOfShape_op
/-
**CategoryTheory.Limits.hasProducts_opposite** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits`。
形式化陈述：hasProducts_opposite [HasCoproducts.{v₂} C] : HasProducts.{v₂} Cᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasProducts_opposite [HasCoproducts.{v₂} C] : HasProducts.{v₂} Cᵒᵖ := fun _ =>
  inferInstance
/-
**CategoryTheory.Limits.hasProducts_of_opposite** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：hasProducts_of_opposite [HasCoproducts.{v₂} Cᵒᵖ] : HasProducts.{v₂} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasProductsOfShape_of_opposite`：hasProductsOfShape
_of_opposite [HasCoproductsOfShape X Cᵒᵖ] : HasProductsOfShape X C
-/
theorem hasProducts_of_opposite [HasCoproducts.{v₂} Cᵒᵖ] : HasProducts.{v₂} C := fun X =>
  hasProductsOfShape_of_opposite X
/-
**CategoryTheory.Limits.hasCoproducts_opposite** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：hasCoproducts_opposite [HasProducts.{v₂} C] : HasCoproducts.{v₂} Cᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoproducts_opposite [HasProducts.{v₂} C] : HasCoproducts.{v₂} Cᵒᵖ := fun _ =>
  inferInstance
/-
**CategoryTheory.Limits.hasCoproducts_of_opposite** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：hasCoproducts_of_opposite [HasProducts.{v₂} Cᵒᵖ] : HasCoproducts.{v₂} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasCoproductsOfShape_of_opposite`：hasCoproductsOfS
hape_of_opposite [HasProductsOfShape X Cᵒᵖ] : HasCoproductsOfShape X C
-/
theorem hasCoproducts_of_opposite [HasProducts.{v₂} Cᵒᵖ] : HasCoproducts.{v₂} C := fun X =>
  hasCoproductsOfShape_of_opposite X
/-
**CategoryTheory.Limits.hasFiniteCoproducts_opposite** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：hasFiniteCoproducts_opposite [HasFiniteProducts C] : HasFiniteCoproducts C
ᵒᵖ where out _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance hasFiniteCoproducts_opposite [HasFiniteProducts C] : HasFiniteCoproducts Cᵒᵖ where
  out _ := Limits.hasCoproductsOfShape_opposite _
/-
**CategoryTheory.Limits.hasFiniteCoproducts_of_opposite** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteCoproducts_of_opposite [HasFiniteProducts Cᵒᵖ] : HasFiniteCoprodu
cts C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasCoproductsOfShape_of_opposite`：hasCoproductsOfS
hape_of_opposite [HasProductsOfShape X Cᵒᵖ] : HasCoproductsOfShape X C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem hasFiniteCoproducts_of_opposite [HasFiniteProducts Cᵒᵖ] : HasFiniteCoproducts C :=
  { out := fun _ => hasCoproductsOfShape_of_opposite _ }
/-
**CategoryTheory.Limits.hasFiniteProducts_opposite** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：hasFiniteProducts_opposite [HasFiniteCoproducts C] : HasFiniteProducts Cᵒᵖ
 where out _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance hasFiniteProducts_opposite [HasFiniteCoproducts C] : HasFiniteProducts Cᵒᵖ where
  out _ := inferInstance
/-
**CategoryTheory.Limits.hasFiniteProducts_of_opposite** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasFiniteProducts_of_opposite [HasFiniteCoproducts Cᵒᵖ] : HasFiniteProduct
s C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasProductsOfShape_of_opposite`：hasProductsOfShape
_of_opposite [HasCoproductsOfShape X Cᵒᵖ] : HasProductsOfShape X C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem hasFiniteProducts_of_opposite [HasFiniteCoproducts Cᵒᵖ] : HasFiniteProducts C :=
  { out := fun _ => hasProductsOfShape_of_opposite _ }

section OppositeCoproducts

variable {α : Type*} {Z : α → C}

section
variable [HasCoproduct Z]

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasLimit (Discrete.functor Z).op := hasLimit_op_of_hasColimit (Discrete.functor Z)
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasLimit ((Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op) :=
  hasLimit_equivalence_comp (Discrete.opposite α).symm
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasProduct (op <| Z ·) := hasLimit_of_iso
  ((Discrete.natIsoFunctor ≪≫ Discrete.natIso (fun _ ↦ by rfl)) :
    (Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op ≅
    Discrete.functor (op <| Z ·))

/-- A `Cofan` gives a `Fan` in the opposite category. -/
@[simp, implicit_reducible]
/-
**CategoryTheory.Limits.Cofan.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s.Cofan`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {α : T
ype u_1} → {Z : α → C} → CategoryTheory.Limits.Cofan Z → CategoryTheory.Limits.F
an fun x => Opposite.op (Z x)
参数：Z x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Cofan` gives a `Fan` in the opposite category.
-/
def Cofan.op (c : Cofan Z) : Fan (op <| Z ·) := Fan.mk _ (fun a ↦ (c.inj a).op)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If a `Cofan` is colimit, then its opposite is limit. -/
-- noncomputability is just for performance (compilation takes a while)
/-
**CategoryTheory.Limits.Cofan.IsColimit.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Cofan.IsColimit`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {α : T
ype u_1} →       {Z : α → C} →         {c : CategoryTheory.Limits.Cofan Z} → Cat
egoryTheory.Limits.IsColimit c → CategoryTheory.Limits.IsLimit c.op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def Cofan.IsColimit.op {c : Cofan Z} (hc : IsColimit c) : IsLimit c.op := by
  let e : Discrete.functor (Opposite.op <| Z ·) ≅ (Discrete.opposite α).inverse ⋙
    (Discrete.functor Z).op := Discrete.natIso (fun _ ↦ Iso.refl _)
  refine IsLimit.ofIsoLimit ((IsLimit.postcomposeInvEquiv e _).2
    (IsLimit.whiskerEquivalence hc.op (Discrete.opposite α).symm))
    (Cone.ext (Iso.refl _) (fun ⟨a⟩ ↦ ?_))
  simp [e, Cofan.inj]

/--
The canonical isomorphism from the opposite of an abstract coproduct to the corresponding product
in the opposite category.
-/
/-
**CategoryTheory.Limits.opCoproductIsoProduct'** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：opCoproductIsoProduct' {c : Cofan Z} {f : Fan (op <| Z ·)} (hc : IsColimit
 c) (hf : IsLimit f) : op c.pt ≅ f.pt
参数：op <| Z ·；hc : IsColimit c；hf : IsLimit f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism from the opposite of an abstract coproduct to the corr
esponding product
in the opposite category.
-/
def opCoproductIsoProduct' {c : Cofan Z} {f : Fan (op <| Z ·)}
    (hc : IsColimit c) (hf : IsLimit f) : op c.pt ≅ f.pt :=
  IsLimit.conePointUniqueUpToIso (Cofan.IsColimit.op hc) hf

variable (Z) in
/--
The canonical isomorphism from the opposite of the coproduct to the product in the opposite
category.
-/
/-
**CategoryTheory.Limits.opCoproductIsoProduct** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：opCoproductIsoProduct : op (∐ Z) ≅ ∏ᶜ (op <| Z ·)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasProductOppositeOp`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   [CategoryTheory
.Limits.HasCoproduct Z], CategoryThe…

--- 原说明 ---
The canonical isomorphism from the opposite of the coproduct to the product in t
he opposite
category.
-/
def opCoproductIsoProduct :
    op (∐ Z) ≅ ∏ᶜ (op <| Z ·) :=
  opCoproductIsoProduct' (coproductIsCoproduct Z) (productIsProduct (op <| Z ·))

end

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.opCoproductIsoProduct'_hom_comp_proj** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1}
 {Z : α → C}   {c : CategoryTheory.Limits.Cofan Z} {f : CategoryTheory.Limits.Fa
n fun x => Opposite.op (Z x)}   (hc : CategoryTheory.Limits.IsColimit c) (hf : C
ategoryTheory.Limits.IsLimit f) (i : α),   CategoryTheory.CategoryStruct.comp (C
ategoryTheory.Limits.opCoproductIsoProduct' hc hf).hom (f.proj i) = (c.inj i).op
参数：Z x；hc : CategoryTheory.Limits.IsColimit c；hf : CategoryTheory.Limits.IsLimit
 f；i : α；CategoryTheory.Limits.opCoproductIsoProduct' hc hf；f.proj i；c.inj i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opCoproductIsoProduct'_hom_comp_proj {c : Cofan Z} {f : Fan (op <| Z ·)}
    (hc : IsColimit c) (hf : IsLimit f) (i : α) :
    (opCoproductIsoProduct' hc hf).hom ≫ f.proj i = (c.inj i).op := by
  simp [opCoproductIsoProduct', Fan.proj]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.opCoproductIsoProduct_hom_comp_** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opCoproductIsoProduct_hom_comp_π [HasCoproduct Z] (i : α) :
    (opCoproductIsoProduct Z).hom ≫ Pi.π _ i = (Sigma.ι _ i).op :=
  Limits.opCoproductIsoProduct'_hom_comp_proj ..
/-
**CategoryTheory.Limits.opCoproductIsoProduct'_inv_comp_inj** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1}
 {Z : α → C}   {c : CategoryTheory.Limits.Cofan Z} {f : CategoryTheory.Limits.Fa
n fun x => Opposite.op (Z x)}   (hc : CategoryTheory.Limits.IsColimit c) (hf : C
ategoryTheory.Limits.IsLimit f) (b : α),   CategoryTheory.CategoryStruct.comp (C
ategoryTheory.Limits.opCoproductIsoProduct' hc hf).inv (c.inj b).op = f.proj b
参数：Z x；hc : CategoryTheory.Limits.IsColimit c；hf : CategoryTheory.Limits.IsLimit
 f；b : α；CategoryTheory.Limits.opCoproductIsoProduct' hc hf；c.inj b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
-/
theorem opCoproductIsoProduct'_inv_comp_inj {c : Cofan Z} {f : Fan (op <| Z ·)}
    (hc : IsColimit c) (hf : IsLimit f) (b : α) :
    (opCoproductIsoProduct' hc hf).inv ≫ (c.inj b).op = f.proj b :=
  IsLimit.conePointUniqueUpToIso_inv_comp (Cofan.IsColimit.op hc) hf ⟨b⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.opCoproductIsoProduct'_comp_self** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1}
 {Z : α → C}   {c c' : CategoryTheory.Limits.Cofan Z} {f : CategoryTheory.Limits
.Fan fun x => Opposite.op (Z x)}   (hc : CategoryTheory.Limits.IsColimit c) (hc'
 : CategoryTheory.Limits.IsColimit c')   (hf : CategoryTheory.Limits.IsLimit f),
   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.opCoproductIsoProdu
ct' hc hf).hom       (CategoryTheory.Limits.opCoproductIsoProduct' hc' hf).inv =
     (hc.coconePointUniqueUpToIso hc').op.inv
参数：Z x；hc : CategoryTheory.Limits.IsColimit c；hc' : CategoryTheory.Limits.IsColi
mit c'；hf : CategoryTheory.Limits.IsLimit f；CategoryTheory.Limits.opCoproductIso
Product' hc hf；CategoryTheory.Limits.opCoproductIsoProduct' hc' hf；hc.coconePoin
tUniqueUpToIso hc'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.op_inv`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.inv = α.inv.op
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_inv`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.opCoproductIsoProduct'_inv_comp_inj`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   {c :
 CategoryTheory.Limits.Cofan Z} {f : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
theorem opCoproductIsoProduct'_comp_self {c c' : Cofan Z} {f : Fan (op <| Z ·)}
    (hc : IsColimit c) (hc' : IsColimit c') (hf : IsLimit f) :
    (opCoproductIsoProduct' hc hf).hom ≫ (opCoproductIsoProduct' hc' hf).inv =
    (hc.coconePointUniqueUpToIso hc').op.inv := by
  apply Quiver.Hom.unop_inj
  apply hc'.hom_ext
  intro ⟨j⟩
  change c'.inj _ ≫ _ = _
  simp only [unop_op, unop_comp, Discrete.functor_obj, Iso.op_inv,
    Quiver.Hom.unop_op, IsColimit.comp_coconePointUniqueUpToIso_inv]
  apply Quiver.Hom.op_inj
  simp only [op_comp, op_unop, Quiver.Hom.op_unop, Category.assoc,
    opCoproductIsoProduct'_inv_comp_inj]
  rw [← opCoproductIsoProduct'_inv_comp_inj hc hf]
  simp only [Iso.hom_inv_id_assoc]
  rfl

variable (Z) in
/-
**CategoryTheory.Limits.opCoproductIsoProduct_inv_comp_** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem opCoproductIsoProduct_inv_comp_ι [HasCoproduct Z] (b : α) :
    (opCoproductIsoProduct Z).inv ≫ (Sigma.ι Z b).op = Pi.π (op <| Z ·) b :=
  opCoproductIsoProduct'_inv_comp_inj _ _ b

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.desc_op_comp_opCoproductIsoProduct'_hom** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1}
 {Z : α → C}   {c : CategoryTheory.Limits.Cofan Z} {f : CategoryTheory.Limits.Fa
n fun x => Opposite.op (Z x)}   (hc : CategoryTheory.Limits.IsColimit c) (hf : C
ategoryTheory.Limits.IsLimit f) (c' : CategoryTheory.Limits.Cofan Z),   Category
Theory.CategoryStruct.comp (hc.desc c').op (CategoryTheory.Limits.opCoproductIso
Product' hc hf).hom =     hf.lift c'.op
参数：Z x；hc : CategoryTheory.Limits.IsColimit c；hf : CategoryTheory.Limits.IsLimit
 f；c' : CategoryTheory.Limits.Cofan Z；hc.desc c'；CategoryTheory.Limits.opCoprodu
ctIsoProduct' hc hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.opCoproductIsoProduct'_inv_comp_inj`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   {c :
 CategoryTheory.Limits.Cofan Z} {f : CategoryTh…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
theorem desc_op_comp_opCoproductIsoProduct'_hom {c : Cofan Z} {f : Fan (op <| Z ·)}
    (hc : IsColimit c) (hf : IsLimit f) (c' : Cofan Z) :
    (hc.desc c').op ≫ (opCoproductIsoProduct' hc hf).hom = hf.lift c'.op := by
  refine (Iso.eq_comp_inv _).mp (Quiver.Hom.unop_inj (hc.hom_ext (fun ⟨j⟩ ↦ Quiver.Hom.op_inj ?_)))
  simp only [unop_op, Discrete.functor_obj, Quiver.Hom.unop_op, IsColimit.fac,
    Cofan.op, unop_comp, op_comp, op_unop, Quiver.Hom.op_unop, Category.assoc]
  erw [opCoproductIsoProduct'_inv_comp_inj, IsLimit.fac]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.desc_op_comp_opCoproductIsoProduct_hom** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：desc_op_comp_opCoproductIsoProduct_hom [HasCoproduct Z] {X : C} (π : (a : 
α) -> Z a ⟶ X) : (Sigma.desc π).op ≫ (opCoproductIsoProduct Z).hom = Pi.lift (fu
n a => (π a).op)
参数：π : (a : α) -> Z a ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasProductOppositeOp`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   [CategoryTheory
.Limits.HasCoproduct Z], CategoryThe…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.desc_op_comp_opCoproductIsoProduct'_hom`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   
{c : CategoryTheory.Limits.Cofan Z} {f : CategoryTh…
-/
theorem desc_op_comp_opCoproductIsoProduct_hom [HasCoproduct Z] {X : C} (π : (a : α) → Z a ⟶ X) :
    (Sigma.desc π).op ≫ (opCoproductIsoProduct Z).hom = Pi.lift (fun a ↦ (π a).op) := by
  convert!
    desc_op_comp_opCoproductIsoProduct'_hom (coproductIsCoproduct Z) (productIsProduct (op <| Z ·))
      (Cofan.mk _ π)
  · simp [Sigma.desc, coproductIsCoproduct]
  · simp [productIsProduct]

end OppositeCoproducts

section OppositeProducts

variable {α : Type*} {Z : α → C}

section
variable [HasProduct Z]

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasColimit (Discrete.functor Z).op := hasColimit_op_of_hasLimit (Discrete.functor Z)
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasColimit ((Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op) :=
  hasColimit_equivalence_comp (Discrete.opposite α).symm
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasCoproduct (op <| Z ·) := hasColimit_of_iso
  ((Discrete.natIsoFunctor ≪≫ Discrete.natIso (fun _ ↦ by rfl)) :
    (Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op ≅
    Discrete.functor (op <| Z ·)).symm

/-- A `Fan` gives a `Cofan` in the opposite category. -/
@[simp]
/-
**CategoryTheory.Limits.Fan.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.
Fan`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {α : T
ype u_1} → {Z : α → C} → CategoryTheory.Limits.Fan Z → CategoryTheory.Limits.Cof
an fun x => Opposite.op (Z x)
参数：Z x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Fan` gives a `Cofan` in the opposite category.
-/
def Fan.op (f : Fan Z) : Cofan (op <| Z ·) := Cofan.mk _ (fun a ↦ (f.proj a).op)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If a `Fan` is limit, then its opposite is colimit. -/
-- noncomputability is just for performance (compilation takes a while)
/-
**CategoryTheory.Limits.Fan.IsLimit.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.Fan.IsLimit`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {α : T
ype u_1} →       {Z : α → C} →         {f : CategoryTheory.Limits.Fan Z} → Categ
oryTheory.Limits.IsLimit f → CategoryTheory.Limits.IsColimit f.op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def Fan.IsLimit.op {f : Fan Z} (hf : IsLimit f) : IsColimit f.op := by
  let e : Discrete.functor (Opposite.op <| Z ·) ≅ (Discrete.opposite α).inverse ⋙
    (Discrete.functor Z).op := Discrete.natIso (fun _ ↦ Iso.refl _)
  refine IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv e _).2
    (IsColimit.whiskerEquivalence hf.op (Discrete.opposite α).symm))
    (Cocone.ext (Iso.refl _) (fun ⟨a⟩ ↦ ?_))
  simp [e, Fan.proj]

/--
The canonical isomorphism from the opposite of an abstract product to the corresponding coproduct
in the opposite category.
-/
/-
**CategoryTheory.Limits.opProductIsoCoproduct'** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：opProductIsoCoproduct' {f : Fan Z} {c : Cofan (op <| Z ·)} (hf : IsLimit f
) (hc : IsColimit c) : op f.pt ≅ c.pt
参数：op <| Z ·；hf : IsLimit f；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism from the opposite of an abstract product to the corres
ponding coproduct
in the opposite category.
-/
def opProductIsoCoproduct' {f : Fan Z} {c : Cofan (op <| Z ·)}
    (hf : IsLimit f) (hc : IsColimit c) : op f.pt ≅ c.pt :=
  IsColimit.coconePointUniqueUpToIso (Fan.IsLimit.op hf) hc

variable (Z) in
/--
The canonical isomorphism from the opposite of the product to the coproduct in the opposite
category.
-/
/-
**CategoryTheory.Limits.opProductIsoCoproduct** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：opProductIsoCoproduct : op (∏ᶜ Z) ≅ ∐ (op <| Z ·)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasCoproductOppositeOp`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   [CategoryTheo
ry.Limits.HasProduct Z], CategoryTheor…

--- 原说明 ---
The canonical isomorphism from the opposite of the product to the coproduct in t
he opposite
category.
-/
def opProductIsoCoproduct :
    op (∏ᶜ Z) ≅ ∐ (op <| Z ·) :=
  opProductIsoCoproduct' (productIsProduct Z) (coproductIsCoproduct (op <| Z ·))

end

/-
**CategoryTheory.Limits.proj_comp_opProductIsoCoproduct'_hom** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1}
 {Z : α → C} {f : CategoryTheory.Limits.Fan Z}   {c : CategoryTheory.Limits.Cofa
n fun x => Opposite.op (Z x)} (hf : CategoryTheory.Limits.IsLimit f)   (hc : Cat
egoryTheory.Limits.IsColimit c) (b : α),   CategoryTheory.CategoryStruct.comp (f
.proj b).op (CategoryTheory.Limits.opProductIsoCoproduct' hf hc).hom = c.inj b
参数：Z x；hf : CategoryTheory.Limits.IsLimit f；hc : CategoryTheory.Limits.IsColimit
 c；b : α；f.proj b；CategoryTheory.Limits.opProductIsoCoproduct' hf hc。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
theorem proj_comp_opProductIsoCoproduct'_hom {f : Fan Z} {c : Cofan (op <| Z ·)}
    (hf : IsLimit f) (hc : IsColimit c) (b : α) :
    (f.proj b).op ≫ (opProductIsoCoproduct' hf hc).hom = c.inj b :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (Fan.IsLimit.op hf) hc ⟨b⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.opProductIsoCoproduct'_comp_self** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1}
 {Z : α → C}   {f f' : CategoryTheory.Limits.Fan Z} {c : CategoryTheory.Limits.C
ofan fun x => Opposite.op (Z x)}   (hf : CategoryTheory.Limits.IsLimit f) (hf' :
 CategoryTheory.Limits.IsLimit f')   (hc : CategoryTheory.Limits.IsColimit c),  
 CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.opProductIsoCoproduct
' hf hc).hom       (CategoryTheory.Limits.opProductIsoCoproduct' hf' hc).inv =  
   (hf.conePointUniqueUpToIso hf').op.inv
参数：Z x；hf : CategoryTheory.Limits.IsLimit f；hf' : CategoryTheory.Limits.IsLimit 
f'；hc : CategoryTheory.Limits.IsColimit c；CategoryTheory.Limits.opProductIsoCopr
oduct' hf hc；CategoryTheory.Limits.opProductIsoCoproduct' hf' hc；hf.conePointUni
queUpToIso hf'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.op_inv`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.inv = α.inv.op
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.Limits.proj_comp_opProductIsoCoproduct'_hom`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C} {f : 
CategoryTheory.Limits.Fan Z}   {c : CategoryTheo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem opProductIsoCoproduct'_comp_self {f f' : Fan Z} {c : Cofan (op <| Z ·)}
    (hf : IsLimit f) (hf' : IsLimit f') (hc : IsColimit c) :
    (opProductIsoCoproduct' hf hc).hom ≫ (opProductIsoCoproduct' hf' hc).inv =
    (hf.conePointUniqueUpToIso hf').op.inv := by
  apply Quiver.Hom.unop_inj
  apply hf.hom_ext
  intro ⟨j⟩
  change _ ≫ f.proj _ = _
  simp only [unop_op, unop_comp, Category.assoc, Discrete.functor_obj, Iso.op_inv,
    Quiver.Hom.unop_op, IsLimit.conePointUniqueUpToIso_inv_comp]
  apply Quiver.Hom.op_inj
  simp only [op_comp, op_unop, Quiver.Hom.op_unop, proj_comp_opProductIsoCoproduct'_hom]
  rw [← proj_comp_opProductIsoCoproduct'_hom hf' hc]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

variable (Z) in
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_comp_opProductIsoCoproduct_hom [HasProduct Z] (b : α) :
    (Pi.π Z b).op ≫ (opProductIsoCoproduct Z).hom = Sigma.ι (op <| Z ·) b :=
  proj_comp_opProductIsoCoproduct'_hom _ _ b

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.opProductIsoCoproduct'_inv_comp_lift** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1}
 {Z : α → C} {f : CategoryTheory.Limits.Fan Z}   {c : CategoryTheory.Limits.Cofa
n fun x => Opposite.op (Z x)} (hf : CategoryTheory.Limits.IsLimit f)   (hc : Cat
egoryTheory.Limits.IsColimit c) (f' : CategoryTheory.Limits.Fan Z),   CategoryTh
eory.CategoryStruct.comp (CategoryTheory.Limits.opProductIsoCoproduct' hf hc).in
v (hf.lift f').op =     hc.desc f'.op
参数：Z x；hf : CategoryTheory.Limits.IsLimit f；hc : CategoryTheory.Limits.IsColimit
 c；f' : CategoryTheory.Limits.Fan Z；CategoryTheory.Limits.opProductIsoCoproduct'
 hf hc；hf.lift f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.proj_comp_opProductIsoCoproduct'_hom`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C} {f : 
CategoryTheory.Limits.Fan Z}   {c : CategoryTheo…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
theorem opProductIsoCoproduct'_inv_comp_lift {f : Fan Z} {c : Cofan (op <| Z ·)}
    (hf : IsLimit f) (hc : IsColimit c) (f' : Fan Z) :
    (opProductIsoCoproduct' hf hc).inv ≫ (hf.lift f').op = hc.desc f'.op := by
  refine (Iso.inv_comp_eq _).mpr (Quiver.Hom.unop_inj (hf.hom_ext (fun ⟨j⟩ ↦ Quiver.Hom.op_inj ?_)))
  simp only [Discrete.functor_obj, unop_op, Quiver.Hom.unop_op, IsLimit.fac, Fan.op, unop_comp,
    Category.assoc, op_comp, op_unop, Quiver.Hom.op_unop]
  erw [← Category.assoc, proj_comp_opProductIsoCoproduct'_hom, IsColimit.fac]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.opProductIsoCoproduct_inv_comp_lift** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：opProductIsoCoproduct_inv_comp_lift [HasProduct Z] {X : C} (π : (a : α) ->
 X ⟶ Z a) : (opProductIsoCoproduct Z).inv ≫ (Pi.lift π).op = Sigma.desc (fun a =
> (π a).op)
参数：π : (a : α) -> X ⟶ Z a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasCoproductOppositeOp`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   [CategoryTheo
ry.Limits.HasProduct Z], CategoryTheor…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.opProductIsoCoproduct'_inv_comp_lift`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C} {f : 
CategoryTheory.Limits.Fan Z}   {c : CategoryTheo…
-/
theorem opProductIsoCoproduct_inv_comp_lift [HasProduct Z] {X : C} (π : (a : α) → X ⟶ Z a) :
    (opProductIsoCoproduct Z).inv ≫ (Pi.lift π).op = Sigma.desc (fun a ↦ (π a).op) := by
  convert!
    opProductIsoCoproduct'_inv_comp_lift (productIsProduct Z) (coproductIsCoproduct (op <| Z ·))
      (Fan.mk _ π)
  · simp [Pi.lift, productIsProduct]
  · simp [coproductIsCoproduct]

end OppositeProducts

section BinaryProducts

variable {A B : C} [HasBinaryProduct A B]

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasBinaryCoproduct (op A) (op B) := by
  have : HasProduct fun x ↦ (WalkingPair.casesOn x A B : C) := ‹_›
  change HasCoproduct _
  convert! (inferInstance : HasCoproduct fun x ↦ op (WalkingPair.casesOn x A B : C)) with x
  cases x <;> rfl

set_option backward.isDefEq.respectTransparency false in
variable (A B) in
/--
The canonical isomorphism from the opposite of the binary product to the coproduct in the opposite
category.
-/
/-
**CategoryTheory.Limits.opProdIsoCoprod** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：opProdIsoCoprod : op (A ⨯ B) ≅ (op A ⨿ op B) where hom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasBinaryCoproductOppositeOp`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A B : C} [CategoryTheory.Limits.Has
BinaryProduct A B],   CategoryTheory.Limits.…

--- 原说明 ---
The canonical isomorphism from the opposite of the binary product to the coprodu
ct in the opposite
category.
-/
def opProdIsoCoprod : op (A ⨯ B) ≅ (op A ⨿ op B) where
  hom := (prod.lift coprod.inl.unop coprod.inr.unop).op
  inv := coprod.desc prod.fst.op prod.snd.op
  hom_inv_id := by
    apply Quiver.Hom.unop_inj
    ext <;>
    · simp only
      apply Quiver.Hom.op_inj
      simp
  inv_hom_id := by
    ext <;>
    · simp only [colimit.ι_desc_assoc]
      apply Quiver.Hom.unop_inj
      simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.fst_opProdIsoCoprod_hom** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：fst_opProdIsoCoprod_hom : prod.fst.op ≫ (opProdIsoCoprod A B).hom = coprod
.inl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasBinaryCoproductOppositeOp`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A B : C} [CategoryTheory.Limits.Has
BinaryProduct A B],   CategoryTheory.Limits.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.opProdIsoCoprod.eq_1`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] (A B : C)   [inst_1 : CategoryTheory.Limits.HasB
inaryProduct A B],   CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Limits.prod.lift_fst`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `Quiver.Hom.op_unop`：Quiver.Hom.op_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) : f.unop.
op = f
-/
lemma fst_opProdIsoCoprod_hom : prod.fst.op ≫ (opProdIsoCoprod A B).hom = coprod.inl := by
  rw [opProdIsoCoprod, ← op_comp, prod.lift_fst, Quiver.Hom.op_unop]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.snd_opProdIsoCoprod_hom** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：snd_opProdIsoCoprod_hom : prod.snd.op ≫ (opProdIsoCoprod A B).hom = coprod
.inr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasBinaryCoproductOppositeOp`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A B : C} [CategoryTheory.Limits.Has
BinaryProduct A B],   CategoryTheory.Limits.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.opProdIsoCoprod.eq_1`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] (A B : C)   [inst_1 : CategoryTheory.Limits.HasB
inaryProduct A B],   CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Limits.prod.lift_snd`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `Quiver.Hom.op_unop`：Quiver.Hom.op_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) : f.unop.
op = f
-/
lemma snd_opProdIsoCoprod_hom : prod.snd.op ≫ (opProdIsoCoprod A B).hom = coprod.inr := by
  rw [opProdIsoCoprod, ← op_comp, prod.lift_snd, Quiver.Hom.op_unop]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inl_opProdIsoCoprod_inv** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：inl_opProdIsoCoprod_inv : coprod.inl ≫ (opProdIsoCoprod A B).inv = prod.fs
t.op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasBinaryCoproductOppositeOp`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A B : C} [CategoryTheory.Limits.Has
BinaryProduct A B],   CategoryTheory.Limits.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用引理 `CategoryTheory.Limits.fst_opProdIsoCoprod_hom`：fst_opProdIsoCoprod_hom :
 prod.fst.op ≫ (opProdIsoCoprod A B).hom = coprod.inl
-/
lemma inl_opProdIsoCoprod_inv : coprod.inl ≫ (opProdIsoCoprod A B).inv = prod.fst.op := by
  rw [Iso.comp_inv_eq, fst_opProdIsoCoprod_hom]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_opProdIsoCoprod_inv** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：inr_opProdIsoCoprod_inv : coprod.inr ≫ (opProdIsoCoprod A B).inv = prod.sn
d.op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasBinaryCoproductOppositeOp`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A B : C} [CategoryTheory.Limits.Has
BinaryProduct A B],   CategoryTheory.Limits.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用引理 `CategoryTheory.Limits.snd_opProdIsoCoprod_hom`：snd_opProdIsoCoprod_hom :
 prod.snd.op ≫ (opProdIsoCoprod A B).hom = coprod.inr
-/
lemma inr_opProdIsoCoprod_inv : coprod.inr ≫ (opProdIsoCoprod A B).inv = prod.snd.op := by
  rw [Iso.comp_inv_eq, snd_opProdIsoCoprod_hom]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.opProdIsoCoprod_hom_fst** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：opProdIsoCoprod_hom_fst : (opProdIsoCoprod A B).hom.unop ≫ prod.fst = copr
od.inl.unop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasBinaryCoproductOppositeOp`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A B : C} [CategoryTheory.Limits.Has
BinaryProduct A B],   CategoryTheory.Limits.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opProdIsoCoprod_hom_fst : (opProdIsoCoprod A B).hom.unop ≫ prod.fst = coprod.inl.unop := by
  simp [opProdIsoCoprod]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.opProdIsoCoprod_hom_snd** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：opProdIsoCoprod_hom_snd : (opProdIsoCoprod A B).hom.unop ≫ prod.snd = copr
od.inr.unop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasBinaryCoproductOppositeOp`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A B : C} [CategoryTheory.Limits.Has
BinaryProduct A B],   CategoryTheory.Limits.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opProdIsoCoprod_hom_snd : (opProdIsoCoprod A B).hom.unop ≫ prod.snd = coprod.inr.unop := by
  simp [opProdIsoCoprod]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.opProdIsoCoprod_inv_inl** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：opProdIsoCoprod_inv_inl : (opProdIsoCoprod A B).inv.unop ≫ coprod.inl.unop
 = prod.fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasBinaryCoproductOppositeOp`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A B : C} [CategoryTheory.Limits.Has
BinaryProduct A B],   CategoryTheory.Limits.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用引理 `CategoryTheory.Limits.inl_opProdIsoCoprod_inv`：inl_opProdIsoCoprod_inv :
 coprod.inl ≫ (opProdIsoCoprod A B).inv = prod.fst.op
· 使用定理 `Quiver.Hom.unop_op`：Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop
 = f
-/
lemma opProdIsoCoprod_inv_inl : (opProdIsoCoprod A B).inv.unop ≫ coprod.inl.unop = prod.fst := by
  rw [← unop_comp, inl_opProdIsoCoprod_inv, Quiver.Hom.unop_op]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.opProdIsoCoprod_inv_inr** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：opProdIsoCoprod_inv_inr : (opProdIsoCoprod A B).inv.unop ≫ coprod.inr.unop
 = prod.snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasBinaryCoproductOppositeOp`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A B : C} [CategoryTheory.Limits.Has
BinaryProduct A B],   CategoryTheory.Limits.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用引理 `CategoryTheory.Limits.inr_opProdIsoCoprod_inv`：inr_opProdIsoCoprod_inv :
 coprod.inr ≫ (opProdIsoCoprod A B).inv = prod.snd.op
· 使用定理 `Quiver.Hom.unop_op`：Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop
 = f
-/
lemma opProdIsoCoprod_inv_inr : (opProdIsoCoprod A B).inv.unop ≫ coprod.inr.unop = prod.snd := by
  rw [← unop_comp, inr_opProdIsoCoprod_inv, Quiver.Hom.unop_op]

end BinaryProducts

end CategoryTheory.Limits

