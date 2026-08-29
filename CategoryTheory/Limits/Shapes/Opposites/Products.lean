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

/--
Instance `hasCoproductsOfShape_opposite` / 实例 `hasCoproductsOfShape_opposite`

English:
instance hasCoproductsOfShape_opposite
  signature: [HasProductsOfShape X C]
  body: by
  have : HasLimitsOfShape (Discrete X)ᵒᵖ C :=
    hasLimitsOfShape_of_equivalence (Discrete.opposite X).symm
  infer_instance

中文:
实例 hasCoproductsOfShape_opposite
  签名: [HasProductsOfShape X C]
  定义体: by
  have : HasLimitsOfShape (Discrete X)ᵒᵖ C :=
    hasLimitsOfShape_of_equivalence (Discrete.opposite X).symm
  infer_instance

Depends on / 依赖: Discrete, Discrete.opposite, HasLimitsOfShape, hasLimitsOfShape_of_equivalence, infer_instance, opposite
-/
instance hasCoproductsOfShape_opposite [HasProductsOfShape X C] : HasCoproductsOfShape X Cᵒᵖ := by
  have : HasLimitsOfShape (Discrete X)ᵒᵖ C :=
    hasLimitsOfShape_of_equivalence (Discrete.opposite X).symm
  infer_instance

/--
theorem `hasCoproductsOfShape_of_opposite` / 定理 `hasCoproductsOfShape_of_opposite`

English:
theorem hasCoproductsOfShape_of_opposite
  given: [HasProductsOfShape X Cᵒᵖ]
  statement: HasCoproductsOfShape X C
  proof: haveI : HasLimitsOfShape (Discrete X)ᵒᵖ Cᵒᵖ :=
    hasLimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasColimitsOfShape_of_hasLimitsOfShape_op

中文:
定理 hasCoproductsOfShape_of_opposite
  条件: [HasProductsOfShape X Cᵒᵖ]
  结论: HasCoproductsOfShape X C
  证明: haveI : HasLimitsOfShape (Discrete X)ᵒᵖ Cᵒᵖ :=
    hasLimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasColimitsOfShape_of_hasLimitsOfShape_op

Depends on / 依赖: Discrete, Discrete.opposite, HasLimitsOfShape, hasColimitsOfShape_of_hasLimitsOfShape_op, hasLimitsOfShape_of_equivalence, opposite
-/
theorem hasCoproductsOfShape_of_opposite [HasProductsOfShape X Cᵒᵖ] : HasCoproductsOfShape X C :=
  haveI : HasLimitsOfShape (Discrete X)ᵒᵖ Cᵒᵖ :=
    hasLimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasColimitsOfShape_of_hasLimitsOfShape_op

/--
Instance `hasProductsOfShape_opposite` / 实例 `hasProductsOfShape_opposite`

English:
instance hasProductsOfShape_opposite
  signature: [HasCoproductsOfShape X C]
  body: haveI : HasColimitsOfShape (Discrete X)ᵒᵖ C :=
    hasColimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasLimitsOfShape_op_of_hasColimitsOfShape

中文:
实例 hasProductsOfShape_opposite
  签名: [HasCoproductsOfShape X C]
  定义体: haveI : HasColimitsOfShape (Discrete X)ᵒᵖ C :=
    hasColimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasLimitsOfShape_op_of_hasColimitsOfShape

Depends on / 依赖: Discrete, Discrete.opposite, HasColimitsOfShape, hasColimitsOfShape_of_equivalence, hasLimitsOfShape_op_of_hasColimitsOfShape, opposite
-/
instance hasProductsOfShape_opposite [HasCoproductsOfShape X C] : HasProductsOfShape X Cᵒᵖ :=
  haveI : HasColimitsOfShape (Discrete X)ᵒᵖ C :=
    hasColimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasLimitsOfShape_op_of_hasColimitsOfShape

/--
theorem `hasProductsOfShape_of_opposite` / 定理 `hasProductsOfShape_of_opposite`

English:
theorem hasProductsOfShape_of_opposite
  given: [HasCoproductsOfShape X Cᵒᵖ]
  statement: HasProductsOfShape X C
  proof: haveI : HasColimitsOfShape (Discrete X)ᵒᵖ Cᵒᵖ :=
    hasColimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasLimitsOfShape_of_hasColimitsOfShape_op

中文:
定理 hasProductsOfShape_of_opposite
  条件: [HasCoproductsOfShape X Cᵒᵖ]
  结论: HasProductsOfShape X C
  证明: haveI : HasColimitsOfShape (Discrete X)ᵒᵖ Cᵒᵖ :=
    hasColimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasLimitsOfShape_of_hasColimitsOfShape_op

Depends on / 依赖: Discrete, Discrete.opposite, HasColimitsOfShape, hasColimitsOfShape_of_equivalence, hasLimitsOfShape_of_hasColimitsOfShape_op, opposite
-/
theorem hasProductsOfShape_of_opposite [HasCoproductsOfShape X Cᵒᵖ] : HasProductsOfShape X C :=
  haveI : HasColimitsOfShape (Discrete X)ᵒᵖ Cᵒᵖ :=
    hasColimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasLimitsOfShape_of_hasColimitsOfShape_op

/--
Instance `hasProducts_opposite` / 实例 `hasProducts_opposite`

English:
instance hasProducts_opposite
  signature: [HasCoproducts.{v₂} C]
  body: fun _ =>
  inferInstance

中文:
实例 hasProducts_opposite
  签名: [HasCoproducts.{v₂} C]
  定义体: fun _ =>
  inferInstance
-/
instance hasProducts_opposite [HasCoproducts.{v₂} C] : HasProducts.{v₂} Cᵒᵖ := fun _ =>
  inferInstance

/--
theorem `hasProducts_of_opposite` / 定理 `hasProducts_of_opposite`

English:
theorem hasProducts_of_opposite
  given: [HasCoproducts.{v₂} Cᵒᵖ]
  statement: HasProducts.{v₂} C
  proof: fun X =>
  hasProductsOfShape_of_opposite X

中文:
定理 hasProducts_of_opposite
  条件: [HasCoproducts.{v₂} Cᵒᵖ]
  结论: HasProducts.{v₂} C
  证明: fun X =>
  hasProductsOfShape_of_opposite X
-/
theorem hasProducts_of_opposite [HasCoproducts.{v₂} Cᵒᵖ] : HasProducts.{v₂} C := fun X =>
  hasProductsOfShape_of_opposite X

/--
Instance `hasCoproducts_opposite` / 实例 `hasCoproducts_opposite`

English:
instance hasCoproducts_opposite
  signature: [HasProducts.{v₂} C]
  body: fun _ =>
  inferInstance

中文:
实例 hasCoproducts_opposite
  签名: [HasProducts.{v₂} C]
  定义体: fun _ =>
  inferInstance
-/
instance hasCoproducts_opposite [HasProducts.{v₂} C] : HasCoproducts.{v₂} Cᵒᵖ := fun _ =>
  inferInstance

/--
theorem `hasCoproducts_of_opposite` / 定理 `hasCoproducts_of_opposite`

English:
theorem hasCoproducts_of_opposite
  given: [HasProducts.{v₂} Cᵒᵖ]
  statement: HasCoproducts.{v₂} C
  proof: fun X =>
  hasCoproductsOfShape_of_opposite X

中文:
定理 hasCoproducts_of_opposite
  条件: [HasProducts.{v₂} Cᵒᵖ]
  结论: HasCoproducts.{v₂} C
  证明: fun X =>
  hasCoproductsOfShape_of_opposite X
-/
theorem hasCoproducts_of_opposite [HasProducts.{v₂} Cᵒᵖ] : HasCoproducts.{v₂} C := fun X =>
  hasCoproductsOfShape_of_opposite X

/--
Instance `hasFiniteCoproducts_opposite` / 实例 `hasFiniteCoproducts_opposite`

English:
instance hasFiniteCoproducts_opposite
  signature: [HasFiniteProducts C]
  body: Limits.hasCoproductsOfShape_opposite _

中文:
实例 hasFiniteCoproducts_opposite
  签名: [有FiniteProducts C]
  定义体: Limits.hasCoproductsOfShape_opposite _

Depends on / 依赖: Limits, Limits.hasCoproductsOfShape_opposite, hasCoproductsOfShape_opposite
-/
instance hasFiniteCoproducts_opposite [HasFiniteProducts C] : HasFiniteCoproducts Cᵒᵖ where
  out _ := Limits.hasCoproductsOfShape_opposite _

/--
theorem `hasFiniteCoproducts_of_opposite` / 定理 `hasFiniteCoproducts_of_opposite`

English:
theorem hasFiniteCoproducts_of_opposite
  given: [HasFiniteProducts Cᵒᵖ]
  statement: HasFiniteCoproducts C
  proof: { out := fun _ => hasCoproductsOfShape_of_opposite _ }

中文:
定理 hasFiniteCoproducts_of_opposite
  条件: [有FiniteProducts Cᵒᵖ]
  结论: 有FiniteCoproducts C
  证明: { out := fun _ => hasCoproductsOfShape_of_opposite _ }

Depends on / 依赖: hasCoproductsOfShape_of_opposite
-/
theorem hasFiniteCoproducts_of_opposite [HasFiniteProducts Cᵒᵖ] : HasFiniteCoproducts C :=
  { out := fun _ => hasCoproductsOfShape_of_opposite _ }

/--
Instance `hasFiniteProducts_opposite` / 实例 `hasFiniteProducts_opposite`

English:
instance hasFiniteProducts_opposite
  signature: [HasFiniteCoproducts C]
  body: inferInstance

中文:
实例 hasFiniteProducts_opposite
  签名: [有FiniteCoproducts C]
  定义体: inferInstance
-/
instance hasFiniteProducts_opposite [HasFiniteCoproducts C] : HasFiniteProducts Cᵒᵖ where
  out _ := inferInstance

/--
theorem `hasFiniteProducts_of_opposite` / 定理 `hasFiniteProducts_of_opposite`

English:
theorem hasFiniteProducts_of_opposite
  given: [HasFiniteCoproducts Cᵒᵖ]
  statement: HasFiniteProducts C
  proof: { out := fun _ => hasProductsOfShape_of_opposite _ }

中文:
定理 hasFiniteProducts_of_opposite
  条件: [有FiniteCoproducts Cᵒᵖ]
  结论: 有FiniteProducts C
  证明: { out := fun _ => hasProductsOfShape_of_opposite _ }

Depends on / 依赖: hasProductsOfShape_of_opposite
-/
theorem hasFiniteProducts_of_opposite [HasFiniteCoproducts Cᵒᵖ] : HasFiniteProducts C :=
  { out := fun _ => hasProductsOfShape_of_opposite _ }

section OppositeCoproducts

variable {α : Type*} {Z : α -> C}

section
variable [HasCoproduct Z]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimit (Discrete.functor Z).op
  body: hasLimit_op_of_hasColimit (Discrete.functor Z)

中文:
实例 :
  签名: 有极限 (离散.functor Z).op
  定义体: hasLimit_op_of_hasColimit (Discrete.functor Z)

Depends on / 依赖: Discrete, Discrete.functor, functor, hasLimit_op_of_hasColimit
-/
instance : HasLimit (Discrete.functor Z).op := hasLimit_op_of_hasColimit (Discrete.functor Z)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimit ((Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op)
  body: hasLimit_equivalence_comp (Discrete.opposite α).symm

中文:
实例 :
  签名: 有极限 ((离散.opposite α).inverse ⋙ (离散.functor Z).op)
  定义体: hasLimit_equivalence_comp (Discrete.opposite α).symm

Depends on / 依赖: Discrete, Discrete.opposite, hasLimit_equivalence_comp, opposite
-/
instance : HasLimit ((Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op) :=
  hasLimit_equivalence_comp (Discrete.opposite α).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasProduct (op <| Z ·)
  body: hasLimit_of_iso
  ((Discrete.natIsoFunctor ≪≫ Discrete.natIso (fun _ => by rfl)) :
    (Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op ≅
    Discrete.functor (op <| Z ·))

中文:
实例 :
  签名: HasProduct (op <| Z ·)
  定义体: hasLimit_of_iso
  ((Discrete.natIsoFunctor ≪≫ Discrete.natIso (fun _ => by rfl)) :
    (Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op ≅
    Discrete.functor (op <| Z ·))

Depends on / 依赖: hasLimit_of_iso
-/
instance : HasProduct (op <| Z ·) := hasLimit_of_iso
  ((Discrete.natIsoFunctor ≪≫ Discrete.natIso (fun _ => by rfl)) :
    (Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op ≅
    Discrete.functor (op <| Z ·))

/-- A `Cofan` gives a `Fan` in the opposite category. -/
@[simp, implicit_reducible]
/--
Definition of `Cofan.op` / `Cofan.op` 的定义

English:
definition Cofan.op
  signature: (c : Cofan Z)
  body: Fan.mk _ (fun a => (c.inj a).op)

中文:
定义 Cofan.op
  签名: (c : Cofan Z)
  定义体: Fan.mk _ (fun a => (c.inj a).op)

Depends on / 依赖: Fan.mk, c.inj
-/
def Cofan.op (c : Cofan Z) : Fan (op <| Z ·) := Fan.mk _ (fun a => (c.inj a).op)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- noncomputability is just for performance (compilation takes a while)
/--
Definition of `Cofan.IsColimit.op` / `Cofan.IsColimit.op` 的定义

English:
definition Cofan.IsColimit.op
  signature: {c : Cofan Z} (hc : IsColimit c)
  body: by
  let e : Discrete.functor (Opposite.op <| Z ·) ≅ (Discrete.opposite α).inverse ⋙
    (Discrete.functor Z).op := Discrete.natIso (fun _ => Iso.refl _)
  refine IsLimit.ofIsoLimit ((IsLimit.postcomposeInvEquiv e _).2
    (IsLimit.whiskerEquivalence hc.op (Discrete.opposite α).symm))
    (Cone.ext (Iso.refl _) (fun ⟨a⟩ => ?_))
  simp [e, Cofan.inj]

中文:
定义 Cofan.是余极限.op
  签名: {c : Cofan Z} (hc : 是余极限 c)
  定义体: by
  let e : Discrete.functor (Opposite.op <| Z ·) ≅ (Discrete.opposite α).inverse ⋙
    (Discrete.functor Z).op := Discrete.natIso (fun _ => Iso.refl _)
  refine IsLimit.ofIsoLimit ((IsLimit.postcomposeInvEquiv e _).2
    (IsLimit.whiskerEquivalence hc.op (Discrete.opposite α).symm))
    (Cone.ext (Iso.refl _) (fun ⟨a⟩ => ?_))
  simp [e, Cofan.inj]

Depends on / 依赖: Cofan.inj, Cone.ext, Discrete, Discrete.functor, Discrete.natIso, Discrete.opposite, IsLimit, IsLimit.ofIsoLimit, IsLimit.postcomposeInvEquiv, IsLimit.whiskerEquivalence, Iso.refl, Opposite, Opposite.op, functor, hc.op, inverse, natIso, ofIsoLimit, opposite, postcomposeInvEquiv
-/
noncomputable def Cofan.IsColimit.op {c : Cofan Z} (hc : IsColimit c) : IsLimit c.op := by
  let e : Discrete.functor (Opposite.op <| Z ·) ≅ (Discrete.opposite α).inverse ⋙
    (Discrete.functor Z).op := Discrete.natIso (fun _ => Iso.refl _)
  refine IsLimit.ofIsoLimit ((IsLimit.postcomposeInvEquiv e _).2
    (IsLimit.whiskerEquivalence hc.op (Discrete.opposite α).symm))
    (Cone.ext (Iso.refl _) (fun ⟨a⟩ => ?_))
  simp [e, Cofan.inj]

/--
Definition of `opCoproductIsoProduct'` / `opCoproductIsoProduct'` 的定义

English:
definition opCoproductIsoProduct'
  signature: {c : Cofan Z} {f : Fan (op <| Z ·)}
  body: IsLimit.conePointUniqueUpToIso (Cofan.IsColimit.op hc) hf

中文:
定义 opCoproductIsoProduct'
  签名: {c : Cofan Z} {f : Fan (op <| Z ·)}
  定义体: IsLimit.conePointUniqueUpToIso (Cofan.IsColimit.op hc) hf

Depends on / 依赖: Cofan.IsColimit.op, IsColimit, IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso
-/
def opCoproductIsoProduct' {c : Cofan Z} {f : Fan (op <| Z ·)}
    (hc : IsColimit c) (hf : IsLimit f) : op c.pt ≅ f.pt :=
  IsLimit.conePointUniqueUpToIso (Cofan.IsColimit.op hc) hf

variable (Z) in
/--
Definition of `opCoproductIsoProduct` / `opCoproductIsoProduct` 的定义

English:
definition opCoproductIsoProduct
  signature: :
  body: opCoproductIsoProduct' (coproductIsCoproduct Z) (productIsProduct (op <| Z ·))

中文:
定义 opCoproductIsoProduct
  签名: :
  定义体: opCoproductIsoProduct' (coproductIsCoproduct Z) (productIsProduct (op <| Z ·))

Depends on / 依赖: coproductIsCoproduct, opCoproductIsoProduct, productIsProduct
-/
def opCoproductIsoProduct :
    op (∐ Z) ≅ ∏ᶜ (op <| Z ·) :=
  opCoproductIsoProduct' (coproductIsCoproduct Z) (productIsProduct (op <| Z ·))

end

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `opCoproductIsoProduct'_hom_comp_proj` / 引理 `opCoproductIsoProduct'_hom_comp_proj`

English:
lemma opCoproductIsoProduct'_hom_comp_proj
  statement: {c : Cofan Z} {f : Fan (op <| Z ·)}
  proof: by
  simp [opCoproductIsoProduct', Fan.proj]

@[reassoc (attr := simp)]

中文:
引理 opCoproductIsoProduct'_hom_comp_proj
  结论: {c : Cofan Z} {f : Fan (op <| Z ·)}
  证明: by
  simp [opCoproductIsoProduct', Fan.proj]

@[reassoc (attr := simp)]
-/
lemma opCoproductIsoProduct'_hom_comp_proj {c : Cofan Z} {f : Fan (op <| Z ·)}
    (hc : IsColimit c) (hf : IsLimit f) (i : α) :
    (opCoproductIsoProduct' hc hf).hom ≫ f.proj i = (c.inj i).op := by
  simp [opCoproductIsoProduct', Fan.proj]

@[reassoc (attr := simp)]
/--
lemma `opCoproductIsoProduct_hom_comp_π` / 引理 `opCoproductIsoProduct_hom_comp_π`

English:
lemma opCoproductIsoProduct_hom_comp_π
  given: [HasCoproduct Z] (i : α)
  proof: Limits.opCoproductIsoProduct'_hom_comp_proj ..

中文:
引理 opCoproductIsoProduct_hom_comp_π
  条件: [HasCoproduct Z] (i : α)
  证明: Limits.opCoproductIsoProduct'_hom_comp_proj ..

Depends on / 依赖: Limits, Limits.opCoproductIsoProduct, _hom_comp_proj, opCoproductIsoProduct
-/
lemma opCoproductIsoProduct_hom_comp_π [HasCoproduct Z] (i : α) :
    (opCoproductIsoProduct Z).hom ≫ Pi.π _ i = (Sigma.ι _ i).op :=
  Limits.opCoproductIsoProduct'_hom_comp_proj ..

/--
theorem `opCoproductIsoProduct'_inv_comp_inj` / 定理 `opCoproductIsoProduct'_inv_comp_inj`

English:
theorem opCoproductIsoProduct'_inv_comp_inj
  statement: {c : Cofan Z} {f : Fan (op <| Z ·)}
  proof: IsLimit.conePointUniqueUpToIso_inv_comp (Cofan.IsColimit.op hc) hf ⟨b⟩

中文:
定理 opCoproductIsoProduct'_inv_comp_inj
  结论: {c : Cofan Z} {f : Fan (op <| Z ·)}
  证明: IsLimit.conePointUniqueUpToIso_inv_comp (Cofan.IsColimit.op hc) hf ⟨b⟩
-/
theorem opCoproductIsoProduct'_inv_comp_inj {c : Cofan Z} {f : Fan (op <| Z ·)}
    (hc : IsColimit c) (hf : IsLimit f) (b : α) :
    (opCoproductIsoProduct' hc hf).inv ≫ (c.inj b).op = f.proj b :=
  IsLimit.conePointUniqueUpToIso_inv_comp (Cofan.IsColimit.op hc) hf ⟨b⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `opCoproductIsoProduct'_comp_self` / 定理 `opCoproductIsoProduct'_comp_self`

English:
theorem opCoproductIsoProduct'_comp_self
  statement: {c c' : Cofan Z} {f : Fan (op <| Z ·)}
  proof: by
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

中文:
定理 opCoproductIsoProduct'_comp_self
  结论: {c c' : Cofan Z} {f : Fan (op <| Z ·)}
  证明: by
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
/--
theorem `opCoproductIsoProduct_inv_comp_ι` / 定理 `opCoproductIsoProduct_inv_comp_ι`

English:
theorem opCoproductIsoProduct_inv_comp_ι
  given: [HasCoproduct Z] (b : α)
  proof: opCoproductIsoProduct'_inv_comp_inj _ _ b

中文:
定理 opCoproductIsoProduct_inv_comp_ι
  条件: [HasCoproduct Z] (b : α)
  证明: opCoproductIsoProduct'_inv_comp_inj _ _ b

Depends on / 依赖: _inv_comp_inj, opCoproductIsoProduct
-/
theorem opCoproductIsoProduct_inv_comp_ι [HasCoproduct Z] (b : α) :
    (opCoproductIsoProduct Z).inv ≫ (Sigma.ι Z b).op = Pi.π (op <| Z ·) b :=
  opCoproductIsoProduct'_inv_comp_inj _ _ b

set_option backward.isDefEq.respectTransparency false in
/--
theorem `desc_op_comp_opCoproductIsoProduct'_hom` / 定理 `desc_op_comp_opCoproductIsoProduct'_hom`

English:
theorem desc_op_comp_opCoproductIsoProduct'_hom
  statement: {c : Cofan Z} {f : Fan (op <| Z ·)}
  proof: by
  refine (Iso.eq_comp_inv _).mp (Quiver.Hom.unop_inj (hc.hom_ext (fun ⟨j⟩ => Quiver.Hom.op_inj ?_)))
  simp only [unop_op, Discrete.functor_obj, Quiver.Hom.unop_op, IsColimit.fac,
    Cofan.op, unop_comp, op_comp, op_unop, Quiver.Hom.op_unop, Category.assoc]
  erw [opCoproductIsoProduct'_inv_comp_inj, IsLimit.fac]
  rfl

中文:
定理 desc_op_comp_opCoproductIsoProduct'_hom
  结论: {c : Cofan Z} {f : Fan (op <| Z ·)}
  证明: by
  refine (Iso.eq_comp_inv _).mp (Quiver.Hom.unop_inj (hc.hom_ext (fun ⟨j⟩ => Quiver.Hom.op_inj ?_)))
  simp only [unop_op, Discrete.functor_obj, Quiver.Hom.unop_op, IsColimit.fac,
    Cofan.op, unop_comp, op_comp, op_unop, Quiver.Hom.op_unop, Category.assoc]
  erw [opCoproductIsoProduct'_inv_comp_inj, IsLimit.fac]
  rfl

Depends on / 依赖: Category, Category.assoc, Cofan.op, Discrete, Discrete.functor_obj, IsColimit, IsColimit.fac, IsLimit, IsLimit.fac, Iso.eq_comp_inv, Quiver, Quiver.Hom.op_inj, Quiver.Hom.op_unop, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, _inv_comp_inj, eq_comp_inv, functor_obj, hc.hom_ext, hom_ext
-/
theorem desc_op_comp_opCoproductIsoProduct'_hom {c : Cofan Z} {f : Fan (op <| Z ·)}
    (hc : IsColimit c) (hf : IsLimit f) (c' : Cofan Z) :
    (hc.desc c').op ≫ (opCoproductIsoProduct' hc hf).hom = hf.lift c'.op := by
  refine (Iso.eq_comp_inv _).mp (Quiver.Hom.unop_inj (hc.hom_ext (fun ⟨j⟩ => Quiver.Hom.op_inj ?_)))
  simp only [unop_op, Discrete.functor_obj, Quiver.Hom.unop_op, IsColimit.fac,
    Cofan.op, unop_comp, op_comp, op_unop, Quiver.Hom.op_unop, Category.assoc]
  erw [opCoproductIsoProduct'_inv_comp_inj, IsLimit.fac]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `desc_op_comp_opCoproductIsoProduct_hom` / 定理 `desc_op_comp_opCoproductIsoProduct_hom`

English:
theorem desc_op_comp_opCoproductIsoProduct_hom
  given: [HasCoproduct Z] {X : C} (π : (a : α) -> Z a ⟶ X)
  proof: by
  convert!
    desc_op_comp_opCoproductIsoProduct'_hom (coproductIsCoproduct Z) (productIsProduct (op <| Z ·))
      (Cofan.mk _ π)
  · simp [Sigma.desc, coproductIsCoproduct]
  · simp [productIsProduct]

中文:
定理 desc_op_comp_opCoproductIsoProduct_hom
  条件: [HasCoproduct Z] {X : C} (π : (a : α) -> Z a ⟶ X)
  证明: by
  convert!
    desc_op_comp_opCoproductIsoProduct'_hom (coproductIsCoproduct Z) (productIsProduct (op <| Z ·))
      (Cofan.mk _ π)
  · simp [Sigma.desc, coproductIsCoproduct]
  · simp [productIsProduct]

Depends on / 依赖: Cofan.mk, Sigma.desc, _hom, convert, coproductIsCoproduct, desc_op_comp_opCoproductIsoProduct, productIsProduct
-/
theorem desc_op_comp_opCoproductIsoProduct_hom [HasCoproduct Z] {X : C} (π : (a : α) -> Z a ⟶ X) :
    (Sigma.desc π).op ≫ (opCoproductIsoProduct Z).hom = Pi.lift (fun a => (π a).op) := by
  convert!
    desc_op_comp_opCoproductIsoProduct'_hom (coproductIsCoproduct Z) (productIsProduct (op <| Z ·))
      (Cofan.mk _ π)
  · simp [Sigma.desc, coproductIsCoproduct]
  · simp [productIsProduct]

end OppositeCoproducts

section OppositeProducts

variable {α : Type*} {Z : α -> C}

section
variable [HasProduct Z]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimit (Discrete.functor Z).op
  body: hasColimit_op_of_hasLimit (Discrete.functor Z)

中文:
实例 :
  签名: 有余极限 (离散.functor Z).op
  定义体: hasColimit_op_of_hasLimit (Discrete.functor Z)

Depends on / 依赖: Discrete, Discrete.functor, functor, hasColimit_op_of_hasLimit
-/
instance : HasColimit (Discrete.functor Z).op := hasColimit_op_of_hasLimit (Discrete.functor Z)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimit ((Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op)
  body: hasColimit_equivalence_comp (Discrete.opposite α).symm

中文:
实例 :
  签名: 有余极限 ((离散.opposite α).inverse ⋙ (离散.functor Z).op)
  定义体: hasColimit_equivalence_comp (Discrete.opposite α).symm

Depends on / 依赖: Discrete, Discrete.opposite, hasColimit_equivalence_comp, opposite
-/
instance : HasColimit ((Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op) :=
  hasColimit_equivalence_comp (Discrete.opposite α).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCoproduct (op <| Z ·)
  body: hasColimit_of_iso
  ((Discrete.natIsoFunctor ≪≫ Discrete.natIso (fun _ => by rfl)) :
    (Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op ≅
    Discrete.functor (op <| Z ·)).symm

中文:
实例 :
  签名: HasCoproduct (op <| Z ·)
  定义体: hasColimit_of_iso
  ((Discrete.natIsoFunctor ≪≫ Discrete.natIso (fun _ => by rfl)) :
    (Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op ≅
    Discrete.functor (op <| Z ·)).symm

Depends on / 依赖: hasColimit_of_iso
-/
instance : HasCoproduct (op <| Z ·) := hasColimit_of_iso
  ((Discrete.natIsoFunctor ≪≫ Discrete.natIso (fun _ => by rfl)) :
    (Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op ≅
    Discrete.functor (op <| Z ·)).symm

/-- A `Fan` gives a `Cofan` in the opposite category. -/
@[simp]
/--
Definition of `Fan.op` / `Fan.op` 的定义

English:
definition Fan.op
  signature: (f : Fan Z)
  body: Cofan.mk _ (fun a => (f.proj a).op)

中文:
定义 Fan.op
  签名: (f : Fan Z)
  定义体: Cofan.mk _ (fun a => (f.proj a).op)

Depends on / 依赖: Cofan.mk, f.proj
-/
def Fan.op (f : Fan Z) : Cofan (op <| Z ·) := Cofan.mk _ (fun a => (f.proj a).op)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- noncomputability is just for performance (compilation takes a while)
/--
Definition of `Fan.IsLimit.op` / `Fan.IsLimit.op` 的定义

English:
definition Fan.IsLimit.op
  signature: {f : Fan Z} (hf : IsLimit f)
  body: by
  let e : Discrete.functor (Opposite.op <| Z ·) ≅ (Discrete.opposite α).inverse ⋙
    (Discrete.functor Z).op := Discrete.natIso (fun _ => Iso.refl _)
  refine IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv e _).2
    (IsColimit.whiskerEquivalence hf.op (Discrete.opposite α).symm))
    (Cocone.ext (Iso.refl _) (fun ⟨a⟩ => ?_))
  simp [e, Fan.proj]

中文:
定义 Fan.是极限.op
  签名: {f : Fan Z} (hf : 是极限 f)
  定义体: by
  let e : Discrete.functor (Opposite.op <| Z ·) ≅ (Discrete.opposite α).inverse ⋙
    (Discrete.functor Z).op := Discrete.natIso (fun _ => Iso.refl _)
  refine IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv e _).2
    (IsColimit.whiskerEquivalence hf.op (Discrete.opposite α).symm))
    (Cocone.ext (Iso.refl _) (fun ⟨a⟩ => ?_))
  simp [e, Fan.proj]

Depends on / 依赖: Cocone, Cocone.ext, Discrete, Discrete.functor, Discrete.natIso, Discrete.opposite, Fan.proj, IsColimit, IsColimit.ofIsoColimit, IsColimit.precomposeHomEquiv, IsColimit.whiskerEquivalence, Iso.refl, Opposite, Opposite.op, functor, hf.op, inverse, natIso, ofIsoColimit, opposite
-/
noncomputable def Fan.IsLimit.op {f : Fan Z} (hf : IsLimit f) : IsColimit f.op := by
  let e : Discrete.functor (Opposite.op <| Z ·) ≅ (Discrete.opposite α).inverse ⋙
    (Discrete.functor Z).op := Discrete.natIso (fun _ => Iso.refl _)
  refine IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv e _).2
    (IsColimit.whiskerEquivalence hf.op (Discrete.opposite α).symm))
    (Cocone.ext (Iso.refl _) (fun ⟨a⟩ => ?_))
  simp [e, Fan.proj]

/--
Definition of `opProductIsoCoproduct'` / `opProductIsoCoproduct'` 的定义

English:
definition opProductIsoCoproduct'
  signature: {f : Fan Z} {c : Cofan (op <| Z ·)}
  body: IsColimit.coconePointUniqueUpToIso (Fan.IsLimit.op hf) hc

中文:
定义 opProductIsoCoproduct'
  签名: {f : Fan Z} {c : Cofan (op <| Z ·)}
  定义体: IsColimit.coconePointUniqueUpToIso (Fan.IsLimit.op hf) hc

Depends on / 依赖: Fan.IsLimit.op, IsColimit, IsColimit.coconePointUniqueUpToIso, IsLimit, coconePointUniqueUpToIso
-/
def opProductIsoCoproduct' {f : Fan Z} {c : Cofan (op <| Z ·)}
    (hf : IsLimit f) (hc : IsColimit c) : op f.pt ≅ c.pt :=
  IsColimit.coconePointUniqueUpToIso (Fan.IsLimit.op hf) hc

variable (Z) in
/--
Definition of `opProductIsoCoproduct` / `opProductIsoCoproduct` 的定义

English:
definition opProductIsoCoproduct
  signature: :
  body: opProductIsoCoproduct' (productIsProduct Z) (coproductIsCoproduct (op <| Z ·))

中文:
定义 opProductIsoCoproduct
  签名: :
  定义体: opProductIsoCoproduct' (productIsProduct Z) (coproductIsCoproduct (op <| Z ·))

Depends on / 依赖: coproductIsCoproduct, opProductIsoCoproduct, productIsProduct
-/
def opProductIsoCoproduct :
    op (∏ᶜ Z) ≅ ∐ (op <| Z ·) :=
  opProductIsoCoproduct' (productIsProduct Z) (coproductIsCoproduct (op <| Z ·))

end

/--
theorem `proj_comp_opProductIsoCoproduct'_hom` / 定理 `proj_comp_opProductIsoCoproduct'_hom`

English:
theorem proj_comp_opProductIsoCoproduct'_hom
  statement: {f : Fan Z} {c : Cofan (op <| Z ·)}
  proof: IsColimit.comp_coconePointUniqueUpToIso_hom (Fan.IsLimit.op hf) hc ⟨b⟩

中文:
定理 proj_comp_opProductIsoCoproduct'_hom
  结论: {f : Fan Z} {c : Cofan (op <| Z ·)}
  证明: IsColimit.comp_coconePointUniqueUpToIso_hom (Fan.IsLimit.op hf) hc ⟨b⟩

Depends on / 依赖: Fan.IsLimit.op, IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, IsLimit, comp_coconePointUniqueUpToIso_hom
-/
theorem proj_comp_opProductIsoCoproduct'_hom {f : Fan Z} {c : Cofan (op <| Z ·)}
    (hf : IsLimit f) (hc : IsColimit c) (b : α) :
    (f.proj b).op ≫ (opProductIsoCoproduct' hf hc).hom = c.inj b :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (Fan.IsLimit.op hf) hc ⟨b⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `opProductIsoCoproduct'_comp_self` / 定理 `opProductIsoCoproduct'_comp_self`

English:
theorem opProductIsoCoproduct'_comp_self
  statement: {f f' : Fan Z} {c : Cofan (op <| Z ·)}
  proof: by
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

中文:
定理 opProductIsoCoproduct'_comp_self
  结论: {f f' : Fan Z} {c : Cofan (op <| Z ·)}
  证明: by
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
/--
theorem `π_comp_opProductIsoCoproduct_hom` / 定理 `π_comp_opProductIsoCoproduct_hom`

English:
theorem π_comp_opProductIsoCoproduct_hom
  given: [HasProduct Z] (b : α)
  proof: proj_comp_opProductIsoCoproduct'_hom _ _ b

中文:
定理 π_comp_opProductIsoCoproduct_hom
  条件: [HasProduct Z] (b : α)
  证明: proj_comp_opProductIsoCoproduct'_hom _ _ b

Depends on / 依赖: _hom, proj_comp_opProductIsoCoproduct
-/
theorem π_comp_opProductIsoCoproduct_hom [HasProduct Z] (b : α) :
    (Pi.π Z b).op ≫ (opProductIsoCoproduct Z).hom = Sigma.ι (op <| Z ·) b :=
  proj_comp_opProductIsoCoproduct'_hom _ _ b

set_option backward.isDefEq.respectTransparency false in
/--
theorem `opProductIsoCoproduct'_inv_comp_lift` / 定理 `opProductIsoCoproduct'_inv_comp_lift`

English:
theorem opProductIsoCoproduct'_inv_comp_lift
  statement: {f : Fan Z} {c : Cofan (op <| Z ·)}
  proof: by
  refine (Iso.inv_comp_eq _).mpr (Quiver.Hom.unop_inj (hf.hom_ext (fun ⟨j⟩ => Quiver.Hom.op_inj ?_)))
  simp only [Discrete.functor_obj, unop_op, Quiver.Hom.unop_op, IsLimit.fac, Fan.op, unop_comp,
    Category.assoc, op_comp, op_unop, Quiver.Hom.op_unop]
  erw [← Category.assoc, proj_comp_opProductIsoCoproduct'_hom, IsColimit.fac]
  rfl

中文:
定理 opProductIsoCoproduct'_inv_comp_lift
  结论: {f : Fan Z} {c : Cofan (op <| Z ·)}
  证明: by
  refine (Iso.inv_comp_eq _).mpr (Quiver.Hom.unop_inj (hf.hom_ext (fun ⟨j⟩ => Quiver.Hom.op_inj ?_)))
  simp only [Discrete.functor_obj, unop_op, Quiver.Hom.unop_op, IsLimit.fac, Fan.op, unop_comp,
    Category.assoc, op_comp, op_unop, Quiver.Hom.op_unop]
  erw [← Category.assoc, proj_comp_opProductIsoCoproduct'_hom, IsColimit.fac]
  rfl
-/
theorem opProductIsoCoproduct'_inv_comp_lift {f : Fan Z} {c : Cofan (op <| Z ·)}
    (hf : IsLimit f) (hc : IsColimit c) (f' : Fan Z) :
    (opProductIsoCoproduct' hf hc).inv ≫ (hf.lift f').op = hc.desc f'.op := by
  refine (Iso.inv_comp_eq _).mpr (Quiver.Hom.unop_inj (hf.hom_ext (fun ⟨j⟩ => Quiver.Hom.op_inj ?_)))
  simp only [Discrete.functor_obj, unop_op, Quiver.Hom.unop_op, IsLimit.fac, Fan.op, unop_comp,
    Category.assoc, op_comp, op_unop, Quiver.Hom.op_unop]
  erw [← Category.assoc, proj_comp_opProductIsoCoproduct'_hom, IsColimit.fac]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `opProductIsoCoproduct_inv_comp_lift` / 定理 `opProductIsoCoproduct_inv_comp_lift`

English:
theorem opProductIsoCoproduct_inv_comp_lift
  given: [HasProduct Z] {X : C} (π : (a : α) -> X ⟶ Z a)
  proof: by
  convert!
    opProductIsoCoproduct'_inv_comp_lift (productIsProduct Z) (coproductIsCoproduct (op <| Z ·))
      (Fan.mk _ π)
  · simp [Pi.lift, productIsProduct]
  · simp [coproductIsCoproduct]

中文:
定理 opProductIsoCoproduct_inv_comp_lift
  条件: [HasProduct Z] {X : C} (π : (a : α) -> X ⟶ Z a)
  证明: by
  convert!
    opProductIsoCoproduct'_inv_comp_lift (productIsProduct Z) (coproductIsCoproduct (op <| Z ·))
      (Fan.mk _ π)
  · simp [Pi.lift, productIsProduct]
  · simp [coproductIsCoproduct]

Depends on / 依赖: Fan.mk, Pi.lift, _inv_comp_lift, convert, coproductIsCoproduct, opProductIsoCoproduct, productIsProduct
-/
theorem opProductIsoCoproduct_inv_comp_lift [HasProduct Z] {X : C} (π : (a : α) -> X ⟶ Z a) :
    (opProductIsoCoproduct Z).inv ≫ (Pi.lift π).op = Sigma.desc (fun a => (π a).op) := by
  convert!
    opProductIsoCoproduct'_inv_comp_lift (productIsProduct Z) (coproductIsCoproduct (op <| Z ·))
      (Fan.mk _ π)
  · simp [Pi.lift, productIsProduct]
  · simp [coproductIsCoproduct]

end OppositeProducts

section BinaryProducts

variable {A B : C} [HasBinaryProduct A B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasBinaryCoproduct (op A) (op B)
  body: by
  have : HasProduct fun x => (WalkingPair.casesOn x A B : C) := ‹_›
  change HasCoproduct _
  convert! (inferInstance : HasCoproduct fun x => op (WalkingPair.casesOn x A B : C)) with x
  cases x <;> rfl

中文:
实例 :
  签名: HasBinaryCoproduct (op A) (op B)
  定义体: by
  have : HasProduct fun x => (WalkingPair.casesOn x A B : C) := ‹_›
  change HasCoproduct _
  convert! (inferInstance : HasCoproduct fun x => op (WalkingPair.casesOn x A B : C)) with x
  cases x <;> rfl

Depends on / 依赖: HasCoproduct, HasProduct, WalkingPair, WalkingPair.casesOn, casesOn, convert
-/
instance : HasBinaryCoproduct (op A) (op B) := by
  have : HasProduct fun x => (WalkingPair.casesOn x A B : C) := ‹_›
  change HasCoproduct _
  convert! (inferInstance : HasCoproduct fun x => op (WalkingPair.casesOn x A B : C)) with x
  cases x <;> rfl

set_option backward.isDefEq.respectTransparency false in
variable (A B) in
/--
Definition of `opProdIsoCoprod` / `opProdIsoCoprod` 的定义

English:
definition opProdIsoCoprod
  signature: : op (A ⨯ B) ≅ (op A ⨿ op B) where
  body: (prod.lift coprod.inl.unop coprod.inr.unop).op
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

中文:
定义 opProdIsoCoprod
  签名: : op (A ⨯ B) ≅ (op A ⨿ op B) where
  定义体: (prod.lift coprod.inl.unop coprod.inr.unop).op
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

Depends on / 依赖: coprod, coprod.inl.unop, coprod.inr.unop, prod.lift
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
/--
lemma `fst_opProdIsoCoprod_hom` / 引理 `fst_opProdIsoCoprod_hom`

English:
lemma fst_opProdIsoCoprod_hom
  statement: prod.fst.op ≫ (opProdIsoCoprod A B).hom = coprod.inl
  proof: by
  rw [opProdIsoCoprod]; rw [← op_comp]; rw [prod.lift_fst]; rw [Quiver.Hom.op_unop]

中文:
引理 fst_opProdIsoCoprod_hom
  结论: 乘积.fst.op ≫ (opProdIsoCoprod A B).hom = coprod.inl
  证明: by
  rw [opProdIsoCoprod]; rw [← op_comp]; rw [prod.lift_fst]; rw [Quiver.Hom.op_unop]

Depends on / 依赖: Quiver, Quiver.Hom.op_unop, lift_fst, opProdIsoCoprod, op_comp, op_unop, prod.lift_fst
-/
lemma fst_opProdIsoCoprod_hom : prod.fst.op ≫ (opProdIsoCoprod A B).hom = coprod.inl := by
  rw [opProdIsoCoprod]; rw [← op_comp]; rw [prod.lift_fst]; rw [Quiver.Hom.op_unop]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `snd_opProdIsoCoprod_hom` / 引理 `snd_opProdIsoCoprod_hom`

English:
lemma snd_opProdIsoCoprod_hom
  statement: prod.snd.op ≫ (opProdIsoCoprod A B).hom = coprod.inr
  proof: by
  rw [opProdIsoCoprod]; rw [← op_comp]; rw [prod.lift_snd]; rw [Quiver.Hom.op_unop]

@[reassoc (attr := simp)]

中文:
引理 snd_opProdIsoCoprod_hom
  结论: 乘积.snd.op ≫ (opProdIsoCoprod A B).hom = coprod.inr
  证明: by
  rw [opProdIsoCoprod]; rw [← op_comp]; rw [prod.lift_snd]; rw [Quiver.Hom.op_unop]

@[reassoc (attr := simp)]

Depends on / 依赖: Quiver, Quiver.Hom.op_unop, lift_snd, opProdIsoCoprod, op_comp, op_unop, prod.lift_snd
-/
lemma snd_opProdIsoCoprod_hom : prod.snd.op ≫ (opProdIsoCoprod A B).hom = coprod.inr := by
  rw [opProdIsoCoprod]; rw [← op_comp]; rw [prod.lift_snd]; rw [Quiver.Hom.op_unop]

@[reassoc (attr := simp)]
/--
lemma `inl_opProdIsoCoprod_inv` / 引理 `inl_opProdIsoCoprod_inv`

English:
lemma inl_opProdIsoCoprod_inv
  statement: coprod.inl ≫ (opProdIsoCoprod A B).inv = prod.fst.op
  proof: by
  rw [Iso.comp_inv_eq]; rw [fst_opProdIsoCoprod_hom]

@[reassoc (attr := simp)]

中文:
引理 inl_opProdIsoCoprod_inv
  结论: coprod.inl ≫ (opProdIsoCoprod A B).inv = 乘积.fst.op
  证明: by
  rw [Iso.comp_inv_eq]; rw [fst_opProdIsoCoprod_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq, fst_opProdIsoCoprod_hom
-/
lemma inl_opProdIsoCoprod_inv : coprod.inl ≫ (opProdIsoCoprod A B).inv = prod.fst.op := by
  rw [Iso.comp_inv_eq]; rw [fst_opProdIsoCoprod_hom]

@[reassoc (attr := simp)]
/--
lemma `inr_opProdIsoCoprod_inv` / 引理 `inr_opProdIsoCoprod_inv`

English:
lemma inr_opProdIsoCoprod_inv
  statement: coprod.inr ≫ (opProdIsoCoprod A B).inv = prod.snd.op
  proof: by
  rw [Iso.comp_inv_eq]; rw [snd_opProdIsoCoprod_hom]

中文:
引理 inr_opProdIsoCoprod_inv
  结论: coprod.inr ≫ (opProdIsoCoprod A B).inv = 乘积.snd.op
  证明: by
  rw [Iso.comp_inv_eq]; rw [snd_opProdIsoCoprod_hom]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq, snd_opProdIsoCoprod_hom
-/
lemma inr_opProdIsoCoprod_inv : coprod.inr ≫ (opProdIsoCoprod A B).inv = prod.snd.op := by
  rw [Iso.comp_inv_eq]; rw [snd_opProdIsoCoprod_hom]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `opProdIsoCoprod_hom_fst` / 引理 `opProdIsoCoprod_hom_fst`

English:
lemma opProdIsoCoprod_hom_fst
  statement: (opProdIsoCoprod A B).hom.unop ≫ prod.fst = coprod.inl.unop
  proof: by
  simp [opProdIsoCoprod]

中文:
引理 opProdIsoCoprod_hom_fst
  结论: (opProdIsoCoprod A B).hom.unop ≫ 乘积.fst = coprod.inl.unop
  证明: by
  simp [opProdIsoCoprod]

Depends on / 依赖: opProdIsoCoprod
-/
lemma opProdIsoCoprod_hom_fst : (opProdIsoCoprod A B).hom.unop ≫ prod.fst = coprod.inl.unop := by
  simp [opProdIsoCoprod]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `opProdIsoCoprod_hom_snd` / 引理 `opProdIsoCoprod_hom_snd`

English:
lemma opProdIsoCoprod_hom_snd
  statement: (opProdIsoCoprod A B).hom.unop ≫ prod.snd = coprod.inr.unop
  proof: by
  simp [opProdIsoCoprod]

@[reassoc (attr := simp)]

中文:
引理 opProdIsoCoprod_hom_snd
  结论: (opProdIsoCoprod A B).hom.unop ≫ 乘积.snd = coprod.inr.unop
  证明: by
  simp [opProdIsoCoprod]

@[reassoc (attr := simp)]

Depends on / 依赖: opProdIsoCoprod
-/
lemma opProdIsoCoprod_hom_snd : (opProdIsoCoprod A B).hom.unop ≫ prod.snd = coprod.inr.unop := by
  simp [opProdIsoCoprod]

@[reassoc (attr := simp)]
/--
lemma `opProdIsoCoprod_inv_inl` / 引理 `opProdIsoCoprod_inv_inl`

English:
lemma opProdIsoCoprod_inv_inl
  statement: (opProdIsoCoprod A B).inv.unop ≫ coprod.inl.unop = prod.fst
  proof: by
  rw [← unop_comp]; rw [inl_opProdIsoCoprod_inv]; rw [Quiver.Hom.unop_op]

@[reassoc (attr := simp)]

中文:
引理 opProdIsoCoprod_inv_inl
  结论: (opProdIsoCoprod A B).inv.unop ≫ coprod.inl.unop = 乘积.fst
  证明: by
  rw [← unop_comp]; rw [inl_opProdIsoCoprod_inv]; rw [Quiver.Hom.unop_op]

@[reassoc (attr := simp)]

Depends on / 依赖: Quiver, Quiver.Hom.unop_op, inl_opProdIsoCoprod_inv, unop_comp, unop_op
-/
lemma opProdIsoCoprod_inv_inl : (opProdIsoCoprod A B).inv.unop ≫ coprod.inl.unop = prod.fst := by
  rw [← unop_comp]; rw [inl_opProdIsoCoprod_inv]; rw [Quiver.Hom.unop_op]

@[reassoc (attr := simp)]
/--
lemma `opProdIsoCoprod_inv_inr` / 引理 `opProdIsoCoprod_inv_inr`

English:
lemma opProdIsoCoprod_inv_inr
  statement: (opProdIsoCoprod A B).inv.unop ≫ coprod.inr.unop = prod.snd
  proof: by
  rw [← unop_comp]; rw [inr_opProdIsoCoprod_inv]; rw [Quiver.Hom.unop_op]

中文:
引理 opProdIsoCoprod_inv_inr
  结论: (opProdIsoCoprod A B).inv.unop ≫ coprod.inr.unop = 乘积.snd
  证明: by
  rw [← unop_comp]; rw [inr_opProdIsoCoprod_inv]; rw [Quiver.Hom.unop_op]

Depends on / 依赖: Quiver, Quiver.Hom.unop_op, inr_opProdIsoCoprod_inv, unop_comp, unop_op
-/
lemma opProdIsoCoprod_inv_inr : (opProdIsoCoprod A B).inv.unop ≫ coprod.inr.unop = prod.snd := by
  rw [← unop_comp]; rw [inr_opProdIsoCoprod_inv]; rw [Quiver.Hom.unop_op]

end BinaryProducts

end CategoryTheory.Limits
