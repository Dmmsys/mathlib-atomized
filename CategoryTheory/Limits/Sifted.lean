/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.Products.Associator
/-!
# Sifted categories

A category `C` is sifted if `C` is nonempty and the diagonal functor `C ⥤ C × C` is final.
Sifted categories can be characterized as those such that the colimit functor `(C ⥤ Type) ⥤ Type `
preserves finite products. We achieve this characterization in this file.

## Main results
- `isSifted_of_hasBinaryCoproducts_and_nonempty`: A nonempty category with binary coproducts is
  sifted.
- `IsSifted.colimPreservesFiniteProductsOfIsSifted`: The `Type`-valued colimit functor for sifted
  diagrams preserves finite products.
- `IsSifted.of_colimit_preservesFiniteProducts`: The converse: if the `Type`-valued colimit functor
  preserves finite products, the category is sifted.
- `IsSifted.of_final_functor_from_sifted`: A category admitting a final functor from a sifted
  category is itself sifted.

## References
- [nLab, *Sifted category*](https://ncatlab.org/nlab/show/sifted+category)
- [*Algebraic Theories*, Chapter 2.][Adamek_Rosicky_Vitale_2010]
-/

public section

universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory

open Limits CategoryTheory.Functor

section

variable (C : Type u) [Category.{v} C]

/-- A category `C` `IsSiftedOrEmpty` if the diagonal functor `C ⥤ C × C` is final. -/
/-
**CategoryTheory.IsSiftedOrEmpty** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：IsSiftedOrEmpty : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` `IsSiftedOrEmpty` if the diagonal functor `C ⥤ C × C` is final.
-/
abbrev IsSiftedOrEmpty : Prop := Final (diag C)

/-- A category `C` `IsSifted` if
1. the diagonal functor `C ⥤ C × C` is final.
2. there exists some object. -/
/-
**CategoryTheory.IsSifted** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` `IsSifted` if
1. the diagonal functor `C ⥤ C × C` is final.
2. there exists some object.
-/
class IsSifted : Prop extends IsSiftedOrEmpty C where
  [nonempty : Nonempty C]

/- This instance is scoped since
- it applies unconditionally (which can be a performance drain),
- infers a *very* generic typeclass,
- and does so from a *very* specialised class. -/
attribute [scoped instance] IsSifted.nonempty

namespace IsSifted

variable {C}

set_option backward.defeqAttrib.useBackward true in
/-- Being sifted is preserved by equivalences of categories -/
/-
**CategoryTheory.IsSifted.isSifted_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.IsSifted`。
形式化陈述：isSifted_of_equiv [IsSifted C] {D : Type u₁} [Category.{v₁} D] (e : D ≌ C)
 : IsSifted D
参数：e : D ≌ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Equivalence.fun_inv_map`：fun_inv_map (e : C ≌ D) (X Y : D
) (f : X ⟶ Y) : e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitI
nv.app Y
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Functor.final_iff_comp_equivalence`：final_iff_comp_equiva
lence [IsEquivalence G] : Final F ↔ Final (F ⋙ G)
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.Functor.final_iff_final_comp`：final_iff_final_comp [Final
 F] : Final G ↔ Final (F ⋙ G)
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.final_of_natIso`：final_of_natIso {F F' : C ⥤ D} [
Final F] (i : F ≅ F') : Final F' where out _
· 使用定理 `CategoryTheory.IsSifted.toFinal`：∀ {C : Type u} {inst : CategoryTheory.C
ategory.{v, u} C} [self : CategoryTheory.IsSifted C],   (CategoryTheory.Functor.
diag C).Final
· 使用定理 `CategoryTheory.IsSifted.nonempty`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C} [self : CategoryTheory.IsSifted C], Nonempty C

--- 原说明 ---
Being sifted is preserved by equivalences of categories
-/
lemma isSifted_of_equiv [IsSifted C] {D : Type u₁} [Category.{v₁} D] (e : D ≌ C) : IsSifted D :=
  letI : Final (diag D) := by
    let : D × D ≌ C × C := Equivalence.prod e e
    have sq : (e.inverse ⋙ diag D ⋙ this.functor ≅ diag C) :=
        NatIso.ofComponents (fun c ↦ by dsimp [this]
                                        exact Iso.prod (e.counitIso.app c) (e.counitIso.app c))
    apply_rules [final_iff_comp_equivalence _ this.functor |>.mpr,
      final_iff_final_comp e.inverse _ |>.mpr, final_of_natIso sq.symm]
  letI : _root_.Nonempty D := ⟨e.inverse.obj (_root_.Nonempty.some IsSifted.nonempty)⟩
  ⟨⟩

/-- In particular a category is sifted iff and only if it is so when viewed as a small category -/
/-
**CategoryTheory.IsSifted.isSifted_iff_asSmallIsSifted** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.IsSifted`。
形式化陈述：isSifted_iff_asSmallIsSifted : IsSifted C ↔ IsSifted (AsSmall.{w} C) where
 mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsSifted.isSifted_of_equiv`：isSifted_of_equiv [IsSifted C
] {D : Type u₁} [Category.{v₁} D] (e : D ≌ C) : IsSifted D

--- 原说明 ---
In particular a category is sifted iff and only if it is so when viewed as a sma
ll category
-/
lemma isSifted_iff_asSmallIsSifted : IsSifted C ↔ IsSifted (AsSmall.{w} C) where
  mp _ := isSifted_of_equiv AsSmall.equiv.symm
  mpr _ := isSifted_of_equiv AsSmall.equiv

/-- A sifted category is connected. -/
/-
**CategoryTheory.IsSifted.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsSifted`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sifted category is connected.
-/
instance [IsSifted C] : IsConnected C :=
  isConnected_of_zigzag
    (by intro c₁ c₂
        have X : StructuredArrow (c₁, c₂) (diag C) :=
          letI S : Final (diag C) := by infer_instance
          Nonempty.some (S.out (c₁, c₂)).is_nonempty
        use [X.right, c₂]
        constructor
        · constructor
          · exact Zag.of_hom X.hom.fst
          · simpa using Zag.of_inv X.hom.snd
        · rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A category with binary coproducts is sifted or empty. -/
/-
**CategoryTheory.IsSifted.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsSifted`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category with binary coproducts is sifted or empty.
-/
instance [HasBinaryCoproducts C] : IsSiftedOrEmpty C := by
    constructor
    rintro ⟨c₁, c₂⟩
    have : _root_.Nonempty <| StructuredArrow (c₁, c₂) (diag C) :=
      ⟨.mk ((coprod.inl : c₁ ⟶ c₁ ⨿ c₂), (coprod.inr : c₂ ⟶ c₁ ⨿ c₂))⟩
    apply isConnected_of_zigzag
    rintro ⟨_, c, f⟩ ⟨_, c', g⟩
    dsimp only [const_obj_obj, diag_obj] at f g
    use [.mk ((coprod.inl : c₁ ⟶ c₁ ⨿ c₂), (coprod.inr : c₂ ⟶ c₁ ⨿ c₂)), .mk (g.fst, g.snd)]
    simp only [colimit.cocone_x, diag_obj, Prod.mk.eta, List.isChain_cons_cons,
      List.isChain_singleton, and_true, ne_eq, reduceCtorEq, not_false_eq_true,
      List.getLast_cons, List.cons_ne_self, List.getLast_singleton]
    exact ⟨⟨Zag.of_inv <| StructuredArrow.homMk <| coprod.desc f.fst f.snd,
      Zag.of_hom <| StructuredArrow.homMk <| coprod.desc g.fst g.snd⟩, rfl⟩

/-- A nonempty category with binary coproducts is sifted. -/
/-
**CategoryTheory.IsSifted.isSifted_of_hasBinaryCoproducts_and_nonempty** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.IsSifted`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [Nonempty C] [Cat
egoryTheory.Limits.HasBinaryCoproducts C],   CategoryTheory.IsSifted C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSifted.instIsSiftedOrEmptyOfHasBinaryCoproducts`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasBin
aryCoproducts C],   CategoryTheory.IsSiftedOrEmpty C

--- 原说明 ---
A nonempty category with binary coproducts is sifted.
-/
instance isSifted_of_hasBinaryCoproducts_and_nonempty [_root_.Nonempty C] [HasBinaryCoproducts C] :
    IsSifted C where

section Prod

variable {D : Type u₁} [Category.{v₁} D]

/-
**CategoryTheory.IsSifted.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsSifted`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsSiftedOrEmpty C] [IsSiftedOrEmpty D] :
    IsSiftedOrEmpty (C × D) :=
  let e : (C × C) × (D × D) ≌ (C × D) × (C × D) := prod.prodμ ..
  final_of_natIso (Iso.refl ((Functor.diag C).prod (Functor.diag D) ⋙ e.functor))

/-- The product of two sifted categories is sifted. -/
/-
**CategoryTheory.IsSifted.prod_isSifted** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.IsSifted`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u₁} [in
st_1 : CategoryTheory.Category.{v₁, u₁} D]   [CategoryTheory.IsSifted C] [Catego
ryTheory.IsSifted D], CategoryTheory.IsSifted (C × D)
参数：C × D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSifted.instIsSiftedOrEmptyProd`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {D : Type u₁} [inst_1 : CategoryTheory.Categor
y.{v₁, u₁} D]   [CategoryTheory.IsSif…
· 使用定理 `CategoryTheory.IsSifted.toFinal`：∀ {C : Type u} {inst : CategoryTheory.C
ategory.{v, u} C} [self : CategoryTheory.IsSifted C],   (CategoryTheory.Functor.
diag C).Final
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
· 使用定理 `CategoryTheory.IsSifted.nonempty`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C} [self : CategoryTheory.IsSifted C], Nonempty C

--- 原说明 ---
The product of two sifted categories is sifted.
-/
instance prod_isSifted [IsSifted C] [IsSifted D] : IsSifted (C × D) where

end Prod

end IsSifted

end

section

variable {C : Type u} [Category.{v} C] [IsSiftedOrEmpty C] {D : Type u₁} [Category.{v₁} D]
  {D' : Type u₂} [Category.{v₂} D'] (F : C ⥤ D) (G : C ⥤ D')

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Final] [G.Final] : (F.prod' G).Final :=
  show (diag C ⋙ F.prod G).Final from final_comp _ _

end

noncomputable section SmallCategory

open MonoidalCategory CartesianMonoidalCategory

namespace IsSifted

variable {C : Type u} [SmallCategory C]

section

open scoped MonoidalCategory.ExternalProduct

variable (X Y : C ⥤ Type u)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Through the isomorphisms `PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂` and
`externalProductCompDiagIso`, the comparison map `colimit.pre (X ⊠ Y) (diag C)` identifies with the
product comparison map for the colimit functor. -/
/-
**CategoryTheory.IsSifted.factorization_prodComparison_colim** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.IsSifted`。
形式化陈述：factorization_prodComparison_colim : (HasColimit.isoOfNatIso ((externalPro
ductCompDiagIso _ _).app (X, Y)).symm).hom ≫ colimit.pre (X ⊠ Y) (diag C) ≫ (Pre
servesColimit₂.isoColimitUncurryWhiskeringLeft₂ X Y <| curriedTensor Type u).hom
 = CartesianMonoidalCategory.prodComparison colim X Y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.instHasColimitProd`：∀ {J : Type u_1} {K : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} K] {C : Type u_…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `CategoryTheory.Limits.instHasColimitProdObjFunctorUncurryWhiskeringLeft₂
OfPreservesColimit₂`：∀ {J₁ : Type u_1} {J₂ : Type u_2} [inst : CategoryTheory.Ca
tegory.{v_1, u_1} J₁]   [inst_1 : CategoryTheory.Category.{v_2, u_2} J₂] {C₁ : T
y…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.instIsLeftAdjointTensorLeft`：∀ (X : Type v₁), (CategoryTh
eory.MonoidalCategory.tensorLeft X).IsLeftAdjoint
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom_assoc`：∀ {J : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre_assoc`：∀ {J : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} K]   {C : Type u} [inst…
· 使用引理 `CategoryTheory.Limits.PreservesColimit₂.ι_comp_isoColimitUncurryWhiskeri
ngLeft₂_hom`：ι_comp_isoColimitUncurryWhiskeringLeft₂_hom (j : J₁ × J₂) : colimit
.ι (uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G)) j ≫ (Pr…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.comp_lift`：comp_lift {V W X Y :
 C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) : f ≫ lift g h = lift (f ≫ g) (f ≫ h)
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst_comp_snd_comp`：lift_fs
t_comp_snd_comp {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z) : lift (fst _ _ ≫ g) (snd
 _ _ ≫ g') = g otimesₘ g'

--- 原说明 ---
Through the isomorphisms `PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂` an
d
`externalProductCompDiagIso`, the comparison map `colimit.pre (X ⊠ Y) (diag C)` 
identifies with the
product comparison map for the colimit functor.
-/
lemma factorization_prodComparison_colim :
    (HasColimit.isoOfNatIso ((externalProductCompDiagIso _ _).app (X, Y)).symm).hom ≫
      colimit.pre (X ⊠ Y) (diag C) ≫
        (PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂ X Y <|
          curriedTensor <| Type u).hom =
    CartesianMonoidalCategory.prodComparison colim X Y := by
  apply colimit.hom_ext
  intro j
  dsimp [externalProductBifunctor, CartesianMonoidalCategory.prodComparison,
    externalProductBifunctorCurried, externalProduct]
  cat_disch

variable [IsSifted C]

set_option backward.isDefEq.respectTransparency false in
/-- If `C` is sifted, the canonical product comparison map for the `colim` functor
`(C ⥤ Type) ⥤ Type` is an isomorphism. -/
/-
**CategoryTheory.IsSifted.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsSifted`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is sifted, the canonical product comparison map for the `colim` functor
`(C ⥤ Type) ⥤ Type` is an isomorphism.
-/
instance : IsIso (CartesianMonoidalCategory.prodComparison colim X Y) := by
  rw [← factorization_prodComparison_colim]
  infer_instance
/-
**CategoryTheory.IsSifted.colim_preservesLimits_pair_of_sSifted** 是 Mathlib 中的一个
实例，位于命名空间 `CategoryTheory.IsSifted`。
形式化陈述：colim_preservesLimits_pair_of_sSifted {X Y : C ⥤ Type u} : PreservesLimit 
(pair X Y) colim
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.preservesLimit_pair_of_isIso_pr
odComparison`：preservesLimit_pair_of_isIso_prodComparison (A B : C) [IsIso (prod
Comparison F A B)] : PreservesLimit (pair A B) F
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.IsSifted.instIsIsoObjFunctorTypeColimTensorObjProdCompari
son`：∀ {C : Type u} [inst : CategoryTheory.SmallCategory C] (X Y : CategoryTheor
y.Functor C (Type u))   [CategoryTheory.IsSifted C],   CategoryTh…
-/
instance colim_preservesLimits_pair_of_sSifted {X Y : C ⥤ Type u} :
    PreservesLimit (pair X Y) colim :=
  preservesLimit_pair_of_isIso_prodComparison _ _ _

/-- Sifted colimits commute with binary products -/
/-
**CategoryTheory.IsSifted.colim_preservesBinaryProducts_of_isSifted** 是 Mathlib 
中的一个实例，位于命名空间 `CategoryTheory.IsSifted`。
形式化陈述：colim_preservesBinaryProducts_of_isSifted : PreservesLimitsOfShape (Discre
te WalkingPair) (colim : (C ⥤ _) ⥤ Type u)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t

--- 原说明 ---
Sifted colimits commute with binary products
-/
instance colim_preservesBinaryProducts_of_isSifted :
    PreservesLimitsOfShape (Discrete WalkingPair) (colim : (C ⥤ _) ⥤ Type u) := by
  constructor
  intro F
  apply preservesLimit_of_iso_diagram colim (diagramIsoPair F).symm

/-- If `C` is sifted, the `colimit` functor `(C ⥤ Type) ⥤ Type` preserves terminal objects -/
/-
**CategoryTheory.IsSifted.colim_preservesTerminal_of_isSifted** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.IsSifted`。
形式化陈述：colim_preservesTerminal_of_isSifted : PreservesLimit (Functor.empty.{0} (C
 ⥤ Type u)) colim
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesTerminal_of_iso`：preservesTerminal_of_iso
 (f : G.obj (⊤_ C) ≅ ⊤_ D) : PreservesLimit (Functor.empty.{0} C) G
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.IsSifted.instIsConnected`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.IsSifted C], CategoryTheory.IsConnecte
d C
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `C` is sifted, the `colimit` functor `(C ⥤ Type) ⥤ Type` preserves terminal o
bjects
-/
instance colim_preservesTerminal_of_isSifted :
    PreservesLimit (Functor.empty.{0} (C ⥤ Type u)) colim := by
  apply preservesTerminal_of_iso
  symm
  apply (_ : ⊤_ (Type u) ≅ PUnit.{u + 1}).trans
  · apply_rules [(Types.colimitConstPUnitIsoPUnit C).symm.trans, HasColimit.isoOfNatIso,
      IsTerminal.uniqueUpToIso _ terminalIsTerminal, evaluationJointlyReflectsLimits]
    exact fun _ ↦ isLimitChangeEmptyCone _ Types.isTerminalPUnit _ <| Iso.refl _
  · exact Types.isTerminalEquivIsoPUnit (⊤_ (Type u)) |>.toFun terminalIsTerminal
/-
**CategoryTheory.IsSifted.colim_preservesLimitsOfShape_pempty_of_isSifted** 是 Ma
thlib 中的一个实例，位于命名空间 `CategoryTheory.IsSifted`。
形式化陈述：colim_preservesLimitsOfShape_pempty_of_isSifted : PreservesLimitsOfShape (
Discrete PEmpty.{1}) (colim : (C ⥤ _) ⥤ Type u)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_pempty_of_preservesTerminal
`：preservesLimitsOfShape_pempty_of_preservesTerminal [PreservesLimit (Functor.em
pty.{0} C) G] : PreservesLimitsOfShape (Discrete PEmpty.{1}) G…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance colim_preservesLimitsOfShape_pempty_of_isSifted :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (colim : (C ⥤ _) ⥤ Type u) :=
  preservesLimitsOfShape_pempty_of_preservesTerminal _

/-- If `C` is sifted, the `colim` functor `(C ⥤ Type) ⥤ Type` preserves finite products. -/
/-
**CategoryTheory.IsSifted.colim_preservesFiniteProducts_of_isSifted** 是 Mathlib 
中的一个实例，位于命名空间 `CategoryTheory.IsSifted`。
形式化陈述：colim_preservesFiniteProducts_of_isSifted : PreservesFiniteProducts (colim
 : (C ⥤ _) ⥤ Type u)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesFiniteProducts.of_preserves_binary_and_te
rminal`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [
inst_1 : CategoryTheory.Category.{v', u'} D]   (F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…

--- 原说明 ---
If `C` is sifted, the `colim` functor `(C ⥤ Type) ⥤ Type` preserves finite produ
cts.
-/
instance colim_preservesFiniteProducts_of_isSifted :
    PreservesFiniteProducts (colim : (C ⥤ _) ⥤ Type u) :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal colim

end

section

variable (C)

open Opposite in
open scoped MonoidalCategory.ExternalProduct in
/-- If the `colim` functor `(C ⥤ Type) ⥤ Type` preserves binary products, then `C` is sifted or
empty. -/
/-
**CategoryTheory.IsSifted.isSiftedOrEmpty_of_colim_preservesBinaryProducts** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.IsSifted`。
形式化陈述：isSiftedOrEmpty_of_colim_preservesBinaryProducts [PreservesLimitsOfShape (
Discrete WalkingPair) (colim : (C ⥤ Type u) ⥤ Type u)] : IsSiftedOrEmpty C
参数：Discrete WalkingPair；colim : (C ⥤ Type u) ⥤ Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Functor.final_of_colimit_comp_coyoneda_iso_pUnit`：final_o
f_colimit_comp_coyoneda_iso_pUnit (I : forall d, colimit (F ⋙ coyoneda.obj (op d
)) ≅ PUnit) : Final F
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If the `colim` functor `(C ⥤ Type) ⥤ Type` preserves binary products, then `C` i
s sifted or
empty.
-/
theorem isSiftedOrEmpty_of_colim_preservesBinaryProducts
    [PreservesLimitsOfShape (Discrete WalkingPair) (colim : (C ⥤ Type u) ⥤ Type u)] :
    IsSiftedOrEmpty C := by
  apply final_of_colimit_comp_coyoneda_iso_pUnit
  rintro ⟨c₁, c₂⟩
  calc colimit <| diag C ⋙ coyoneda.obj (op (c₁, c₂))
    _ ≅ colimit <| _ ⋙ (coyoneda.obj _) ⊠ (coyoneda.obj _) :=
      HasColimit.isoOfNatIso <| isoWhiskerLeft _ <| .refl _
    _ ≅ colimit (_ ⊗ _) := HasColimit.isoOfNatIso <| .refl _
    _ ≅ (colimit _) ⊗ (colimit _) := CartesianMonoidalCategory.prodComparisonIso colim _ _
    _ ≅ PUnit ⊗ PUnit :=
      (Coyoneda.colimitCoyonedaIso _) ⊗ᵢ (Coyoneda.colimitCoyonedaIso _)
    _ ≅ PUnit := λ_ _
/-
**CategoryTheory.IsSifted.isSiftedOrEmpty_of_colim_preservesFiniteProducts** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.IsSifted`。
形式化陈述：isSiftedOrEmpty_of_colim_preservesFiniteProducts [h : PreservesFiniteProdu
cts (colim : (C ⥤ Type u) ⥤ Type u)] : IsSiftedOrEmpty C
参数：colim : (C ⥤ Type u) ⥤ Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.IsSifted.isSiftedOrEmpty_of_colim_preservesBinaryProducts
`：isSiftedOrEmpty_of_colim_preservesBinaryProducts [PreservesLimitsOfShape (Disc
rete WalkingPair) (colim : (C ⥤ Type u) ⥤ Type u)] : IsSiftedO…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma isSiftedOrEmpty_of_colim_preservesFiniteProducts
    [h : PreservesFiniteProducts (colim : (C ⥤ Type u) ⥤ Type u)] :
    IsSiftedOrEmpty C :=
  isSiftedOrEmpty_of_colim_preservesBinaryProducts C
/-
**CategoryTheory.IsSifted.nonempty_of_colim_preservesLimitsOfShapeFinZero** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.IsSifted`。
形式化陈述：nonempty_of_colim_preservesLimitsOfShapeFinZero [PreservesLimitsOfShape (D
iscrete (Fin 0)) (colim : (C ⥤ Type u) ⥤ Type u)] : Nonempty C
参数：Discrete (Fin 0)；colim : (C ⥤ Type u) ⥤ Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.isConnected_iff_colimit_constPUnitFunctor_is
o_pUnit`：isConnected_iff_colimit_constPUnitFunctor_iso_pUnit [HasColimit (constP
UnitFunctor.{w} C)] : IsConnected C ↔ Nonempty (colimit (constPUnitFu…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_equiv`：preservesLimitsOf
Shape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Pres
ervesLimitsOfShape J F] : PreservesLimitsOf…
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J
-/
lemma nonempty_of_colim_preservesLimitsOfShapeFinZero
    [PreservesLimitsOfShape (Discrete (Fin 0)) (colim : (C ⥤ Type u) ⥤ Type u)] :
    Nonempty C := by
  suffices connected : IsConnected C by infer_instance
  rw [Types.isConnected_iff_colimit_constPUnitFunctor_iso_pUnit]
  constructor
  haveI : PreservesLimitsOfShape (Discrete PEmpty) (colim : (C ⥤ _) ⥤ Type u) :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence finZeroEquiv') _
  apply HasColimit.isoOfNatIso (_ : Types.constPUnitFunctor C ≅ (⊤_ (C ⥤ Type u))) |>.trans
  · apply PreservesTerminal.iso colim |>.trans
    exact Types.terminalIso
  · apply_rules [IsTerminal.uniqueUpToIso _ terminalIsTerminal, evaluationJointlyReflectsLimits]
    intro _
    exact isLimitChangeEmptyCone _ Types.isTerminalPUnit _ <| Iso.refl _

/-- If the `colim` functor `(C ⥤ Type) ⥤ Type` preserves finite products, then `C` is sifted. -/
/-
**CategoryTheory.IsSifted.of_colim_preservesFiniteProducts** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.IsSifted`。
形式化陈述：of_colim_preservesFiniteProducts [h : PreservesFiniteProducts (colim : (C 
⥤ Type u) ⥤ Type u)] : IsSifted C
参数：colim : (C ⥤ Type u) ⥤ Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `CategoryTheory.IsSifted.isSiftedOrEmpty_of_colim_preservesFiniteProducts
`：isSiftedOrEmpty_of_colim_preservesFiniteProducts [h : PreservesFiniteProducts 
(colim : (C ⥤ Type u) ⥤ Type u)] : IsSiftedOrEmpty C
· 使用引理 `CategoryTheory.IsSifted.nonempty_of_colim_preservesLimitsOfShapeFinZero`
：nonempty_of_colim_preservesLimitsOfShapeFinZero [PreservesLimitsOfShape (Discre
te (Fin 0)) (colim : (C ⥤ Type u) ⥤ Type u)] : Nonempty C
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If the `colim` functor `(C ⥤ Type) ⥤ Type` preserves finite products, then `C` i
s sifted.
-/
theorem of_colim_preservesFiniteProducts
    [h : PreservesFiniteProducts (colim : (C ⥤ Type u) ⥤ Type u)] :
    IsSifted C := by
  have := isSiftedOrEmpty_of_colim_preservesFiniteProducts C
  have := nonempty_of_colim_preservesLimitsOfShapeFinZero C
  constructor

variable {C}

/-- Auxiliary version of `IsSifted.of_final_functor_from_sifted` where everything is a
small category. -/
/-
**CategoryTheory.IsSifted.of_final_functor_from_sifted'** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.IsSifted`。
形式化陈述：of_final_functor_from_sifted' {D : Type u} [SmallCategory D] [IsSifted C] 
(F : C ⥤ D) [Final F] : IsSifted D
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_natIso`：preservesLimitsO
fShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] : Preser
vesLimitsOfShape J G where preservesLimit {K…
· 使用定理 `CategoryTheory.Limits.comp_preservesLimitsOfShape`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsSifted.of_colim_preservesFiniteProducts`：of_colim_prese
rvesFiniteProducts [h : PreservesFiniteProducts (colim : (C ⥤ Type u) ⥤ Type u)]
 : IsSifted C

--- 原说明 ---
Auxiliary version of `IsSifted.of_final_functor_from_sifted` where everything is
 a
small category.
-/
theorem of_final_functor_from_sifted'
    {D : Type u} [SmallCategory D] [IsSifted C] (F : C ⥤ D) [Final F] : IsSifted D := by
  have : PreservesFiniteProducts (colim : (D ⥤ Type u) ⥤ _) :=
    ⟨fun n ↦ preservesLimitsOfShape_of_natIso (Final.colimIso F)⟩
  exact of_colim_preservesFiniteProducts D

end

end IsSifted

end SmallCategory

variable {C : Type u} [Category.{v} C]

/-- A functor admitting a final functor from a sifted category is sifted. -/
/-
**CategoryTheory.IsSifted.of_final_functor_from_sifted** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.IsSifted`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u₁} [in
st_1 : CategoryTheory.Category.{v₁, u₁} D]   [h₁ : CategoryTheory.IsSifted C] (F
 : CategoryTheory.Functor C D) [F.Final], CategoryTheory.IsSifted D
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.IsSifted.isSifted_iff_asSmallIsSifted`：isSifted_iff_asSma
llIsSifted : IsSifted C ↔ IsSifted (AsSmall.{w} C) where mp _
· 使用定理 `CategoryTheory.IsSifted.of_final_functor_from_sifted'`：of_final_functor_
from_sifted' {D : Type u} [SmallCategory D] [IsSifted C] (F : C ⥤ D) [Final F] :
 IsSifted D
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
A functor admitting a final functor from a sifted category is sifted.
-/
theorem IsSifted.of_final_functor_from_sifted {D : Type u₁} [Category.{v₁} D] [h₁ : IsSifted C]
    (F : C ⥤ D) [Final F] : IsSifted D := by
  rw [isSifted_iff_asSmallIsSifted] at h₁ ⊢
  exact of_final_functor_from_sifted' <|
    AsSmall.equiv.{_, _, max u₁ v₁}.inverse ⋙ F ⋙ AsSmall.equiv.{_, _, max u v}.functor

end CategoryTheory

