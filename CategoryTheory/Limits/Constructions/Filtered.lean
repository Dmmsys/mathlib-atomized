/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Constructing colimits from finite colimits and filtered colimits

We construct colimits of size `w` from finite colimits and filtered colimits of size `w`. Since
`w`-sized colimits are constructed from coequalizers and `w`-sized coproducts, it suffices to
construct `w`-sized coproducts from finite coproducts and `w`-sized filtered colimits.

The idea is simple: to construct coproducts of shape `α`, we take the colimit of the filtered
diagram of all coproducts of finite subsets of `α`.

We also deduce the dual statement by invoking the original statement in `Cᵒᵖ`.
-/

@[expose] public section


universe w v u

noncomputable section

open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C] {α : Type w}

namespace CategoryTheory.Limits

namespace CoproductsFromFiniteFiltered

variable [HasFiniteCoproducts C]

set_option backward.isDefEq.respectTransparency false in
/-- If `C` has finite coproducts, a functor `Discrete α ⥤ C` lifts to a functor
`Finset (Discrete α) ⥤ C` by taking coproducts. -/
@[simps!]
/-
**CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinsetObj** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Limits.CoproductsFromFiniteFiltered`。
形式化陈述：liftToFinsetObj (F : Discrete α ⥤ C) : Finset (Discrete α) ⥤ C where obj s
参数：F : Discrete α ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` has finite coproducts, a functor `Discrete α ⥤ C` lifts to a functor
`Finset (Discrete α) ⥤ C` by taking coproducts.
-/
def liftToFinsetObj (F : Discrete α ⥤ C) : Finset (Discrete α) ⥤ C where
  obj s := ∐ fun x : s => F.obj x
  map {_ Y} h := Sigma.desc fun y =>
    Sigma.ι (fun (x : { x // x ∈ Y }) => F.obj x) ⟨y, h.down.down y.2⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `C` has finite coproducts and filtered colimits, we can construct arbitrary coproducts by
taking the colimit of the diagram formed by the coproducts of finite sets over the indexing type. -/
@[simps!]
/-
**CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinsetColimitCocone**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.CoproductsFromFiniteFiltered`。
形式化陈述：liftToFinsetColimitCocone [HasColimitsOfShape (Finset (Discrete α)) C] (F 
: Discrete α ⥤ C) : ColimitCocone F where cocone
参数：Finset (Discrete α)；F : Discrete α ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` has finite coproducts and filtered colimits, we can construct arbitrary c
oproducts by
taking the colimit of the diagram formed by the coproducts of finite sets over t
he indexing type.
-/
def liftToFinsetColimitCocone [HasColimitsOfShape (Finset (Discrete α)) C]
    (F : Discrete α ⥤ C) : ColimitCocone F where
  cocone :=
    { pt := colimit (liftToFinsetObj F)
      ι :=
        Discrete.natTrans fun j =>
          Sigma.ι (fun x : ({j} : Finset (Discrete α)) => F.obj x) ⟨j, by simp⟩ ≫
            colimit.ι (liftToFinsetObj F) {j} }
  isColimit :=
    { desc := fun s =>
        colimit.desc (liftToFinsetObj F)
          { pt := s.pt
            ι := { app := fun _ => Sigma.desc fun x => s.ι.app x } }
      uniq := fun s m h => by
        apply colimit.hom_ext
        rintro t
        dsimp [liftToFinsetObj]
        apply colimit.hom_ext
        rintro ⟨⟨j, hj⟩⟩
        convert! h j using 1
        · simp [← colimit.w (liftToFinsetObj F) ⟨⟨Finset.singleton_subset_iff.2 hj⟩⟩]
          rfl
        · simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (C) (α) in
/-- The functor taking a functor `Discrete α ⥤ C` to a functor `Finset (Discrete α) ⥤ C` by taking
coproducts. -/
@[simps!]
/-
**CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinset** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Limits.CoproductsFromFiniteFiltered`。
形式化陈述：liftToFinset : (Discrete α ⥤ C) ⥤ (Finset (Discrete α) ⥤ C) where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor taking a functor `Discrete α ⥤ C` to a functor `Finset (Discrete α) 
⥤ C` by taking
coproducts.
-/
def liftToFinset : (Discrete α ⥤ C) ⥤ (Finset (Discrete α) ⥤ C) where
  obj := liftToFinsetObj
  map := fun β => { app := fun _ => Sigma.map (fun x => β.app x.val) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The converse of the construction in `liftToFinsetColimitCocone`: we can form a cocone on the
coproduct of `f` whose legs are the coproducts over the finite subsets of `α`. -/
@[simps!]
/-
**CategoryTheory.Limits.CoproductsFromFiniteFiltered.finiteSubcoproductsCocone**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.CoproductsFromFiniteFiltered`。
形式化陈述：finiteSubcoproductsCocone (f : α -> C) [HasCoproduct f] : Cocone (liftToFi
nsetObj (Discrete.functor f)) where pt
参数：f : α -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The converse of the construction in `liftToFinsetColimitCocone`: we can form a c
ocone on the
coproduct of `f` whose legs are the coproducts over the finite subsets of `α`.
-/
def finiteSubcoproductsCocone (f : α → C) [HasCoproduct f] :
    Cocone (liftToFinsetObj (Discrete.functor f)) where
  pt := ∐ f
  ι := { app S := Sigma.desc fun s => Sigma.ι f _ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cocone `finiteSubcoproductsCocone` is a colimit cocone. -/
/-
**CategoryTheory.Limits.CoproductsFromFiniteFiltered.isColimitFiniteSubproductsC
ocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.CoproductsFromFiniteFilte
red`。
形式化陈述：isColimitFiniteSubproductsCocone (f : α -> C) [HasColimitsOfShape (Finset 
(Discrete α)) C] [HasCoproduct f] : IsColimit (finiteSubcoproductsCocone f)
参数：f : α -> C；Finset (Discrete α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone `finiteSubcoproductsCocone` is a colimit cocone.
-/
def isColimitFiniteSubproductsCocone (f : α → C) [HasColimitsOfShape (Finset (Discrete α)) C]
    [HasCoproduct f] : IsColimit (finiteSubcoproductsCocone f) :=
  IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext (IsColimit.coconePointUniqueUpToIso
      (liftToFinsetColimitCocone (Discrete.functor f)).isColimit (colimit.isColimit _) :) (by
    intro S
    simp only [liftToFinsetObj_obj, Discrete.functor_obj_eq_as, finiteSubcoproductsCocone_pt,
      colimit.cocone_x, colimit.cocone_ι, finiteSubcoproductsCocone_ι_app]
    ext j
    rw [← Category.assoc]
    convert!
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (liftToFinsetColimitCocone (Discrete.functor f)).isColimit (colimit.isColimit _) j
    · simp [← colimit.w (liftToFinsetObj _) (homOfLE (x := {j.1}) (y := S) (by simp))]
    · simp))

end CoproductsFromFiniteFiltered

open CoproductsFromFiniteFiltered

/-
**CategoryTheory.Limits.hasCoproducts_of_finite_and_filtered** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasCoproducts_of_finite_and_filtered [HasFiniteCoproducts C] [HasFilteredC
olimitsOfSize.{w, w} C] : HasCoproducts.{w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.isFiltered_of_directed_le_nonempty`：∀ (α : Type u) [inst 
: Preorder α] [IsDirectedOrder α] [Nonempty α], CategoryTheory.IsFiltered α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem hasCoproducts_of_finite_and_filtered [HasFiniteCoproducts C]
    [HasFilteredColimitsOfSize.{w, w} C] : HasCoproducts.{w} C := fun α => by
  exact ⟨fun F => HasColimit.mk (liftToFinsetColimitCocone F)⟩
/-
**CategoryTheory.Limits.has_colimits_of_finite_and_filtered** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：has_colimits_of_finite_and_filtered [HasFiniteColimits C] [HasFilteredColi
mitsOfSize.{w, w} C] : HasColimitsOfSize.{w, w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasCoproducts_of_finite_and_filtered`：hasCoproduct
s_of_finite_and_filtered [HasFiniteCoproducts C] [HasFilteredColimitsOfSize.{w, 
w} C] : HasCoproducts.{w} C
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Limits.has_colimits_of_hasCoequalizers_and_coproducts`：ha
s_colimits_of_hasCoequalizers_and_coproducts [HasCoproducts.{w} C] [HasCoequaliz
ers C] : HasColimitsOfSize.{w, w} C where has_colimits_of_…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
-/
theorem has_colimits_of_finite_and_filtered [HasFiniteColimits C]
    [HasFilteredColimitsOfSize.{w, w} C] : HasColimitsOfSize.{w, w} C :=
  have : HasCoproducts.{w} C := hasCoproducts_of_finite_and_filtered
  has_colimits_of_hasCoequalizers_and_coproducts
/-
**CategoryTheory.Limits.hasProducts_of_finite_and_cofiltered** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasProducts_of_finite_and_cofiltered [HasFiniteProducts C] [HasCofilteredL
imitsOfSize.{w, w} C] : HasProducts.{w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasCoproducts_of_finite_and_filtered`：hasCoproduct
s_of_finite_and_filtered [HasFiniteCoproducts C] [HasFilteredColimitsOfSize.{w, 
w} C] : HasCoproducts.{w} C
· 使用定理 `CategoryTheory.Limits.hasProducts_of_opposite`：hasProducts_of_opposite [
HasCoproducts.{v₂} Cᵒᵖ] : HasProducts.{v₂} C
-/
theorem hasProducts_of_finite_and_cofiltered [HasFiniteProducts C]
    [HasCofilteredLimitsOfSize.{w, w} C] : HasProducts.{w} C :=
  have : HasCoproducts.{w} Cᵒᵖ := hasCoproducts_of_finite_and_filtered
  hasProducts_of_opposite
/-
**CategoryTheory.Limits.has_limits_of_finite_and_cofiltered** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：has_limits_of_finite_and_cofiltered [HasFiniteLimits C] [HasCofilteredLimi
tsOfSize.{w, w} C] : HasLimitsOfSize.{w, w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasProducts_of_finite_and_cofiltered`：hasProducts_
of_finite_and_cofiltered [HasFiniteProducts C] [HasCofilteredLimitsOfSize.{w, w}
 C] : HasProducts.{w} C
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `CategoryTheory.Limits.has_limits_of_hasEqualizers_and_products`：has_limi
ts_of_hasEqualizers_and_products [HasProducts.{w} C] [HasEqualizers C] : HasLimi
tsOfSize.{w, w} C
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
-/
theorem has_limits_of_finite_and_cofiltered [HasFiniteLimits C]
    [HasCofilteredLimitsOfSize.{w, w} C] : HasLimitsOfSize.{w, w} C :=
  have : HasProducts.{w} C := hasProducts_of_finite_and_cofiltered
  has_limits_of_hasEqualizers_and_products

namespace CoproductsFromFiniteFiltered

section

variable [HasFiniteCoproducts C] [HasColimitsOfShape (Finset (Discrete α)) C]
    [HasColimitsOfShape (Discrete α) C]

set_option backward.isDefEq.respectTransparency false in
/-- Helper construction for `liftToFinsetColimIso`. -/
@[reassoc]
/-
**CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinsetColimIso_aux** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.CoproductsFromFiniteFiltered`。
形式化陈述：liftToFinsetColimIso_aux (F : Discrete α ⥤ C) {J : Finset (Discrete α)} (j
 : J) : Sigma.ι (F.obj ·.val) j ≫ colimit.ι (liftToFinsetObj F) J ≫ (colimit.iso
ColimitCocone (liftToFinsetColimitCocone F)).inv = colimit.ι F j
参数：F : Discrete α ⥤ C；Discrete α；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.uniqueUpToIso_inv`：∀ {J : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Ca
tegory.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Cocone.forget_map`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsColimit.descCoconeMorphism_hom`：∀ {J : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheo
ry.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinsetColimitCo
cone_isColimit_desc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {α
 : Type w}   [inst_1 : CategoryTheory.Limits.HasFiniteCoproducts C]   [inst_2 : 
C…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Helper construction for `liftToFinsetColimIso`.
-/
theorem liftToFinsetColimIso_aux (F : Discrete α ⥤ C) {J : Finset (Discrete α)} (j : J) :
    Sigma.ι (F.obj ·.val) j ≫ colimit.ι (liftToFinsetObj F) J ≫
      (colimit.isoColimitCocone (liftToFinsetColimitCocone F)).inv
    = colimit.ι F j := by
  simp [colimit.isoColimitCocone, IsColimit.coconePointUniqueUpToIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `liftToFinset` functor, precomposed with forming a colimit, is a coproduct on the original
functor. -/
/-
**CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinsetColimIso** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.CoproductsFromFiniteFiltered`。
形式化陈述：liftToFinsetColimIso : liftToFinset C α ⋙ colim ≅ colim
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `liftToFinset` functor, precomposed with forming a colimit, is a coproduct o
n the original
functor.
-/
def liftToFinsetColimIso : liftToFinset C α ⋙ colim ≅ colim :=
  NatIso.ofComponents
    (fun F => Iso.symm <| colimit.isoColimitCocone (liftToFinsetColimitCocone F))
    (fun β => by
      simp only [Functor.comp_obj, colim_obj, Functor.comp_map, colim_map, Iso.symm_hom]
      ext J
      simp only [liftToFinset_obj_obj]
      ext j
      simp [liftToFinset, liftToFinsetColimIso_aux, liftToFinsetColimIso_aux_assoc])

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `liftToFinset`, when composed with the evaluation functor, results in the whiskering composed
with `colim`. -/
/-
**CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinsetEvaluationIso**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.CoproductsFromFiniteFiltered`。
形式化陈述：liftToFinsetEvaluationIso [HasFiniteCoproducts C] (I : Finset (Discrete α)
) : liftToFinset C α ⋙ (evaluation _ _).obj I ≅ (Functor.whiskeringLeft _ _ _).o
bj (Discrete.functor (·.val)) ⋙ colim (J
参数：I : Finset (Discrete α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`liftToFinset`, when composed with the evaluation functor, results in the whiske
ring composed
with `colim`.
-/
def liftToFinsetEvaluationIso [HasFiniteCoproducts C] (I : Finset (Discrete α)) :
    liftToFinset C α ⋙ (evaluation _ _).obj I ≅
    (Functor.whiskeringLeft _ _ _).obj (Discrete.functor (·.val)) ⋙ colim (J := Discrete I) :=
  NatIso.ofComponents (fun _ => HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _))
    fun _ => by dsimp; ext; simp

end CoproductsFromFiniteFiltered

namespace ProductsFromFiniteCofiltered

variable [HasFiniteProducts C]

set_option backward.isDefEq.respectTransparency false in
/-- If `C` has finite coproducts, a functor `Discrete α ⥤ C` lifts to a functor
`Finset (Discrete α) ⥤ C` by taking coproducts. -/
@[simps!]
/-
**CategoryTheory.Limits.ProductsFromFiniteCofiltered.liftToFinsetObj** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Limits.ProductsFromFiniteCofiltered`。
形式化陈述：liftToFinsetObj (F : Discrete α ⥤ C) : (Finset (Discrete α))ᵒᵖ ⥤ C where o
bj s
参数：F : Discrete α ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` has finite coproducts, a functor `Discrete α ⥤ C` lifts to a functor
`Finset (Discrete α) ⥤ C` by taking coproducts.
-/
def liftToFinsetObj (F : Discrete α ⥤ C) : (Finset (Discrete α))ᵒᵖ ⥤ C where
  obj s := ∏ᶜ (fun x : s.unop => F.obj x)
  map {Y _} h := Pi.lift fun y =>
    Pi.π (fun (x : { x // x ∈ Y.unop }) => F.obj x) ⟨y, h.unop.down.down y.2⟩


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `C` has finite coproducts and filtered colimits, we can construct arbitrary coproducts by
taking the colimit of the diagram formed by the coproducts of finite sets over the indexing type. -/
@[simps!]
/-
**CategoryTheory.Limits.ProductsFromFiniteCofiltered.liftToFinsetLimitCone** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.ProductsFromFiniteCofiltered`。
形式化陈述：liftToFinsetLimitCone [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C] (F : Di
screte α ⥤ C) : LimitCone F where cone
参数：Finset (Discrete α)；F : Discrete α ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` has finite coproducts and filtered colimits, we can construct arbitrary c
oproducts by
taking the colimit of the diagram formed by the coproducts of finite sets over t
he indexing type.
-/
def liftToFinsetLimitCone [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
    (F : Discrete α ⥤ C) : LimitCone F where
  cone :=
    { pt := limit (liftToFinsetObj F)
      π := Discrete.natTrans fun j =>
        limit.π (liftToFinsetObj F) ⟨{j}⟩ ≫ Pi.π _ (⟨j, by simp⟩ : ({j} : Finset (Discrete α))) }
  isLimit :=
    { lift := fun s =>
        limit.lift (liftToFinsetObj F)
          { pt := s.pt
            π := { app := fun _ => Pi.lift fun x => s.π.app x } }
      uniq := fun s m h => by
        apply limit.hom_ext
        rintro t
        dsimp [liftToFinsetObj]
        apply limit.hom_ext
        rintro ⟨⟨j, hj⟩⟩
        convert! h j using 1
        · simp [← limit.w (liftToFinsetObj F) ⟨⟨⟨Finset.singleton_subset_iff.2 hj⟩⟩⟩]
          rfl
        · simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The converse of the construction in `liftToFinsetLimitCone`: we can form a cone on the
product of `f` whose legs are the products over the finite subsets of `α`. -/
@[simps!]
/-
**CategoryTheory.Limits.ProductsFromFiniteCofiltered.finiteSubproductsCone** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.ProductsFromFiniteCofiltered`。
形式化陈述：finiteSubproductsCone (f : α -> C) [HasProduct f] : Cone (liftToFinsetObj 
(Discrete.functor f)) where pt
参数：f : α -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The converse of the construction in `liftToFinsetLimitCone`: we can form a cone 
on the
product of `f` whose legs are the products over the finite subsets of `α`.
-/
def finiteSubproductsCone (f : α → C) [HasProduct f] :
    Cone (liftToFinsetObj (Discrete.functor f)) where
  pt := ∏ᶜ f
  π := { app S := Pi.lift fun s => Pi.π f _ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cone `finiteSubproductsCone` is a limit cone. -/
/-
**CategoryTheory.Limits.ProductsFromFiniteCofiltered.isLimitFiniteSubproductsCon
e** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.ProductsFromFiniteCofiltered`
。
形式化陈述：isLimitFiniteSubproductsCone (f : α -> C) [HasLimitsOfShape (Finset (Discr
ete α))ᵒᵖ C] [HasProduct f] : IsLimit (finiteSubproductsCone f)
参数：f : α -> C；Finset (Discrete α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone `finiteSubproductsCone` is a limit cone.
-/
def isLimitFiniteSubproductsCone (f : α → C) [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
    [HasProduct f] : IsLimit (finiteSubproductsCone f) :=
  IsLimit.ofIsoLimit (limit.isLimit _)
    (Cone.ext (IsLimit.conePointUniqueUpToIso
      (liftToFinsetLimitCone (Discrete.functor f)).isLimit (limit.isLimit _) :) (by
    intro S
    simp only [limit.cone_x, Functor.const_obj_obj, liftToFinsetObj_obj, Discrete.functor_obj_eq_as,
      limit.cone_π, finiteSubproductsCone_pt, finiteSubproductsCone_π_app]
    ext j
    simp only [Discrete.functor_obj_eq_as, Category.assoc, limit.lift_π, Fan.mk_pt, Fan.mk_π_app,
      limit.conePointUniqueUpToIso_hom_comp, liftToFinsetLimitCone_cone_pt, Discrete.mk_as,
      liftToFinsetLimitCone_cone_π_app]
    simp [← limit.w (liftToFinsetObj _)
      (Quiver.Hom.op (homOfLE (x := {j.1}) (y := S.unop) (by simp)))]))

variable (C) (α)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor taking a functor `Discrete α ⥤ C` to a functor `Finset (Discrete α) ⥤ C` by taking
coproducts. -/
@[simps!]
/-
**CategoryTheory.Limits.ProductsFromFiniteCofiltered.liftToFinset** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Limits.ProductsFromFiniteCofiltered`。
形式化陈述：liftToFinset : (Discrete α ⥤ C) ⥤ ((Finset (Discrete α))ᵒᵖ ⥤ C) where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor taking a functor `Discrete α ⥤ C` to a functor `Finset (Discrete α) 
⥤ C` by taking
coproducts.
-/
def liftToFinset : (Discrete α ⥤ C) ⥤ ((Finset (Discrete α))ᵒᵖ ⥤ C) where
  obj := liftToFinsetObj
  map := fun β => { app := fun _ => Pi.map (fun x => β.app x.val) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `liftToFinset` functor, precomposed with forming a colimit, is a coproduct on the original
functor. -/
/-
**CategoryTheory.Limits.ProductsFromFiniteCofiltered.liftToFinsetLimIso** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.Limits.ProductsFromFiniteCofiltered`。
形式化陈述：liftToFinsetLimIso [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C] [HasLimits
OfShape (Discrete α) C] : liftToFinset C α ⋙ lim ≅ lim
参数：Finset (Discrete α)；Discrete α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `liftToFinset` functor, precomposed with forming a colimit, is a coproduct o
n the original
functor.
-/
def liftToFinsetLimIso [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
    [HasLimitsOfShape (Discrete α) C] : liftToFinset C α ⋙ lim ≅ lim :=
  NatIso.ofComponents
    (fun F => Iso.symm <| limit.isoLimitCone (liftToFinsetLimitCone F))
    (fun β => by
      simp only [Functor.comp_obj, lim_obj, Functor.comp_map, lim_map, Iso.symm_hom]
      ext J
      simp [liftToFinset])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `liftToFinset`, when composed with the evaluation functor, results in the whiskering composed
with `colim`. -/
/-
**CategoryTheory.Limits.ProductsFromFiniteCofiltered.liftToFinsetEvaluationIso**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.ProductsFromFiniteCofiltered`。
形式化陈述：liftToFinsetEvaluationIso (I : Finset (Discrete α)) : liftToFinset C α ⋙ (
evaluation _ _).obj ⟨I⟩ ≅ (Functor.whiskeringLeft _ _ _).obj (Discrete.functor (
·.val)) ⋙ lim (J
参数：I : Finset (Discrete α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`liftToFinset`, when composed with the evaluation functor, results in the whiske
ring composed
with `colim`.
-/
def liftToFinsetEvaluationIso (I : Finset (Discrete α)) :
    liftToFinset C α ⋙ (evaluation _ _).obj ⟨I⟩ ≅
    (Functor.whiskeringLeft _ _ _).obj (Discrete.functor (·.val)) ⋙ lim (J := Discrete I) :=
  NatIso.ofComponents (fun _ => HasLimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _))
    fun _ => by dsimp; ext; simp [Pi.map]

end ProductsFromFiniteCofiltered

end CategoryTheory.Limits

