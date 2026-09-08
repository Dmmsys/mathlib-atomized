/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Morphisms to a colimit in a Grothendieck abelian category

Let `C : Type u` be an abelian category `[Category.{v} C]` which
satisfies `IsGrothendieckAbelian.{w} C`. We may expect
that all the objects `X : C` are `κ`-presentable for some regular
cardinal `κ`. However, we only prove a weaker result (which
is enough in order to obtain the existence of enough
injectives (TODO)): let `κ` be a big enough regular
cardinal such that if `Y : J ⥤ C` is a functor from
a `κ`-filtered category, and `c : Cocone Y` is a colimit cocone,
then the map from the colimit of the types `X ⟶ Y j` to
`X ⟶ c.pt` is injective, and it is bijective under the
additional assumption that for any map `f : j ⟶ j'` in `J`,
`Y.map f` is a monomorphism, see
`IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite

attribute [local instance] IsFiltered.isConnected

namespace IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {X : C} {J : Type w} [SmallCategory J]

namespace IsPresentable

variable {Y : J ⥤ C} {c : Cocone Y} (hc : IsColimit c)

namespace injectivity₀

variable {j₀ : J} (y : X ⟶ Y.obj j₀) (hy : y ≫ c.ι.app j₀ = 0)

/-!
Given `y : X ⟶ Y.obj j₀`, we introduce a natural
transformation `g : X ⟶ Y.obj t.right` for `t : Under j₀`.
We consider the kernel of this morphism: we have a natural exact sequence
`kernel (g y) ⟶ X ⟶ Y.obj t.right` for all `t : Under j₀`. Under the
assumption that the composition `y ≫ c.ι.app j₀ : X ⟶ c.pt` is zero,
we get that after passing to the colimit, the right map `X ⟶ c.pt` is
zero, which implies that the left map `f : colimit (kernel (g y)) ⟶ X`
is an epimorphism (see `epi_f`). If `κ` is a regular cardinal that is
bigger than the cardinality of `Subobject X` and `J` is `κ`-filtered,
it follows that for some `φ : j₀ ⟶ j` in `Under j₀`,
the inclusion `(kernel.ι (g y)).app j` is an isomorphism,
which implies that `y ≫ Y.map φ = 0` (see the lemma `injectivity₀`).
-/

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `X ⟶ Y.obj t.right` for `t : Under j₀`
that is induced by `y : X ⟶ Y.obj j₀`. -/
@[simps]
/-
**CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity₀.g** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity₀`。
形式化陈述：g : (Functor.const _).obj X ⟶ Under.forget j₀ ⋙ Y where app t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `X ⟶ Y.obj t.right` for `t : Under j₀`
that is induced by `y : X ⟶ Y.obj j₀`.
-/
def g : (Functor.const _).obj X ⟶ Under.forget j₀ ⋙ Y where
  app t := y ≫ Y.map t.hom
  naturality t₁ t₂ f := by
    dsimp
    simp only [Category.id_comp, Category.assoc, ← Functor.map_comp, Under.w]

/-- The obvious morphism `colimit (kernel (g y)) ⟶ X` (which is an epimorphism
if `J` is filtered, see `epi_f`). -/
/-
**CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity₀.f** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity₀`。
形式化陈述：f : colimit (kernel (g y)) ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious morphism `colimit (kernel (g y)) ⟶ X` (which is an epimorphism
if `J` is filtered, see `epi_f`).
-/
noncomputable def f : colimit (kernel (g y)) ⟶ X :=
  IsColimit.map (colimit.isColimit _) (constCocone _ X) (kernel.ι _)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity₀.hf** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity₀`
。
形式化陈述：hf (j : Under j₀) : colimit.ι (kernel (g y)) j ≫ f y = (kernel.ι (g y)).ap
p j
参数：j : Under j₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Abelian.hasEqualizers`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasEq
ualizers C
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.Limits.IsColimit.ι_map`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, 
u₃} C]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hf (j : Under j₀) :
    colimit.ι (kernel (g y)) j ≫ f y = (kernel.ι (g y)).app j :=
  (IsColimit.ι_map _ _ _ _).trans (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {y} in
include hc hy in
/-
**CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity₀.epi_f** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivit
y₀`。
形式化陈述：epi_f [IsFiltered J] : Epi (f y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.epi_f`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : C
ategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Abelian.hasEqualizers`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasEq
ualizers C
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasFilteredColimitsOfSize`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelia
n C}   [self : CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.IsFiltered.under`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] [CategoryTheory.IsFilteredOrEmpty C] (c : C),   CategoryThe
ory.IsFiltered (Categ…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity₀.hf`：hf (
j : Under j₀) : colimit.ι (kernel (g y)) j ≫ f y = (kernel.ι (g y)).app j
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.colim.exact_mapShortComplex`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {J : Type u'} [inst_1 : CategoryTheory.Categ
ory.{v', u'} J]   [inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.AB5OfSize.ofShape`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasFilteredColimitsOfSize.{
w, w', v, u} C}   [sel…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.ab5OfSize`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self : C
ategoryTheory.IsGrothendieckAbelian.…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.IsFiltered.isConnected`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [CategoryTheory.IsFiltered C], CategoryTheory.IsConnecte
d C
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Under.final_forget`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] [CategoryTheory.IsFilteredOrEmpty C] (c : C),   (Category
Theory.Under.forget c).…
-/
lemma epi_f [IsFiltered J] : Epi (f y) := by
  exact (colim.exact_mapShortComplex
    ((ShortComplex.mk _ _ (kernel.condition (g y))).exact_of_f_is_kernel
      (kernelIsKernel (g y)))
    (colimit.isColimit _) (isColimitConstCocone _ _)
    ((Functor.Final.isColimitWhiskerEquiv (Under.forget j₀) c).symm hc) (f y) 0
    (fun j ↦ by simpa using! hf y j)
    (fun _ ↦ by simpa using! hy.symm)).epi_f rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The kernel of `g y` gives a family of subobjects of `X` indexed by `Under j₀`, and
we consider it as a functor `Under j₀ ⥤ MonoOver X`. -/
@[simps]
/-
**CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity₀.F** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity₀`。
形式化陈述：F : Under j₀ ⥤ MonoOver X where obj j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of `g y` gives a family of subobjects of `X` indexed by `Under j₀`, a
nd
we consider it as a functor `Under j₀ ⥤ MonoOver X`.
-/
noncomputable def F : Under j₀ ⥤ MonoOver X where
  obj j := MonoOver.mk ((kernel.ι (g y)).app j)
  map {j j'} f := MonoOver.homMk ((kernel (g y)).map f)

end injectivity₀

section

variable {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (hXκ : HasCardinalLT (Subobject X) κ)

include hXκ hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open injectivity₀ in
/-
**CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.IsPresentable`。
形式化陈述：injectivity (j₀ : J) (y₁ y₂ : X ⟶ Y.obj j₀) (hy : y₁ ≫ c.ι.app j₀ = y₂ ≫ c
.ι.app j₀) : exists (j : J) (φ : j₀ ⟶ j), y₁ ≫ Y.map φ = y₂ ≫ Y.map φ
参数：j₀ : J；y₁ y₂ : X ⟶ Y.obj j₀；hy : y₁ ≫ c.ι.app j₀ = y₂ ≫ c.ι.app j₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity₀`：injecti
vity₀ {j₀ : J} (y : X ⟶ Y.obj j₀) (hy : y ≫ c.ι.app j₀ = 0) : exists (j : J) (φ 
: j₀ ⟶ j), y ≫ Y.map φ = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma injectivity₀ {j₀ : J} (y : X ⟶ Y.obj j₀) (hy : y ≫ c.ι.app j₀ = 0) :
    ∃ (j : J) (φ : j₀ ⟶ j), y ≫ Y.map φ = 0 := by
  have := isFiltered_of_isCardinalFiltered J κ
  obtain ⟨j, h⟩ := exists_isIso_of_functor_from_monoOver (F y) hXκ _
      (colimit.isColimit (kernel (g y))) (f y) (fun j ↦ by simpa using! hf y j)
      (epi_f hc hy)
  dsimp at h
  refine ⟨j.right, j.hom, ?_⟩
  simpa only [← cancel_epi ((kernel.ι (g y)).app j), comp_zero]
    using! NatTrans.congr_app (kernel.condition (g y)) j
/-
**CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.IsPresentable`。
形式化陈述：injectivity (j₀ : J) (y₁ y₂ : X ⟶ Y.obj j₀) (hy : y₁ ≫ c.ι.app j₀ = y₂ ≫ c
.ι.app j₀) : exists (j : J) (φ : j₀ ⟶ j), y₁ ≫ Y.map φ = y₂ ≫ Y.map φ
参数：j₀ : J；y₁ y₂ : X ⟶ Y.obj j₀；hy : y₁ ≫ c.ι.app j₀ = y₂ ≫ c.ι.app j₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity₀`：injecti
vity₀ {j₀ : J} (y : X ⟶ Y.obj j₀) (hy : y ≫ c.ι.app j₀ = 0) : exists (j : J) (φ 
: j₀ ⟶ j), y ≫ Y.map φ = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma injectivity (j₀ : J) (y₁ y₂ : X ⟶ Y.obj j₀)
    (hy : y₁ ≫ c.ι.app j₀ = y₂ ≫ c.ι.app j₀) :
    ∃ (j : J) (φ : j₀ ⟶ j), y₁ ≫ Y.map φ = y₂ ≫ Y.map φ := by
  obtain ⟨j, φ, hφ⟩ := injectivity₀ hc hXκ (y₁ - y₂)
    (by rw [Preadditive.sub_comp, sub_eq_zero, hy])
  exact ⟨j, φ, by simpa only [Preadditive.sub_comp, sub_eq_zero] using hφ⟩

end

namespace surjectivity

variable (z : X ⟶ c.pt)

/-!
Let `z : X ⟶ c.pt` (where `c` is a colimit cocone for `Y : J ⥤ C`).
We consider the pullback of `c.ι` and of the constant
map `(Functor.const J).map z`. If we assume that `c.ι` is a monomorphism,
then this pullback evaluated at `j : J` can be identified to a subobject of `X`
(this is the inverse image by `z` of `Y.obj j` considered as a subobject of `c.pt`).
This corresponds to a functor `F z : J ⥤ MonoOver X`, and when taking the colimit
(computed in `C`), we obtain an epimorphism
`f z : colimit (pullback c.ι ((Functor.const J).map z)) ⟶ X`
when `J` is filtered (see `epi_f`). If `κ` is a regular cardinal that is
bigger than the cardinality of `Subobject X` and `J` is `κ`-filtered,
we deduce that `z` factors as `X ⟶ Y.obj j ⟶ c.pt` for some `j`
(see the lemma `surjectivity`).
-/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor `J ⥤ MonoOver X` which sends `j : J` to the inverse image by `z : X ⟶ c.pt`
of the subobject `Y.obj j` of `c.pt`; it is defined here as the object in `MonoOver X`
corresponding to the monomorphism
`(pullback.snd c.ι ((Functor.const _).map z)).app j`. -/
@[simps]
/-
**CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity.F** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity`。
形式化陈述：F [Mono c.ι] : J ⥤ MonoOver X where obj j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `J ⥤ MonoOver X` which sends `j : J` to the inverse image by `z : X 
⟶ c.pt`
of the subobject `Y.obj j` of `c.pt`; it is defined here as the object in `MonoO
ver X`
corresponding to the monomorphism
`(pullback.snd c.ι ((Functor.const _).map z)).app j`.
-/
noncomputable def F [Mono c.ι] : J ⥤ MonoOver X where
  obj j := MonoOver.mk ((pullback.snd c.ι ((Functor.const _).map z)).app j)
  map {j j'} f := MonoOver.homMk ((pullback c.ι ((Functor.const _).map z)).map f)

/-- The canonical map `colimit (pullback c.ι ((Functor.const J).map z)) ⟶ X`,
which is an isomorphism when `J` is filtered, see `isIso_f`. -/
/-
**CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity.f** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity`。
形式化陈述：f : colimit (pullback c.ι ((Functor.const J).map z)) ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `colimit (pullback c.ι ((Functor.const J).map z)) ⟶ X`,
which is an isomorphism when `J` is filtered, see `isIso_f`.
-/
noncomputable def f : colimit (pullback c.ι ((Functor.const J).map z)) ⟶ X :=
  colimit.desc _ (Cocone.mk X
    { app j := (pullback.snd c.ι ((Functor.const _).map z)).app j })
/-
**CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity.hf** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity`
。
形式化陈述：hf (j : J) : colimit.ι (pullback c.ι ((Functor.const J).map z)) j ≫ f z = 
(pullback.snd c.ι ((Functor.const J).map z)).app j
参数：j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
-/
lemma hf (j : J) :
    colimit.ι (pullback c.ι ((Functor.const J).map z)) j ≫ f z =
      (pullback.snd c.ι ((Functor.const J).map z)).app j :=
  colimit.ι_desc _ _

include hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity.isIso_f** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjecti
vity`。
形式化陈述：isIso_f [IsFiltered J] : IsIso (f z)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasFilteredColimitsOfSize`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelia
n C}   [self : CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
· 使用定理 `CategoryTheory.IsFiltered.isConnected`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [CategoryTheory.IsFiltered C], CategoryTheory.IsConnecte
d C
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.ι_colimMap_assoc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.colimit.comp_coconePointUniqueUpToIso_hom`：∀ {J : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Cate
goryTheory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.constCocone_ι`：∀ (J : Type u₁) [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} C]   (X : C),   (Catego…
· 使用定理 `CategoryTheory.NatTrans.id_app`：id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ 
F).app X = 𝟙 (F.obj X)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity.hf`：hf (
j : J) : colimit.ι (pullback c.ι ((Functor.const J).map z)) j ≫ f z = (pullback.
snd c.ι ((Functor.const J).map z)).app j
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.isomorphisms`：∀ 
(C : Type u) [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheory.Morphi
smProperty.isomorphisms C).IsStableUnderBaseChange
· 使用定理 `CategoryTheory.IsPullback.map`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.preservesFiniteLimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.AB5OfSize.ofShape`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasFilteredColimitsOfSize.{
w, w', v, u} C}   [sel…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.ab5OfSize`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self : C
ategoryTheory.IsGrothendieckAbelian.…
（共 37 条，此处仅展示前 30 条）
-/
lemma isIso_f [IsFiltered J] : IsIso (f z) := by
  refine ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff ?_).1
    (MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback c.ι ((Functor.const _).map z)).map colim) ?_)
  · refine Arrow.isoMk (Iso.refl _)
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitConstCocone J X)) ?_
    dsimp
    ext j
    rw [Category.id_comp, ι_colimMap_assoc, colimit.comp_coconePointUniqueUpToIso_hom,
      constCocone_ι, NatTrans.id_app, Category.comp_id]
    apply hf
  · refine ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff ?_).2
      ((inferInstance : IsIso (𝟙 c.pt)))
    exact Arrow.isoMk (IsColimit.coconePointUniqueUpToIso (colimit.isColimit Y) hc)
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
        (isColimitConstCocone J c.pt))
/-
**CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity.epi_f** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivi
ty`。
形式化陈述：epi_f [IsFiltered J] : Epi (f z)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity.isIso_f`
：isIso_f [IsFiltered J] : IsIso (f z)
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
-/
lemma epi_f [IsFiltered J] : Epi (f z) := by
  have := isIso_f hc z
  infer_instance

end surjectivity

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
open surjectivity in
/-
**CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.IsPresentable`。
形式化陈述：surjectivity [forall (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)] {κ : Cardina
l.{w}} [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ] (hXκ : HasCardinalLT (Su
bobject X) κ) (z : X ⟶ c.pt) : exists (j₀ : J) (y : X ⟶ Y.obj j₀), z = y ≫ c.ι.a
pp j₀
参数：j j' : J；φ : j ⟶ j'；Y.map φ；hXκ : HasCardinalLT (Subobject X) κ；z : X ⟶ c.pt。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `CategoryTheory.Limits.IsColimit.mono_ι_app_of_isFiltered`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u'} [inst_1 : CategoryTheor
y.Category.{v', u'} J]   {X : CategoryTheory.F…
· 使用定理 `CategoryTheory.NatTrans.mono_of_mono_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasFilteredColimitsOfSize`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelia
n C}   [self : CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.IsFiltered.under`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] [CategoryTheory.IsFilteredOrEmpty C] (c : C),   CategoryThe
ory.IsFiltered (Categ…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.Functor.instPreservesMonomorphisms`：∀ {C : Type u_1} {D :
 Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_obje
ct`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.preservesFiniteLimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.AB5OfSize.ofShape`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasFilteredColimitsOfSize.{
w, w', v, u} C}   [sel…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.ab5OfSize`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self : C
ategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.exists_isIso_of_functor_from_monoOv
er`：exists_isIso_of_functor_from_monoOver {κ : Cardinal.{w}} [hκ : Fact κ.IsRegu
lar] [IsCardinalFiltered J κ] (hXκ : HasCardinalLT (Subobject X)…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity.hf`：hf (
j : J) : colimit.ι (pullback c.ι ((Functor.const J).map z)) j ≫ f z = (pullback.
snd c.ι ((Functor.const J).map z)).app j
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity.epi_f`：e
pi_f [IsFiltered J] : Epi (f z)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.eq_inv_comp`：eq_inv_comp (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Functor.const_map_app`：∀ (J : Type u₁) [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} C]   {X Y : C} (f : X ⟶…
-/
lemma surjectivity [∀ (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)]
    {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hXκ : HasCardinalLT (Subobject X) κ) (z : X ⟶ c.pt) :
    ∃ (j₀ : J) (y : X ⟶ Y.obj j₀), z = y ≫ c.ι.app j₀ := by
  have := isFiltered_of_isCardinalFiltered J κ
  have := hc.mono_ι_app_of_isFiltered
  have := NatTrans.mono_of_mono_app c.ι
  obtain ⟨j, _⟩ := exists_isIso_of_functor_from_monoOver (F z) hXκ _
    (colimit.isColimit _) (f z) (hf z) (epi_f hc z)
  refine ⟨j, inv ((F z).obj j).obj.hom ≫ (pullback.fst c.ι _).app j, ?_⟩
  dsimp
  rw [Category.assoc, IsIso.eq_inv_comp, ← NatTrans.comp_app, pullback.condition,
    NatTrans.comp_app, Functor.const_map_app]

end IsPresentable

open IsPresentable in
/-- If `X` is an object in a Grothendieck abelian category, then
the functor `coyoneda.obj (op X)` commutes with colimits corresponding
to diagrams of monomorphisms indexed by `κ`-filtered categories
for a big enough regular cardinal `κ`. -/
/-
**CategoryTheory.IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian`。
形式化陈述：preservesColimit_coyoneda_obj_of_mono (Y : J ⥤ C) {κ : Cardinal.{w}} [hκ :
 Fact κ.IsRegular] [IsCardinalFiltered J κ] (hXκ : HasCardinalLT (Subobject X) κ
) [forall (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)] : PreservesColimit Y ((coyone
da.obj (op X))) where preserves {c} hc
参数：Y : J ⥤ C；hXκ : HasCardinalLT (Subobject X) κ；j j' : J；φ : j ⟶ j'；Y.map φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity`：surject
ivity [forall (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)] {κ : Cardinal.{w}} [hκ : 
Fact κ.IsRegular] [IsCardinalFiltered J κ] (hXκ : Has…
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.IsPresentable.injectivity`：injectiv
ity (j₀ : J) (y₁ y₂ : X ⟶ Y.obj j₀) (hy : y₁ ≫ c.ι.app j₀ = y₂ ≫ c.ι.app j₀) : e
xists (j : J) (φ : j₀ ⟶ j), y₁ ≫ Y.map φ = y₂ ≫ Y.ma…

--- 原说明 ---
If `X` is an object in a Grothendieck abelian category, then
the functor `coyoneda.obj (op X)` commutes with colimits corresponding
to diagrams of monomorphisms indexed by `κ`-filtered categories
for a big enough regular cardinal `κ`.
-/
lemma preservesColimit_coyoneda_obj_of_mono
    (Y : J ⥤ C) {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
    [IsCardinalFiltered J κ] (hXκ : HasCardinalLT (Subobject X) κ)
    [∀ (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)] :
    PreservesColimit Y ((coyoneda.obj (op X))) where
  preserves {c} hc := ⟨by
    have := isFiltered_of_isCardinalFiltered J κ
    exact Types.FilteredColimit.isColimitOf' _ _
      (surjectivity hc hXκ) (injectivity hc hXκ)⟩

end IsGrothendieckAbelian

end CategoryTheory

