/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Preadditive.LiftToFinset
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-!
# The Gabriel-Popescu theorem

We prove the following Gabriel-Popescu theorem: if `C` is a Grothendieck abelian category and
`G` is a separator, then the functor `preadditiveCoyonedaObj G : C ⥤ ModuleCat (End G)ᵐᵒᵖ` sending
`X` to `Hom(G, X)` is fully faithful and has an exact left adjoint.

We closely follow the elementary proof given by Barry Mitchell.

## Future work

The left adjoint `tensorObj G` actually exists as soon as `C` is cocomplete and additive, so the
construction could be generalized.

The theorem as stated here implies that `C` is a Serre quotient of `ModuleCat (End G)ᵐᵒᵖ`.

## References

* [Barry Mitchell, *A quick proof of the Gabriel-Popesco theorem*][mitchell1981]
-/

@[expose] public section

universe v u

open CategoryTheory Limits Abelian

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

/-
**CategoryTheory.IsGrothendieckAbelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.IsGrothendieckAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : C} : (preadditiveCoyonedaObj G).IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating.{v} (isCoseparator_coseparator _) _

/-- The left adjoint of the functor `Hom(G, ·)`, which can be thought of as `· ⊗ G`. -/
/-
**CategoryTheory.IsGrothendieckAbelian.tensorObj** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.IsGrothendieckAbelian`。
形式化陈述：tensorObj (G : C) : ModuleCat (End G)ᵐᵒᵖ ⥤ C
参数：G : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.instIsRightAdjointModuleCatMulOppos
iteEndPreadditiveCoyonedaObj`：∀ {C : Type u} [inst : CategoryTheory.Category.{v,
 u} C] [inst_1 : CategoryTheory.Abelian C]   [CategoryTheory.IsGrothendieckAbeli
an.{v, v, …

--- 原说明 ---
The left adjoint of the functor `Hom(G, ·)`, which can be thought of as `· ⊗ G`.
-/
noncomputable def tensorObj (G : C) : ModuleCat (End G)ᵐᵒᵖ ⥤ C :=
  (preadditiveCoyonedaObj G).leftAdjoint

/-- The tensor-hom adjunction `(· ⊗ G) ⊣ Hom(G, ·)`. -/
/-
**CategoryTheory.IsGrothendieckAbelian.tensorObjPreadditiveCoyonedaObjAdjunction
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsGrothendieckAbelian`。
形式化陈述：tensorObjPreadditiveCoyonedaObjAdjunction (G : C) : tensorObj G ⊣ preaddit
iveCoyonedaObj G
参数：G : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.instIsRightAdjointModuleCatMulOppos
iteEndPreadditiveCoyonedaObj`：∀ {C : Type u} [inst : CategoryTheory.Category.{v,
 u} C] [inst_1 : CategoryTheory.Abelian C]   [CategoryTheory.IsGrothendieckAbeli
an.{v, v, …

--- 原说明 ---
The tensor-hom adjunction `(· ⊗ G) ⊣ Hom(G, ·)`.
-/
noncomputable def tensorObjPreadditiveCoyonedaObjAdjunction (G : C) :
    tensorObj G ⊣ preadditiveCoyonedaObj G :=
  Adjunction.ofIsRightAdjoint _
/-
**CategoryTheory.IsGrothendieckAbelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.IsGrothendieckAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : C} : (tensorObj G).IsLeftAdjoint :=
  (tensorObjPreadditiveCoyonedaObjAdjunction G).isLeftAdjoint

namespace GabrielPopescuAux

open CoproductsFromFiniteFiltered

/-- This is the map `⨁ₘ G ⟶ A` induced by `M ⟶ Hom(G, A)`. -/
/-
**CategoryTheory.IsGrothendieckAbelian.GabrielPopescuAux.d** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.IsGrothendieckAbelian.GabrielPopescuAux`。
形式化陈述：d {G A : C} {M : ModuleCat (End G)ᵐᵒᵖ} (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G
 ⟶ A)) : ∐ (fun (_ : M) => G) ⟶ A
参数：End G；g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the map `⨁ₘ G ⟶ A` induced by `M ⟶ Hom(G, A)`.
-/
noncomputable def d {G A : C} {M : ModuleCat (End G)ᵐᵒᵖ}
    (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) : ∐ (fun (_ : M) => G) ⟶ A :=
  Sigma.desc fun (m : M) => g m

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.IsGrothendieckAbelian.GabrielPopescuAux.** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.IsGrothendieckAbelian.GabrielPopescuAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_d {G A : C} {M : ModuleCat (End G)ᵐᵒᵖ} (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) (m : M) :
    Sigma.ι _ m ≫ d g = g.hom m := by
  simp [d]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local instance] IsFiltered.isConnected in
/-- This is the "Lemma" in [mitchell1981]. -/
/-
**CategoryTheory.IsGrothendieckAbelian.GabrielPopescuAux.kernel_** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.GabrielPopescuAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the "Lemma" in [mitchell1981].
-/
theorem kernel_ι_d_comp_d {G : C} (hG : IsSeparator G) {A B : C} {M : ModuleCat (End G)ᵐᵒᵖ}
    (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) (hg : Mono g)
    (f : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ B)) :
    kernel.ι (d g) ≫ d f = 0 := by
  refine (isColimitFiniteSubproductsCocone (fun (_ : M) => G)).pullback_zero_ext (fun F => ?_)
  dsimp only [liftToFinsetObj_obj, Discrete.functor_obj_eq_as, finiteSubcoproductsCocone_pt,
    Functor.const_obj_obj]
  classical
  rw [finiteSubcoproductsCocone_ι_app_eq_sum, ← pullback.condition_assoc]
  refine (Preadditive.isSeparator_iff G).1 hG _ (fun h => ?_)
  rw [Preadditive.comp_sum_assoc, Preadditive.comp_sum_assoc, Preadditive.sum_comp]
  simp only [Category.assoc, ι_d]
  let r (x : F) : (End G)ᵐᵒᵖ := MulOpposite.op (h ≫ pullback.fst _ _ ≫ Sigma.π _ x)
  suffices ∑ x ∈ F.attach, r x • f.hom x.1.as = 0 by simpa [End.smul_left, r] using this
  simp only [← map_smul, ← map_sum]
  suffices ∑ x ∈ F.attach, r x • x.1.as = 0 by simp [this]
  simp only [← g.hom.map_eq_zero_iff ((ModuleCat.mono_iff_injective _).1 hg), map_sum, map_smul]
  simp only [← ι_d g, End.smul_left, MulOpposite.unop_op, Category.assoc, r]
  simp [← Preadditive.comp_sum, ← Preadditive.sum_comp', pullback.condition_assoc]
/-
**CategoryTheory.IsGrothendieckAbelian.GabrielPopescuAux.exists_d_comp_eq_d** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.GabrielPopescuAux`。
形式化陈述：exists_d_comp_eq_d {G : C} (hG : IsSeparator G) {A} (B : C) [Injective B] 
{M : ModuleCat (End G)ᵐᵒᵖ} (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) (hg : Mono 
g) (f : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ B)) : exists (l : A ⟶ B), d g ≫ l = d f
参数：hG : IsSeparator G；B : C；End G；g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)；hg : M
ono g；f : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasCoproductsOfShape_of_hasCoproducts`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproduc
ts C] (J : Type w),   CategoryTheory.Limits.HasCo…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.instEpiFactorThruImageOfHasLimitWalkingParallelPai
rParallelPair`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C
} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasImage f]   [∀ {Z : C} (g…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasCountableLimitsOfCountabl
eCategory`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] (J : T
ype u_2)   [CategoryTheory.Limits.HasCountableLimits C] [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.hasCountableLimits_of_hasLimits`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasLimits C
],   CategoryTheory.Limits.HasCountableLimi…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasLimits`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Category
Theory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.instCountableCategoryOfFinCategory`：∀ (α : Type u_1) [ins
t : CategoryTheory.SmallCategory α] [CategoryTheory.FinCategory α],   CategoryTh
eory.CountableCategory α
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_kernels`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelian 
C],   CategoryTheory.Limits.HasKernels…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.kernelFactorThruImage_hom_comp_ι`：kernelFactorThru
Image_hom_comp_ι : (kernelFactorThruImage f).hom ≫ kernel.ι f = kernel.ι (factor
ThruImage f)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.GabrielPopescuAux.kernel_ι_d_comp_d
`：kernel_ι_d_comp_d {G : C} (hG : IsSeparator G) {A B : C} {M : ModuleCat (End G
)ᵐᵒᵖ} (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) (hg : Mono g) …
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Injective.comp_factorThru`：comp_factorThru {J X Y : C} [I
njective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : f ≫ factorThru g f = g
· 使用定理 `CategoryTheory.Abelian.comp_epiDesc`：comp_epiDesc [Epi f] {T : C} (g : X
 ⟶ T) (hg : kernel.ι f ≫ g = 0) : f ≫ epiDesc f g hg = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_d_comp_eq_d {G : C} (hG : IsSeparator G) {A} (B : C) [Injective B]
    {M : ModuleCat (End G)ᵐᵒᵖ} (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) (hg : Mono g)
    (f : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ B)) : ∃ (l : A ⟶ B), d g ≫ l = d f := by
  let l₁ : image (d g) ⟶ B := epiDesc (factorThruImage (d g)) (d f) (by
    rw [← kernelFactorThruImage_hom_comp_ι, Category.assoc, kernel_ι_d_comp_d hG _ hg, comp_zero])
  let l₂ : A ⟶ B := Injective.factorThru l₁ (Limits.image.ι (d g))
  refine ⟨l₂, ?_⟩
  simp only [l₂, l₁]
  conv_lhs => congr; rw [← Limits.image.fac (d g)]
  simp [-Limits.image.fac]

end GabrielPopescuAux

open GabrielPopescuAux

set_option backward.isDefEq.respectTransparency false in
/-- Faithfulness follows because `G` is a separator, see
`isSeparator_iff_faithful_preadditiveCoyonedaObj`. -/
/-
**CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.full** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.IsGrothendieckAbelian.GabrielPopescu`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [CategoryTheory.IsGrothendieckAbelian.{v, v, u} C] (G : C),
   CategoryTheory.IsSeparator G → (CategoryTheory.preadditiveCoyonedaObj G).Full
参数：G : C；CategoryTheory.preadditiveCoyonedaObj G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasCoproductsOfShape_of_hasCoproducts`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproduc
ts C] (J : Type w),   CategoryTheory.Limits.HasCo…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isSeparator_iff_epi`：isSeparator_iff_epi (G : C) [forall 
A : C, HasCoproduct fun _ : G ⟶ A => G] : IsSeparator G ↔ forall A : C, Epi (Sig
ma.desc fun f : G ⟶ A =>…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.GabrielPopescuAux.kernel_ι_d_comp_d
`：kernel_ι_d_comp_d {G : C} (hG : IsSeparator G) {A B : C} {M : ModuleCat (End G
)ᵐᵒᵖ} (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) (hg : Mono g) …
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.preadditiveCoyonedaObj_map`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (X : C) {X_1
 Y : C}   (f : X_1 ⟶ Y),   (Cat…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `CategoryTheory.Abelian.comp_epiDesc`：comp_epiDesc [Epi f] {T : C} (g : X
 ⟶ T) (hg : kernel.ι f ≫ g = 0) : f ≫ epiDesc f g hg = g

--- 原说明 ---
Faithfulness follows because `G` is a separator, see
`isSeparator_iff_faithful_preadditiveCoyonedaObj`.
-/
theorem GabrielPopescu.full (G : C) (hG : IsSeparator G) : (preadditiveCoyonedaObj G).Full where
  map_surjective {A B} f := by
    have := (isSeparator_iff_epi G).1 hG A
    have h := kernel_ι_d_comp_d hG (𝟙 _) inferInstance f
    simp only [ModuleCat.hom_id, LinearMap.id_coe, id_eq, d] at h
    refine ⟨epiDesc _ _ h, ?_⟩
    ext q
    simpa [-comp_epiDesc] using! Sigma.ι _ q ≫= comp_epiDesc _ _ h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.preservesInjectiveObjects*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.GabrielPopescu`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [CategoryTheory.IsGrothendieckAbelian.{v, v, u} C] (G : C),
   CategoryTheory.IsSeparator G → (CategoryTheory.preadditiveCoyonedaObj G).Pres
ervesInjectiveObjects
参数：G : C；CategoryTheory.preadditiveCoyonedaObj G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.injective_iff_injective_object`：injective_iff_injective_object : 
Module.Injective R M ↔ CategoryTheory.Injective (ModuleCat.of R M)
· 使用定理 `Module.Baer.injective`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst
_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q],   Module.Baer R Q → Module.In
jective R Q
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasCoproductsOfShape_of_hasCoproducts`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproduc
ts C] (J : Type w),   CategoryTheory.Limits.HasCo…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.GabrielPopescuAux.exists_d_comp_eq_
d`：exists_d_comp_eq_d {G : C} (hG : IsSeparator G) {A} (B : C) [Injective B] {M 
: ModuleCat (End G)ᵐᵒᵖ} (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A…
· 使用定理 `ModuleCat.mono_iff_injective`：mono_iff_injective : Mono f ↔ Function.Inj
ective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
-/
theorem GabrielPopescu.preservesInjectiveObjects (G : C) (hG : IsSeparator G) :
    (preadditiveCoyonedaObj G).PreservesInjectiveObjects where
  injective_obj {B} hB := by
    rw [← Module.injective_iff_injective_object]
    simp only [preadditiveCoyonedaObj_obj_carrier]
    refine Module.Baer.injective (fun M g => ?_)
    have h := exists_d_comp_eq_d hG B (ModuleCat.ofHom
      ⟨⟨fun i => i.1.unop, by cat_disch⟩, by cat_disch⟩) ?_ (ModuleCat.ofHom g)
    · obtain ⟨l, hl⟩ := h
      refine ⟨((preadditiveCoyonedaObj G).map l).hom ∘ₗ
        (Preadditive.homSelfLinearEquivEndMulOpposite G).symm.toLinearMap, ?_⟩
      intro f hf
      simpa [d] using! Sigma.ι _ ⟨f, hf⟩ ≫= hl
    · rw [ModuleCat.mono_iff_injective]
      cat_disch

/-- `tensorObj G` is left exact: it is additive and preserves monomorphisms and cokernels,
so it preserves homology and therefore finite limits. -/
/-
**CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.preservesFiniteLimits** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.GabrielPopescu`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.IsGrothendieckAbelian.{v, v, u} C]
 (G : C),   CategoryTheory.IsSeparator G →     CategoryTheory.Limits.PreservesFi
niteLimits (CategoryTheory.IsGrothendieckAbelian.tensorObj G)
参数：G : C；CategoryTheory.IsGrothendieckAbelian.tensorObj G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.preservesInjectiveOb
jects`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Catego
ryTheory.Abelian C]   [CategoryTheory.IsGrothendieckAbelian.{v, v, …
· 使用定理 `CategoryTheory.Functor.preservesMonomorphisms_of_adjunction_of_preserves
InjectiveObjects`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D
 : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.En…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_initial_objec
t`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [in
st_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `ModuleCat.instHasZeroObject`：∀ {R : Type u} [inst : Ring R], CategoryThe
ory.Limits.HasZeroObject (ModuleCat R)
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.instIsLeftAdjointModuleCatMulOpposi
teEndTensorObj`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1
 : CategoryTheory.Abelian C]   [inst_2 : CategoryTheory.IsGrothendieckAbelia…
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoprod
ucts`：preservesBinaryBiproducts_of_preservesBinaryCoproducts [PreservesColimitsO
fShape (Discrete WalkingPair) F] : PreservesBinaryBiproducts F whe…
· 使用定理 `CategoryTheory.Functor.additive_of_preservesBinaryBiproducts`：additive_o
f_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F] [
PreservesBinaryBiproducts F] : Additive F where ma…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Functor.preservesHomology_of_preservesMonos_and_cokernels
`：preservesHomology_of_preservesMonos_and_cokernels [PreservesZeroMorphisms L] [
PreservesMonomorphisms L] [forall {X Y} (f : X ⟶ Y), Preserves…
· 使用引理 `CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology`：prese
rvesFiniteLimits_of_preservesHomology [HasFiniteProducts C] [HasKernels C] : Pre
servesFiniteLimits F
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasCountableProducts`：∀ (C : 
Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.H
asCountableProducts C],   CategoryTheory.Limits.HasFi…
· 使用定理 `CategoryTheory.Limits.hasCountableProducts_of_hasCountableLimits`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.
HasCountableLimits C],   CategoryTheory.Limits.HasCoun…
· 使用定理 `CategoryTheory.Limits.hasCountableLimits_of_hasLimits`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasLimits C
],   CategoryTheory.Limits.HasCountableLimi…
· 使用定理 `ModuleCat.hasLimits'`：∀ {R : Type u} [inst : Ring R], CategoryTheory.Lim
its.HasLimits (ModuleCat R)
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C

--- 原说明 ---
`tensorObj G` is left exact: it is additive and preserves monomorphisms and coke
rnels,
so it preserves homology and therefore finite limits.
-/
theorem GabrielPopescu.preservesFiniteLimits (G : C) (hG : IsSeparator G) :
    PreservesFiniteLimits (tensorObj G) := by
  have := preservesInjectiveObjects G hG
  have : (tensorObj G).PreservesMonomorphisms :=
    (tensorObj G).preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
      (tensorObjPreadditiveCoyonedaObjAdjunction G)
  have : PreservesBinaryBiproducts (tensorObj G) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (tensorObj G).Additive := Functor.additive_of_preservesBinaryBiproducts _
  have : (tensorObj G).PreservesHomology :=
    (tensorObj G).preservesHomology_of_preservesMonos_and_cokernels
  exact (tensorObj G).preservesFiniteLimits_of_preservesHomology

end CategoryTheory.IsGrothendieckAbelian

