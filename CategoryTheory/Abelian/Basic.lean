/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Johan Commelin, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Abelian.NonPreadditive

/-!
# Abelian categories

This file contains the definition and basic properties of abelian categories.

There are many definitions of abelian category. Our definition is as follows:
A category is called abelian if it is preadditive,
has finite products, kernels, and cokernels,
and if every monomorphism and epimorphism is normal.

It should be noted that if we also assume finite coproducts, then preadditivity is
actually a consequence of the other properties, as we show in
`Mathlib/CategoryTheory/Abelian/NonPreadditive.lean`. However, this fact is of little practical
relevance, since essentially all interesting abelian categories come with a
preadditive structure. In this way, by requiring preadditivity, we allow the
user to pass in the "native" preadditive structure for the specific category they are
working with.

## Main definitions

* `Abelian` is the type class indicating that a category is abelian. It extends `Preadditive`.
* `Abelian.image f` is `kernel (cokernel.π f)`, and
* `Abelian.coimage f` is `cokernel (kernel.ι f)`.

## Main results

* In an abelian category, mono + epi = iso.
* If `f : X ⟶ Y`, then the map `factorThruImage f : X ⟶ image f` is an epimorphism, and the map
  `factorThruCoimage f : coimage f ⟶ Y` is a monomorphism.
* Factoring through the image and coimage is a strong epi-mono factorisation. This means that
  * every abelian category has images. We provide the isomorphism
    `imageIsoImage : abelian.image f ≅ limits.image f`.
  * the canonical morphism `coimageImageComparison : coimage f ⟶ image f`
    is an isomorphism.
* We provide the alternate characterisation of an abelian category as a category with
  (co)kernels and finite products, and in which the canonical coimage-image comparison morphism
  is always an isomorphism.
* Every epimorphism is a cokernel of its kernel. Every monomorphism is a kernel of its cokernel.
* The pullback of an epimorphism is an epimorphism. The pushout of a monomorphism is a monomorphism.
  (This is not to be confused with the fact that the pullback of a monomorphism is a monomorphism,
  which is true in any category).

## Implementation notes

The typeclass `Abelian` does not extend `NonPreadditiveAbelian`,
to avoid having to deal with comparing the two `HasZeroMorphisms` instances
(one from `Preadditive` in `Abelian`, and the other a field of `NonPreadditiveAbelian`).
As a consequence, at the beginning of this file we trivially build
a `NonPreadditiveAbelian` instance from an `Abelian` instance,
and use this to restate a number of theorems,
in each case just reusing the proof from `Mathlib/CategoryTheory/Abelian/NonPreadditive.lean`.

We don't show this yet, but abelian categories are finitely complete and finitely cocomplete.
However, the limits we can construct at this level of generality will most likely be less nice than
the ones that can be created in specific applications. For this reason, we adopt the following
convention:

* If the statement of a theorem involves limits, the existence of these limits should be made an
  explicit typeclass parameter.
* If a limit only appears in a proof, but not in the statement of a theorem, the limit should not
  be a typeclass parameter, but instead be created using `Abelian.hasPullbacks` or a similar
  definition.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
* [P. Aluffi, *Algebra: Chapter 0*][aluffi2016]

-/

@[expose] public section


noncomputable section

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (C)

/-- A (preadditive) category `C` is called abelian if it has all finite products,
all kernels and cokernels, and if every monomorphism is the kernel of some morphism
and every epimorphism is the cokernel of some morphism.

(This definition implies the existence of zero objects:
finite products give a terminal object, and in a preadditive category
any terminal object is a zero object.)
-/
@[wikidata Q318737]
/-
**CategoryTheory.Abelian** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (preadditive) category `C` is called abelian if it has all finite products,
all kernels and cokernels, and if every monomorphism is the kernel of some morph
ism
and every epimorphism is the cokernel of some morphism.

(This definition implies the existence of zero objects:
finite products give a terminal object, and in a preadditive category
any terminal object is a zero object.)
-/
class Abelian extends Preadditive C, IsNormalMonoCategory C, IsNormalEpiCategory C where
  [has_finite_products : HasFiniteProducts C]
  [has_kernels : HasKernels C]
  [has_cokernels : HasCokernels C]

-- These instances should have a lower priority, or typeclass search times out.
attribute [instance 100] Abelian.has_finite_products
attribute [instance 100] Abelian.has_kernels Abelian.has_cokernels

end CategoryTheory

open CategoryTheory

/-!
We begin by providing an alternative constructor:
a preadditive category with kernels, cokernels, and finite products,
in which the coimage-image comparison morphism is always an isomorphism,
is an abelian category.
-/


namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [Limits.HasKernels C] [Limits.HasCokernels C]

namespace OfCoimageImageComparisonIsIso

/-- The factorisation of a morphism through its abelian image. -/
@[simps]
/-
**CategoryTheory.Abelian.OfCoimageImageComparisonIsIso.imageMonoFactorisation** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian.OfCoimageImageComparisonIsIso`。
形式化陈述：imageMonoFactorisation {X Y : C} (f : X ⟶ Y) : MonoFactorisation f where I
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The factorisation of a morphism through its abelian image.
-/
def imageMonoFactorisation {X Y : C} (f : X ⟶ Y) : MonoFactorisation f where
  I := Abelian.image f
  m := kernel.ι _
  m_mono := inferInstance
  e := kernel.lift _ f (cokernel.condition _)
  fac := kernel.lift_ι _ _ _

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.OfCoimageImageComparisonIsIso.imageMonoFactorisation_e'
** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Abelian.OfCoimageImageComparisonIsIso
`。
形式化陈述：imageMonoFactorisation_e' {X Y : C} (f : X ⟶ Y) : (imageMonoFactorisation 
f).e = cokernel.π _ ≫ Abelian.coimageImageComparison f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
] {X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageMonoFactorisation_e' {X Y : C} (f : X ⟶ Y) :
    (imageMonoFactorisation f).e = cokernel.π _ ≫ Abelian.coimageImageComparison f := by
  dsimp
  ext
  simp only [Abelian.coimageImageComparison, Category.assoc,
    cokernel.π_desc_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- If the coimage-image comparison morphism for a morphism `f` is an isomorphism,
we obtain an image factorisation of `f`. -/
/-
**CategoryTheory.Abelian.OfCoimageImageComparisonIsIso.imageFactorisation** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian.OfCoimageImageComparisonIsIso`。
形式化陈述：imageFactorisation {X Y : C} (f : X ⟶ Y) [IsIso (Abelian.coimageImageCompa
rison f)] : ImageFactorisation f where F
参数：f : X ⟶ Y；Abelian.coimageImageComparison f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the coimage-image comparison morphism for a morphism `f` is an isomorphism,
we obtain an image factorisation of `f`.
-/
def imageFactorisation {X Y : C} (f : X ⟶ Y) [IsIso (Abelian.coimageImageComparison f)] :
    ImageFactorisation f where
  F := imageMonoFactorisation f
  isImage :=
    { lift := fun F => inv (Abelian.coimageImageComparison f) ≫ cokernel.desc _ F.e F.kernel_ι_comp
      lift_fac := fun F => by
        rw [imageMonoFactorisation_m]
        simp only [Category.assoc]
        rw [IsIso.inv_comp_eq]
        ext
        simp }

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.OfCoimageImageComparisonIsIso.** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.Abelian.OfCoimageImageComparisonIsIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] {X Y : C} (f : X ⟶ Y) [Mono f]
    [IsIso (Abelian.coimageImageComparison f)] : IsIso (imageMonoFactorisation f).e := by
  rw [imageMonoFactorisation_e']
  exact IsIso.comp_isIso

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.OfCoimageImageComparisonIsIso.** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.Abelian.OfCoimageImageComparisonIsIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] {X Y : C} (f : X ⟶ Y) [Epi f] : IsIso (imageMonoFactorisation f).m := by
  dsimp
  infer_instance

variable [∀ {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f)]

/-- A category in which coimage-image comparisons are all isomorphisms has images. -/
/-
**CategoryTheory.Abelian.OfCoimageImageComparisonIsIso.hasImages** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Abelian.OfCoimageImageComparisonIsIso`。
形式化陈述：hasImages : HasImages C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…

--- 原说明 ---
A category in which coimage-image comparisons are all isomorphisms has images.
-/
theorem hasImages : HasImages C :=
  { has_image := fun {_} {_} f => { exists_image := ⟨imageFactorisation f⟩ } }

variable [Limits.HasFiniteProducts C]

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

set_option backward.isDefEq.respectTransparency false in
/-- A category with finite products in which coimage-image comparisons are all isomorphisms
is a normal mono category.
-/
/-
**CategoryTheory.Abelian.OfCoimageImageComparisonIsIso.isNormalMonoCategory** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.OfCoimageImageComparisonIsIso`。
形式化陈述：isNormalMonoCategory : IsNormalMonoCategory C where normalMonoOfMono f m
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Abelian.OfCoimageImageComparisonIsIso.instIsIsoEImageMono
FactorisationOfHasZeroObjectOfMonoOfCoimageImageComparison`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [
inst_2 : CategoryTheory.Limits.HasKernel…
· 使用定理 `CategoryTheory.Limits.hasZeroObject_of_hasFiniteBiproducts`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   [CategoryTheory.Limits.HasFin…
· 使用定理 `CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadd
itive C]   [CategoryTheory.Limits.HasFiniteProducts …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.IsIso.inv_comp_eq`：inv_comp_eq (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.fac`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.Lim
its.MonoFactorisation f), Categor…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.KernelFork.ι_ofι`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y P : C}   (f : X ⟶ Y) (ι : …

--- 原说明 ---
A category with finite products in which coimage-image comparisons are all isomo
rphisms
is a normal mono category.
-/
lemma isNormalMonoCategory : IsNormalMonoCategory C where
  normalMonoOfMono f m := ⟨{
      Z := _
      g := cokernel.π f
      w := by simp
      isLimit := by
        haveI : Limits.HasImages C := hasImages
        haveI : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
        haveI : HasZeroObject C := Limits.hasZeroObject_of_hasFiniteBiproducts _
        have aux (s : KernelFork (cokernel.π f)) :
            (limit.lift (parallelPair (cokernel.π f) 0) s ≫ inv (imageMonoFactorisation f).e) ≫
            Fork.ι (KernelFork.ofι _ (cokernel.condition f)) = Fork.ι s := ?_
        · refine isLimitAux _ (fun A => limit.lift _ _ ≫ inv (imageMonoFactorisation f).e) aux ?_
          intro A g hg
          rw [KernelFork.ι_ofι] at hg
          rw [← cancel_mono f, hg, ← aux, KernelFork.ι_ofι]
        · simp only [KernelFork.ι_ofι, Category.assoc]
          convert! limit.lift_π s WalkingParallelPair.zero using 2
          rw [IsIso.inv_comp_eq, eq_comm]
          exact (imageMonoFactorisation f).fac }⟩

set_option backward.isDefEq.respectTransparency false in
/-- A category with finite products in which coimage-image comparisons are all isomorphisms
is a normal epi category.
-/
/-
**CategoryTheory.Abelian.OfCoimageImageComparisonIsIso.isNormalEpiCategory** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.OfCoimageImageComparisonIsIso`。
形式化陈述：isNormalEpiCategory : IsNormalEpiCategory C where normalEpiOfEpi f m
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Abelian.OfCoimageImageComparisonIsIso.instIsIsoMImageMono
FactorisationOfHasZeroObjectOfEpi`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.L
imits.HasKernel…
· 使用定理 `CategoryTheory.Limits.hasZeroObject_of_hasFiniteBiproducts`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   [CategoryTheory.Limits.HasFin…
· 使用定理 `CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadd
itive C]   [CategoryTheory.Limits.HasFiniteProducts …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.IsIso.comp_inv_eq`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `CategoryTheory.Abelian.OfCoimageImageComparisonIsIso.imageMonoFactorisat
ion_e'`：imageMonoFactorisation_e' {X Y : C} (f : X ⟶ Y) : (imageMonoFactorisatio
n f).e = cokernel.π _ ≫ Abelian.coimageImageComparison f
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.fac`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.Lim
its.MonoFactorisation f), Categor…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.CokernelCofork.π_ofπ`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
 {X Y P : C}   (f : X ⟶ Y) (π : …

--- 原说明 ---
A category with finite products in which coimage-image comparisons are all isomo
rphisms
is a normal epi category.
-/
lemma isNormalEpiCategory : IsNormalEpiCategory C where
  normalEpiOfEpi f m := ⟨{
      W := kernel f
      g := kernel.ι _
      w := kernel.condition _
      isColimit := by
        haveI : Limits.HasImages C := hasImages
        haveI : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
        haveI : HasZeroObject C := Limits.hasZeroObject_of_hasFiniteBiproducts _
        have aux (s : CokernelCofork (kernel.ι f)) :
            Cofork.π (CokernelCofork.ofπ _ (kernel.condition f)) ≫
              inv (imageMonoFactorisation f).m ≫ inv (Abelian.coimageImageComparison f) ≫
                colimit.desc (parallelPair (kernel.ι f) 0) s = Cofork.π s := ?_
        · refine isColimitAux _ (fun A => inv (imageMonoFactorisation f).m ≫
                  inv (Abelian.coimageImageComparison f) ≫ colimit.desc _ _) aux ?_
          intro A g hg
          rw [CokernelCofork.π_ofπ] at hg
          rw [← cancel_epi f, hg, ← aux, CokernelCofork.π_ofπ]
        · simp only [CokernelCofork.π_ofπ, ← Category.assoc]
          convert! colimit.ι_desc s WalkingParallelPair.one using 2
          rw [IsIso.comp_inv_eq, IsIso.comp_inv_eq, eq_comm, ← imageMonoFactorisation_e']
          exact (imageMonoFactorisation f).fac }⟩

end OfCoimageImageComparisonIsIso

variable [∀ {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f)]
  [Limits.HasFiniteProducts C]

attribute [local instance] OfCoimageImageComparisonIsIso.isNormalMonoCategory

attribute [local instance] OfCoimageImageComparisonIsIso.isNormalEpiCategory

/-- A preadditive category with kernels, cokernels, and finite products,
in which the coimage-image comparison morphism is always an isomorphism,
is an abelian category. -/
@[stacks 0109
"The Stacks project uses this characterisation at the definition of an abelian category.",
  instance_reducible]
/-
**CategoryTheory.Abelian.ofCoimageImageComparisonIsIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Abelian`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.HasKernel
s C] →         [inst_3 : CategoryTheory.Limits.HasCokernels C] →           [∀ {X
 Y : C} (f : X ⟶ Y), CategoryTheory.IsIso (CategoryTheory.Abelian.coimageImageCo
mparison f)] →             [CategoryTheory.Limits.HasFiniteProducts C] → Categor
yTheory.Abelian C
参数：f : X ⟶ Y；CategoryTheory.Abelian.coimageImageComparison f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.OfCoimageImageComparisonIsIso.isNormalMonoCategor
y`：isNormalMonoCategory : IsNormalMonoCategory C where normalMonoOfMono f m
· 使用引理 `CategoryTheory.Abelian.OfCoimageImageComparisonIsIso.isNormalEpiCategory
`：isNormalEpiCategory : IsNormalEpiCategory C where normalEpiOfEpi f m
-/
def ofCoimageImageComparisonIsIso : Abelian C where

end CategoryTheory.Abelian

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

-- Porting note: this should be an instance,
-- but triggers https://github.com/leanprover/lean4/issues/2055
-- (this is still the case despite that issue being closed now).
-- We set it as a local instance instead.
-- instance (priority := 100)
-- Turning it into a global instance breaks `Mathlib/Algebra/Category/ModuleCat/Sheaf/Free.lean`.
/-- An abelian category has finite biproducts. -/
/-
**CategoryTheory.Abelian.hasFiniteBiproducts** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Abelian`。
形式化陈述：hasFiniteBiproducts : HasFiniteBiproducts C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadd
itive C]   [CategoryTheory.Limits.HasFiniteProducts …
· 使用定理 `CategoryTheory.Abelian.has_finite_products`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory
.Limits.HasFiniteProducts C

--- 原说明 ---
An abelian category has finite biproducts.
-/
theorem hasFiniteBiproducts : HasFiniteBiproducts C :=
  Limits.HasFiniteBiproducts.of_hasFiniteProducts

attribute [local instance] hasFiniteBiproducts
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasBinaryBiproducts : HasBinaryBiproducts C :=
  Limits.hasBinaryBiproducts_of_finite_biproducts _
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasZeroObject : HasZeroObject C :=
  hasZeroObject_of_hasInitial_object

section ToNonPreadditiveAbelian

/-- Every abelian category is, in particular, `NonPreadditiveAbelian`. -/
@[instance_reducible]
/-
**CategoryTheory.Abelian.nonPreadditiveAbelian** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Abelian`。
形式化陈述：nonPreadditiveAbelian : NonPreadditiveAbelian C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Abelian.has_finite_products`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory
.Limits.HasFiniteProducts C

--- 原说明 ---
Every abelian category is, in particular, `NonPreadditiveAbelian`.
-/
def nonPreadditiveAbelian : NonPreadditiveAbelian C :=
  { ‹Abelian C› with }

end ToNonPreadditiveAbelian

section

/-! We now promote some instances that were constructed using `nonPreadditiveAbelian`. -/


attribute [local instance] nonPreadditiveAbelian

variable {P Q : C} (f : P ⟶ Q)

/-- The map `p : P ⟶ image f` is an epimorphism -/
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `p : P ⟶ image f` is an epimorphism
-/
instance : Epi (Abelian.factorThruImage f) := by infer_instance
/-
**CategoryTheory.Abelian.isIso_factorThruImage** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Abelian`。
形式化陈述：isIso_factorThruImage [Mono f] : IsIso (Abelian.factorThruImage f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_cokernels`：∀ {C : Type u} {inst
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelia
n C],   CategoryTheory.Limits.HasCokerne…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_kernels`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelian 
C],   CategoryTheory.Limits.HasKernels…
-/
instance isIso_factorThruImage [Mono f] : IsIso (Abelian.factorThruImage f) := by infer_instance

/-- The canonical morphism `i : coimage f ⟶ Q` is a monomorphism -/
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `i : coimage f ⟶ Q` is a monomorphism
-/
instance : Mono (Abelian.factorThruCoimage f) := by infer_instance
/-
**CategoryTheory.Abelian.isIso_factorThruCoimage** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Abelian`。
形式化陈述：isIso_factorThruCoimage [Epi f] : IsIso (Abelian.factorThruCoimage f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_kernels`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelian 
C],   CategoryTheory.Limits.HasKernels…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_cokernels`：∀ {C : Type u} {inst
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelia
n C],   CategoryTheory.Limits.HasCokerne…
-/
instance isIso_factorThruCoimage [Epi f] : IsIso (Abelian.factorThruCoimage f) := by infer_instance

end

section Factor

attribute [local instance] nonPreadditiveAbelian

variable {P Q : C} (f : P ⟶ Q)

section

/-
**CategoryTheory.Abelian.mono_of_kernel_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono_of_kernel_ι_eq_zero (h : kernel.ι f = 0) : Mono f :=
  mono_of_kernel_zero h
/-
**CategoryTheory.Abelian.epi_of_cokernel_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem epi_of_cokernel_π_eq_zero (h : cokernel.π f = 0) : Epi f :=
  epi_of_cokernel_zero h

end

section

variable {f}

/-
**CategoryTheory.Abelian.image_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Abelia
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_ι_comp_eq_zero {R : C} {g : Q ⟶ R} (h : f ≫ g = 0) : Abelian.image.ι f ≫ g = 0 :=
  zero_of_epi_comp (Abelian.factorThruImage f) <| by simp [h]
/-
**CategoryTheory.Abelian.comp_coimage_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_coimage_π_eq_zero {R : C} {g : Q ⟶ R} (h : f ≫ g = 0) : f ≫ Abelian.coimage.π g = 0 :=
  zero_of_comp_mono (Abelian.factorThruCoimage g) <| by simp [h]

end

/-- Factoring through the image is a strong epi-mono factorisation. -/
@[simps]
/-
**CategoryTheory.Abelian.imageStrongEpiMonoFactorisation** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Abelian`。
形式化陈述：imageStrongEpiMonoFactorisation : StrongEpiMonoFactorisation f where I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Factoring through the image is a strong epi-mono factorisation.
-/
def imageStrongEpiMonoFactorisation : StrongEpiMonoFactorisation f where
  I := Abelian.image f
  m := image.ι f
  m_mono := by infer_instance
  e := Abelian.factorThruImage f
  e_strong_epi := strongEpi_of_epi _

/-- Factoring through the coimage is a strong epi-mono factorisation. -/
@[simps]
/-
**CategoryTheory.Abelian.coimageStrongEpiMonoFactorisation** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Abelian`。
形式化陈述：coimageStrongEpiMonoFactorisation : StrongEpiMonoFactorisation f where I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Factoring through the coimage is a strong epi-mono factorisation.
-/
def coimageStrongEpiMonoFactorisation : StrongEpiMonoFactorisation f where
  I := Abelian.coimage f
  m := Abelian.factorThruCoimage f
  m_mono := by infer_instance
  e := coimage.π f
  e_strong_epi := strongEpi_of_epi _

end Factor

section HasStrongEpiMonoFactorisations

/-- An abelian category has strong epi-mono factorisations. -/
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abelian category has strong epi-mono factorisations.
-/
instance (priority := 100) : HasStrongEpiMonoFactorisations C :=
  HasStrongEpiMonoFactorisations.mk fun f => imageStrongEpiMonoFactorisation f

-- In particular, this means that it has well-behaved images.
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : HasImages C := by infer_instance
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : HasImageMaps C := by infer_instance

end HasStrongEpiMonoFactorisations

section Images

variable {X Y : C} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-- The coimage-image comparison morphism is always an isomorphism in an abelian category.
See `CategoryTheory.Abelian.ofCoimageImageComparisonIsIso` for the converse.
-/
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coimage-image comparison morphism is always an isomorphism in an abelian cat
egory.
See `CategoryTheory.Abelian.ofCoimageImageComparisonIsIso` for the converse.
-/
instance : IsIso (coimageImageComparison f) := by
  convert!
    Iso.isIso_hom
      (IsImage.isoExt (coimageStrongEpiMonoFactorisation f).toMonoIsImage
        (imageStrongEpiMonoFactorisation f).toMonoIsImage)
  ext
  change _ = _ ≫ (imageStrongEpiMonoFactorisation f).m
  simp [-imageStrongEpiMonoFactorisation_m]

/-- There is a canonical isomorphism between the abelian coimage and the abelian image of a
    morphism. -/
/-
**CategoryTheory.Abelian.coimageIsoImage** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Abelian`。
形式化陈述：coimageIsoImage : Abelian.coimage f ≅ Abelian.image f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.instIsIsoCoimageImageComparison`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {X 
Y : C} (f : X ⟶ Y),   CategoryTheory.IsIso (…

--- 原说明 ---
There is a canonical isomorphism between the abelian coimage and the abelian ima
ge of a
    morphism.
-/
abbrev coimageIsoImage : Abelian.coimage f ≅ Abelian.image f :=
  asIso (coimageImageComparison f)

/-- There is a canonical isomorphism between the abelian coimage and the categorical image of a
    morphism. -/
/-
**CategoryTheory.Abelian.coimageIsoImage'** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Abelian`。
形式化陈述：coimageIsoImage' : Abelian.coimage f ≅ image f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a canonical isomorphism between the abelian coimage and the categorical
 image of a
    morphism.
-/
abbrev coimageIsoImage' : Abelian.coimage f ≅ image f :=
  IsImage.isoExt (coimageStrongEpiMonoFactorisation f).toMonoIsImage (Image.isImage f)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.coimageIsoImage'_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Abelian`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {X Y : C} (f : X ⟶ Y),   (CategoryTheory.Abelian.coimageIsoIm
age' f).hom =     CategoryTheory.Limits.cokernel.desc (CategoryTheory.Limits.ker
nel.ι f) (CategoryTheory.Limits.factorThruImage f) ⋯
参数：f : X ⟶ Y；CategoryTheory.Abelian.coimageIsoImage' f；CategoryTheory.Limits.ker
nel.ι f；CategoryTheory.Limits.factorThruImage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsImage.isoExt_hom`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   {F F' : CategoryTheory.Limits
.MonoFactorisation f} (hF : Ca…
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsImage.lift_ι`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] {F : CategoryTh…
· 使用定理 `CategoryTheory.Abelian.coimageStrongEpiMonoFactorisation_m`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]
 {P Q : C} (f : P ⟶ Q),   (CategoryTheory.Abelia…
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coimageIsoImage'_hom :
    (coimageIsoImage' f).hom =
      cokernel.desc _ (factorThruImage f) (by simp [← cancel_mono (Limits.image.ι f)]) := by
  ext
  simp only [← cancel_mono (Limits.image.ι f), IsImage.isoExt_hom, cokernel.π_desc,
    Category.assoc, IsImage.lift_ι, coimageStrongEpiMonoFactorisation_m,
    Limits.image.fac]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.factorThruImage_comp_coimageIsoImage'_inv** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Abelian`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (
CategoryTheory.Limits.factorThruImage f)       (CategoryTheory.Abelian.coimageIs
oImage' f).inv =     CategoryTheory.Limits.cokernel.π (CategoryTheory.Limits.ker
nel.ι f)
参数：f : X ⟶ Y；CategoryTheory.Limits.factorThruImage f；CategoryTheory.Abelian.coim
ageIsoImage' f；CategoryTheory.Limits.kernel.ι f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsImage.isoExt_inv`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   {F F' : CategoryTheory.Limits
.MonoFactorisation f} (hF : Ca…
· 使用定理 `CategoryTheory.Limits.image.fac_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…
· 使用定理 `CategoryTheory.Abelian.coimageStrongEpiMonoFactorisation_e`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]
 {P Q : C} (f : P ⟶ Q),   (CategoryTheory.Abelia…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThruImage_comp_coimageIsoImage'_inv :
    factorThruImage f ≫ (coimageIsoImage' f).inv = cokernel.π _ := by
  simp only [IsImage.isoExt_inv, image.isImage_lift, image.fac_lift,
    coimageStrongEpiMonoFactorisation_e]

variable {Z : C} (g : Y ⟶ Z)
/-
**CategoryTheory.Abelian.image.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma image.ι_comp_eq_zero : image.ι f ≫ g = 0 ↔ f ≫ g = 0 := by
  simp [← cancel_epi (Abelian.factorThruImage _)]
/-
**CategoryTheory.Abelian.coimage.comp_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coimage.comp_π_eq_zero : f ≫ coimage.π g = 0 ↔ f ≫ g = 0 := by
  simp [← cancel_mono (Abelian.factorThruCoimage _)]

/-- `Abelian.image` as a functor from the arrow category. -/
@[simps]
/-
**CategoryTheory.Abelian.im** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian`。
形式化陈述：im : Arrow C ⥤ C where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Abelian.image` as a functor from the arrow category.
-/
def im : Arrow C ⥤ C where
  obj f := Abelian.image f.hom
  map {f g} u := kernel.lift _ (Abelian.image.ι f.hom ≫ u.right) <| by simp [← Arrow.w_assoc u]

/-- `Abelian.coimage` as a functor from the arrow category. -/
@[simps]
/-
**CategoryTheory.Abelian.coim** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian`
。
形式化陈述：coim : Arrow C ⥤ C where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Abelian.coimage` as a functor from the arrow category.
-/
def coim : Arrow C ⥤ C where
  obj f := Abelian.coimage f.hom
  map {f g} u := cokernel.desc _ (u.left ≫ Abelian.coimage.π g.hom) <| by
    simp [← Category.assoc, coimage.comp_π_eq_zero]; simp

set_option backward.defeqAttrib.useBackward true in
/-- The image and coimage of an arrow are naturally isomorphic. -/
@[simps!]
/-
**CategoryTheory.Abelian.coimIsoIm** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abe
lian`。
形式化陈述：coimIsoIm : coim (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image and coimage of an arrow are naturally isomorphic.
-/
def coimIsoIm : coim (C := C) ≅ im :=
  NatIso.ofComponents fun _ ↦ Abelian.coimageIsoImage _

/-- There is a canonical isomorphism between the abelian image and the categorical image of a
    morphism. -/
/-
**CategoryTheory.Abelian.imageIsoImage** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Abelian`。
形式化陈述：imageIsoImage : Abelian.image f ≅ image f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a canonical isomorphism between the abelian image and the categorical i
mage of a
    morphism.
-/
abbrev imageIsoImage : Abelian.image f ≅ image f :=
  IsImage.isoExt (imageStrongEpiMonoFactorisation f).toMonoIsImage (Image.isImage f)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.imageIsoImage_hom_comp_image_** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imageIsoImage_hom_comp_image_ι : (imageIsoImage f).hom ≫ Limits.image.ι _ = kernel.ι _ := by
  simp only [IsImage.isoExt_hom, IsImage.lift_ι, imageStrongEpiMonoFactorisation_m]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.imageIsoImage_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Abelian`。
形式化陈述：imageIsoImage_inv : (imageIsoImage f).inv = kernel.lift _ (Limits.image.ι 
f) (by simp [← cancel_epi (factorThruImage f)])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.image.ext`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f] {W : C} {g h : …
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.NormalMonoCategory.hasEqualizers`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   [CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Abelian.has_finite_products`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory
.Limits.HasFiniteProducts C
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsImage.isoExt_inv`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   {F F' : CategoryTheory.Limits
.MonoFactorisation f} (hF : Ca…
· 使用定理 `CategoryTheory.Limits.image.isImage_lift`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasImage f] (F : CategoryTh…
· 使用定理 `CategoryTheory.Limits.image.fac_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…
· 使用定理 `CategoryTheory.Abelian.imageStrongEpiMonoFactorisation_e`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {
P Q : C} (f : P ⟶ Q),   (CategoryTheory.Abelia…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.equalizer_as_kernel`：equalizer_as_kernel : equaliz
er.ι f 0 = kernel.ι f
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
-/
theorem imageIsoImage_inv :
    (imageIsoImage f).inv =
      kernel.lift _ (Limits.image.ι f) (by simp [← cancel_epi (factorThruImage f)]) := by
  ext
  rw [IsImage.isoExt_inv, image.isImage_lift, Limits.image.fac_lift,
    imageStrongEpiMonoFactorisation_e, Category.assoc, kernel.lift_ι, equalizer_as_kernel,
    kernel.lift_ι, Limits.image.fac]

end Images

section CokernelOfKernel

variable {X Y : C} {f : X ⟶ Y}

attribute [local instance] nonPreadditiveAbelian

/-- In an abelian category, an epi is the cokernel of its kernel. More precisely:
    If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` is a cokernel
    of `fork.ι s`. -/
/-
**CategoryTheory.Abelian.epiIsCokernelOfKernel** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Abelian`。
形式化陈述：epiIsCokernelOfKernel [Epi f] (s : Fork f 0) (h : IsLimit s) : IsColimit (
CokernelCofork.ofπ f (KernelFork.condition s))
参数：s : Fork f 0；h : IsLimit s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In an abelian category, an epi is the cokernel of its kernel. More precisely:
    If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` 
is a cokernel
    of `fork.ι s`.
-/
def epiIsCokernelOfKernel [Epi f] (s : Fork f 0) (h : IsLimit s) :
    IsColimit (CokernelCofork.ofπ f (KernelFork.condition s)) :=
  NonPreadditiveAbelian.epiIsCokernelOfKernel s h

/-- In an abelian category, a mono is the kernel of its cokernel. More precisely:
    If `f` is a monomorphism and `s` is some colimit cokernel cocone on `f`, then `f` is a kernel
    of `cofork.π s`. -/
/-
**CategoryTheory.Abelian.monoIsKernelOfCokernel** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Abelian`。
形式化陈述：monoIsKernelOfCokernel [Mono f] (s : Cofork f 0) (h : IsColimit s) : IsLim
it (KernelFork.ofι f (CokernelCofork.condition s))
参数：s : Cofork f 0；h : IsColimit s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In an abelian category, a mono is the kernel of its cokernel. More precisely:
    If `f` is a monomorphism and `s` is some colimit cokernel cocone on `f`, the
n `f` is a kernel
    of `cofork.π s`.
-/
def monoIsKernelOfCokernel [Mono f] (s : Cofork f 0) (h : IsColimit s) :
    IsLimit (KernelFork.ofι f (CokernelCofork.condition s)) :=
  NonPreadditiveAbelian.monoIsKernelOfCokernel s h

variable (f)

/-- In an abelian category, any morphism that turns to zero when precomposed with the kernel of an
    epimorphism factors through that epimorphism. -/
/-
**CategoryTheory.Abelian.epiDesc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abeli
an`。
形式化陈述：epiDesc [Epi f] {T : C} (g : X ⟶ T) (hg : kernel.ι f ≫ g = 0) : Y ⟶ T
参数：g : X ⟶ T；hg : kernel.ι f ≫ g = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In an abelian category, any morphism that turns to zero when precomposed with th
e kernel of an
    epimorphism factors through that epimorphism.
-/
def epiDesc [Epi f] {T : C} (g : X ⟶ T) (hg : kernel.ι f ≫ g = 0) : Y ⟶ T :=
  (epiIsCokernelOfKernel _ (limit.isLimit _)).desc (CokernelCofork.ofπ _ hg)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.comp_epiDesc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Abelian`。
形式化陈述：comp_epiDesc [Epi f] {T : C} (g : X ⟶ T) (hg : kernel.ι f ≫ g = 0) : f ≫ e
piDesc f g hg = g
参数：g : X ⟶ T；hg : kernel.ι f ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_kernels`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelian 
C],   CategoryTheory.Limits.HasKernels…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.KernelFork.condition`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
 {X Y : C}   {f : X ⟶ Y} (s : Ca…
-/
theorem comp_epiDesc [Epi f] {T : C} (g : X ⟶ T) (hg : kernel.ι f ≫ g = 0) :
    f ≫ epiDesc f g hg = g :=
  (epiIsCokernelOfKernel _ (limit.isLimit _)).fac (CokernelCofork.ofπ _ hg) WalkingParallelPair.one

/-- In an abelian category, any morphism that turns to zero when postcomposed with the cokernel of a
    monomorphism factors through that monomorphism. -/
/-
**CategoryTheory.Abelian.monoLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abel
ian`。
形式化陈述：monoLift [Mono f] {T : C} (g : T ⟶ Y) (hg : g ≫ cokernel.π f = 0) : T ⟶ X
参数：g : T ⟶ Y；hg : g ≫ cokernel.π f = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In an abelian category, any morphism that turns to zero when postcomposed with t
he cokernel of a
    monomorphism factors through that monomorphism.
-/
def monoLift [Mono f] {T : C} (g : T ⟶ Y) (hg : g ≫ cokernel.π f = 0) : T ⟶ X :=
  (monoIsKernelOfCokernel _ (colimit.isColimit _)).lift (KernelFork.ofι _ hg)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.monoLift_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Abelian`。
形式化陈述：monoLift_comp [Mono f] {T : C} (g : T ⟶ Y) (hg : g ≫ cokernel.π f = 0) : m
onoLift f g hg ≫ f = g
参数：g : T ⟶ Y；hg : g ≫ cokernel.π f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_cokernels`：∀ {C : Type u} {inst
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelia
n C],   CategoryTheory.Limits.HasCokerne…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.CokernelCofork.condition`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   {f : X ⟶ Y} (s : Ca…
-/
theorem monoLift_comp [Mono f] {T : C} (g : T ⟶ Y) (hg : g ≫ cokernel.π f = 0) :
    monoLift f g hg ≫ f = g :=
  (monoIsKernelOfCokernel _ (colimit.isColimit _)).fac (KernelFork.ofι _ hg)
    WalkingParallelPair.zero

section

variable {D : Type*} [Category* D] [HasZeroMorphisms D]

set_option backward.isDefEq.respectTransparency false in
/-- If `F : D ⥤ C` is a functor to an abelian category, `i : X ⟶ Y` is a morphism
admitting a cokernel such that `F` preserves this cokernel and `F.map i` is a mono,
then `F.map X` identifies to the kernel of `F.map (cokernel.π i)`. -/
/-
**CategoryTheory.Abelian.isLimitMapConeOfKernelForkOf** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : D ⥤ C` is a functor to an abelian category, `i : X ⟶ Y` is a morphism
admitting a cokernel such that `F` preserves this cokernel and `F.map i` is a mo
no,
then `F.map X` identifies to the kernel of `F.map (cokernel.π i)`.
-/
noncomputable def isLimitMapConeOfKernelForkOfι
    {X Y : D} (i : X ⟶ Y) [HasCokernel i] (F : D ⥤ C)
    [F.PreservesZeroMorphisms] [Mono (F.map i)]
    [PreservesColimit (parallelPair i 0) F] :
    IsLimit (F.mapCone (KernelFork.ofι i (cokernel.condition i))) := by
  let e : parallelPair (cokernel.π (F.map i)) 0 ≅ parallelPair (cokernel.π i) 0 ⋙ F :=
    parallelPair.ext (Iso.refl _) (asIso (cokernelComparison i F)) (by simp) (by simp)
  refine IsLimit.postcomposeInvEquiv e _ ?_
  let hi := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel (F.map i))
  refine IsLimit.ofIsoLimit hi (Fork.ext (Iso.refl _) ?_)
  change 𝟙 _ ≫ F.map i ≫ 𝟙 _ = F.map i
  rw [Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- If `F : D ⥤ C` is a functor to an abelian category, `p : X ⟶ Y` is a morphism
admitting a kernel such that `F` preserves this kernel and `F.map p` is an epi,
then `F.map Y` identifies to the cokernel of `F.map (kernel.ι p)`. -/
/-
**CategoryTheory.Abelian.isColimitMapCoconeOfCokernelCoforkOf** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : D ⥤ C` is a functor to an abelian category, `p : X ⟶ Y` is a morphism
admitting a kernel such that `F` preserves this kernel and `F.map p` is an epi,
then `F.map Y` identifies to the cokernel of `F.map (kernel.ι p)`.
-/
noncomputable def isColimitMapCoconeOfCokernelCoforkOfπ
    {X Y : D} (p : X ⟶ Y) [HasKernel p] (F : D ⥤ C)
    [F.PreservesZeroMorphisms] [Epi (F.map p)]
    [PreservesLimit (parallelPair p 0) F] :
    IsColimit (F.mapCocone (CokernelCofork.ofπ p (kernel.condition p))) := by
  let e : parallelPair (kernel.ι p) 0 ⋙ F ≅ parallelPair (kernel.ι (F.map p)) 0 :=
    parallelPair.ext (asIso (kernelComparison p F)) (Iso.refl _) (by simp) (by simp)
  refine IsColimit.precomposeInvEquiv e _ ?_
  let hp := Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (F.map p))
  refine IsColimit.ofIsoColimit hp (Cofork.ext (Iso.refl _) ?_)
  change F.map p ≫ 𝟙 _ = 𝟙 _ ≫ F.map p
  rw [Category.comp_id, Category.id_comp]

end

end CokernelOfKernel

section

/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasEqualizers : HasEqualizers C :=
  Preadditive.hasEqualizers_of_hasKernels

/-- Any abelian category has pullbacks -/
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any abelian category has pullbacks
-/
instance (priority := 100) hasPullbacks : HasPullbacks C :=
  hasPullbacks_of_hasBinaryProducts_of_hasEqualizers C

end

section

/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasCoequalizers : HasCoequalizers C :=
  Preadditive.hasCoequalizers_of_hasCokernels

/-- Any abelian category has pushouts -/
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any abelian category has pushouts
-/
instance (priority := 100) hasPushouts : HasPushouts C :=
  hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers C
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasFiniteLimits : HasFiniteLimits C :=
  Limits.hasFiniteLimits_of_hasEqualizers_and_finite_products
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasFiniteColimits : HasFiniteColimits C :=
  Limits.hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end

namespace PullbackToBiproductIsKernel

variable [Limits.HasPullbacks C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

/-! This section contains a slightly technical result about pullbacks and biproducts.
    We will need it in the proof that the pullback of an epimorphism is an epimorphism. -/


/-- The canonical map `pullback f g ⟶ X ⊞ Y` -/
/-
**CategoryTheory.Abelian.PullbackToBiproductIsKernel.pullbackToBiproduct** 是 Mat
hlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Abelian.PullbackToBiproductIsKernel`。
形式化陈述：pullbackToBiproduct : pullback f g ⟶ X ⊞ Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `pullback f g ⟶ X ⊞ Y`
-/
abbrev pullbackToBiproduct : pullback f g ⟶ X ⊞ Y :=
  biprod.lift (pullback.fst f g) (pullback.snd f g)

/-- The canonical map `pullback f g ⟶ X ⊞ Y` induces a kernel cone on the map
    `biproduct X Y ⟶ Z` induced by `f` and `g`. A slightly more intuitive way to think of
    this may be that it induces an equalizer fork on the maps induced by `(f, 0)` and
    `(0, g)`. -/
/-
**CategoryTheory.Abelian.PullbackToBiproductIsKernel.pullbackToBiproductFork** 是
 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Abelian.PullbackToBiproductIsKernel`。
形式化陈述：pullbackToBiproductFork : KernelFork (biprod.desc f (-g))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `pullback f g ⟶ X ⊞ Y` induces a kernel cone on the map
    `biproduct X Y ⟶ Z` induced by `f` and `g`. A slightly more intuitive way to
 think of
    this may be that it induces an equalizer fork on the maps induced by `(f, 0)
` and
    `(0, g)`.
-/
abbrev pullbackToBiproductFork : KernelFork (biprod.desc f (-g)) :=
  KernelFork.ofι (pullbackToBiproduct f g) <| by
    rw [biprod.lift_desc, comp_neg, pullback.condition, add_neg_cancel]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map `pullback f g ⟶ X ⊞ Y` is a kernel of the map induced by
    `(f, -g)`. -/
/-
**CategoryTheory.Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian.PullbackToBiproductIsKernel`。
形式化陈述：isLimitPullbackToBiproduct : IsLimit (pullbackToBiproductFork f g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `pullback f g ⟶ X ⊞ Y` is a kernel of the map induced by
    `(f, -g)`.
-/
def isLimitPullbackToBiproduct : IsLimit (pullbackToBiproductFork f g) :=
  Fork.IsLimit.mk _
    (fun s =>
      pullback.lift (Fork.ι s ≫ biprod.fst) (Fork.ι s ≫ biprod.snd) <|
        sub_eq_zero.1 <| by
          rw [Category.assoc, Category.assoc, ← comp_sub, sub_eq_add_neg, ← comp_neg, ←
            biprod.desc_eq, KernelFork.condition s])
    (fun s => by
      apply biprod.hom_ext <;> rw [Fork.ι_ofι, Category.assoc]
      · rw [biprod.lift_fst, pullback.lift_fst]
      · rw [biprod.lift_snd, pullback.lift_snd])
    fun s m h => by apply pullback.hom_ext <;> simp [← h]

end PullbackToBiproductIsKernel

namespace BiproductToPushoutIsCokernel

variable [Limits.HasPushouts C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

/-- The canonical map `Y ⊞ Z ⟶ pushout f g` -/
/-
**CategoryTheory.Abelian.BiproductToPushoutIsCokernel.biproductToPushout** 是 Mat
hlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Abelian.BiproductToPushoutIsCokernel`。
形式化陈述：biproductToPushout : Y ⊞ Z ⟶ pushout f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `Y ⊞ Z ⟶ pushout f g`
-/
abbrev biproductToPushout : Y ⊞ Z ⟶ pushout f g :=
  biprod.desc (pushout.inl _ _) (pushout.inr _ _)

/-- The canonical map `Y ⊞ Z ⟶ pushout f g` induces a cokernel cofork on the map
    `X ⟶ Y ⊞ Z` induced by `f` and `-g`. -/
/-
**CategoryTheory.Abelian.BiproductToPushoutIsCokernel.biproductToPushoutCofork**
 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Abelian.BiproductToPushoutIsCokernel`
。
形式化陈述：biproductToPushoutCofork : CokernelCofork (biprod.lift f (-g))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `Y ⊞ Z ⟶ pushout f g` induces a cokernel cofork on the map
    `X ⟶ Y ⊞ Z` induced by `f` and `-g`.
-/
abbrev biproductToPushoutCofork : CokernelCofork (biprod.lift f (-g)) :=
  CokernelCofork.ofπ (biproductToPushout f g) <| by
    rw [biprod.lift_desc, neg_comp, pushout.condition, add_neg_cancel]

set_option backward.isDefEq.respectTransparency false in
/-- The cofork induced by the canonical map `Y ⊞ Z ⟶ pushout f g` is in fact a colimit cokernel
    cofork. -/
/-
**CategoryTheory.Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushou
t** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian.BiproductToPushoutIsCokernel
`。
形式化陈述：isColimitBiproductToPushout : IsColimit (biproductToPushoutCofork f g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofork induced by the canonical map `Y ⊞ Z ⟶ pushout f g` is in fact a colim
it cokernel
    cofork.
-/
def isColimitBiproductToPushout : IsColimit (biproductToPushoutCofork f g) :=
  Cofork.IsColimit.mk _
    (fun s =>
      pushout.desc (biprod.inl ≫ Cofork.π s) (biprod.inr ≫ Cofork.π s) <|
        sub_eq_zero.1 <| by
          rw [← Category.assoc, ← Category.assoc, ← sub_comp, sub_eq_add_neg, ← neg_comp, ←
            biprod.lift_eq, Cofork.condition s, zero_comp])
    (fun s => by apply biprod.hom_ext' <;> simp)
    fun s m h => by apply pushout.hom_ext <;> simp [← h]

end BiproductToPushoutIsCokernel

section EpiPullback

variable [Limits.HasPullbacks C] {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category, the pullback of an epimorphism is an epimorphism.
    Proof from [aluffi2016, IX.2.3], cf. [borceux-vol2, 1.7.6] -/
/-
**CategoryTheory.Abelian.epi_pullback_of_epi_f** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Abelian`。
形式化陈述：epi_pullback_of_epi_f [Epi f] : Epi (pullback.snd f g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.epi_of_cancel_zero`：epi_of_cancel_zero {P Q :
 C} (f : P ⟶ Q) (h : forall {R : C} (g : Q ⟶ R), f ≫ g = 0 -> g = 0) : Epi f
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.biprod.lift_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [in
st_2 : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.Limits.KernelFork.condition`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
 {X Y : C}   {f : X ⟶ Y} (s : Ca…
· 使用定理 `CategoryTheory.Limits.biprod.epi_desc_of_epi_left`：∀ {C : Type uC} [inst
 : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.HasZeroMorphisms.comp_zero`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   (f : X ⟶ Y) (Z : C), …

--- 原说明 ---
In an abelian category, the pullback of an epimorphism is an epimorphism.
    Proof from [aluffi2016, IX.2.3], cf. [borceux-vol2, 1.7.6]
-/
instance epi_pullback_of_epi_f [Epi f] : Epi (pullback.snd f g) :=
  -- It will suffice to consider some morphism e : Y ⟶ R such that
    -- pullback.snd f g ≫ e = 0 and show that e = 0.
    epi_of_cancel_zero _ fun {R} e h => by
    -- Consider the morphism u := (0, e) : X ⊞ Y⟶ R.
    let u := biprod.desc (0 : X ⟶ R) e
    -- The composite pullback f g ⟶ X ⊞ Y ⟶ R is zero by assumption.
    have hu : PullbackToBiproductIsKernel.pullbackToBiproduct f g ≫ u = 0 := by simpa [u]
    -- pullbackToBiproduct f g is a kernel of (f, -g), so (f, -g) is a
    -- cokernel of pullbackToBiproduct f g
    have :=
      epiIsCokernelOfKernel _
        (PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g)
    -- We use this fact to obtain a factorization of u through (f, -g) via some d : Z ⟶ R.
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' this u hu
    dsimp at d; dsimp [u] at hd
    -- But then f ≫ d = 0:
    have : f ≫ d = 0 := calc
      f ≫ d = (biprod.inl ≫ biprod.desc f (-g)) ≫ d := by rw [biprod.inl_desc]
      _ = biprod.inl ≫ u := by rw [Category.assoc, hd]
      _ = 0 := biprod.inl_desc _ _
    -- But f is an epimorphism, so d = 0...
    have : d = 0 := (cancel_epi f).1 (by simpa)
    -- ...or, in other words, e = 0.
    calc
      e = biprod.inr ≫ biprod.desc (0 : X ⟶ R) e := by rw [biprod.inr_desc]
      _ = biprod.inr ≫ biprod.desc f (-g) ≫ d := by rw [← hd]
      _ = biprod.inr ≫ biprod.desc f (-g) ≫ 0 := by rw [this]
      _ = (biprod.inr ≫ biprod.desc f (-g)) ≫ 0 := by rw [← Category.assoc]
      _ = 0 := HasZeroMorphisms.comp_zero _ _

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category, the pullback of an epimorphism is an epimorphism. -/
/-
**CategoryTheory.Abelian.epi_pullback_of_epi_g** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Abelian`。
形式化陈述：epi_pullback_of_epi_g [Epi g] : Epi (pullback.fst f g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.epi_of_cancel_zero`：epi_of_cancel_zero {P Q :
 C} (f : P ⟶ Q) (h : forall {R : C} (g : Q ⟶ R), f ≫ g = 0 -> g = 0) : Epi f
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.biprod.lift_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [in
st_2 : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.Limits.KernelFork.condition`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
 {X Y : C}   {f : X ⟶ Y} (s : Ca…
· 使用定理 `CategoryTheory.Limits.biprod.epi_desc_of_epi_right`：∀ {C : Type uC} [ins
t : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Preadditive.instEpiNegHom`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {P Q : C} {f 
: P ⟶ Q}   [CategoryTheory.Epi…
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Preadditive.neg_comp`：neg_comp : (-f) ≫ g = -f ≫ g
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.HasZeroMorphisms.comp_zero`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   (f : X ⟶ Y) (Z : C), …

--- 原说明 ---
In an abelian category, the pullback of an epimorphism is an epimorphism.
-/
instance epi_pullback_of_epi_g [Epi g] : Epi (pullback.fst f g) :=
  -- It will suffice to consider some morphism e : X ⟶ R such that
  -- pullback.fst f g ≫ e = 0 and show that e = 0.
  epi_of_cancel_zero _ fun {R} e h => by
    -- Consider the morphism u := (e, 0) : X ⊞ Y ⟶ R.
    let u := biprod.desc e (0 : Y ⟶ R)
    -- The composite pullback f g ⟶ X ⊞ Y ⟶ R is zero by assumption.
    have hu : PullbackToBiproductIsKernel.pullbackToBiproduct f g ≫ u = 0 := by simpa [u]
    -- pullbackToBiproduct f g is a kernel of (f, -g), so (f, -g) is a
    -- cokernel of pullbackToBiproduct f g
    have :=
      epiIsCokernelOfKernel _
        (PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g)
    -- We use this fact to obtain a factorization of u through (f, -g) via some d : Z ⟶ R.
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' this u hu
    dsimp at d; dsimp [u] at hd
    -- But then (-g) ≫ d = 0:
    have : (-g) ≫ d = 0 := calc
      (-g) ≫ d = (biprod.inr ≫ biprod.desc f (-g)) ≫ d := by rw [biprod.inr_desc]
      _ = biprod.inr ≫ u := by rw [Category.assoc, hd]
      _ = 0 := biprod.inr_desc _ _
    -- But g is an epimorphism, thus so is -g, so d = 0...
    have : d = 0 := (cancel_epi (-g)).1 (by simpa)
    -- ...or, in other words, e = 0.
    calc
      e = biprod.inl ≫ biprod.desc e (0 : Y ⟶ R) := by rw [biprod.inl_desc]
      _ = biprod.inl ≫ biprod.desc f (-g) ≫ d := by rw [← hd]
      _ = biprod.inl ≫ biprod.desc f (-g) ≫ 0 := by rw [this]
      _ = (biprod.inl ≫ biprod.desc f (-g)) ≫ 0 := by rw [← Category.assoc]
      _ = 0 := HasZeroMorphisms.comp_zero _ _

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.epi_snd_of_isLimit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Abelian`。
形式化陈述：epi_snd_of_isLimit [Epi f] {s : PullbackCone f g} (hs : IsLimit s) : Epi s
.snd
参数：hs : IsLimit s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
theorem epi_snd_of_isLimit [Epi f] {s : PullbackCone f g} (hs : IsLimit s) : Epi s.snd := by
  have : Epi (NatTrans.app (limit.cone (cospan f g)).π WalkingCospan.right) :=
    Abelian.epi_pullback_of_epi_f f g
  apply epi_of_epi_fac (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) hs _)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.epi_fst_of_isLimit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Abelian`。
形式化陈述：epi_fst_of_isLimit [Epi g] {s : PullbackCone f g} (hs : IsLimit s) : Epi s
.fst
参数：hs : IsLimit s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
theorem epi_fst_of_isLimit [Epi g] {s : PullbackCone f g} (hs : IsLimit s) : Epi s.fst := by
  have : Epi (NatTrans.app (limit.cone (cospan f g)).π WalkingCospan.left) :=
    Abelian.epi_pullback_of_epi_g f g
  apply epi_of_epi_fac (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) hs _)

/-- Suppose `f` and `g` are two morphisms with a common codomain and suppose we have written `g` as
    an epimorphism followed by a monomorphism. If `f` factors through the mono part of this
    factorization, then any pullback of `g` along `f` is an epimorphism. -/
/-
**CategoryTheory.Abelian.epi_fst_of_factor_thru_epi_mono_factorization** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Abelian`。
形式化陈述：epi_fst_of_factor_thru_epi_mono_factorization (g₁ : Y ⟶ W) [Epi g₁] (g₂ : 
W ⟶ Z) [Mono g₂] (hg : g₁ ≫ g₂ = g) (f' : X ⟶ W) (hf : f' ≫ g₂ = f) (t : Pullbac
kCone f g) (ht : IsLimit t) : Epi t.fst
参数：g₁ : Y ⟶ W；g₂ : W ⟶ Z；hg : g₁ ≫ g₂ = g；f' : X ⟶ W；hf : f' ≫ g₂ = f；t : Pullba
ckCone f g；ht : IsLimit t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.epi_fst_of_isLimit`：epi_fst_of_isLimit [Epi g] {s
 : PullbackCone f g} (hs : IsLimit s) : Epi s.fst
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…

--- 原说明 ---
Suppose `f` and `g` are two morphisms with a common codomain and suppose we have
 written `g` as
    an epimorphism followed by a monomorphism. If `f` factors through the mono p
art of this
    factorization, then any pullback of `g` along `f` is an epimorphism.
-/
theorem epi_fst_of_factor_thru_epi_mono_factorization (g₁ : Y ⟶ W) [Epi g₁] (g₂ : W ⟶ Z) [Mono g₂]
    (hg : g₁ ≫ g₂ = g) (f' : X ⟶ W) (hf : f' ≫ g₂ = f) (t : PullbackCone f g) (ht : IsLimit t) :
    Epi t.fst := by
  apply epi_fst_of_isLimit _ _ (PullbackCone.isLimitOfFactors f g g₂ f' g₁ hf hg t ht)

end EpiPullback

section MonoPushout

variable [Limits.HasPushouts C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.mono_pushout_of_mono_f** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Abelian`。
形式化陈述：mono_pushout_of_mono_f [Mono f] : Mono (pushout.inr _ _ : Z ⟶ pushout f g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.mono_of_cancel_zero`：mono_of_cancel_zero {Q R
 : C} (f : Q ⟶ R) (h : forall {P : C} (g : P ⟶ Q), g ≫ f = 0 -> g = 0) : Mono f 
where right_cancellation
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.biprod.lift_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [in
st_2 : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.Limits.CokernelCofork.condition`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   {f : X ⟶ Y} (s : Ca…
· 使用定理 `CategoryTheory.Limits.biprod.mono_lift_of_mono_left`：∀ {C : Type uC} [in
st : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
instance mono_pushout_of_mono_f [Mono f] : Mono (pushout.inr _ _ : Z ⟶ pushout f g) :=
  mono_of_cancel_zero _ fun {R} e h => by
    let u := biprod.lift (0 : R ⟶ Y) e
    have hu : u ≫ BiproductToPushoutIsCokernel.biproductToPushout f g = 0 := by simpa [u]
    have :=
      monoIsKernelOfCokernel _
        (BiproductToPushoutIsCokernel.isColimitBiproductToPushout f g)
    obtain ⟨d, hd⟩ := KernelFork.IsLimit.lift' this u hu
    dsimp at d
    dsimp [u] at hd
    have : d ≫ f = 0 := calc
      d ≫ f = d ≫ biprod.lift f (-g) ≫ biprod.fst := by rw [biprod.lift_fst]
      _ = u ≫ biprod.fst := by rw [← Category.assoc, hd]
      _ = 0 := biprod.lift_fst _ _
    have : d = 0 := (cancel_mono f).1 (by simpa)
    calc
      e = biprod.lift (0 : R ⟶ Y) e ≫ biprod.snd := by rw [biprod.lift_snd]
      _ = (d ≫ biprod.lift f (-g)) ≫ biprod.snd := by rw [← hd]
      _ = (0 ≫ biprod.lift f (-g)) ≫ biprod.snd := by rw [this]
      _ = 0 ≫ biprod.lift f (-g) ≫ biprod.snd := by rw [Category.assoc]
      _ = 0 := zero_comp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.mono_pushout_of_mono_g** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Abelian`。
形式化陈述：mono_pushout_of_mono_g [Mono g] : Mono (pushout.inl f g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.mono_of_cancel_zero`：mono_of_cancel_zero {Q R
 : C} (f : Q ⟶ R) (h : forall {P : C} (g : P ⟶ Q), g ≫ f = 0 -> g = 0) : Mono f 
where right_cancellation
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.biprod.lift_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [in
st_2 : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.Limits.CokernelCofork.condition`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   {f : X ⟶ Y} (s : Ca…
· 使用定理 `CategoryTheory.Limits.biprod.mono_lift_of_mono_right`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Preadditive.instMonoNegHom`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {P Q : C} {f
 : P ⟶ Q}   [CategoryTheory.Mon…
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Preadditive.comp_neg`：comp_neg : f ≫ (-g) = -f ≫ g
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
instance mono_pushout_of_mono_g [Mono g] : Mono (pushout.inl f g) :=
  mono_of_cancel_zero _ fun {R} e h => by
    let u := biprod.lift e (0 : R ⟶ Z)
    have hu : u ≫ BiproductToPushoutIsCokernel.biproductToPushout f g = 0 := by simpa [u]
    have :=
      monoIsKernelOfCokernel _
        (BiproductToPushoutIsCokernel.isColimitBiproductToPushout f g)
    obtain ⟨d, hd⟩ := KernelFork.IsLimit.lift' this u hu
    dsimp at d
    dsimp [u] at hd
    have : d ≫ (-g) = 0 := calc
      d ≫ (-g) = d ≫ biprod.lift f (-g) ≫ biprod.snd := by rw [biprod.lift_snd]
      _ = biprod.lift e (0 : R ⟶ Z) ≫ biprod.snd := by rw [← Category.assoc, hd]
      _ = 0 := biprod.lift_snd _ _
    have : d = 0 := (cancel_mono (-g)).1 (by simpa)
    calc
      e = biprod.lift e (0 : R ⟶ Z) ≫ biprod.fst := by rw [biprod.lift_fst]
      _ = (d ≫ biprod.lift f (-g)) ≫ biprod.fst := by rw [← hd]
      _ = (0 ≫ biprod.lift f (-g)) ≫ biprod.fst := by rw [this]
      _ = 0 ≫ biprod.lift f (-g) ≫ biprod.fst := by rw [Category.assoc]
      _ = 0 := zero_comp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.mono_inr_of_isColimit** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Abelian`。
形式化陈述：mono_inr_of_isColimit [Mono f] {s : PushoutCocone f g} (hs : IsColimit s) 
: Mono s.inr
参数：hs : IsColimit s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
theorem mono_inr_of_isColimit [Mono f] {s : PushoutCocone f g} (hs : IsColimit s) : Mono s.inr := by
  have : Mono (NatTrans.app (colimit.cocone (span f g)).ι WalkingCospan.right) :=
    Abelian.mono_pushout_of_mono_f f g
  apply
    mono_of_mono_fac (IsColimit.comp_coconePointUniqueUpToIso_hom hs (colimit.isColimit _) _)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.mono_inl_of_isColimit** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Abelian`。
形式化陈述：mono_inl_of_isColimit [Mono g] {s : PushoutCocone f g} (hs : IsColimit s) 
: Mono s.inl
参数：hs : IsColimit s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
theorem mono_inl_of_isColimit [Mono g] {s : PushoutCocone f g} (hs : IsColimit s) : Mono s.inl := by
  have : Mono (NatTrans.app (colimit.cocone (span f g)).ι WalkingCospan.left) :=
    Abelian.mono_pushout_of_mono_g f g
  apply
    mono_of_mono_fac (IsColimit.comp_coconePointUniqueUpToIso_hom hs (colimit.isColimit _) _)

/-- Suppose `f` and `g` are two morphisms with a common domain and suppose we have written `g` as
    an epimorphism followed by a monomorphism. If `f` factors through the epi part of this
    factorization, then any pushout of `g` along `f` is a monomorphism. -/
/-
**CategoryTheory.Abelian.mono_inl_of_factor_thru_epi_mono_factorization** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Abelian`。
形式化陈述：mono_inl_of_factor_thru_epi_mono_factorization (f : X ⟶ Y) (g : X ⟶ Z) (g₁
 : X ⟶ W) [Epi g₁] (g₂ : W ⟶ Z) [Mono g₂] (hg : g₁ ≫ g₂ = g) (f' : W ⟶ Y) (hf : 
g₁ ≫ f' = f) (t : PushoutCocone f g) (ht : IsColimit t) : Mono t.inl
参数：f : X ⟶ Y；g : X ⟶ Z；g₁ : X ⟶ W；g₂ : W ⟶ Z；hg : g₁ ≫ g₂ = g；f' : W ⟶ Y；hf : g₁
 ≫ f' = f；t : PushoutCocone f g；ht : IsColimit t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.mono_inl_of_isColimit`：mono_inl_of_isColimit [Mon
o g] {s : PushoutCocone f g} (hs : IsColimit s) : Mono s.inl
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h

--- 原说明 ---
Suppose `f` and `g` are two morphisms with a common domain and suppose we have w
ritten `g` as
    an epimorphism followed by a monomorphism. If `f` factors through the epi pa
rt of this
    factorization, then any pushout of `g` along `f` is a monomorphism.
-/
theorem mono_inl_of_factor_thru_epi_mono_factorization (f : X ⟶ Y) (g : X ⟶ Z) (g₁ : X ⟶ W) [Epi g₁]
    (g₂ : W ⟶ Z) [Mono g₂] (hg : g₁ ≫ g₂ = g) (f' : W ⟶ Y) (hf : g₁ ≫ f' = f)
    (t : PushoutCocone f g) (ht : IsColimit t) : Mono t.inl := by
  apply mono_inl_of_isColimit _ _ (PushoutCocone.isColimitOfFactors _ _ _ _ _ hf hg t ht)

end MonoPushout

end CategoryTheory.Abelian

namespace CategoryTheory.NonPreadditiveAbelian

variable (C : Type u) [Category.{v} C] [NonPreadditiveAbelian C]

/-- Every `NonPreadditiveAbelian` category can be promoted to an abelian category. -/
@[instance_reducible]
/-
**CategoryTheory.NonPreadditiveAbelian.abelian** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.NonPreadditiveAbelian`。
形式化陈述：abelian : Abelian C where toPreadditive
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_finite_products`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditive
Abelian C],   CategoryTheory.Limits.HasFiniteP…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_kernels`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelian 
C],   CategoryTheory.Limits.HasKernels…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_cokernels`：∀ {C : Type u} {inst
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelia
n C],   CategoryTheory.Limits.HasCokerne…

--- 原说明 ---
Every `NonPreadditiveAbelian` category can be promoted to an abelian category.
-/
def abelian : Abelian C where
  toPreadditive := NonPreadditiveAbelian.preadditive
  normalMonoOfMono := fun f _ ↦ ⟨normalMonoOfMono f⟩
  normalEpiOfEpi := fun f _ ↦ ⟨normalEpiOfEpi f⟩

end CategoryTheory.NonPreadditiveAbelian

namespace CategoryTheory.Abelian

variable {C : Type*} [Category C] [Preadditive C]

/-- A preadditive category `C` with finite products is abelian when this
/-
**CategoryTheory.Abelian.is** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure is nonempty for any morphism `f` in `C`, see `Abelian.mk'`. -/
/-
**CategoryTheory.Abelian.AbelianStruct** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory
.Abelian`。
形式化陈述：AbelianStruct {X Y : C} (f : X ⟶ Y) where /-- a limit kernel fork of `f` -
/ kernelFork : KernelFork f /-- the kernel fork is a limit -/ isLimitKernelFork 
: IsLimit kernelFork /-- a colimit cokernel cofork of `f` -/ cokernelCofork : Co
kernelCofork f /-- the cokernel cofork is a a limit -/ isColimitCokernelCofork :
 IsColimit cokernelCofork /-- the image of `f` -/ image : C /-- the projection t
o the image -/ imageπ : X ⟶ image ι_imageπ : kernelFork.ι ≫ imageπ = 0
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preadditive category `C` with finite products is abelian when this
structure is nonempty for any morphism `f` in `C`, see `Abelian.mk'`.
-/
structure AbelianStruct {X Y : C} (f : X ⟶ Y) where
  /-- a limit kernel fork of `f` -/
  kernelFork : KernelFork f
  /-- the kernel fork is a limit -/
  isLimitKernelFork : IsLimit kernelFork
  /-- a colimit cokernel cofork of `f` -/
  cokernelCofork : CokernelCofork f
  /-- the cokernel cofork is a a limit -/
  isColimitCokernelCofork : IsColimit cokernelCofork
  /-- the image of `f` -/
  image : C
  /-- the projection to the image -/
  imageπ : X ⟶ image
  ι_imageπ : kernelFork.ι ≫ imageπ = 0 := by cat_disch
  /-- the image is a cokernel -/
  imageIsCokernel : IsColimit (CokernelCofork.ofπ _ ι_imageπ)
  /-- the inclusion of the image -/
  imageι : image ⟶ Y
  imageι_π : imageι ≫ cokernelCofork.π = 0 := by cat_disch
  /-- the image is a kernel -/
  imageIsKernel : IsLimit (KernelFork.ofι _ imageι_π)
  fac : imageπ ≫ imageι = f := by cat_disch

namespace AbelianStruct

attribute [reassoc (attr := simp)] ι_imageπ imageι_π fac

end AbelianStruct

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for abelian categories. We assume that the category `C` is
preadditive, has finite products, and that any morphism `f : X ⟶ Y` has
a kernel `i : K ⟶ X`, a cokernel `p : Y ⟶ Q` such that `f` factors as `f = π ≫ ι`
where `π : X ⟶ I` is a cokernel of `i` and `ι : I ⟶ Y` is a kernel of `p`.
This assumption is packaged in a structure `AbelianStruct f`. -/
@[instance_reducible]
/-
**CategoryTheory.Abelian.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian`。
形式化陈述：mk' [HasFiniteProducts C] (h : forall ⦃X Y : C⦄ (f : X ⟶ Y), Nonempty (Abe
lianStruct f)) : Abelian C where has_kernels
参数：h : forall ⦃X Y : C⦄ (f : X ⟶ Y), Nonempty (AbelianStruct f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for abelian categories. We assume that the category `C` is
preadditive, has finite products, and that any morphism `f : X ⟶ Y` has
a kernel `i : K ⟶ X`, a cokernel `p : Y ⟶ Q` such that `f` factors as `f = π ≫ ι
`
where `π : X ⟶ I` is a cokernel of `i` and `ι : I ⟶ Y` is a kernel of `p`.
This assumption is packaged in a structure `AbelianStruct f`.
-/
noncomputable def mk' [HasFiniteProducts C]
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Nonempty (AbelianStruct f)) :
    Abelian C where
  has_kernels := ⟨fun f ↦ ⟨_, (h f).some.isLimitKernelFork⟩⟩
  has_cokernels := ⟨fun f ↦ ⟨_, (h f).some.isColimitCokernelCofork⟩⟩
  normalMonoOfMono f _ := by
    obtain ⟨hf⟩ := h f
    exact ⟨{
      Z := hf.cokernelCofork.pt
      g := hf.cokernelCofork.π
      w := by simp
      isLimit :=
        have : IsIso hf.imageπ :=
          CokernelCofork.IsColimit.isIso_π _ hf.imageIsCokernel (by simp [← cancel_mono f])
        IsLimit.ofIsoLimit hf.imageIsKernel (Fork.ext (asIso hf.imageπ)).symm }⟩
  normalEpiOfEpi f _ := by
    obtain ⟨hf⟩ := h f
    exact ⟨{
      W := hf.kernelFork.pt
      g := hf.kernelFork.ι
      w := by simp
      isColimit :=
        have : IsIso hf.imageι :=
          KernelFork.IsLimit.isIso_ι _ hf.imageIsKernel (by simp [← cancel_epi f])
        IsColimit.ofIsoColimit hf.imageIsCokernel (Cofork.ext (asIso hf.imageι)) }⟩

end CategoryTheory.Abelian

