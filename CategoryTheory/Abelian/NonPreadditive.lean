/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Equalizers
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Every NonPreadditiveAbelian category is preadditive

In mathlib, we define an abelian category as a preadditive category with finite products,
kernels and cokernels, and in which every monomorphism and epimorphism is normal.

While virtually every interesting abelian category has a natural preadditive structure (which is why
it is included in the definition), preadditivity is not actually needed: Every category that has
all of the other properties appearing in the definition of an abelian category admits a preadditive
structure. This is the construction we carry out in this file.

The proof proceeds in roughly five steps:
1. Prove some results (for example that all equalizers exist) that would be trivial if we already
   had the preadditive structure but are a bit of work without it.
2. Develop images and coimages to show that every monomorphism is the kernel of its cokernel.

The results of the first two steps are also useful for the "normal" development of abelian
categories, and will be used there.

3. For every object `A`, define a "subtraction" morphism `σ : A ⨯ A ⟶ A` and use it to define
   subtraction on morphisms as `f - g := prod.lift f g ≫ σ`.
4. Prove a small number of identities about this subtraction from the definition of `σ`.
5. From these identities, prove a large number of other identities that imply that defining
   `f + g := f - (0 - g)` indeed gives an abelian group structure on morphisms such that composition
   is bilinear.

The construction is non-trivial and it is quite remarkable that this abelian group structure can
be constructed purely from the existence of a few limits and colimits. Even more remarkably,
since abelian categories admit exactly one preadditive structure (see
`subsingleton_preadditive_of_hasBinaryBiproducts`), the construction manages to exactly
reconstruct any natural preadditive structure the category may have.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]

-/

@[expose] public section


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

section

universe v u

variable (C : Type u) [Category.{v} C]

/-- We call a category `NonPreadditiveAbelian` if it has a zero object, kernels, cokernels, finite
products and coproducts, and every monomorphism and every epimorphism is normal.

Notice that every such category is abelian (see `CategoryTheory.NonPreadditiveAbelian.preadditive`),
so in practice it is preferable to work directly with `Abelian`.
-/
/-
**CategoryTheory.NonPreadditiveAbelian** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We call a category `NonPreadditiveAbelian` if it has a zero object, kernels, cok
ernels, finite
products and coproducts, and every monomorphism and every epimorphism is normal.

Notice that every such category is abelian (see `CategoryTheory.NonPreadditiveAb
elian.preadditive`),
so in practice it is preferable to work directly with `Abelian`.
-/
class NonPreadditiveAbelian extends HasZeroMorphisms C, IsNormalMonoCategory C,
    IsNormalEpiCategory C where
  [has_zero_object : HasZeroObject C]
  [has_kernels : HasKernels C]
  [has_cokernels : HasCokernels C]
  [has_finite_products : HasFiniteProducts C]
  [has_finite_coproducts : HasFiniteCoproducts C]

attribute [instance] NonPreadditiveAbelian.has_zero_object

attribute [instance] NonPreadditiveAbelian.has_kernels

attribute [instance] NonPreadditiveAbelian.has_cokernels

attribute [instance] NonPreadditiveAbelian.has_finite_products

attribute [instance] NonPreadditiveAbelian.has_finite_coproducts

end

end CategoryTheory

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [NonPreadditiveAbelian C]

namespace CategoryTheory.NonPreadditiveAbelian

section Factor

variable {P Q : C} (f : P ⟶ Q)

/-- The map `p : P ⟶ image f` is an epimorphism -/
/-
**CategoryTheory.NonPreadditiveAbelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.NonPreadditiveAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `p : P ⟶ image f` is an epimorphism
-/
instance : Epi (Abelian.factorThruImage f) :=
  let I := Abelian.image f
  let p := Abelian.factorThruImage f
  let i := kernel.ι (cokernel.π f)
  -- It will suffice to consider some g : I ⟶ R such that p ≫ g = 0 and show that g = 0.
  NormalMonoCategory.epi_of_zero_cancel
  _ fun R (g : I ⟶ R) (hpg : p ≫ g = 0) => by
  -- Since C is abelian, u := ker g ≫ i is the kernel of some morphism h.
  let u := kernel.ι g ≫ i
  have hu := normalMonoOfMono u
  let h := hu.g
  -- By hypothesis, p factors through the kernel of g via some t.
  obtain ⟨t, ht⟩ := kernel.lift' g p hpg
  have fh : f ≫ h = 0 :=
    calc
      f ≫ h = (p ≫ i) ≫ h := (Abelian.image.fac f).symm ▸ rfl
      _ = ((t ≫ kernel.ι g) ≫ i) ≫ h := ht ▸ rfl
      _ = t ≫ u ≫ h := by simp only [u, Category.assoc]
      _ = t ≫ 0 := hu.w ▸ rfl
      _ = 0 := HasZeroMorphisms.comp_zero _ _
  -- h factors through the cokernel of f via some l.
  obtain ⟨l, hl⟩ := cokernel.desc' f h fh
  have hih : i ≫ h = 0 :=
    calc
      i ≫ h = i ≫ cokernel.π f ≫ l := hl ▸ rfl
      _ = 0 ≫ l := by rw [← Category.assoc, kernel.condition]
      _ = 0 := zero_comp
  -- i factors through u = ker h via some s.
  obtain ⟨s, hs⟩ := NormalMono.lift' u i hih
  have hs' : (s ≫ kernel.ι g) ≫ i = 𝟙 I ≫ i := by rw [Category.assoc, hs, Category.id_comp]
  have : Epi (kernel.ι g) := epi_of_epi_fac ((cancel_mono _).1 hs')
  -- ker g is an epimorphism, but ker g ≫ g = 0 = ker g ≫ 0, so g = 0 as required.
  exact zero_of_epi_comp _ (kernel.condition g)
/-
**CategoryTheory.NonPreadditiveAbelian.isIso_factorThruImage** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.NonPreadditiveAbelian`。
形式化陈述：isIso_factorThruImage [Mono f] : IsIso (Abelian.factorThruImage f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.toIsNormalMonoCategory`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreaddit
iveAbelian C],   CategoryTheory.IsNormalMonoCateg…
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
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.instEpiFactorThruImage`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.NonPreadd
itiveAbelian C] {P Q : C}   (f : P ⟶ Q), Category…
-/
instance isIso_factorThruImage [Mono f] : IsIso (Abelian.factorThruImage f) :=
  isIso_of_mono_of_epi <| Abelian.factorThruImage f

/-- The canonical morphism `i : coimage f ⟶ Q` is a monomorphism -/
/-
**CategoryTheory.NonPreadditiveAbelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.NonPreadditiveAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `i : coimage f ⟶ Q` is a monomorphism
-/
instance : Mono (Abelian.factorThruCoimage f) :=
  let I := Abelian.coimage f
  let i := Abelian.factorThruCoimage f
  let p := cokernel.π (kernel.ι f)
  NormalEpiCategory.mono_of_cancel_zero _ fun R (g : R ⟶ I) (hgi : g ≫ i = 0) => by
    -- Since C is abelian, u := p ≫ coker g is the cokernel of some morphism h.
    let u := p ≫ cokernel.π g
    have hu := normalEpiOfEpi u
    let h := hu.g
    -- By hypothesis, i factors through the cokernel of g via some t.
    obtain ⟨t, ht⟩ := cokernel.desc' g i hgi
    have hf : h ≫ f = 0 :=
      calc
        h ≫ f = h ≫ p ≫ i := (Abelian.coimage.fac f).symm ▸ rfl
        _ = h ≫ p ≫ cokernel.π g ≫ t := ht ▸ rfl
        _ = h ≫ u ≫ t := by simp only [u, Category.assoc]
        _ = 0 ≫ t := by rw [← Category.assoc, hu.w]
        _ = 0 := zero_comp
    -- h factors through the kernel of f via some l.
    obtain ⟨l, hl⟩ := kernel.lift' f h hf
    have hhp : h ≫ p = 0 :=
      calc
        h ≫ p = (l ≫ kernel.ι f) ≫ p := hl ▸ rfl
        _ = l ≫ 0 := by rw [Category.assoc, cokernel.condition]
        _ = 0 := comp_zero
    -- p factors through u = coker h via some s.
    obtain ⟨s, hs⟩ := NormalEpi.desc' u p hhp
    have hs' : p ≫ cokernel.π g ≫ s = p ≫ 𝟙 I := by rw [← Category.assoc, hs, Category.comp_id]
    have : Mono (cokernel.π g) := mono_of_mono_fac ((cancel_epi _).1 hs')
    -- coker g is a monomorphism, but g ≫ coker g = 0 = 0 ≫ coker g, so g = 0 as required.
    exact zero_of_comp_mono _ (cokernel.condition g)
/-
**CategoryTheory.NonPreadditiveAbelian.isIso_factorThruCoimage** 是 Mathlib 中的一个实
例，位于命名空间 `CategoryTheory.NonPreadditiveAbelian`。
形式化陈述：isIso_factorThruCoimage [Epi f] : IsIso (Abelian.factorThruCoimage f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.toIsNormalMonoCategory`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreaddit
iveAbelian C],   CategoryTheory.IsNormalMonoCateg…
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
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.instMonoFactorThruCoimage`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.NonPre
additiveAbelian C] {P Q : C}   (f : P ⟶ Q), Category…
-/
instance isIso_factorThruCoimage [Epi f] : IsIso (Abelian.factorThruCoimage f) :=
  isIso_of_mono_of_epi _

end Factor

section CokernelOfKernel

variable {X Y : C} {f : X ⟶ Y}

set_option backward.isDefEq.respectTransparency false in
/-- In a `NonPreadditiveAbelian` category, an epi is the cokernel of its kernel. More precisely:
If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` is a cokernel
of `Fork.ι s`. -/
/-
**CategoryTheory.NonPreadditiveAbelian.epiIsCokernelOfKernel** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.NonPreadditiveAbelian`。
形式化陈述：epiIsCokernelOfKernel [Epi f] (s : Fork f 0) (h : IsLimit s) : IsColimit (
CokernelCofork.ofπ f (KernelFork.condition s))
参数：s : Fork f 0；h : IsLimit s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a `NonPreadditiveAbelian` category, an epi is the cokernel of its kernel. Mor
e precisely:
If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` is a
 cokernel
of `Fork.ι s`.
-/
def epiIsCokernelOfKernel [Epi f] (s : Fork f 0) (h : IsLimit s) :
    IsColimit (CokernelCofork.ofπ f (KernelFork.condition s)) :=
  IsCokernel.cokernelIso _ _
    (cokernel.ofIsoComp _ _ (Limits.IsLimit.conePointUniqueUpToIso (limit.isLimit _) h)
      (ConeMorphism.w (Limits.IsLimit.uniqueUpToIso (limit.isLimit _) h).hom _))
    (asIso <| Abelian.factorThruCoimage f) (Abelian.coimage.fac f)

set_option backward.isDefEq.respectTransparency false in
/-- In a `NonPreadditiveAbelian` category, a mono is the kernel of its cokernel. More precisely:
If `f` is a monomorphism and `s` is some colimit cokernel cocone on `f`, then `f` is a kernel
of `Cofork.π s`. -/
/-
**CategoryTheory.NonPreadditiveAbelian.monoIsKernelOfCokernel** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.NonPreadditiveAbelian`。
形式化陈述：monoIsKernelOfCokernel [Mono f] (s : Cofork f 0) (h : IsColimit s) : IsLim
it (KernelFork.ofι f (CokernelCofork.condition s))
参数：s : Cofork f 0；h : IsColimit s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a `NonPreadditiveAbelian` category, a mono is the kernel of its cokernel. Mor
e precisely:
If `f` is a monomorphism and `s` is some colimit cokernel cocone on `f`, then `f
` is a kernel
of `Cofork.π s`.
-/
def monoIsKernelOfCokernel [Mono f] (s : Cofork f 0) (h : IsColimit s) :
    IsLimit (KernelFork.ofι f (CokernelCofork.condition s)) :=
  IsKernel.isoKernel _ _
    (kernel.ofCompIso _ _ (Limits.IsColimit.coconePointUniqueUpToIso h (colimit.isColimit _))
      (CoconeMorphism.w (Limits.IsColimit.uniqueUpToIso h <| colimit.isColimit _).hom _))
    (asIso <| Abelian.factorThruImage f) (Abelian.image.fac f)

end CokernelOfKernel

section

/-- The composite `A ⟶ A ⨯ A ⟶ cokernel (Δ A)`, where the first map is `(𝟙 A, 0)` and the second map
is the canonical projection into the cokernel. -/
/-
**CategoryTheory.NonPreadditiveAbelian.r** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.NonPreadditiveAbelian`。
形式化陈述：r (A : C) : A ⟶ cokernel (diag A)
参数：A : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composite `A ⟶ A ⨯ A ⟶ cokernel (Δ A)`, where the first map is `(𝟙 A, 0)` an
d the second map
is the canonical projection into the cokernel.
-/
abbrev r (A : C) : A ⟶ cokernel (diag A) :=
  prod.lift (𝟙 A) 0 ≫ cokernel.π (diag A)
/-
**CategoryTheory.NonPreadditiveAbelian.mono_** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.NonPreadditiveAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mono_Δ {A : C} : Mono (diag A) :=
  mono_of_mono_fac <| prod.lift_fst _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.NonPreadditiveAbelian.mono_r** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.NonPreadditiveAbelian`。
形式化陈述：mono_r {A : C} : Mono (r A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_finite_products`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditive
Abelian C],   CategoryTheory.Limits.HasFiniteP…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_cokernels`：∀ {C : Type u} {inst
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelia
n C],   CategoryTheory.Limits.HasCokerne…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.NormalEpiCategory.mono_of_cancel_zero`：mono_of_cancel_zer
o {X Y : C} (f : X ⟶ Y) (hf : forall (Z : C) (g : Z ⟶ X) (_ : g ≫ f = 0), g = 0)
 : Mono f
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_finite_coproducts`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditi
veAbelian C],   CategoryTheory.Limits.HasFiniteC…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.toIsNormalEpiCategory`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditi
veAbelian C],   CategoryTheory.IsNormalEpiCatego…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_zero_object`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbel
ian C],   CategoryTheory.Limits.HasZeroObj…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.prod.lift_snd`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `CategoryTheory.Limits.KernelFork.ι_ofι`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y P : C}   (f : X ⟶ Y) (ι : …
· 使用定理 `CategoryTheory.Limits.HasZeroMorphisms.comp_zero`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   (f : X ⟶ Y) (Z : C), …
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.Limits.prod.lift_fst`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
instance mono_r {A : C} : Mono (r A) := by
  let hl : IsLimit (KernelFork.ofι (diag A) (cokernel.condition (diag A))) :=
    monoIsKernelOfCokernel _ (colimit.isColimit _)
  apply NormalEpiCategory.mono_of_cancel_zero
  intro Z x hx
  have hxx : (x ≫ prod.lift (𝟙 A) (0 : A ⟶ A)) ≫ cokernel.π (diag A) = 0 := by
    rw [Category.assoc, hx]
  obtain ⟨y, hy⟩ := KernelFork.IsLimit.lift' hl _ hxx
  rw [KernelFork.ι_ofι] at hy
  have hyy : y = 0 := by
    erw [← Category.comp_id y, ← Limits.prod.lift_snd (𝟙 A) (𝟙 A), ← Category.assoc, hy,
      Category.assoc, prod.lift_snd, HasZeroMorphisms.comp_zero]
  have : Mono (prod.lift (𝟙 A) (0 : A ⟶ A)) := mono_of_mono_fac (prod.lift_fst _ _)
  apply (cancel_mono (prod.lift (𝟙 A) (0 : A ⟶ A))).1
  rw [← hy, hyy, zero_comp, zero_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.NonPreadditiveAbelian.epi_r** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.NonPreadditiveAbelian`。
形式化陈述：epi_r {A : C} : Epi (r A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_finite_products`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditive
Abelian C],   CategoryTheory.Limits.HasFiniteP…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.prod.lift_snd`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.KernelFork.condition`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
 {X Y : C}   {f : X ⟶ Y} (s : Ca…
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.Limits.prod.lift_fst`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsRegularEpi`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {B X : C} {f : X ⟶ B} [h : CategoryTheory.IsR
egularEpi f],   CategoryTheory.Effe…
· 使用定理 `CategoryTheory.instIsRegularEpiOfIsSplitEpi`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplitEp
i f],   CategoryTheory.IsRegularE…
· 使用定理 `CategoryTheory.NormalMonoCategory.epi_of_zero_cancel`：epi_of_zero_cancel
 {X Y : C} (f : X ⟶ Y) (hf : forall (Z : C) (g : Y ⟶ Z) (_ : f ≫ g = 0), g = 0) 
: Epi f
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_kernels`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelian 
C],   CategoryTheory.Limits.HasKernels…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.toIsNormalMonoCategory`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreaddit
iveAbelian C],   CategoryTheory.IsNormalMonoCateg…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_zero_object`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbel
ian C],   CategoryTheory.Limits.HasZeroObj…
（共 39 条，此处仅展示前 30 条）
-/
instance epi_r {A : C} : Epi (r A) := by
  have hlp : prod.lift (𝟙 A) (0 : A ⟶ A) ≫ Limits.prod.snd = 0 := prod.lift_snd _ _
  let hp1 : IsLimit (KernelFork.ofι (prod.lift (𝟙 A) (0 : A ⟶ A)) hlp) := by
    refine Fork.IsLimit.mk _ (fun s => Fork.ι s ≫ Limits.prod.fst) ?_ ?_
    · intro s
      apply Limits.prod.hom_ext <;> simp
    · intro s m h
      have : Mono (prod.lift (𝟙 A) (0 : A ⟶ A)) := mono_of_mono_fac (prod.lift_fst _ _)
      apply (cancel_mono (prod.lift (𝟙 A) (0 : A ⟶ A))).1
      convert! h
      apply Limits.prod.hom_ext <;> simp
  let hp2 : IsColimit (CokernelCofork.ofπ (Limits.prod.snd : A ⨯ A ⟶ A) hlp) :=
    epiIsCokernelOfKernel _ hp1
  apply NormalMonoCategory.epi_of_zero_cancel
  intro Z z hz
  have h : prod.lift (𝟙 A) (0 : A ⟶ A) ≫ cokernel.π (diag A) ≫ z = 0 := by rw [← Category.assoc, hz]
  obtain ⟨t, ht⟩ := CokernelCofork.IsColimit.desc' hp2 _ h
  rw [CokernelCofork.π_ofπ] at ht
  have htt : t = 0 := by
    rw [← Category.id_comp t]
    change 𝟙 A ≫ t = 0
    rw [← Limits.prod.lift_snd (𝟙 A) (𝟙 A), Category.assoc, ht, ← Category.assoc,
      cokernel.condition, zero_comp]
  apply (cancel_epi (cokernel.π (diag A))).1
  rw [← ht, htt, comp_zero, comp_zero]
/-
**CategoryTheory.NonPreadditiveAbelian.isIso_r** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.NonPreadditiveAbelian`。
形式化陈述：isIso_r {A : C} : IsIso (r A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.toIsNormalMonoCategory`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreaddit
iveAbelian C],   CategoryTheory.IsNormalMonoCateg…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_finite_products`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditive
Abelian C],   CategoryTheory.Limits.HasFiniteP…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_cokernels`：∀ {C : Type u} {inst
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditiveAbelia
n C],   CategoryTheory.Limits.HasCokerne…
-/
instance isIso_r {A : C} : IsIso (r A) :=
  isIso_of_mono_of_epi _

/-- The composite `A ⨯ A ⟶ cokernel (diag A) ⟶ A` given by the natural projection into the cokernel
followed by the inverse of `r`. In the category of modules, using the normal kernels and
cokernels, this map is equal to the map `(a, b) ↦ a - b`, hence the name `σ` for "subtraction". -/
/-
**CategoryTheory.NonPreadditiveAbelian.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.NonPreadditiveAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composite `A ⨯ A ⟶ cokernel (diag A) ⟶ A` given by the natural projection in
to the cokernel
followed by the inverse of `r`. In the category of modules, using the normal ker
nels and
cokernels, this map is equal to the map `(a, b) ↦ a - b`, hence the name `σ` for
 "subtraction".
-/
abbrev σ {A : C} : A ⨯ A ⟶ A :=
  cokernel.π (diag A) ≫ inv (r A)

end

@[reassoc]
/-
**CategoryTheory.NonPreadditiveAbelian.diag_** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.NonPreadditiveAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_σ {X : C} : diag X ≫ σ = 0 := by rw [cokernel.condition_assoc, zero_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.NonPreadditiveAbelian.lift_** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.NonPreadditiveAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_σ {X : C} : prod.lift (𝟙 X) 0 ≫ σ = 𝟙 X := by rw [← Category.assoc, IsIso.hom_inv_id]

@[reassoc]
/-
**CategoryTheory.NonPreadditiveAbelian.lift_map** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.NonPreadditiveAbelian`。
形式化陈述：lift_map {X Y : C} (f : X ⟶ Y) : prod.lift (𝟙 X) 0 ≫ Limits.prod.map f f =
 f ≫ prod.lift (𝟙 Y) 0
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_finite_products`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditive
Abelian C],   CategoryTheory.Limits.HasFiniteP…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_map {X Y : C} (f : X ⟶ Y) :
    prod.lift (𝟙 X) 0 ≫ Limits.prod.map f f = f ≫ prod.lift (𝟙 Y) 0 := by simp

/-- σ is a cokernel of Δ X. -/
/-
**CategoryTheory.NonPreadditiveAbelian.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.NonPreadditiveAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
σ is a cokernel of Δ X.
-/
def isColimitσ {X : C} : IsColimit (CokernelCofork.ofπ (σ : X ⨯ X ⟶ X) diag_σ) :=
  cokernel.cokernelIso _ σ (asIso (r X)).symm (by rw [Iso.symm_hom, asIso_inv])

set_option backward.isDefEq.respectTransparency false in
/-- This is the key identity satisfied by `σ`. -/
/-
**CategoryTheory.NonPreadditiveAbelian.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.NonPreadditiveAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the key identity satisfied by `σ`.
-/
theorem σ_comp {X Y : C} (f : X ⟶ Y) : σ ≫ f = Limits.prod.map f f ≫ σ := by
  obtain ⟨g, hg⟩ :=
    CokernelCofork.IsColimit.desc' isColimitσ (Limits.prod.map f f ≫ σ) (by
      rw [prod.diag_map_assoc, diag_σ, comp_zero])
  suffices hfg : f = g by rw [← hg, Cofork.π_ofπ, hfg]
  calc
    f = f ≫ prod.lift (𝟙 Y) 0 ≫ σ := by rw [lift_σ, Category.comp_id]
    _ = prod.lift (𝟙 X) 0 ≫ Limits.prod.map f f ≫ σ := by rw [lift_map_assoc]
    _ = prod.lift (𝟙 X) 0 ≫ σ ≫ g := by rw [← hg, CokernelCofork.π_ofπ]
    _ = g := by rw [← Category.assoc, lift_σ, Category.id_comp]

section

-- We write `f - g` for `prod.lift f g ≫ σ`.
/-- Subtraction of morphisms in a `NonPreadditiveAbelian` category. -/
@[instance_reducible]
/-
**CategoryTheory.NonPreadditiveAbelian.hasSub** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.NonPreadditiveAbelian`。
形式化陈述：hasSub {X Y : C} : Sub (X ⟶ Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subtraction of morphisms in a `NonPreadditiveAbelian` category.
-/
def hasSub {X Y : C} : Sub (X ⟶ Y) :=
  ⟨fun f g => prod.lift f g ≫ σ⟩

attribute [local instance] hasSub

-- We write `-f` for `0 - f`.
/-- Negation of morphisms in a `NonPreadditiveAbelian` category. -/
@[instance_reducible]
/-
**CategoryTheory.NonPreadditiveAbelian.hasNeg** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.NonPreadditiveAbelian`。
形式化陈述：hasNeg {X Y : C} : Neg (X ⟶ Y) where neg
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negation of morphisms in a `NonPreadditiveAbelian` category.
-/
def hasNeg {X Y : C} : Neg (X ⟶ Y) where
  neg := fun f => 0 - f

attribute [local instance] hasNeg

-- We write `f + g` for `f - (-g)`.
/-- Addition of morphisms in a `NonPreadditiveAbelian` category. -/
@[instance_reducible]
/-
**CategoryTheory.NonPreadditiveAbelian.hasAdd** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.NonPreadditiveAbelian`。
形式化陈述：hasAdd {X Y : C} : Add (X ⟶ Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Addition of morphisms in a `NonPreadditiveAbelian` category.
-/
def hasAdd {X Y : C} : Add (X ⟶ Y) :=
  ⟨fun f g => f - -g⟩

attribute [local instance] hasAdd
/-
**CategoryTheory.NonPreadditiveAbelian.sub_def** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NonPreadditiveAbelian`。
形式化陈述：sub_def {X Y : C} (a b : X ⟶ Y) : a - b = prod.lift a b ≫ σ
参数：a b : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_def {X Y : C} (a b : X ⟶ Y) : a - b = prod.lift a b ≫ σ := rfl
/-
**CategoryTheory.NonPreadditiveAbelian.add_def** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NonPreadditiveAbelian`。
形式化陈述：add_def {X Y : C} (a b : X ⟶ Y) : a + b = a - -b
参数：a b : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_def {X Y : C} (a b : X ⟶ Y) : a + b = a - -b := rfl
/-
**CategoryTheory.NonPreadditiveAbelian.neg_def** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NonPreadditiveAbelian`。
形式化陈述：neg_def {X Y : C} (a : X ⟶ Y) : -a = 0 - a
参数：a : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_def {X Y : C} (a : X ⟶ Y) : -a = 0 - a := rfl
/-
**CategoryTheory.NonPreadditiveAbelian.sub_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.NonPreadditiveAbelian`。
形式化陈述：sub_zero {X Y : C} (a : X ⟶ Y) : a - 0 = a
参数：a : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_finite_products`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditive
Abelian C],   CategoryTheory.Limits.HasFiniteP…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_def`：sub_def {X Y : C} (a b : X
 ⟶ Y) : a - b = prod.lift a b ≫ σ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.lift_σ`：lift_σ {X : C} : prod.lift 
(𝟙 X) 0 ≫ σ = 𝟙 X
-/
theorem sub_zero {X Y : C} (a : X ⟶ Y) : a - 0 = a := by
  rw [sub_def]
  conv_lhs =>
    congr; congr; rw [← Category.comp_id a]
    case a.g => rw [show 0 = a ≫ (0 : Y ⟶ Y) by simp]
  rw [← prod.comp_lift, Category.assoc, lift_σ, Category.comp_id]
/-
**CategoryTheory.NonPreadditiveAbelian.sub_self** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.NonPreadditiveAbelian`。
形式化陈述：sub_self {X Y : C} (a : X ⟶ Y) : a - a = 0
参数：a : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_finite_products`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditive
Abelian C],   CategoryTheory.Limits.HasFiniteP…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_def`：sub_def {X Y : C} (a b : X
 ⟶ Y) : a - b = prod.lift a b ≫ σ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.diag_σ`：diag_σ {X : C} : diag X ≫ σ
 = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
theorem sub_self {X Y : C} (a : X ⟶ Y) : a - a = 0 := by
  rw [sub_def, ← Category.comp_id a, ← prod.comp_lift, Category.assoc, diag_σ, comp_zero]
/-
**CategoryTheory.NonPreadditiveAbelian.lift_sub_lift** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.NonPreadditiveAbelian`。
形式化陈述：lift_sub_lift {X Y : C} (a b c d : X ⟶ Y) : prod.lift a b - prod.lift c d 
= prod.lift (a - c) (b - d)
参数：a b c d : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_finite_products`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditive
Abelian C],   CategoryTheory.Limits.HasFiniteP…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.σ_comp`：σ_comp {X Y : C} (f : X ⟶ Y
) : σ ≫ f = Limits.prod.map f f ≫ σ
· 使用定理 `CategoryTheory.Limits.prod.lift_map_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Ha
sBinaryProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.prod.lift_fst`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `CategoryTheory.Limits.prod.lift_snd`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
-/
theorem lift_sub_lift {X Y : C} (a b c d : X ⟶ Y) :
    prod.lift a b - prod.lift c d = prod.lift (a - c) (b - d) := by
  simp only [sub_def]
  ext
  · rw [Category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_fst, prod.lift_fst, prod.lift_fst]
  · rw [Category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_snd, prod.lift_snd, prod.lift_snd]
/-
**CategoryTheory.NonPreadditiveAbelian.sub_sub_sub** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.NonPreadditiveAbelian`。
形式化陈述：sub_sub_sub {X Y : C} (a b c d : X ⟶ Y) : a - c - (b - d) = a - b - (c - d
)
参数：a b c d : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_finite_products`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditive
Abelian C],   CategoryTheory.Limits.HasFiniteP…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_def`：sub_def {X Y : C} (a b : X
 ⟶ Y) : a - b = prod.lift a b ≫ σ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.lift_sub_lift`：lift_sub_lift {X Y :
 C} (a b c d : X ⟶ Y) : prod.lift a b - prod.lift c d = prod.lift (a - c) (b - d
)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.σ_comp`：σ_comp {X Y : C} (f : X ⟶ Y
) : σ ≫ f = Limits.prod.map f f ≫ σ
· 使用定理 `CategoryTheory.Limits.prod.lift_map_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Ha
sBinaryProduct W X] [inst_2 : C…
-/
theorem sub_sub_sub {X Y : C} (a b c d : X ⟶ Y) : a - c - (b - d) = a - b - (c - d) := by
  rw [sub_def, ← lift_sub_lift, sub_def, Category.assoc, σ_comp, prod.lift_map_assoc]; rfl
/-
**CategoryTheory.NonPreadditiveAbelian.neg_sub** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NonPreadditiveAbelian`。
形式化陈述：neg_sub {X Y : C} (a b : X ⟶ Y) : -a - b = -b - a
参数：a b : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_def`：neg_def {X Y : C} (a : X ⟶
 Y) : -a = 0 - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_zero`：sub_zero {X Y : C} (a : X
 ⟶ Y) : a - 0 = a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_sub_sub`：sub_sub_sub {X Y : C} 
(a b c d : X ⟶ Y) : a - c - (b - d) = a - b - (c - d)
-/
theorem neg_sub {X Y : C} (a b : X ⟶ Y) : -a - b = -b - a := by
  conv_lhs => rw [neg_def, ← sub_zero b, sub_sub_sub, sub_zero, ← neg_def]
/-
**CategoryTheory.NonPreadditiveAbelian.neg_neg** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NonPreadditiveAbelian`。
形式化陈述：neg_neg {X Y : C} (a : X ⟶ Y) : - -a = a
参数：a : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_def`：neg_def {X Y : C} (a : X ⟶
 Y) : -a = 0 - a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_self`：sub_self {X Y : C} (a : X
 ⟶ Y) : a - a = 0
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_sub_sub`：sub_sub_sub {X Y : C} 
(a b c d : X ⟶ Y) : a - c - (b - d) = a - b - (c - d)
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_zero`：sub_zero {X Y : C} (a : X
 ⟶ Y) : a - 0 = a
-/
theorem neg_neg {X Y : C} (a : X ⟶ Y) : - -a = a := by
  rw [neg_def, neg_def]
  conv_lhs =>
    congr; rw [← sub_self a]
  rw [sub_sub_sub, sub_zero, sub_self, sub_zero]
/-
**CategoryTheory.NonPreadditiveAbelian.add_comm** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.NonPreadditiveAbelian`。
形式化陈述：add_comm {X Y : C} (a b : X ⟶ Y) : a + b = b + a
参数：a b : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_def`：add_def {X Y : C} (a b : X
 ⟶ Y) : a + b = a - -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_neg`：neg_neg {X Y : C} (a : X ⟶
 Y) : - -a = a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_def`：neg_def {X Y : C} (a : X ⟶
 Y) : -a = 0 - a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_sub_sub`：sub_sub_sub {X Y : C} 
(a b c d : X ⟶ Y) : a - c - (b - d) = a - b - (c - d)
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_sub`：neg_sub {X Y : C} (a b : X
 ⟶ Y) : -a - b = -b - a
-/
theorem add_comm {X Y : C} (a b : X ⟶ Y) : a + b = b + a := by
  rw [add_def]
  conv_lhs => rw [← neg_neg a]
  rw [neg_def, neg_def, neg_def, sub_sub_sub]
  conv_lhs =>
    congr
    next => skip
    rw [← neg_def, neg_sub]
  rw [sub_sub_sub, add_def, ← neg_def, neg_neg b, neg_def]
/-
**CategoryTheory.NonPreadditiveAbelian.add_neg** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NonPreadditiveAbelian`。
形式化陈述：add_neg {X Y : C} (a b : X ⟶ Y) : a + -b = a - b
参数：a b : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_def`：add_def {X Y : C} (a b : X
 ⟶ Y) : a + b = a - -b
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_neg`：neg_neg {X Y : C} (a : X ⟶
 Y) : - -a = a
-/
theorem add_neg {X Y : C} (a b : X ⟶ Y) : a + -b = a - b := by rw [add_def, neg_neg]
/-
**CategoryTheory.NonPreadditiveAbelian.add_neg_cancel** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.NonPreadditiveAbelian`。
形式化陈述：add_neg_cancel {X Y : C} (a : X ⟶ Y) : a + -a = 0
参数：a : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_neg`：add_neg {X Y : C} (a b : X
 ⟶ Y) : a + -b = a - b
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_self`：sub_self {X Y : C} (a : X
 ⟶ Y) : a - a = 0
-/
theorem add_neg_cancel {X Y : C} (a : X ⟶ Y) : a + -a = 0 := by rw [add_neg, sub_self]
/-
**CategoryTheory.NonPreadditiveAbelian.neg_add_cancel** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.NonPreadditiveAbelian`。
形式化陈述：neg_add_cancel {X Y : C} (a : X ⟶ Y) : -a + a = 0
参数：a : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_comm`：add_comm {X Y : C} (a b :
 X ⟶ Y) : a + b = b + a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_neg_cancel`：add_neg_cancel {X Y
 : C} (a : X ⟶ Y) : a + -a = 0
-/
theorem neg_add_cancel {X Y : C} (a : X ⟶ Y) : -a + a = 0 := by rw [add_comm, add_neg_cancel]
/-
**CategoryTheory.NonPreadditiveAbelian.neg_sub'** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.NonPreadditiveAbelian`。
形式化陈述：neg_sub' {X Y : C} (a b : X ⟶ Y) : -(a - b) = -a + b
参数：a b : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_def`：neg_def {X Y : C} (a : X ⟶
 Y) : -a = 0 - a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_self`：sub_self {X Y : C} (a : X
 ⟶ Y) : a - a = 0
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_sub_sub`：sub_sub_sub {X Y : C} 
(a b c d : X ⟶ Y) : a - c - (b - d) = a - b - (c - d)
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_def`：add_def {X Y : C} (a b : X
 ⟶ Y) : a + b = a - -b
-/
theorem neg_sub' {X Y : C} (a b : X ⟶ Y) : -(a - b) = -a + b := by
  rw [neg_def, neg_def]
  conv_lhs => rw [← sub_self (0 : X ⟶ Y)]
  rw [sub_sub_sub, add_def, neg_def]
/-
**CategoryTheory.NonPreadditiveAbelian.neg_add** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NonPreadditiveAbelian`。
形式化陈述：neg_add {X Y : C} (a b : X ⟶ Y) : -(a + b) = -a - b
参数：a b : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_def`：add_def {X Y : C} (a b : X
 ⟶ Y) : a + b = a - -b
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_sub'`：neg_sub' {X Y : C} (a b :
 X ⟶ Y) : -(a - b) = -a + b
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_neg`：add_neg {X Y : C} (a b : X
 ⟶ Y) : a + -b = a - b
-/
theorem neg_add {X Y : C} (a b : X ⟶ Y) : -(a + b) = -a - b := by rw [add_def, neg_sub', add_neg]
/-
**CategoryTheory.NonPreadditiveAbelian.sub_add** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NonPreadditiveAbelian`。
形式化陈述：sub_add {X Y : C} (a b c : X ⟶ Y) : a - b + c = a - (b - c)
参数：a b c : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_def`：add_def {X Y : C} (a b : X
 ⟶ Y) : a + b = a - -b
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_def`：neg_def {X Y : C} (a : X ⟶
 Y) : -a = 0 - a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_sub_sub`：sub_sub_sub {X Y : C} 
(a b c d : X ⟶ Y) : a - c - (b - d) = a - b - (c - d)
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_zero`：sub_zero {X Y : C} (a : X
 ⟶ Y) : a - 0 = a
-/
theorem sub_add {X Y : C} (a b c : X ⟶ Y) : a - b + c = a - (b - c) := by
  rw [add_def, neg_def, sub_sub_sub, sub_zero]
/-
**CategoryTheory.NonPreadditiveAbelian.add_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.NonPreadditiveAbelian`。
形式化陈述：add_assoc {X Y : C} (a b c : X ⟶ Y) : a + b + c = a + (b + c)
参数：a b c : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_def`：add_def {X Y : C} (a b : X
 ⟶ Y) : a + b = a - -b
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_add`：sub_add {X Y : C} (a b c :
 X ⟶ Y) : a - b + c = a - (b - c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_neg`：add_neg {X Y : C} (a b : X
 ⟶ Y) : a + -b = a - b
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_sub'`：neg_sub' {X Y : C} (a b :
 X ⟶ Y) : -(a - b) = -a + b
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_neg`：neg_neg {X Y : C} (a : X ⟶
 Y) : - -a = a
-/
theorem add_assoc {X Y : C} (a b c : X ⟶ Y) : a + b + c = a + (b + c) := by
  conv_lhs =>
    congr; rw [add_def]
  rw [sub_add, ← add_neg, neg_sub', neg_neg]
/-
**CategoryTheory.NonPreadditiveAbelian.add_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.NonPreadditiveAbelian`。
形式化陈述：add_zero {X Y : C} (a : X ⟶ Y) : a + 0 = a
参数：a : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_def`：add_def {X Y : C} (a b : X
 ⟶ Y) : a + b = a - -b
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_def`：neg_def {X Y : C} (a : X ⟶
 Y) : -a = 0 - a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_self`：sub_self {X Y : C} (a : X
 ⟶ Y) : a - a = 0
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_zero`：sub_zero {X Y : C} (a : X
 ⟶ Y) : a - 0 = a
-/
theorem add_zero {X Y : C} (a : X ⟶ Y) : a + 0 = a := by rw [add_def, neg_def, sub_self, sub_zero]
/-
**CategoryTheory.NonPreadditiveAbelian.comp_sub** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.NonPreadditiveAbelian`。
形式化陈述：comp_sub {X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g - h) = f ≫ g - f ≫
 h
参数：f : X ⟶ Y；g h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_finite_products`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditive
Abelian C],   CategoryTheory.Limits.HasFiniteP…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_def`：sub_def {X Y : C} (a b : X
 ⟶ Y) : a - b = prod.lift a b ≫ σ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
-/
theorem comp_sub {X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g - h) = f ≫ g - f ≫ h := by
  rw [sub_def, ← Category.assoc, prod.comp_lift, sub_def]
/-
**CategoryTheory.NonPreadditiveAbelian.sub_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.NonPreadditiveAbelian`。
形式化陈述：sub_comp {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z) : (f - g) ≫ h = f ≫ h - g ≫
 h
参数：f g : X ⟶ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.has_finite_products`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.NonPreadditive
Abelian C],   CategoryTheory.Limits.HasFiniteP…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_def`：sub_def {X Y : C} (a b : X
 ⟶ Y) : a - b = prod.lift a b ≫ σ
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.σ_comp`：σ_comp {X Y : C} (f : X ⟶ Y
) : σ ≫ f = Limits.prod.map f f ≫ σ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
-/
theorem sub_comp {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z) : (f - g) ≫ h = f ≫ h - g ≫ h := by
  rw [sub_def, Category.assoc, σ_comp, ← Category.assoc, prod.lift_map, sub_def]
/-
**CategoryTheory.NonPreadditiveAbelian.comp_add** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.NonPreadditiveAbelian`。
形式化陈述：comp_add (X Y Z : C) (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫
 h
参数：X Y Z : C；f : X ⟶ Y；g h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_def`：add_def {X Y : C} (a b : X
 ⟶ Y) : a + b = a - -b
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.comp_sub`：comp_sub {X Y Z : C} (f :
 X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g - h) = f ≫ g - f ≫ h
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_def`：neg_def {X Y : C} (a : X ⟶
 Y) : -a = 0 - a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
theorem comp_add (X Y Z : C) (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫ h := by
  rw [add_def, comp_sub, neg_def, comp_sub, comp_zero, add_def, neg_def]
/-
**CategoryTheory.NonPreadditiveAbelian.add_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.NonPreadditiveAbelian`。
形式化陈述：add_comp (X Y Z : C) (f g : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫
 h
参数：X Y Z : C；f g : X ⟶ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_def`：add_def {X Y : C} (a b : X
 ⟶ Y) : a + b = a - -b
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.sub_comp`：sub_comp {X Y Z : C} (f g
 : X ⟶ Y) (h : Y ⟶ Z) : (f - g) ≫ h = f ≫ h - g ≫ h
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_def`：neg_def {X Y : C} (a : X ⟶
 Y) : -a = 0 - a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
theorem add_comp (X Y Z : C) (f g : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫ h := by
  rw [add_def, sub_comp, neg_def, sub_comp, zero_comp, add_def, neg_def]

/-- Every `NonPreadditiveAbelian` category is preadditive. -/
@[instance_reducible]
/-
**CategoryTheory.NonPreadditiveAbelian.preadditive** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.NonPreadditiveAbelian`。
形式化陈述：preadditive : Preadditive C where homGroup X Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_assoc`：add_assoc {X Y : C} (a b
 c : X ⟶ Y) : a + b + c = a + (b + c)
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_neg`：neg_neg {X Y : C} (a : X ⟶
 Y) : - -a = a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_zero`：add_zero {X Y : C} (a : X
 ⟶ Y) : a + 0 = a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.neg_add_cancel`：neg_add_cancel {X Y
 : C} (a : X ⟶ Y) : -a + a = 0
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_comm`：add_comm {X Y : C} (a b :
 X ⟶ Y) : a + b = b + a
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.add_comp`：add_comp (X Y Z : C) (f g
 : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫ h
· 使用定理 `CategoryTheory.NonPreadditiveAbelian.comp_add`：comp_add (X Y Z : C) (f :
 X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫ h

--- 原说明 ---
Every `NonPreadditiveAbelian` category is preadditive.
-/
def preadditive : Preadditive C where
  homGroup X Y :=
    { add_assoc := add_assoc
      zero_add := neg_neg
      add_zero := add_zero
      neg_add_cancel := neg_add_cancel
      sub_eq_add_neg f g := (add_neg f g).symm
      add_comm := add_comm
      nsmul := nsmulRec
      zsmul := zsmulRec }
  add_comp := add_comp
  comp_add := comp_add

end

end CategoryTheory.NonPreadditiveAbelian

