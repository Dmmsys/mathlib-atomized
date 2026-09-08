/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Preserving (co)kernels

Constructions to relate the notions of preserving (co)kernels and reflecting (co)kernels
to concrete (co)forks.

In particular, we show that `kernel_comparison f g G` is an isomorphism iff `G` preserves
the limit of the parallel pair `f,0`, as well as the dual result.
-/

@[expose] public section


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

namespace CategoryTheory.Limits

namespace KernelFork

variable {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
  (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.KernelFork.map_condition** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits.KernelFork`。
形式化陈述：map_condition : G.map c.ι ≫ G.map f = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.KernelFork.condition`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
 {X Y : C}   {f : X ⟶ Y} (s : Ca…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
-/
lemma map_condition : G.map c.ι ≫ G.map f = 0 := by
  rw [← G.map_comp, c.condition, G.map_zero]

/-- A kernel fork for `f` is mapped to a kernel fork for `G.map f` if `G` is a functor
which preserves zero morphisms. -/
/-
**CategoryTheory.Limits.KernelFork.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.KernelFork`。
形式化陈述：map : KernelFork (G.map f)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.KernelFork.map_condition`：map_condition : G.map c.
ι ≫ G.map f = 0

--- 原说明 ---
A kernel fork for `f` is mapped to a kernel fork for `G.map f` if `G` is a funct
or
which preserves zero morphisms.
-/
def map : KernelFork (G.map f) :=
  KernelFork.ofι (G.map c.ι) (c.map_condition G)

@[simp]
/-
**CategoryTheory.Limits.KernelFork.map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Limits.KernelFork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_ι : (c.map G).ι = G.map c.ι := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The underlying cone of a kernel fork is mapped to a limit cone if and only if
the mapped kernel fork is limit. -/
/-
**CategoryTheory.Limits.KernelFork.isLimitMapConeEquiv** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.KernelFork`。
形式化陈述：isLimitMapConeEquiv : IsLimit (G.mapCone c) ≃ IsLimit (c.map G)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The underlying cone of a kernel fork is mapped to a limit cone if and only if
the mapped kernel fork is limit.
-/
def isLimitMapConeEquiv :
    IsLimit (G.mapCone c) ≃ IsLimit (c.map G) := by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_ <;> simp
  exact Cone.ext (Iso.refl _) (by rintro (_ | _) <;> cat_disch)

/-- A limit kernel fork is mapped to a limit kernel fork by a functor `G` when this functor
preserves the corresponding limit. -/
/-
**CategoryTheory.Limits.KernelFork.mapIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.KernelFork`。
形式化陈述：mapIsLimit (hc : IsLimit c) (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]
 [PreservesLimit (parallelPair f 0) G] : IsLimit (c.map G)
参数：hc : IsLimit c；G : C ⥤ D；parallelPair f 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A limit kernel fork is mapped to a limit kernel fork by a functor `G` when this 
functor
preserves the corresponding limit.
-/
def mapIsLimit (hc : IsLimit c) (G : C ⥤ D)
    [Functor.PreservesZeroMorphisms G] [PreservesLimit (parallelPair f 0) G] :
    IsLimit (c.map G) :=
  c.isLimitMapConeEquiv G (isLimitOfPreserves G hc)

end KernelFork

section Kernels

variable (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]
  {X Y Z : C} {f : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = 0)

/-- The map of a kernel fork is a limit iff
the kernel fork consisting of the mapped morphisms is a limit.
This essentially lets us commute `KernelFork.ofι` with `Functor.mapCone`.

This is a variant of `isLimitMapConeForkEquiv` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
/-
**CategoryTheory.Limits.isLimitMapConeForkEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：isLimitMapConeForkEquiv' : IsLimit (G.mapCone (KernelFork.ofι h w)) ≃ IsLi
mit (KernelFork.ofι (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero])
 : Fork (G.map f) 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map of a kernel fork is a limit iff
the kernel fork consisting of the mapped morphisms is a limit.
This essentially lets us commute `KernelFork.ofι` with `Functor.mapCone`.

This is a variant of `isLimitMapConeForkEquiv` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isLimitMapConeForkEquiv' :
    IsLimit (G.mapCone (KernelFork.ofι h w)) ≃
      IsLimit
        (KernelFork.ofι (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
          Fork (G.map f) 0) :=
  KernelFork.isLimitMapConeEquiv _ _

/-- The property of preserving kernels expressed in terms of kernel forks.

This is a variant of `isLimitForkMapOfIsLimit` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
/-
**CategoryTheory.Limits.isLimitForkMapOfIsLimit'** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：isLimitForkMapOfIsLimit' [PreservesLimit (parallelPair f 0) G] (l : IsLimi
t (KernelFork.ofι h w)) : IsLimit (KernelFork.ofι (G.map h) (by simp only [← G.m
ap_comp, w, Functor.map_zero]) : Fork (G.map f) 0)
参数：parallelPair f 0；l : IsLimit (KernelFork.ofι h w)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of preserving kernels expressed in terms of kernel forks.

This is a variant of `isLimitForkMapOfIsLimit` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isLimitForkMapOfIsLimit' [PreservesLimit (parallelPair f 0) G]
    (l : IsLimit (KernelFork.ofι h w)) :
    IsLimit
      (KernelFork.ofι (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
        Fork (G.map f) 0) :=
  isLimitMapConeForkEquiv' G w (isLimitOfPreserves G l)

variable (f)
variable [HasKernel f]

/-- If `G` preserves kernels and `C` has them, then the fork constructed of the mapped morphisms of
a kernel fork is a limit.
-/
/-
**CategoryTheory.Limits.isLimitOfHasKernelOfPreservesLimit** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：isLimitOfHasKernelOfPreservesLimit [PreservesLimit (parallelPair f 0) G] :
 IsLimit (Fork.ofι (G.map (kernel.ι f)) (by simp only [← G.map_comp, kernel.cond
ition, comp_zero, Functor.map_zero]) : Fork (G.map f) 0)
参数：parallelPair f 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…

--- 原说明 ---
If `G` preserves kernels and `C` has them, then the fork constructed of the mapp
ed morphisms of
a kernel fork is a limit.
-/
def isLimitOfHasKernelOfPreservesLimit [PreservesLimit (parallelPair f 0) G] :
    IsLimit
      (Fork.ofι (G.map (kernel.ι f))
          (by simp only [← G.map_comp, kernel.condition, comp_zero, Functor.map_zero]) :
        Fork (G.map f) 0) :=
  isLimitForkMapOfIsLimit' G (kernel.condition f) (kernelIsKernel f)
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PreservesLimit (parallelPair f 0) G] : HasKernel (G.map f) where
  exists_limit := ⟨⟨_, isLimitOfHasKernelOfPreservesLimit G f⟩⟩

variable [HasKernel (G.map f)]

/-- If the kernel comparison map for `G` at `f` is an isomorphism, then `G` preserves the
kernel of `f`.
-/
/-
**CategoryTheory.Limits.PreservesKernel.of_iso_comparison** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.PreservesKernel`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst_2 : CategoryTheory.C
ategory.{v₂, u₂} D] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (G : C
ategoryTheory.Functor C D) [inst_4 : G.PreservesZeroMorphisms] {X Y : C} (f : X 
⟶ Y)   [inst_5 : CategoryTheory.Limits.HasKernel f] [inst_6 : CategoryTheory.Lim
its.HasKernel (G.map f)]   [i : CategoryTheory.IsIso (CategoryTheory.Limits.kern
elComparison f G)],   CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limit
s.parallelPair f 0) G
参数：G : CategoryTheory.Functor C D；f : X ⟶ Y；G.map f；CategoryTheory.Limits.kernel
Comparison f G；CategoryTheory.Limits.parallelPair f 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If the kernel comparison map for `G` at `f` is an isomorphism, then `G` preserve
s the
kernel of `f`.
-/
lemma PreservesKernel.of_iso_comparison [i : IsIso (kernelComparison f G)] :
    PreservesLimit (parallelPair f 0) G := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
  apply (isLimitMapConeForkEquiv' G (kernel.condition f)).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (kernelIsKernel (G.map f)) i

variable [PreservesLimit (parallelPair f 0) G]

/-- If `G` preserves the kernel of `f`, then the kernel comparison map for `G` at `f` is
an isomorphism.
-/
/-
**CategoryTheory.Limits.PreservesKernel.iso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.PreservesKernel`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {D : Type u₂} →         [i
nst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory
.Limits.HasZeroMorphisms D] →             (G : CategoryTheory.Functor C D) →    
           [G.PreservesZeroMorphisms] →                 {X Y : C} →             
      (f : X ⟶ Y) →                     [inst_5 : CategoryTheory.Limits.HasKerne
l f] →                       [inst_6 : CategoryTheory.Limits.HasKernel (G.map f)
] →                         [CategoryTheory.Limits.PreservesLimit (CategoryTheor
y.Limits.parallelPair f 0) G] →                           G.obj (CategoryTheory.
Limits.kernel f) ≅ CategoryTheory.Limits.kernel (G.map f)
参数：G : CategoryTheory.Functor C D；f : X ⟶ Y；G.map f；CategoryTheory.Limits.parall
elPair f 0；CategoryTheory.Limits.kernel f；G.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves the kernel of `f`, then the kernel comparison map for `G` at `f
` is
an isomorphism.
-/
def PreservesKernel.iso : G.obj (kernel f) ≅ kernel (G.map f) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasKernelOfPreservesLimit G f) (limit.isLimit _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.PreservesKernel.iso_inv_** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesKernel.iso_inv_ι :
    (PreservesKernel.iso G f).inv ≫ G.map (kernel.ι f) = kernel.ι (G.map f) :=
  IsLimit.conePointUniqueUpToIso_inv_comp (isLimitOfHasKernelOfPreservesLimit G f)
    (limit.isLimit _) (WalkingParallelPair.zero)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.PreservesKernel.iso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.PreservesKernel`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst_2 : CategoryTheory.C
ategory.{v₂, u₂} D] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (G : C
ategoryTheory.Functor C D) [inst_4 : G.PreservesZeroMorphisms] {X Y : C} (f : X 
⟶ Y)   [inst_5 : CategoryTheory.Limits.HasKernel f] [inst_6 : CategoryTheory.Lim
its.HasKernel (G.map f)]   [inst_7 : CategoryTheory.Limits.PreservesLimit (Categ
oryTheory.Limits.parallelPair f 0) G],   (CategoryTheory.Limits.PreservesKernel.
iso G f).hom = CategoryTheory.Limits.kernelComparison f G
参数：G : CategoryTheory.Functor C D；f : X ⟶ Y；G.map f；CategoryTheory.Limits.parall
elPair f 0；CategoryTheory.Limits.PreservesKernel.iso G f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.kernelComparison_comp_ι`：kernelComparison_comp_ι [
HasKernel f] [HasKernel (G.map f)] : kernelComparison f G ≫ kernel.ι (G.map f) =
 G.map (kernel.ι f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesKernel.iso_hom : (PreservesKernel.iso G f).hom = kernelComparison f G := by
  rw [← cancel_mono (kernel.ι _)]
  simp [PreservesKernel.iso]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (kernelComparison f G) := by
  rw [← PreservesKernel.iso_hom]
  infer_instance

@[reassoc]
/-
**CategoryTheory.Limits.kernel_map_comp_preserves_kernel_iso_inv** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：kernel_map_comp_preserves_kernel_iso_inv {X' Y' : C} (g : X' ⟶ Y') [HasKer
nel g] [HasKernel (G.map g)] [PreservesLimit (parallelPair g 0) G] (p : X ⟶ X') 
(q : Y ⟶ Y') (hpq : f ≫ q = p ≫ g) : kernel.map (G.map f) (G.map g) (G.map p) (G
.map q) (by rw [← G.map_comp, hpq, G.map_comp]) ≫ (PreservesKernel.iso G _).inv 
= (PreservesKernel.iso G _).inv ≫ G.map (kernel.map f g p q hpq)
参数：g : X' ⟶ Y'；G.map g；parallelPair g 0；p : X ⟶ X'；q : Y ⟶ Y'；hpq : f ≫ q = p ≫ 
g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.PreservesKernel.iso_hom`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms C]   {D : Type u₂} [inst_2 : Ca…
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `CategoryTheory.Limits.kernelComparison_comp_kernel_map`：kernelComparison
_comp_kernel_map {X' Y' : C} [HasKernel f] [HasKernel (G.map f)] (g : X' ⟶ Y') [
HasKernel g] [HasKernel (G.map g)] (p : X ⟶ …
-/
theorem kernel_map_comp_preserves_kernel_iso_inv {X' Y' : C} (g : X' ⟶ Y') [HasKernel g]
    [HasKernel (G.map g)] [PreservesLimit (parallelPair g 0) G] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    kernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) ≫
        (PreservesKernel.iso G _).inv =
      (PreservesKernel.iso G _).inv ≫ G.map (kernel.map f g p q hpq) := by
  rw [Iso.comp_inv_eq, Category.assoc, PreservesKernel.iso_hom, Iso.eq_inv_comp,
    PreservesKernel.iso_hom, kernelComparison_comp_kernel_map]

end Kernels

namespace CokernelCofork

variable {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
  (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.CokernelCofork.map_condition** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits.CokernelCofork`。
形式化陈述：map_condition : G.map f ≫ G.map c.π = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.CokernelCofork.condition`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   {f : X ⟶ Y} (s : Ca…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
-/
lemma map_condition : G.map f ≫ G.map c.π = 0 := by
  rw [← G.map_comp, c.condition, G.map_zero]

/-- A cokernel cofork for `f` is mapped to a cokernel cofork for `G.map f` if `G` is a functor
which preserves zero morphisms. -/
/-
**CategoryTheory.Limits.CokernelCofork.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.CokernelCofork`。
形式化陈述：map : CokernelCofork (G.map f)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CokernelCofork.map_condition`：map_condition : G.ma
p f ≫ G.map c.π = 0

--- 原说明 ---
A cokernel cofork for `f` is mapped to a cokernel cofork for `G.map f` if `G` is
 a functor
which preserves zero morphisms.
-/
def map : CokernelCofork (G.map f) :=
  CokernelCofork.ofπ (G.map c.π) (c.map_condition G)

@[simp]
/-
**CategoryTheory.Limits.CokernelCofork.map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Limits.CokernelCofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_π : (c.map G).π = G.map c.π := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The underlying cocone of a cokernel cofork is mapped to a colimit cocone if and only if
the mapped cokernel cofork is colimit. -/
/-
**CategoryTheory.Limits.CokernelCofork.isColimitMapCoconeEquiv** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Limits.CokernelCofork`。
形式化陈述：isColimitMapCoconeEquiv : IsColimit (G.mapCocone c) ≃ IsColimit (c.map G)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The underlying cocone of a cokernel cofork is mapped to a colimit cocone if and 
only if
the mapped cokernel cofork is colimit.
-/
def isColimitMapCoconeEquiv :
    IsColimit (G.mapCocone c) ≃ IsColimit (c.map G) := by
  refine (IsColimit.precomposeHomEquiv ?_ _).symm.trans (IsColimit.equivIsoColimit ?_)
  refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_ <;> simp
  exact Cocone.ext (Iso.refl _) (by rintro (_ | _) <;> cat_disch)

/-- A colimit cokernel cofork is mapped to a colimit cokernel cofork by a functor `G`
when this functor preserves the corresponding colimit. -/
/-
**CategoryTheory.Limits.CokernelCofork.mapIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.CokernelCofork`。
形式化陈述：mapIsColimit (hc : IsColimit c) (G : C ⥤ D) [Functor.PreservesZeroMorphism
s G] [PreservesColimit (parallelPair f 0) G] : IsColimit (c.map G)
参数：hc : IsColimit c；G : C ⥤ D；parallelPair f 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A colimit cokernel cofork is mapped to a colimit cokernel cofork by a functor `G
`
when this functor preserves the corresponding colimit.
-/
def mapIsColimit (hc : IsColimit c) (G : C ⥤ D)
    [Functor.PreservesZeroMorphisms G] [PreservesColimit (parallelPair f 0) G] :
    IsColimit (c.map G) :=
  c.isColimitMapCoconeEquiv G (isColimitOfPreserves G hc)

end CokernelCofork

section Cokernels

variable (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]
  {X Y Z : C} {f : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = 0)

/-- The map of a cokernel cofork is a colimit iff
the cokernel cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `CokernelCofork.ofπ` with `Functor.mapCocone`.

This is a variant of `isColimitMapCoconeCoforkEquiv` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
/-
**CategoryTheory.Limits.isColimitMapCoconeCoforkEquiv'** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：isColimitMapCoconeCoforkEquiv' : IsColimit (G.mapCocone (CokernelCofork.of
π h w)) ≃ IsColimit (CokernelCofork.ofπ (G.map h) (by simp only [← G.map_comp, w
, Functor.map_zero]) : Cofork (G.map f) 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map of a cokernel cofork is a colimit iff
the cokernel cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `CokernelCofork.ofπ` with `Functor.mapCocone`.

This is a variant of `isColimitMapCoconeCoforkEquiv` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isColimitMapCoconeCoforkEquiv' :
    IsColimit (G.mapCocone (CokernelCofork.ofπ h w)) ≃
      IsColimit
        (CokernelCofork.ofπ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
          Cofork (G.map f) 0) :=
  CokernelCofork.isColimitMapCoconeEquiv _ _

/-- The property of preserving cokernels expressed in terms of cokernel coforks.

This is a variant of `isColimitCoforkMapOfIsColimit` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
/-
**CategoryTheory.Limits.isColimitCoforkMapOfIsColimit'** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：isColimitCoforkMapOfIsColimit' [PreservesColimit (parallelPair f 0) G] (l 
: IsColimit (CokernelCofork.ofπ h w)) : IsColimit (CokernelCofork.ofπ (G.map h) 
(by simp only [← G.map_comp, w, Functor.map_zero]) : Cofork (G.map f) 0)
参数：parallelPair f 0；l : IsColimit (CokernelCofork.ofπ h w)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of preserving cokernels expressed in terms of cokernel coforks.

This is a variant of `isColimitCoforkMapOfIsColimit` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isColimitCoforkMapOfIsColimit' [PreservesColimit (parallelPair f 0) G]
    (l : IsColimit (CokernelCofork.ofπ h w)) :
    IsColimit
      (CokernelCofork.ofπ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
        Cofork (G.map f) 0) :=
  isColimitMapCoconeCoforkEquiv' G w (isColimitOfPreserves G l)

variable (f)
variable [HasCokernel f]

/--
If `G` preserves cokernels and `C` has them, then the cofork constructed of the mapped morphisms of
a cokernel cofork is a colimit.
-/
/-
**CategoryTheory.Limits.isColimitOfHasCokernelOfPreservesColimit** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isColimitOfHasCokernelOfPreservesColimit [PreservesColimit (parallelPair f
 0) G] : IsColimit (Cofork.ofπ (G.map (cokernel.π f)) (by simp only [← G.map_com
p, cokernel.condition, zero_comp, Functor.map_zero]) : Cofork (G.map f) 0)
参数：parallelPair f 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…

--- 原说明 ---
If `G` preserves cokernels and `C` has them, then the cofork constructed of the 
mapped morphisms of
a cokernel cofork is a colimit.
-/
def isColimitOfHasCokernelOfPreservesColimit [PreservesColimit (parallelPair f 0) G] :
    IsColimit
      (Cofork.ofπ (G.map (cokernel.π f))
          (by simp only [← G.map_comp, cokernel.condition, zero_comp, Functor.map_zero]) :
        Cofork (G.map f) 0) :=
  isColimitCoforkMapOfIsColimit' G (cokernel.condition f) (cokernelIsCokernel f)
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PreservesColimit (parallelPair f 0) G] : HasCokernel (G.map f) where
  exists_colimit := ⟨⟨_, isColimitOfHasCokernelOfPreservesColimit G f⟩⟩

variable [HasCokernel (G.map f)]

/-- If the cokernel comparison map for `G` at `f` is an isomorphism, then `G` preserves the
cokernel of `f`.
-/
/-
**CategoryTheory.Limits.PreservesCokernel.of_iso_comparison** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.PreservesCokernel`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst_2 : CategoryTheory.C
ategory.{v₂, u₂} D] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (G : C
ategoryTheory.Functor C D) [inst_4 : G.PreservesZeroMorphisms] {X Y : C} (f : X 
⟶ Y)   [inst_5 : CategoryTheory.Limits.HasCokernel f] [inst_6 : CategoryTheory.L
imits.HasCokernel (G.map f)]   [i : CategoryTheory.IsIso (CategoryTheory.Limits.
cokernelComparison f G)],   CategoryTheory.Limits.PreservesColimit (CategoryTheo
ry.Limits.parallelPair f 0) G
参数：G : CategoryTheory.Functor C D；f : X ⟶ Y；G.map f；CategoryTheory.Limits.cokern
elComparison f G；CategoryTheory.Limits.parallelPair f 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If the cokernel comparison map for `G` at `f` is an isomorphism, then `G` preser
ves the
cokernel of `f`.
-/
lemma PreservesCokernel.of_iso_comparison [i : IsIso (cokernelComparison f G)] :
    PreservesColimit (parallelPair f 0) G := by
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
  apply (isColimitMapCoconeCoforkEquiv' G (cokernel.condition f)).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ (cokernelIsCokernel (G.map f)) i

variable [PreservesColimit (parallelPair f 0) G]

/-- If `G` preserves the cokernel of `f`, then the cokernel comparison map for `G` at `f` is
an isomorphism.
-/
/-
**CategoryTheory.Limits.PreservesCokernel.iso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.PreservesCokernel`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {D : Type u₂} →         [i
nst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory
.Limits.HasZeroMorphisms D] →             (G : CategoryTheory.Functor C D) →    
           [G.PreservesZeroMorphisms] →                 {X Y : C} →             
      (f : X ⟶ Y) →                     [inst_5 : CategoryTheory.Limits.HasCoker
nel f] →                       [inst_6 : CategoryTheory.Limits.HasCokernel (G.ma
p f)] →                         [CategoryTheory.Limits.PreservesColimit (Categor
yTheory.Limits.parallelPair f 0) G] →                           G.obj (CategoryT
heory.Limits.cokernel f) ≅ CategoryTheory.Limits.cokernel (G.map f)
参数：G : CategoryTheory.Functor C D；f : X ⟶ Y；G.map f；CategoryTheory.Limits.parall
elPair f 0；CategoryTheory.Limits.cokernel f；G.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves the cokernel of `f`, then the cokernel comparison map for `G` a
t `f` is
an isomorphism.
-/
def PreservesCokernel.iso : G.obj (cokernel f) ≅ cokernel (G.map f) :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfHasCokernelOfPreservesColimit G f)
    (colimit.isColimit _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.PreservesCokernel.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesCokernel.π_iso_hom : G.map (cokernel.π f) ≫ (iso G f).hom = cokernel.π (G.map f) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (isColimitOfHasCokernelOfPreservesColimit G f)
    (colimit.isColimit _) (WalkingParallelPair.one)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.PreservesCokernel.iso_inv** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.PreservesCokernel`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst_2 : CategoryTheory.C
ategory.{v₂, u₂} D] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (G : C
ategoryTheory.Functor C D) [inst_4 : G.PreservesZeroMorphisms] {X Y : C} (f : X 
⟶ Y)   [inst_5 : CategoryTheory.Limits.HasCokernel f] [inst_6 : CategoryTheory.L
imits.HasCokernel (G.map f)]   [inst_7 : CategoryTheory.Limits.PreservesColimit 
(CategoryTheory.Limits.parallelPair f 0) G],   (CategoryTheory.Limits.PreservesC
okernel.iso G f).inv = CategoryTheory.Limits.cokernelComparison f G
参数：G : CategoryTheory.Functor C D；f : X ⟶ Y；G.map f；CategoryTheory.Limits.parall
elPair f 0；CategoryTheory.Limits.PreservesCokernel.iso G f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.comp_coconePointUniqueUpToIso_inv`：∀ {J : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Cate
goryTheory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.π_comp_cokernelComparison`：π_comp_cokernelComparis
on [HasCokernel f] [HasCokernel (G.map f)] : cokernel.π (G.map f) ≫ cokernelComp
arison f G = G.map (cokernel.π _)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesCokernel.iso_inv : (PreservesCokernel.iso G f).inv = cokernelComparison f G := by
  rw [← cancel_epi (cokernel.π _)]
  simp [PreservesCokernel.iso]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (cokernelComparison f G) := by
  rw [← PreservesCokernel.iso_inv]
  infer_instance

@[reassoc]
/-
**CategoryTheory.Limits.preserves_cokernel_iso_comp_cokernel_map** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preserves_cokernel_iso_comp_cokernel_map {X' Y' : C} (g : X' ⟶ Y') [HasCok
ernel g] [HasCokernel (G.map g)] [PreservesColimit (parallelPair g 0) G] (p : X 
⟶ X') (q : Y ⟶ Y') (hpq : f ≫ q = p ≫ g) : (PreservesCokernel.iso G _).hom ≫ cok
ernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.m
ap_comp]) = G.map (cokernel.map f g p q hpq) ≫ (PreservesCokernel.iso G _).hom
参数：g : X' ⟶ Y'；G.map g；parallelPair g 0；p : X ⟶ X'；q : Y ⟶ Y'；hpq : f ≫ q = p ≫ 
g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `CategoryTheory.Limits.PreservesCokernel.iso_inv`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {D : Type u₂} [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.cokernel_map_comp_cokernelComparison`：cokernel_map
_comp_cokernelComparison {X' Y' : C} [HasCokernel f] [HasCokernel (G.map f)] (g 
: X' ⟶ Y') [HasCokernel g] [HasCokernel (G.map g…
-/
theorem preserves_cokernel_iso_comp_cokernel_map {X' Y' : C} (g : X' ⟶ Y') [HasCokernel g]
    [HasCokernel (G.map g)] [PreservesColimit (parallelPair g 0) G] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    (PreservesCokernel.iso G _).hom ≫
        cokernel.map (G.map f) (G.map g) (G.map p) (G.map q)
          (by rw [← G.map_comp, hpq, G.map_comp]) =
      G.map (cokernel.map f g p q hpq) ≫ (PreservesCokernel.iso G _).hom := by
  rw [← Iso.comp_inv_eq, Category.assoc, ← Iso.eq_inv_comp, PreservesCokernel.iso_inv,
    cokernel_map_comp_cokernelComparison, PreservesCokernel.iso_inv]

end Cokernels

variable (X Y : C) (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.preservesKernel_zero** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits`。
形式化陈述：preservesKernel_zero : PreservesLimit (parallelPair (0 : X ⟶ Y) 0) G where
 preserves {c} hc
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.KernelFork.IsLimit.isIso_ι`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms C] {X Y : C}   {f : X ⟶ Y} (c : Ca…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance preservesKernel_zero :
    PreservesLimit (parallelPair (0 : X ⟶ Y) 0) G where
  preserves {c} hc := ⟨by
    have := KernelFork.IsLimit.isIso_ι c hc rfl
    refine (KernelFork.isLimitMapConeEquiv c G).symm ?_
    refine IsLimit.ofIsoLimit (KernelFork.IsLimit.ofId _ (G.map_zero _ _)) ?_
    exact (Fork.ext (G.mapIso (asIso (Fork.ι c))).symm (by simp))⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.preservesCokernel_zero** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：preservesCokernel_zero : PreservesColimit (parallelPair (0 : X ⟶ Y) 0) G w
here preserves {c} hc
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.CokernelCofork.IsColimit.isIso_π`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {X Y : C}   {f : X ⟶ Y} (c : Ca…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
noncomputable instance preservesCokernel_zero :
    PreservesColimit (parallelPair (0 : X ⟶ Y) 0) G where
  preserves {c} hc := ⟨by
    have := CokernelCofork.IsColimit.isIso_π c hc rfl
    refine (CokernelCofork.isColimitMapCoconeEquiv c G).symm ?_
    refine IsColimit.ofIsoColimit (CokernelCofork.IsColimit.ofId _ (G.map_zero _ _)) ?_
    exact (Cofork.ext (G.mapIso (asIso (Cofork.π c))) (by simp))⟩

variable {X Y}

/-- The kernel of a zero map is preserved by any functor which preserves zero morphisms. -/
/-
**CategoryTheory.Limits.preservesKernel_zero'** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：preservesKernel_zero' (f : X ⟶ Y) (hf : f = 0) : PreservesLimit (parallelP
air f 0) G
参数：f : X ⟶ Y；hf : f = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The kernel of a zero map is preserved by any functor which preserves zero morphi
sms.
-/
lemma preservesKernel_zero' (f : X ⟶ Y) (hf : f = 0) :
    PreservesLimit (parallelPair f 0) G := by
  rw [hf]
  infer_instance

/-- The cokernel of a zero map is preserved by any functor which preserves zero morphisms. -/
/-
**CategoryTheory.Limits.preservesCokernel_zero'** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：preservesCokernel_zero' (f : X ⟶ Y) (hf : f = 0) : PreservesColimit (paral
lelPair f 0) G
参数：f : X ⟶ Y；hf : f = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The cokernel of a zero map is preserved by any functor which preserves zero morp
hisms.
-/
lemma preservesCokernel_zero' (f : X ⟶ Y) (hf : f = 0) :
    PreservesColimit (parallelPair f 0) G := by
  rw [hf]
  infer_instance

section ZeroObject

variable [HasZeroObject C] [HasZeroObject D]

variable {X Y : C} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
/-- Mapping a `zeroKernelFork` of `f : X ⟶ Y` along a functor `G` that preserves zero morphisms
is isomorphic to the `zeroKernelFork` of `G.map f`. -/
/-
**CategoryTheory.Limits.mapZeroKernelFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：mapZeroKernelFork : (kernel.zeroKernelFork f).map G ≅ (kernel.zeroKernelFo
rk (G.map f))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mapping a `zeroKernelFork` of `f : X ⟶ Y` along a functor `G` that preserves zer
o morphisms
is isomorphic to the `zeroKernelFork` of `G.map f`.
-/
def mapZeroKernelFork :
    (kernel.zeroKernelFork f).map G ≅ (kernel.zeroKernelFork (G.map f)) :=
  Fork.ext G.mapZeroObject

set_option backward.defeqAttrib.useBackward true in
/-- Mapping a `zeroCokernelCofork` of `f : X ⟶ Y` along a functor `G` that preserves zero morphisms
is isomorphic to the `zeroCokernelCofork` of `G.map f`. -/
/-
**CategoryTheory.Limits.mapZeroCokernelCofork** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：mapZeroCokernelCofork : (cokernel.zeroCokernelCofork f).map G ≅ (cokernel.
zeroCokernelCofork (G.map f))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mapping a `zeroCokernelCofork` of `f : X ⟶ Y` along a functor `G` that preserves
 zero morphisms
is isomorphic to the `zeroCokernelCofork` of `G.map f`.
-/
def mapZeroCokernelCofork :
    (cokernel.zeroCokernelCofork f).map G ≅ (cokernel.zeroCokernelCofork (G.map f)) :=
  Cofork.ext G.mapZeroObject

end ZeroObject

end CategoryTheory.Limits

