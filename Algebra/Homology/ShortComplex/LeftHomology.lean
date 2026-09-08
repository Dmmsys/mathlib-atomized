/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Left Homology of short complexes

Given a short complex `S : ShortComplex C`, which consists of two composable
maps `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that `f ≫ g = 0`, we shall define
here the "left homology" `S.leftHomology` of `S`. For this, we introduce the
notion of "left homology data". Such an `h : S.LeftHomologyData` consists of the
data of morphisms `i : K ⟶ X₂` and `π : K ⟶ H` such that `i` identifies
`K` with the kernel of `g : X₂ ⟶ X₃`, and that `π` identifies `H` with the cokernel
of the induced map `f' : X₁ ⟶ K`.

When such a `S.LeftHomologyData` exists, we shall say that `[S.HasLeftHomology]`
and we define `S.leftHomology` to be the `H` field of a chosen left homology data.
Similarly, we define `S.cycles` to be the `K` field.

The dual notion is defined in `RightHomologyData.lean`. In `Homology.lean`,
when `S` has two compatible left and right homology data (i.e. they give
the same `H` up to a canonical isomorphism), we shall define `[S.HasHomology]`
and `S.homology`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

/-- A left homology data for a short complex `S` consists of morphisms `i : K ⟶ S.X₂` and
`π : K ⟶ H` such that `i` identifies `K` to the kernel of `g : S.X₂ ⟶ S.X₃`,
and that `π` identifies `H` to the cokernel of the induced map `f' : S.X₁ ⟶ K` -/
/-
**CategoryTheory.ShortComplex.LeftHomologyData** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] → CategoryTheory.ShortComplex C
 → Type (max u_1 v_1)
参数：max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A left homology data for a short complex `S` consists of morphisms `i : K ⟶ S.X₂
` and
`π : K ⟶ H` such that `i` identifies `K` to the kernel of `g : S.X₂ ⟶ S.X₃`,
and that `π` identifies `H` to the cokernel of the induced map `f' : S.X₁ ⟶ K`
-/
structure LeftHomologyData where
  /-- a choice of kernel of `S.g : S.X₂ ⟶ S.X₃` -/
  K : C
  /-- a choice of cokernel of the induced morphism `S.f' : S.X₁ ⟶ K` -/
  H : C
  /-- the inclusion of cycles in `S.X₂` -/
  i : K ⟶ S.X₂
  /-- the projection from cycles to the (left) homology -/
  π : K ⟶ H
  /-- the kernel condition for `i` -/
  wi : i ≫ S.g = 0
  /-- `i : K ⟶ S.X₂` is a kernel of `g : S.X₂ ⟶ S.X₃` -/
  hi : IsLimit (KernelFork.ofι i wi)
  /-- the cokernel condition for `π` -/
  wπ : hi.lift (KernelFork.ofι _ S.zero) ≫ π = 0
  /-- `π : K ⟶ H` is a cokernel of the induced morphism `S.f' : S.X₁ ⟶ K` -/
  hπ : IsColimit (CokernelCofork.ofπ π wπ)

initialize_simps_projections LeftHomologyData (-hi, -hπ)

namespace LeftHomologyData

set_option backward.isDefEq.respectTransparency false in
/-- The chosen kernels and cokernels of the limits API give a `LeftHomologyData` -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：ofHasKernelOfHasCokernel [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f
 S.zero)] : S.LeftHomologyData where K
参数：kernel.lift S.g S.f S.zero。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…

--- 原说明 ---
The chosen kernels and cokernels of the limits API give a `LeftHomologyData`
-/
noncomputable def ofHasKernelOfHasCokernel
    [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f S.zero)] :
    S.LeftHomologyData where
  K := kernel S.g
  H := cokernel (kernel.lift S.g S.f S.zero)
  i := kernel.ι _
  π := cokernel.π _
  wi := kernel.condition _
  hi := kernelIsKernel _
  wπ := cokernel.condition _
  hπ := cokernelIsCokernel _

attribute [reassoc (attr := simp)] wi wπ

variable {S}
variable (h : S.LeftHomologyData) {A : C}
/-
**CategoryTheory.ShortComplex.LeftHomologyData.** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.ShortComplex.LeftHomologyData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono h.i := ⟨fun _ _ => Fork.IsLimit.hom_ext h.hi⟩
/-
**CategoryTheory.ShortComplex.LeftHomologyData.** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.ShortComplex.LeftHomologyData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi h.π := ⟨fun _ _ => Cofork.IsColimit.hom_ext h.hπ⟩

/-- Any morphism `k : A ⟶ S.X₂` that is a cycle (i.e. `k ≫ S.g = 0`) lifts
to a morphism `A ⟶ K` -/
/-
**CategoryTheory.ShortComplex.LeftHomologyData.liftK** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：liftK (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ h.K
参数：k : A ⟶ S.X₂；hk : k ≫ S.g = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wi`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…

--- 原说明 ---
Any morphism `k : A ⟶ S.X₂` that is a cycle (i.e. `k ≫ S.g = 0`) lifts
to a morphism `A ⟶ K`
-/
def liftK (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ h.K := h.hi.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.liftK_i** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：liftK_i (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : h.liftK k hk ≫ h.i = k
参数：k : A ⟶ S.X₂；hk : k ≫ S.g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wi`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
-/
lemma liftK_i (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : h.liftK k hk ≫ h.i = k :=
  h.hi.fac _ WalkingParallelPair.zero

/-- The (left) homology class `A ⟶ H` attached to a cycle `k : A ⟶ S.X₂` -/
@[simp]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.liftH** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：liftH (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ h.H
参数：k : A ⟶ S.X₂；hk : k ≫ S.g = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (left) homology class `A ⟶ H` attached to a cycle `k : A ⟶ S.X₂`
-/
def liftH (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ h.H := h.liftK k hk ≫ h.π

/-- Given `h : LeftHomologyData S`, this is morphism `S.X₁ ⟶ h.K` induced
by `S.f : S.X₁ ⟶ S.X₂` and the fact that `h.K` is a kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
/-
**CategoryTheory.ShortComplex.LeftHomologyData.f'** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：f' : S.X₁ ⟶ h.K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…

--- 原说明 ---
Given `h : LeftHomologyData S`, this is morphism `S.X₁ ⟶ h.K` induced
by `S.f : S.X₁ ⟶ S.X₂` and the fact that `h.K` is a kernel of `S.g : S.X₂ ⟶ S.X₃
`.
-/
def f' : S.X₁ ⟶ h.K := h.liftK S.f S.zero
/-
**CategoryTheory.ShortComplex.LeftHomologyData.f'_i** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (
h : S.LeftHomologyData), CategoryTheory.CategoryStruct.comp h.f' h.i = S.f
参数：h : S.LeftHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.liftK_i`：liftK_i (k : A ⟶ S
.X₂) (hk : k ≫ S.g = 0) : h.liftK k hk ≫ h.i = k
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
-/
@[reassoc (attr := simp)] lemma f'_i : h.f' ≫ h.i = S.f := liftK_i _ _ _
/-
**CategoryTheory.ShortComplex.LeftHomologyData.f'_** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ShortComplex.LeftHomologyData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[reassoc (attr := simp)] lemma f'_π : h.f' ≫ h.π = 0 := h.wπ

@[reassoc]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.liftK_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ShortComplex.LeftHomologyData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftK_π_eq_zero_of_boundary (k : A ⟶ S.X₂) (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    h.liftK k (by rw [hx, assoc, S.zero, comp_zero]) ≫ h.π = 0 := by
  rw [show 0 = (x ≫ h.f') ≫ h.π by simp]
  congr 1
  simp only [← cancel_mono h.i, hx, liftK_i, assoc, f'_i]

/-- For `h : S.LeftHomologyData`, this is a restatement of `h.hπ`, saying that
`π : h.K ⟶ h.H` is a cokernel of `h.f' : S.X₁ ⟶ h.K`. -/
/-
**CategoryTheory.ShortComplex.LeftHomologyData.h** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex.LeftHomologyData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `h : S.LeftHomologyData`, this is a restatement of `h.hπ`, saying that
`π : h.K ⟶ h.H` is a cokernel of `h.f' : S.X₁ ⟶ h.K`.
-/
def hπ' : IsColimit (CokernelCofork.ofπ h.π h.f'_π) := h.hπ

/-- The morphism `H ⟶ A` induced by a morphism `k : K ⟶ A` such that `f' ≫ k = 0` -/
/-
**CategoryTheory.ShortComplex.LeftHomologyData.descH** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：descH (k : h.K ⟶ A) (hk : h.f' ≫ k = 0) : h.H ⟶ A
参数：k : h.K ⟶ A；hk : h.f' ≫ k = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wi`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wπ`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…

--- 原说明 ---
The morphism `H ⟶ A` induced by a morphism `k : K ⟶ A` such that `f' ≫ k = 0`
-/
def descH (k : h.K ⟶ A) (hk : h.f' ≫ k = 0) : h.H ⟶ A :=
  h.hπ.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ShortComplex.LeftHomologyData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_descH (k : h.K ⟶ A) (hk : h.f' ≫ k = 0) : h.π ≫ h.descH k hk = k :=
  h.hπ.fac (CokernelCofork.ofπ k hk) WalkingParallelPair.one
/-
**CategoryTheory.ShortComplex.LeftHomologyData.isIso_i** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：isIso_i (hg : S.g = 0) : IsIso h.i
参数：hg : S.g = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instMonoI`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.liftK_i`：liftK_i (k : A ⟶ S
.X₂) (hk : k ≫ S.g = 0) : h.liftK k hk ≫ h.i = k
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isIso_i (hg : S.g = 0) : IsIso h.i :=
  ⟨h.liftK (𝟙 S.X₂) (by rw [hg, id_comp]),
    by simp only [← cancel_mono h.i, id_comp, assoc, liftK_i, comp_id], liftK_i _ _ _⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.LeftHomologyData.isIso_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ShortComplex.LeftHomologyData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_π (hf : S.f = 0) : IsIso h.π := by
  have ⟨φ, hφ⟩ := CokernelCofork.IsColimit.desc' h.hπ' (𝟙 _)
    (by rw [← cancel_mono h.i, comp_id, f'_i, zero_comp, hf])
  dsimp at hφ
  exact ⟨φ, hφ, by rw [← cancel_epi h.π, reassoc_of% hφ, comp_id]⟩

variable (S)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- When the second map `S.g` is zero, this is the left homology data on `S` given
by any colimit cokernel cofork of `S.f` -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：ofIsColimitCokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : Is
Colimit c) : S.LeftHomologyData where K
参数：hg : S.g = 0；c : CokernelCofork S.f；hc : IsColimit c。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…

--- 原说明 ---
When the second map `S.g` is zero, this is the left homology data on `S` given
by any colimit cokernel cofork of `S.f`
-/
def ofIsColimitCokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c) :
    S.LeftHomologyData where
  K := S.X₂
  H := c.pt
  i := 𝟙 _
  π := c.π
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.ofId _ hg
  wπ := CokernelCofork.condition _
  hπ := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _))
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork_f'** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComplex C) (
hg : S.g = 0) (c : CategoryTheory.Limits.CokernelCofork S.f)   (hc : CategoryThe
ory.Limits.IsColimit c),   (CategoryTheory.ShortComplex.LeftHomologyData.ofIsCol
imitCokernelCofork S hg c hc).f' = S.f
参数：S : CategoryTheory.ShortComplex C；hg : S.g = 0；c : CategoryTheory.Limits.Coke
rnelCofork S.f；hc : CategoryTheory.Limits.IsColimit c；CategoryTheory.ShortComple
x.LeftHomologyData.ofIsColimitCokernelCofork S hg c hc。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofIsColimitCokernelCofork_f' (hg : S.g = 0) (c : CokernelCofork S.f)
    (hc : IsColimit c) : (ofIsColimitCokernelCofork S hg c hc).f' = S.f := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork_liftK**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：ofIsColimitCokernelCofork_liftK (hg : S.g = 0) (c : CokernelCofork S.f) (h
c : IsColimit c) {T : C} (φ : T ⟶ S.X₂) : dsimp% (ofIsColimitCokernelCofork S hg
 c hc).liftK φ (by simp [hg]) = φ
参数：hg : S.g = 0；c : CokernelCofork S.f；hc : IsColimit c；φ : T ⟶ S.X₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instMonoI`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.liftK_i`：liftK_i (k : A ⟶ S
.X₂) (hk : k ≫ S.g = 0) : h.liftK k hk ≫ h.i = k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofIsColimitCokernelCofork_liftK (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c)
    {T : C} (φ : T ⟶ S.X₂) :
    dsimp% (ofIsColimitCokernelCofork S hg c hc).liftK φ (by simp [hg]) = φ := by
  rw [← cancel_mono (ofIsColimitCokernelCofork S hg c hc).i, liftK_i]
  simp

/-- When the second map `S.g` is zero, this is the left homology data on `S` given by
the chosen `cokernel S.f` -/
@[simps!]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofHasCokernel** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：ofHasCokernel [HasCokernel S.f] (hg : S.g = 0) : S.LeftHomologyData
参数：hg : S.g = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the second map `S.g` is zero, this is the left homology data on `S` given b
y
the chosen `cokernel S.f`
-/
noncomputable def ofHasCokernel [HasCokernel S.f] (hg : S.g = 0) : S.LeftHomologyData :=
  ofIsColimitCokernelCofork S hg _ (cokernelIsCokernel _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When the first map `S.f` is zero, this is the left homology data on `S` given
by any limit kernel fork of `S.g` -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofIsLimitKernelFork** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：ofIsLimitKernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
 S.LeftHomologyData where K
参数：hf : S.f = 0；c : KernelFork S.g；hc : IsLimit c。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…

--- 原说明 ---
When the first map `S.f` is zero, this is the left homology data on `S` given
by any limit kernel fork of `S.g`
-/
def ofIsLimitKernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
    S.LeftHomologyData where
  K := c.pt
  H := c.pt
  i := c.ι
  π := 𝟙 _
  wi := KernelFork.condition _
  hi := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _))
  wπ := Fork.IsLimit.hom_ext hc (by
    dsimp
    simp only [comp_id, zero_comp, Fork.IsLimit.lift_ι, Fork.ι_ofι, hf])
  hπ := CokernelCofork.IsColimit.ofId _ (Fork.IsLimit.hom_ext hc (by
    dsimp
    simp only [comp_id, zero_comp, Fork.IsLimit.lift_ι, Fork.ι_ofι, hf]))
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofIsLimitKernelFork_f'** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComplex C) (
hf : S.f = 0) (c : CategoryTheory.Limits.KernelFork S.g)   (hc : CategoryTheory.
Limits.IsLimit c),   (CategoryTheory.ShortComplex.LeftHomologyData.ofIsLimitKern
elFork S hf c hc).f' = 0
参数：S : CategoryTheory.ShortComplex C；hf : S.f = 0；c : CategoryTheory.Limits.Kern
elFork S.g；hc : CategoryTheory.Limits.IsLimit c；CategoryTheory.ShortComplex.Left
HomologyData.ofIsLimitKernelFork S hf c hc。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instMonoI`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_i`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
@[simp] lemma ofIsLimitKernelFork_f' (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
    (ofIsLimitKernelFork S hf c hc).f' = 0 := by
  rw [← cancel_mono (ofIsLimitKernelFork S hf c hc).i, f'_i, hf, zero_comp]

/-- When the first map `S.f` is zero, this is the left homology data on `S` given
by the chosen `kernel S.g` -/
@[simp]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofHasKernel** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：ofHasKernel [HasKernel S.g] (hf : S.f = 0) : S.LeftHomologyData
参数：hf : S.f = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the first map `S.f` is zero, this is the left homology data on `S` given
by the chosen `kernel S.g`
-/
noncomputable def ofHasKernel [HasKernel S.g] (hf : S.f = 0) : S.LeftHomologyData :=
  ofIsLimitKernelFork S hf _ (kernelIsKernel _)

/-- When both `S.f` and `S.g` are zero, the middle object `S.X₂` gives a left homology data on S -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofZeros** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：ofZeros (hf : S.f = 0) (hg : S.g = 0) : S.LeftHomologyData where K
参数：hf : S.f = 0；hg : S.g = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When both `S.f` and `S.g` are zero, the middle object `S.X₂` gives a left homolo
gy data on S
-/
def ofZeros (hf : S.f = 0) (hg : S.g = 0) : S.LeftHomologyData where
  K := S.X₂
  H := S.X₂
  i := 𝟙 _
  π := 𝟙 _
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.ofId _ hg
  wπ := by
    change S.f ≫ 𝟙 _ = 0
    simp only [hf, zero_comp]
  hπ := CokernelCofork.IsColimit.ofId _ hf
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofZeros_f'** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComplex C) (
hf : S.f = 0) (hg : S.g = 0),   (CategoryTheory.ShortComplex.LeftHomologyData.of
Zeros S hf hg).f' = 0
参数：S : CategoryTheory.ShortComplex C；hf : S.f = 0；hg : S.g = 0；CategoryTheory.Sh
ortComplex.LeftHomologyData.ofZeros S hf hg。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instMonoI`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_i`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…
-/
@[simp] lemma ofZeros_f' (hf : S.f = 0) (hg : S.g = 0) :
    (ofZeros S hf hg).f' = 0 := by
  rw [← cancel_mono ((ofZeros S hf hg).i), zero_comp, f'_i, hf]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {S} in
/-- Given a left homology data `h` of a short complex `S`, we can construct another left homology
data by choosing another kernel and cokernel that are isomorphic to the ones in `h`. -/
/-
**CategoryTheory.ShortComplex.LeftHomologyData.copy** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {S : CategoryTheory.Sho
rtComplex C} →         (h : S.LeftHomologyData) → {K' H' : C} → (K' ≅ h.K) → (H'
 ≅ h.H) → S.LeftHomologyData
参数：h : S.LeftHomologyData；K' ≅ h.K；H' ≅ h.H。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wi`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wπ`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…

--- 原说明 ---
Given a left homology data `h` of a short complex `S`, we can construct another 
left homology
data by choosing another kernel and cokernel that are isomorphic to the ones in 
`h`.
-/
@[simps] def copy {K' H' : C} (eK : K' ≅ h.K) (eH : H' ≅ h.H) : S.LeftHomologyData where
  K := K'
  H := H'
  i := eK.hom ≫ h.i
  π := eK.hom ≫ h.π ≫ eH.inv
  wi := by rw [assoc, h.wi, comp_zero]
  hi := IsKernel.isoKernel _ _ h.hi eK (by simp)
  wπ := by simp [IsKernel.isoKernel]
  hπ := IsColimit.equivOfNatIsoOfIso
    (parallelPair.ext (Iso.refl S.X₁) eK.symm (by simp [IsKernel.isoKernel]) (by simp)) _ _
    (Cocone.ext (by exact eH.symm) (by rintro (_ | _) <;> simp [IsKernel.isoKernel])) h.hπ

end LeftHomologyData

/-- A short complex `S` has left homology when there exists a `S.LeftHomologyData` -/
/-
**CategoryTheory.ShortComplex.HasLeftHomology** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.ShortComplex`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] → CategoryTheory.ShortComplex C
 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A short complex `S` has left homology when there exists a `S.LeftHomologyData`
-/
class HasLeftHomology : Prop where
  condition : Nonempty S.LeftHomologyData

/-- A chosen `S.LeftHomologyData` for a short complex `S` that has left homology -/
/-
**CategoryTheory.ShortComplex.leftHomologyData** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：leftHomologyData [S.HasLeftHomology] : S.LeftHomologyData
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.HasLeftHomology.condition`：∀ {C : Type u_1} 
{inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C}   {S : CategoryTheory.Sho…

--- 原说明 ---
A chosen `S.LeftHomologyData` for a short complex `S` that has left homology
-/
noncomputable def leftHomologyData [S.HasLeftHomology] : S.LeftHomologyData :=
  HasLeftHomology.condition.some

variable {S}

namespace HasLeftHomology

/-
**CategoryTheory.ShortComplex.HasLeftHomology.mk'** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ShortComplex.HasLeftHomology`。
形式化陈述：mk' (h : S.LeftHomologyData) : HasLeftHomology S
参数：h : S.LeftHomologyData。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk' (h : S.LeftHomologyData) : HasLeftHomology S := ⟨Nonempty.intro h⟩
/-
**CategoryTheory.ShortComplex.HasLeftHomology.of_hasKernel_of_hasCokernel** 是 Ma
thlib 中的一个实例，位于命名空间 `CategoryTheory.ShortComplex.HasLeftHomology`。
形式化陈述：of_hasKernel_of_hasCokernel [HasKernel S.g] [HasCokernel (kernel.lift S.g 
S.f S.zero)] : S.HasLeftHomology
参数：kernel.lift S.g S.f S.zero。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用引理 `CategoryTheory.ShortComplex.HasLeftHomology.mk'`：mk' (h : S.LeftHomology
Data) : HasLeftHomology S
-/
instance of_hasKernel_of_hasCokernel [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f S.zero)] :
    S.HasLeftHomology := HasLeftHomology.mk' (LeftHomologyData.ofHasKernelOfHasCokernel S)
/-
**CategoryTheory.ShortComplex.HasLeftHomology.of_hasCokernel** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.ShortComplex.HasLeftHomology`。
形式化陈述：of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] : (ShortCompl
ex.mk f (0 : Y ⟶ Z) comp_zero).HasLeftHomology
参数：f : X ⟶ Y；Z : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.HasLeftHomology.mk'`：mk' (h : S.LeftHomology
Data) : HasLeftHomology S
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
instance of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] :
    (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.ofHasCokernel _ rfl)
/-
**CategoryTheory.ShortComplex.HasLeftHomology.of_hasKernel** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.ShortComplex.HasLeftHomology`。
形式化陈述：of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] : (ShortComplex.m
k (0 : X ⟶ Y) g zero_comp).HasLeftHomology
参数：g : Y ⟶ Z；X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.HasLeftHomology.mk'`：mk' (h : S.LeftHomology
Data) : HasLeftHomology S
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
instance of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] :
    (ShortComplex.mk (0 : X ⟶ Y) g zero_comp).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.ofHasKernel _ rfl)
/-
**CategoryTheory.ShortComplex.HasLeftHomology.of_zeros** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.ShortComplex.HasLeftHomology`。
形式化陈述：of_zeros (X Y Z : C) : (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp)
.HasLeftHomology
参数：X Y Z : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.HasLeftHomology.mk'`：mk' (h : S.LeftHomology
Data) : HasLeftHomology S
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
instance of_zeros (X Y Z : C) :
    (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.ofZeros _ rfl rfl)

end HasLeftHomology

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)

/-- Given left homology data `h₁` and `h₂` for two short complexes `S₁` and `S₂`,
a `LeftHomologyMapData` for a morphism `φ : S₁ ⟶ S₂`
consists of a description of the induced morphisms on the `K` (cycles)
and `H` (left homology) fields of `h₁` and `h₂`. -/
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData** 是 Mathlib 中的一个结构，位于命名空间 `Cat
egoryTheory.ShortComplex`。
形式化陈述：LeftHomologyMapData where /-- the induced map on cycles -/ φK : h₁.K ⟶ h₂.
K /-- the induced map on left homology -/ φH : h₁.H ⟶ h₂.H /-- commutation with 
`i` -/ commi : φK ≫ h₂.i = h₁.i ≫ φ.τ₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given left homology data `h₁` and `h₂` for two short complexes `S₁` and `S₂`,
a `LeftHomologyMapData` for a morphism `φ : S₁ ⟶ S₂`
consists of a description of the induced morphisms on the `K` (cycles)
and `H` (left homology) fields of `h₁` and `h₂`.
-/
structure LeftHomologyMapData where
  /-- the induced map on cycles -/
  φK : h₁.K ⟶ h₂.K
  /-- the induced map on left homology -/
  φH : h₁.H ⟶ h₂.H
  /-- commutation with `i` -/
  commi : φK ≫ h₂.i = h₁.i ≫ φ.τ₂ := by cat_disch
  /-- commutation with `f'` -/
  commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f' := by cat_disch
  /-- commutation with `π` -/
  commπ : h₁.π ≫ φH = φK ≫ h₂.π := by cat_disch

namespace LeftHomologyMapData

attribute [reassoc (attr := simp)] commi commf' commπ

/-- The left homology map data associated to the zero morphism between two short complexes. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.zero** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) : LeftHomologyM
apData 0 h₁ h₂ where φK
参数：h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left homology map data associated to the zero morphism between two short com
plexes.
-/
def zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    LeftHomologyMapData 0 h₁ h₂ where
  φK := 0
  φH := 0

/-- The left homology map data associated to the identity morphism of a short complex. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.id** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：id (h : S.LeftHomologyData) : LeftHomologyMapData (𝟙 S) h h where φK
参数：h : S.LeftHomologyData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left homology map data associated to the identity morphism of a short comple
x.
-/
def id (h : S.LeftHomologyData) : LeftHomologyMapData (𝟙 S) h h where
  φK := 𝟙 _
  φH := 𝟙 _

/-- The composition of left homology map data. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.comp** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.Left
HomologyData} {h₃ : S₃.LeftHomologyData} (ψ : LeftHomologyMapData φ h₁ h₂) (ψ' :
 LeftHomologyMapData φ' h₂ h₃) : LeftHomologyMapData (φ ≫ φ') h₁ h₃ where φK
参数：ψ : LeftHomologyMapData φ h₁ h₂；ψ' : LeftHomologyMapData φ' h₂ h₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of left homology map data.
-/
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃}
    {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData} {h₃ : S₃.LeftHomologyData}
    (ψ : LeftHomologyMapData φ h₁ h₂) (ψ' : LeftHomologyMapData φ' h₂ h₃) :
    LeftHomologyMapData (φ ≫ φ') h₁ h₃ where
  φK := ψ.φK ≫ ψ'.φK
  φH := ψ.φH ≫ ψ'.φH
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.ShortComplex.LeftHomologyMapData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton (LeftHomologyMapData φ h₁ h₂) :=
  ⟨fun ψ₁ ψ₂ => by
    have hK : ψ₁.φK = ψ₂.φK := by rw [← cancel_mono h₂.i, commi, commi]
    have hH : ψ₁.φH = ψ₂.φH := by rw [← cancel_epi h₁.π, commπ, commπ, hK]
    cases ψ₁
    cases ψ₂
    congr⟩
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.ShortComplex.LeftHomologyMapData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (LeftHomologyMapData φ h₁ h₂) := ⟨by
  let φK : h₁.K ⟶ h₂.K := h₂.liftK (h₁.i ≫ φ.τ₂)
    (by rw [assoc, φ.comm₂₃, h₁.wi_assoc, zero_comp])
  have commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f' := by
    rw [← cancel_mono h₂.i, assoc, assoc, LeftHomologyData.liftK_i,
      LeftHomologyData.f'_i_assoc, LeftHomologyData.f'_i, φ.comm₁₂]
  let φH : h₁.H ⟶ h₂.H := h₁.descH (φK ≫ h₂.π)
    (by rw [reassoc_of% commf', h₂.f'_π, comp_zero])
  exact ⟨φK, φH, by simp [φK], commf', by simp [φH]⟩⟩
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.ShortComplex.LeftHomologyMapData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (LeftHomologyMapData φ h₁ h₂) := Unique.mk' _

variable {φ h₁ h₂}
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.congr_** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma congr_φH {γ₁ γ₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φH = γ₂.φH := by rw [eq]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.congr_** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma congr_φK {γ₁ γ₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φK = γ₂.φK := by rw [eq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When `S₁.f`, `S₁.g`, `S₂.f` and `S₂.g` are all zero, the action on left homology of a
morphism `φ : S₁ ⟶ S₂` is given by the action `φ.τ₂` on the middle objects. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.ofZeros** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：ofZeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (
hg₂ : S₂.g = 0) : LeftHomologyMapData φ (LeftHomologyData.ofZeros S₁ hf₁ hg₁) (L
eftHomologyData.ofZeros S₂ hf₂ hg₂) where φK
参数：φ : S₁ ⟶ S₂；hf₁ : S₁.f = 0；hg₁ : S₁.g = 0；hf₂ : S₂.f = 0；hg₂ : S₂.g = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `S₁.f`, `S₁.g`, `S₂.f` and `S₂.g` are all zero, the action on left homology
 of a
morphism `φ : S₁ ⟶ S₂` is given by the action `φ.τ₂` on the middle objects.
-/
def ofZeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    LeftHomologyMapData φ (LeftHomologyData.ofZeros S₁ hf₁ hg₁)
      (LeftHomologyData.ofZeros S₂ hf₂ hg₂) where
  φK := φ.τ₂
  φH := φ.τ₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When `S₁.g` and `S₂.g` are zero and we have chosen colimit cokernel coforks `c₁` and `c₂`
for `S₁.f` and `S₂.f` respectively, the action on left homology of a morphism `φ : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`φ.τ₂ ≫ c₂.π = c₁.π ≫ f`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.ofIsColimitCokernelCofork** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：ofIsColimitCokernelCofork (φ : S₁ ⟶ S₂) (hg₁ : S₁.g = 0) (c₁ : CokernelCof
ork S₁.f) (hc₁ : IsColimit c₁) (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ 
: IsColimit c₂) (f : c₁.pt ⟶ c₂.pt) (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) : LeftHomolo
gyMapData φ (LeftHomologyData.ofIsColimitCokernelCofork S₁ hg₁ c₁ hc₁) (LeftHomo
logyData.ofIsColimitCokernelCofork S₂ hg₂ c₂ hc₂) where φK
参数：φ : S₁ ⟶ S₂；hg₁ : S₁.g = 0；c₁ : CokernelCofork S₁.f；hc₁ : IsColimit c₁；hg₂ : 
S₂.g = 0；c₂ : CokernelCofork S₂.f；hc₂ : IsColimit c₂；f : c₁.pt ⟶ c₂.pt；comm : φ.
τ₂ ≫ c₂.π = c₁.π ≫ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `S₁.g` and `S₂.g` are zero and we have chosen colimit cokernel coforks `c₁`
 and `c₂`
for `S₁.f` and `S₂.f` respectively, the action on left homology of a morphism `φ
 : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`φ.τ₂ ≫ c₂.π = c₁.π ≫ f`.
-/
def ofIsColimitCokernelCofork (φ : S₁ ⟶ S₂)
    (hg₁ : S₁.g = 0) (c₁ : CokernelCofork S₁.f) (hc₁ : IsColimit c₁)
    (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ : IsColimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) :
    LeftHomologyMapData φ (LeftHomologyData.ofIsColimitCokernelCofork S₁ hg₁ c₁ hc₁)
      (LeftHomologyData.ofIsColimitCokernelCofork S₂ hg₂ c₂ hc₂) where
  φK := φ.τ₂
  φH := f
  commπ := comm.symm
  commf' := by simp only [LeftHomologyData.ofIsColimitCokernelCofork_f', φ.comm₁₂]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When `S₁.f` and `S₂.f` are zero and we have chosen limit kernel forks `c₁` and `c₂`
for `S₁.g` and `S₂.g` respectively, the action on left homology of a morphism `φ : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.ofIsLimitKernelFork** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：ofIsLimitKernelFork (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) 
(hc₁ : IsLimit c₁) (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f
 : c₁.pt ⟶ c₂.pt) (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) : LeftHomologyMapData φ (LeftH
omologyData.ofIsLimitKernelFork S₁ hf₁ c₁ hc₁) (LeftHomologyData.ofIsLimitKernel
Fork S₂ hf₂ c₂ hc₂) where φK
参数：φ : S₁ ⟶ S₂；hf₁ : S₁.f = 0；c₁ : KernelFork S₁.g；hc₁ : IsLimit c₁；hf₂ : S₂.f =
 0；c₂ : KernelFork S₂.g；hc₂ : IsLimit c₂；f : c₁.pt ⟶ c₂.pt；comm : c₁.ι ≫ φ.τ₂ = 
f ≫ c₂.ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `S₁.f` and `S₂.f` are zero and we have chosen limit kernel forks `c₁` and `
c₂`
for `S₁.g` and `S₂.g` respectively, the action on left homology of a morphism `φ
 : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι`.
-/
def ofIsLimitKernelFork (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) (hc₁ : IsLimit c₁)
    (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
    LeftHomologyMapData φ (LeftHomologyData.ofIsLimitKernelFork S₁ hf₁ c₁ hc₁)
      (LeftHomologyData.ofIsLimitKernelFork S₂ hf₂ c₂ hc₂) where
  φK := f
  φH := f
  commi := comm.symm

variable (S)

set_option backward.isDefEq.respectTransparency.types false in
/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the left homology map
data (for the identity of `S`) which relates the left homology data `ofZeros` and
`ofIsColimitCokernelCofork`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.compatibilityOfZerosOfIsColimi
tCokernelCofork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.LeftHomol
ogyMapData`。
形式化陈述：compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0
) (c : CokernelCofork S.f) (hc : IsColimit c) : LeftHomologyMapData (𝟙 S) (LeftH
omologyData.ofZeros S hf hg) (LeftHomologyData.ofIsColimitCokernelCofork S hg c 
hc) where φK
参数：hf : S.f = 0；hg : S.g = 0；c : CokernelCofork S.f；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the left
 homology map
data (for the identity of `S`) which relates the left homology data `ofZeros` an
d
`ofIsColimitCokernelCofork`.
-/
def compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0)
    (c : CokernelCofork S.f) (hc : IsColimit c) :
    LeftHomologyMapData (𝟙 S) (LeftHomologyData.ofZeros S hf hg)
      (LeftHomologyData.ofIsColimitCokernelCofork S hg c hc) where
  φK := 𝟙 _
  φH := c.π

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the left homology map
data (for the identity of `S`) which relates the left homology data
`LeftHomologyData.ofIsLimitKernelFork` and `ofZeros` . -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.compatibilityOfZerosOfIsLimitK
ernelFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMap
Data`。
形式化陈述：compatibilityOfZerosOfIsLimitKernelFork (hf : S.f = 0) (hg : S.g = 0) (c :
 KernelFork S.g) (hc : IsLimit c) : LeftHomologyMapData (𝟙 S) (LeftHomologyData.
ofIsLimitKernelFork S hf c hc) (LeftHomologyData.ofZeros S hf hg) where φK
参数：hf : S.f = 0；hg : S.g = 0；c : KernelFork S.g；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the left
 homology map
data (for the identity of `S`) which relates the left homology data
`LeftHomologyData.ofIsLimitKernelFork` and `ofZeros` .
-/
def compatibilityOfZerosOfIsLimitKernelFork (hf : S.f = 0) (hg : S.g = 0)
    (c : KernelFork S.g) (hc : IsLimit c) :
    LeftHomologyMapData (𝟙 S) (LeftHomologyData.ofIsLimitKernelFork S hf c hc)
      (LeftHomologyData.ofZeros S hf hg) where
  φK := c.ι
  φH := c.ι

end LeftHomologyMapData

end

section

variable (S)
variable [S.HasLeftHomology]

/-- The left homology of a short complex, given by the `H` field of a chosen left homology data. -/
/-
**CategoryTheory.ShortComplex.leftHomology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：leftHomology : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left homology of a short complex, given by the `H` field of a chosen left ho
mology data.
-/
noncomputable def leftHomology : C := S.leftHomologyData.H

-- `S.leftHomology` is the simp normal form.
/-
**CategoryTheory.ShortComplex.leftHomologyData_H** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComplex C) [
inst_2 : S.HasLeftHomology], S.leftHomologyData.H = S.leftHomology
参数：S : CategoryTheory.ShortComplex C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma leftHomologyData_H : S.leftHomologyData.H = S.leftHomology := rfl

/-- The cycles of a short complex, given by the `K` field of a chosen left homology data. -/
/-
**CategoryTheory.ShortComplex.cycles** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.S
hortComplex`。
形式化陈述：cycles : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cycles of a short complex, given by the `K` field of a chosen left homology 
data.
-/
noncomputable def cycles : C := S.leftHomologyData.K

/-- The "homology class" map `S.cycles ⟶ S.leftHomology`. -/
/-
**CategoryTheory.ShortComplex.leftHomology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：leftHomology : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "homology class" map `S.cycles ⟶ S.leftHomology`.
-/
noncomputable def leftHomologyπ : S.cycles ⟶ S.leftHomology := S.leftHomologyData.π

/-- The inclusion `S.cycles ⟶ S.X₂`. -/
/-
**CategoryTheory.ShortComplex.iCycles** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
ShortComplex`。
形式化陈述：iCycles : S.cycles ⟶ S.X₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `S.cycles ⟶ S.X₂`.
-/
noncomputable def iCycles : S.cycles ⟶ S.X₂ := S.leftHomologyData.i

/-- The "boundaries" map `S.X₁ ⟶ S.cycles`. (Note that in this homology API, we make no use
of the "image" of this morphism, which under some categorical assumptions would be a subobject
of `S.X₂` contained in `S.cycles`.) -/
/-
**CategoryTheory.ShortComplex.toCycles** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：toCycles : S.X₁ ⟶ S.cycles
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "boundaries" map `S.X₁ ⟶ S.cycles`. (Note that in this homology API, we make
 no use
of the "image" of this morphism, which under some categorical assumptions would 
be a subobject
of `S.X₂` contained in `S.cycles`.)
-/
noncomputable def toCycles : S.X₁ ⟶ S.cycles := S.leftHomologyData.f'

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.iCycles_g** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.ShortComplex`。
形式化陈述：iCycles_g : S.iCycles ≫ S.g = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wi`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
-/
lemma iCycles_g : S.iCycles ≫ S.g = 0 := S.leftHomologyData.wi

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.toCycles_i** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ShortComplex`。
形式化陈述：toCycles_i : S.toCycles ≫ S.iCycles = S.f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_i`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…
-/
lemma toCycles_i : S.toCycles ≫ S.iCycles = S.f := S.leftHomologyData.f'_i

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono S.iCycles := by
  dsimp only [iCycles]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi S.leftHomologyπ := by
  dsimp only [leftHomologyπ]
  infer_instance
/-
**CategoryTheory.ShortComplex.leftHomology_ext_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：leftHomology_ext_iff {A : C} (f₁ f₂ : S.leftHomology ⟶ A) : f₁ = f₂ ↔ S.le
ftHomologyπ ≫ f₁ = S.leftHomologyπ ≫ f₂
参数：f₁ f₂ : S.leftHomology ⟶ A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.instEpiLeftHomologyπ`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   (S : CategoryTheory.Sho…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma leftHomology_ext_iff {A : C} (f₁ f₂ : S.leftHomology ⟶ A) :
    f₁ = f₂ ↔ S.leftHomologyπ ≫ f₁ = S.leftHomologyπ ≫ f₂ := by
  rw [cancel_epi]

@[ext]
/-
**CategoryTheory.ShortComplex.leftHomology_ext** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：leftHomology_ext {A : C} (f₁ f₂ : S.leftHomology ⟶ A) (h : S.leftHomologyπ
 ≫ f₁ = S.leftHomologyπ ≫ f₂) : f₁ = f₂
参数：f₁ f₂ : S.leftHomology ⟶ A；h : S.leftHomologyπ ≫ f₁ = S.leftHomologyπ ≫ f₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftHomology_ext {A : C} (f₁ f₂ : S.leftHomology ⟶ A)
    (h : S.leftHomologyπ ≫ f₁ = S.leftHomologyπ ≫ f₂) : f₁ = f₂ := by
  simpa only [leftHomology_ext_iff] using h
/-
**CategoryTheory.ShortComplex.cycles_ext_iff** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：cycles_ext_iff {A : C} (f₁ f₂ : A ⟶ S.cycles) : f₁ = f₂ ↔ f₁ ≫ S.iCycles =
 f₂ ≫ S.iCycles
参数：f₁ f₂ : A ⟶ S.cycles。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.instMonoICycles`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   (S : CategoryTheory.Sho…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cycles_ext_iff {A : C} (f₁ f₂ : A ⟶ S.cycles) :
    f₁ = f₂ ↔ f₁ ≫ S.iCycles = f₂ ≫ S.iCycles := by
  rw [cancel_mono]

@[ext]
/-
**CategoryTheory.ShortComplex.cycles_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ShortComplex`。
形式化陈述：cycles_ext {A : C} (f₁ f₂ : A ⟶ S.cycles) (h : f₁ ≫ S.iCycles = f₂ ≫ S.iCy
cles) : f₁ = f₂
参数：f₁ f₂ : A ⟶ S.cycles；h : f₁ ≫ S.iCycles = f₂ ≫ S.iCycles。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cycles_ext {A : C} (f₁ f₂ : A ⟶ S.cycles) (h : f₁ ≫ S.iCycles = f₂ ≫ S.iCycles) :
    f₁ = f₂ := by
  simpa only [cycles_ext_iff] using h
/-
**CategoryTheory.ShortComplex.isIso_iCycles** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：isIso_iCycles (hg : S.g = 0) : IsIso S.iCycles
参数：hg : S.g = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.isIso_i`：isIso_i (hg : S.g 
= 0) : IsIso h.i
-/
lemma isIso_iCycles (hg : S.g = 0) : IsIso S.iCycles :=
  LeftHomologyData.isIso_i _ hg

/-- When `S.g = 0`, this is the canonical isomorphism `S.cycles ≅ S.X₂` induced by `S.iCycles`. -/
@[simps! hom]
/-
**CategoryTheory.ShortComplex.cyclesIsoX** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `S.g = 0`, this is the canonical isomorphism `S.cycles ≅ S.X₂` induced by `
S.iCycles`.
-/
noncomputable def cyclesIsoX₂ (hg : S.g = 0) : S.cycles ≅ S.X₂ := by
  have := S.isIso_iCycles hg
  exact asIso S.iCycles

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.cyclesIsoX** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cyclesIsoX₂_hom_inv_id (hg : S.g = 0) :
    S.iCycles ≫ (S.cyclesIsoX₂ hg).inv = 𝟙 _ := (S.cyclesIsoX₂ hg).hom_inv_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.cyclesIsoX** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cyclesIsoX₂_inv_hom_id (hg : S.g = 0) :
    (S.cyclesIsoX₂ hg).inv ≫ S.iCycles = 𝟙 _ := (S.cyclesIsoX₂ hg).inv_hom_id
/-
**CategoryTheory.ShortComplex.isIso_leftHomology** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_leftHomologyπ (hf : S.f = 0) : IsIso S.leftHomologyπ :=
  LeftHomologyData.isIso_π _ hf

/-- When `S.f = 0`, this is the canonical isomorphism `S.cycles ≅ S.leftHomology` induced
by `S.leftHomologyπ`. -/
@[simps! hom]
/-
**CategoryTheory.ShortComplex.cyclesIsoLeftHomology** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：cyclesIsoLeftHomology (hf : S.f = 0) : S.cycles ≅ S.leftHomology
参数：hf : S.f = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.isIso_leftHomologyπ`：isIso_leftHomologyπ (hf
 : S.f = 0) : IsIso S.leftHomologyπ

--- 原说明 ---
When `S.f = 0`, this is the canonical isomorphism `S.cycles ≅ S.leftHomology` in
duced
by `S.leftHomologyπ`.
-/
noncomputable def cyclesIsoLeftHomology (hf : S.f = 0) : S.cycles ≅ S.leftHomology := by
  have := S.isIso_leftHomologyπ hf
  exact asIso S.leftHomologyπ

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.cyclesIsoLeftHomology_hom_inv_id** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：cyclesIsoLeftHomology_hom_inv_id (hf : S.f = 0) : S.leftHomologyπ ≫ (S.cyc
lesIsoLeftHomology hf).inv = 𝟙 _
参数：hf : S.f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma cyclesIsoLeftHomology_hom_inv_id (hf : S.f = 0) :
    S.leftHomologyπ ≫ (S.cyclesIsoLeftHomology hf).inv = 𝟙 _ :=
  (S.cyclesIsoLeftHomology hf).hom_inv_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.cyclesIsoLeftHomology_inv_hom_id** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：cyclesIsoLeftHomology_inv_hom_id (hf : S.f = 0) : (S.cyclesIsoLeftHomology
 hf).inv ≫ S.leftHomologyπ = 𝟙 _
参数：hf : S.f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma cyclesIsoLeftHomology_inv_hom_id (hf : S.f = 0) :
    (S.cyclesIsoLeftHomology hf).inv ≫ S.leftHomologyπ = 𝟙 _ :=
  (S.cyclesIsoLeftHomology hf).inv_hom_id

end

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)

/-- The (unique) left homology map data associated to a morphism of short complexes that
are both equipped with left homology data. -/
/-
**CategoryTheory.ShortComplex.leftHomologyMapData** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ShortComplex`。
形式化陈述：leftHomologyMapData : LeftHomologyMapData φ h₁ h₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unique) left homology map data associated to a morphism of short complexes 
that
are both equipped with left homology data.
-/
def leftHomologyMapData : LeftHomologyMapData φ h₁ h₂ := default

/-- Given a morphism `φ : S₁ ⟶ S₂` of short complexes and left homology data `h₁` and `h₂`
for `S₁` and `S₂` respectively, this is the induced left homology map `h₁.H ⟶ h₁.H`. -/
/-
**CategoryTheory.ShortComplex.leftHomologyMap'** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：leftHomologyMap' : h₁.H ⟶ h₂.H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `φ : S₁ ⟶ S₂` of short complexes and left homology data `h₁` an
d `h₂`
for `S₁` and `S₂` respectively, this is the induced left homology map `h₁.H ⟶ h₁
.H`.
-/
def leftHomologyMap' : h₁.H ⟶ h₂.H := (leftHomologyMapData φ _ _).φH

/-- Given a morphism `φ : S₁ ⟶ S₂` of short complexes and left homology data `h₁` and `h₂`
for `S₁` and `S₂` respectively, this is the induced morphism `h₁.K ⟶ h₁.K` on cycles. -/
/-
**CategoryTheory.ShortComplex.cyclesMap'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ShortComplex`。
形式化陈述：cyclesMap' : h₁.K ⟶ h₂.K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `φ : S₁ ⟶ S₂` of short complexes and left homology data `h₁` an
d `h₂`
for `S₁` and `S₂` respectively, this is the induced morphism `h₁.K ⟶ h₁.K` on cy
cles.
-/
def cyclesMap' : h₁.K ⟶ h₂.K := (leftHomologyMapData φ _ _).φK

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.cyclesMap'_i** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData),   Catego
ryTheory.CategoryStruct.comp (CategoryTheory.ShortComplex.cyclesMap' φ h₁ h₂) h₂
.i =     CategoryTheory.CategoryStruct.comp h₁.i φ.τ₂
参数：φ : S₁ ⟶ S₂；h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；CategoryTheory.
ShortComplex.cyclesMap' φ h₁ h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.commi`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma cyclesMap'_i : cyclesMap' φ h₁ h₂ ≫ h₂.i = h₁.i ≫ φ.τ₂ :=
  LeftHomologyMapData.commi _

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.f'_cyclesMap'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData),   Catego
ryTheory.CategoryStruct.comp h₁.f' (CategoryTheory.ShortComplex.cyclesMap' φ h₁ 
h₂) =     CategoryTheory.CategoryStruct.comp φ.τ₁ h₂.f'
参数：φ : S₁ ⟶ S₂；h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；CategoryTheory.
ShortComplex.cyclesMap' φ h₁ h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instMonoI`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_i`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_i_assoc`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_i`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₁₂`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma f'_cyclesMap' : h₁.f' ≫ cyclesMap' φ h₁ h₂ = φ.τ₁ ≫ h₂.f' := by
  simp only [← cancel_mono h₂.i, assoc, φ.comm₁₂, cyclesMap'_i,
    LeftHomologyData.f'_i_assoc, LeftHomologyData.f'_i]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.leftHomology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：leftHomology : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftHomologyπ_naturality' :
    h₁.π ≫ leftHomologyMap' φ h₁ h₂ = cyclesMap' φ h₁ h₂ ≫ h₂.π :=
  LeftHomologyMapData.commπ _

end

section

variable [HasLeftHomology S₁] [HasLeftHomology S₂] (φ : S₁ ⟶ S₂)

/-- The (left) homology map `S₁.leftHomology ⟶ S₂.leftHomology` induced by a morphism
`S₁ ⟶ S₂` of short complexes. -/
/-
**CategoryTheory.ShortComplex.leftHomologyMap** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：leftHomologyMap : S₁.leftHomology ⟶ S₂.leftHomology
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (left) homology map `S₁.leftHomology ⟶ S₂.leftHomology` induced by a morphis
m
`S₁ ⟶ S₂` of short complexes.
-/
noncomputable def leftHomologyMap : S₁.leftHomology ⟶ S₂.leftHomology :=
  leftHomologyMap' φ _ _

/-- The morphism `S₁.cycles ⟶ S₂.cycles` induced by a morphism `S₁ ⟶ S₂` of short complexes. -/
/-
**CategoryTheory.ShortComplex.cyclesMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ShortComplex`。
形式化陈述：cyclesMap : S₁.cycles ⟶ S₂.cycles
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `S₁.cycles ⟶ S₂.cycles` induced by a morphism `S₁ ⟶ S₂` of short co
mplexes.
-/
noncomputable def cyclesMap : S₁.cycles ⟶ S₂.cycles := cyclesMap' φ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.cyclesMap_i** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ShortComplex`。
形式化陈述：cyclesMap_i : cyclesMap φ ≫ S₂.iCycles = S₁.iCycles ≫ φ.τ₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_i`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {S₁ S₂ : CategoryTheory…
-/
lemma cyclesMap_i : cyclesMap φ ≫ S₂.iCycles = S₁.iCycles ≫ φ.τ₂ :=
  cyclesMap'_i _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.toCycles_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ShortComplex`。
形式化陈述：toCycles_naturality : S₁.toCycles ≫ cyclesMap φ = φ.τ₁ ≫ S₂.toCycles
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.f'_cyclesMap'`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {S₁ S₂ : CategoryTheory…
-/
lemma toCycles_naturality : S₁.toCycles ≫ cyclesMap φ = φ.τ₁ ≫ S₂.toCycles :=
  f'_cyclesMap' _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.leftHomology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：leftHomology : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftHomologyπ_naturality :
    S₁.leftHomologyπ ≫ leftHomologyMap φ = cyclesMap φ ≫ S₂.leftHomologyπ :=
  leftHomologyπ_naturality' _ _ _

end

namespace LeftHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂)

/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}   (γ : Ca
tegoryTheory.ShortComplex.LeftHomologyMapData φ h₁ h₂),   CategoryTheory.ShortCo
mplex.leftHomologyMap' φ h₁ h₂ = γ.φH
参数：γ : CategoryTheory.ShortComplex.LeftHomologyMapData φ h₁ h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyMapData.congr_φH`：congr_φH {γ₁ γ
₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φH = γ₂.φH
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.instSubsingleton`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheor
y.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma leftHomologyMap'_eq : leftHomologyMap' φ h₁ h₂ = γ.φH :=
  LeftHomologyMapData.congr_φH (Subsingleton.elim _ _)
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.cyclesMap'_eq** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}   (γ : Ca
tegoryTheory.ShortComplex.LeftHomologyMapData φ h₁ h₂), CategoryTheory.ShortComp
lex.cyclesMap' φ h₁ h₂ = γ.φK
参数：γ : CategoryTheory.ShortComplex.LeftHomologyMapData φ h₁ h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyMapData.congr_φK`：congr_φK {γ₁ γ
₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φK = γ₂.φK
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.instSubsingleton`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheor
y.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma cyclesMap'_eq : cyclesMap' φ h₁ h₂ = γ.φK :=
  LeftHomologyMapData.congr_φK (Subsingleton.elim _ _)

end LeftHomologyMapData

@[simp]
/-
**CategoryTheory.ShortComplex.leftHomologyMap'_id** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (
h : S.LeftHomologyData),   CategoryTheory.ShortComplex.leftHomologyMap' (Categor
yTheory.CategoryStruct.id S) h h =     CategoryTheory.CategoryStruct.id h.H
参数：h : S.LeftHomologyData；CategoryTheory.CategoryStruct.id S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma leftHomologyMap'_id (h : S.LeftHomologyData) :
    leftHomologyMap' (𝟙 S) h h = 𝟙 _ :=
  (LeftHomologyMapData.id h).leftHomologyMap'_eq

@[simp]
/-
**CategoryTheory.ShortComplex.cyclesMap'_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (
h : S.LeftHomologyData),   CategoryTheory.ShortComplex.cyclesMap' (CategoryTheor
y.CategoryStruct.id S) h h = CategoryTheory.CategoryStruct.id h.K
参数：h : S.LeftHomologyData；CategoryTheory.CategoryStruct.id S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.cyclesMap'_eq`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma cyclesMap'_id (h : S.LeftHomologyData) :
    cyclesMap' (𝟙 S) h h = 𝟙 _ :=
  (LeftHomologyMapData.id h).cyclesMap'_eq

variable (S)

@[simp]
/-
**CategoryTheory.ShortComplex.leftHomologyMap_id** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：leftHomologyMap_id [HasLeftHomology S] : leftHomologyMap (𝟙 S) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_id`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
-/
lemma leftHomologyMap_id [HasLeftHomology S] :
    leftHomologyMap (𝟙 S) = 𝟙 _ :=
  leftHomologyMap'_id _

@[simp]
/-
**CategoryTheory.ShortComplex.cyclesMap_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：cyclesMap_id [HasLeftHomology S] : cyclesMap (𝟙 S) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_id`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {S : CategoryTheory.Sho…
-/
lemma cyclesMap_id [HasLeftHomology S] :
    cyclesMap (𝟙 S) = 𝟙 _ :=
  cyclesMap'_id _

@[simp]
/-
**CategoryTheory.ShortComplex.leftHomologyMap'_zero** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData),   CategoryTheory.Short
Complex.leftHomologyMap' 0 h₁ h₂ = 0
参数：h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma leftHomologyMap'_zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    leftHomologyMap' 0 h₁ h₂ = 0 :=
  (LeftHomologyMapData.zero h₁ h₂).leftHomologyMap'_eq

@[simp]
/-
**CategoryTheory.ShortComplex.cyclesMap'_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData),   CategoryTheory.Short
Complex.cyclesMap' 0 h₁ h₂ = 0
参数：h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.cyclesMap'_eq`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma cyclesMap'_zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    cyclesMap' 0 h₁ h₂ = 0 :=
  (LeftHomologyMapData.zero h₁ h₂).cyclesMap'_eq

variable (S₁ S₂)

@[simp]
/-
**CategoryTheory.ShortComplex.leftHomologyMap_zero** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：leftHomologyMap_zero [HasLeftHomology S₁] [HasLeftHomology S₂] : leftHomol
ogyMap (0 : S₁ ⟶ S₂) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_zero`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma leftHomologyMap_zero [HasLeftHomology S₁] [HasLeftHomology S₂] :
    leftHomologyMap (0 : S₁ ⟶ S₂) = 0 :=
  leftHomologyMap'_zero _ _

@[simp]
/-
**CategoryTheory.ShortComplex.cyclesMap_zero** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：cyclesMap_zero [HasLeftHomology S₁] [HasLeftHomology S₂] : cyclesMap (0 : 
S₁ ⟶ S₂) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_zero`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {S₁ S₂ : CategoryTheory…
-/
lemma cyclesMap_zero [HasLeftHomology S₁] [HasLeftHomology S₂] :
    cyclesMap (0 : S₁ ⟶ S₂) = 0 :=
  cyclesMap'_zero _ _

variable {S₁ S₂}

@[reassoc]
/-
**CategoryTheory.ShortComplex.leftHomologyMap'_comp** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ S₃ : CategoryTheory.ShortCompl
ex C} (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) (h₁ : S₁.LeftHomologyData)   (h₂ : S₂.LeftHo
mologyData) (h₃ : S₃.LeftHomologyData),   CategoryTheory.ShortComplex.leftHomolo
gyMap' (CategoryTheory.CategoryStruct.comp φ₁ φ₂) h₁ h₃ =     CategoryTheory.Cat
egoryStruct.comp (CategoryTheory.ShortComplex.leftHomologyMap' φ₁ h₁ h₂)       (
CategoryTheory.ShortComplex.leftHomologyMap' φ₂ h₂ h₃)
参数：φ₁ : S₁ ⟶ S₂；φ₂ : S₂ ⟶ S₃；h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；h
₃ : S₃.LeftHomologyData；CategoryTheory.CategoryStruct.comp φ₁ φ₂；CategoryTheory.
ShortComplex.leftHomologyMap' φ₁ h₁ h₂；CategoryTheory.ShortComplex.leftHomologyM
ap' φ₂ h₂ h₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.comp_φH`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S₁ S₂ S₃ : CategoryThe…
-/
lemma leftHomologyMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) (h₃ : S₃.LeftHomologyData) :
    leftHomologyMap' (φ₁ ≫ φ₂) h₁ h₃ = leftHomologyMap' φ₁ h₁ h₂ ≫
      leftHomologyMap' φ₂ h₂ h₃ := by
  let γ₁ := leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.leftHomologyMap'_eq, γ₂.leftHomologyMap'_eq, (γ₁.comp γ₂).leftHomologyMap'_eq,
    LeftHomologyMapData.comp_φH]

@[reassoc]
/-
**CategoryTheory.ShortComplex.cyclesMap'_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ S₃ : CategoryTheory.ShortCompl
ex C} (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) (h₁ : S₁.LeftHomologyData)   (h₂ : S₂.LeftHo
mologyData) (h₃ : S₃.LeftHomologyData),   CategoryTheory.ShortComplex.cyclesMap'
 (CategoryTheory.CategoryStruct.comp φ₁ φ₂) h₁ h₃ =     CategoryTheory.CategoryS
truct.comp (CategoryTheory.ShortComplex.cyclesMap' φ₁ h₁ h₂)       (CategoryTheo
ry.ShortComplex.cyclesMap' φ₂ h₂ h₃)
参数：φ₁ : S₁ ⟶ S₂；φ₂ : S₂ ⟶ S₃；h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；h
₃ : S₃.LeftHomologyData；CategoryTheory.CategoryStruct.comp φ₁ φ₂；CategoryTheory.
ShortComplex.cyclesMap' φ₁ h₁ h₂；CategoryTheory.ShortComplex.cyclesMap' φ₂ h₂ h₃
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.cyclesMap'_eq`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.comp_φK`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S₁ S₂ S₃ : CategoryThe…
-/
lemma cyclesMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) (h₃ : S₃.LeftHomologyData) :
    cyclesMap' (φ₁ ≫ φ₂) h₁ h₃ = cyclesMap' φ₁ h₁ h₂ ≫ cyclesMap' φ₂ h₂ h₃ := by
  let γ₁ := leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.cyclesMap'_eq, γ₂.cyclesMap'_eq, (γ₁.comp γ₂).cyclesMap'_eq,
    LeftHomologyMapData.comp_φK]

@[reassoc]
/-
**CategoryTheory.ShortComplex.leftHomologyMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：leftHomologyMap_comp [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHom
ology S₃] (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) : leftHomologyMap (φ₁ ≫ φ₂) = leftHomolo
gyMap φ₁ ≫ leftHomologyMap φ₂
参数：φ₁ : S₁ ⟶ S₂；φ₂ : S₂ ⟶ S₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_comp`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S₁ S₂ S₃ : CategoryThe…
-/
lemma leftHomologyMap_comp [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    leftHomologyMap (φ₁ ≫ φ₂) = leftHomologyMap φ₁ ≫ leftHomologyMap φ₂ :=
  leftHomologyMap'_comp _ _ _ _ _

@[reassoc]
/-
**CategoryTheory.ShortComplex.cyclesMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：cyclesMap_comp [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology 
S₃] (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) : cyclesMap (φ₁ ≫ φ₂) = cyclesMap φ₁ ≫ cyclesM
ap φ₂
参数：φ₁ : S₁ ⟶ S₂；φ₂ : S₂ ⟶ S₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_comp`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {S₁ S₂ S₃ : CategoryThe…
-/
lemma cyclesMap_comp [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    cyclesMap (φ₁ ≫ φ₂) = cyclesMap φ₁ ≫ cyclesMap φ₂ :=
  cyclesMap'_comp _ _ _ _ _

attribute [simp] leftHomologyMap_comp cyclesMap_comp

/-- An isomorphism of short complexes `S₁ ≅ S₂` induces an isomorphism on the `H` fields
of left homology data of `S₁` and `S₂`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.leftHomologyMapIso'** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ShortComplex`。
形式化陈述：leftHomologyMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.Left
HomologyData) : h₁.H ≅ h₂.H where hom
参数：e : S₁ ≅ S₂；h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of short complexes `S₁ ≅ S₂` induces an isomorphism on the `H` fi
elds
of left homology data of `S₁` and `S₂`.
-/
def leftHomologyMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData)
    (h₂ : S₂.LeftHomologyData) : h₁.H ≅ h₂.H where
  hom := leftHomologyMap' e.hom h₁ h₂
  inv := leftHomologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← leftHomologyMap'_comp, e.hom_inv_id, leftHomologyMap'_id]
  inv_hom_id := by rw [← leftHomologyMap'_comp, e.inv_hom_id, leftHomologyMap'_id]
/-
**CategoryTheory.ShortComplex.isIso_leftHomologyMap'_of_isIso** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} (φ : S₁ ⟶ S₂) [CategoryTheory.IsIso φ] (h₁ : S₁.LeftHomologyData)   (h₂ : S₂.
LeftHomologyData), CategoryTheory.IsIso (CategoryTheory.ShortComplex.leftHomolog
yMap' φ h₁ h₂)
参数：φ : S₁ ⟶ S₂；h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；CategoryTheory.
ShortComplex.leftHomologyMap' φ h₁ h₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_leftHomologyMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    IsIso (leftHomologyMap' φ h₁ h₂) :=
  inferInstanceAs <| IsIso (leftHomologyMapIso' (asIso φ) h₁ h₂).hom

/-- An isomorphism of short complexes `S₁ ≅ S₂` induces an isomorphism on the `K` fields
of left homology data of `S₁` and `S₂`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.cyclesMapIso'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：cyclesMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomolo
gyData) : h₁.K ≅ h₂.K where hom
参数：e : S₁ ≅ S₂；h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of short complexes `S₁ ≅ S₂` induces an isomorphism on the `K` fi
elds
of left homology data of `S₁` and `S₂`.
-/
def cyclesMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData)
    (h₂ : S₂.LeftHomologyData) : h₁.K ≅ h₂.K where
  hom := cyclesMap' e.hom h₁ h₂
  inv := cyclesMap' e.inv h₂ h₁
  hom_inv_id := by rw [← cyclesMap'_comp, e.hom_inv_id, cyclesMap'_id]
  inv_hom_id := by rw [← cyclesMap'_comp, e.inv_hom_id, cyclesMap'_id]
/-
**CategoryTheory.ShortComplex.isIso_cyclesMap'_of_isIso** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} (φ : S₁ ⟶ S₂) [CategoryTheory.IsIso φ] (h₁ : S₁.LeftHomologyData)   (h₂ : S₂.
LeftHomologyData), CategoryTheory.IsIso (CategoryTheory.ShortComplex.cyclesMap' 
φ h₁ h₂)
参数：φ : S₁ ⟶ S₂；h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；CategoryTheory.
ShortComplex.cyclesMap' φ h₁ h₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_cyclesMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    IsIso (cyclesMap' φ h₁ h₂) :=
  inferInstanceAs <| IsIso (cyclesMapIso' (asIso φ) h₁ h₂).hom

/-- The isomorphism `S₁.leftHomology ≅ S₂.leftHomology` induced by an isomorphism of
short complexes `S₁ ≅ S₂`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.leftHomologyMapIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：leftHomologyMapIso (e : S₁ ≅ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology]
 : S₁.leftHomology ≅ S₂.leftHomology where hom
参数：e : S₁ ≅ S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `S₁.leftHomology ≅ S₂.leftHomology` induced by an isomorphism of
short complexes `S₁ ≅ S₂`.
-/
noncomputable def leftHomologyMapIso (e : S₁ ≅ S₂) [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] : S₁.leftHomology ≅ S₂.leftHomology where
  hom := leftHomologyMap e.hom
  inv := leftHomologyMap e.inv
  hom_inv_id := by rw [← leftHomologyMap_comp, e.hom_inv_id, leftHomologyMap_id]
  inv_hom_id := by rw [← leftHomologyMap_comp, e.inv_hom_id, leftHomologyMap_id]
/-
**CategoryTheory.ShortComplex.isIso_leftHomologyMap_of_iso** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：isIso_leftHomologyMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasLeftHomology] 
[S₂.HasLeftHomology] : IsIso (leftHomologyMap φ)
参数：φ : S₁ ⟶ S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_leftHomologyMap_of_iso (φ : S₁ ⟶ S₂)
    [IsIso φ] [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    IsIso (leftHomologyMap φ) :=
  inferInstanceAs <| IsIso (leftHomologyMapIso (asIso φ)).hom

/-- The isomorphism `S₁.cycles ≅ S₂.cycles` induced by an isomorphism
of short complexes `S₁ ≅ S₂`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.cyclesMapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：cyclesMapIso (e : S₁ ≅ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology] : S₁.
cycles ≅ S₂.cycles where hom
参数：e : S₁ ≅ S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `S₁.cycles ≅ S₂.cycles` induced by an isomorphism
of short complexes `S₁ ≅ S₂`.
-/
noncomputable def cyclesMapIso (e : S₁ ≅ S₂) [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] : S₁.cycles ≅ S₂.cycles where
  hom := cyclesMap e.hom
  inv := cyclesMap e.inv
  hom_inv_id := by rw [← cyclesMap_comp, e.hom_inv_id, cyclesMap_id]
  inv_hom_id := by rw [← cyclesMap_comp, e.inv_hom_id, cyclesMap_id]
/-
**CategoryTheory.ShortComplex.isIso_cyclesMap_of_iso** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：isIso_cyclesMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasLeftHomology] [S₂.Ha
sLeftHomology] : IsIso (cyclesMap φ)
参数：φ : S₁ ⟶ S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_cyclesMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] : IsIso (cyclesMap φ) :=
  inferInstanceAs <| IsIso (cyclesMapIso (asIso φ)).hom

variable {S}

namespace LeftHomologyData

variable (h : S.LeftHomologyData) [S.HasLeftHomology]

/-- The isomorphism `S.leftHomology ≅ h.H` induced by a left homology data `h` for a
short complex `S`. -/
/-
**CategoryTheory.ShortComplex.LeftHomologyData.leftHomologyIso** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：leftHomologyIso : S.leftHomology ≅ h.H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `S.leftHomology ≅ h.H` induced by a left homology data `h` for a
short complex `S`.
-/
noncomputable def leftHomologyIso : S.leftHomology ≅ h.H :=
  leftHomologyMapIso' (Iso.refl _) _ _

/-- The isomorphism `S.cycles ≅ h.K` induced by a left homology data `h` for a
short complex `S`. -/
/-
**CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：cyclesIso : S.cycles ≅ h.K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `S.cycles ≅ h.K` induced by a left homology data `h` for a
short complex `S`.
-/
noncomputable def cyclesIso : S.cycles ≅ h.K :=
  cyclesMapIso' (Iso.refl _) _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：cyclesIso_hom_comp_i : h.cyclesIso.hom ≫ h.i = S.iCycles
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_i`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cyclesIso_hom_comp_i : h.cyclesIso.hom ≫ h.i = S.iCycles := by
  dsimp [iCycles, LeftHomologyData.cyclesIso]
  simp only [cyclesMap'_i, id_τ₂, comp_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：cyclesIso_inv_comp_iCycles : h.cyclesIso.inv ≫ S.iCycles = h.i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i`：cycle
sIso_hom_comp_i : h.cyclesIso.hom ≫ h.i = S.iCycles
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cyclesIso_inv_comp_iCycles : h.cyclesIso.inv ≫ S.iCycles = h.i := by
  simp only [← h.cyclesIso_hom_comp_i, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.leftHomology** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftHomologyπ_comp_leftHomologyIso_hom :
    S.leftHomologyπ ≫ h.leftHomologyIso.hom = h.cyclesIso.hom ≫ h.π := by
  dsimp only [leftHomologyπ, leftHomologyIso, cyclesIso, leftHomologyMapIso',
    cyclesMapIso', Iso.refl]
  rw [← leftHomologyπ_naturality']

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ShortComplex.LeftHomologyData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_comp_leftHomologyIso_inv :
    h.π ≫ h.leftHomologyIso.inv = h.cyclesIso.inv ≫ S.leftHomologyπ := by
  simp only [← cancel_epi h.cyclesIso.hom, ← cancel_mono h.leftHomologyIso.hom, assoc,
    Iso.inv_hom_id, comp_id, Iso.hom_inv_id_assoc,
    LeftHomologyData.leftHomologyπ_comp_leftHomologyIso_hom]

end LeftHomologyData

namespace LeftHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap_eq** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：leftHomologyMap_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] : leftHomolog
yMap φ = h₁.leftHomologyIso.hom ≫ γ.φH ≫ h₂.leftHomologyIso.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_comp`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S₁ S₂ S₃ : CategoryThe…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma leftHomologyMap_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    leftHomologyMap φ = h₁.leftHomologyIso.hom ≫ γ.φH ≫ h₂.leftHomologyIso.inv := by
  dsimp [LeftHomologyData.leftHomologyIso, leftHomologyMapIso']
  rw [← γ.leftHomologyMap'_eq, ← leftHomologyMap'_comp,
    ← leftHomologyMap'_comp, id_comp, comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.cyclesMap_eq** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：cyclesMap_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] : cyclesMap φ = h₁.
cyclesIso.hom ≫ γ.φK ≫ h₂.cyclesIso.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.cyclesMap'_eq`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_comp`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {S₁ S₂ S₃ : CategoryThe…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma cyclesMap_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    cyclesMap φ = h₁.cyclesIso.hom ≫ γ.φK ≫ h₂.cyclesIso.inv := by
  dsimp [LeftHomologyData.cyclesIso, cyclesMapIso']
  rw [← γ.cyclesMap'_eq, ← cyclesMap'_comp, ← cyclesMap'_comp, id_comp, comp_id]
  rfl
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap_comm** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：leftHomologyMap_comm [S₁.HasLeftHomology] [S₂.HasLeftHomology] : leftHomol
ogyMap φ ≫ h₂.leftHomologyIso.hom = h₁.leftHomologyIso.hom ≫ γ.φH
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap_eq`：left
HomologyMap_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] : leftHomologyMap φ = h
₁.leftHomologyIso.hom ≫ γ.φH ≫ h₂.leftHomologyIso.inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftHomologyMap_comm [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    leftHomologyMap φ ≫ h₂.leftHomologyIso.hom = h₁.leftHomologyIso.hom ≫ γ.φH := by
  simp only [γ.leftHomologyMap_eq, assoc, Iso.inv_hom_id, comp_id]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.cyclesMap_comm** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：cyclesMap_comm [S₁.HasLeftHomology] [S₂.HasLeftHomology] : cyclesMap φ ≫ h
₂.cyclesIso.hom = h₁.cyclesIso.hom ≫ γ.φK
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyMapData.cyclesMap_eq`：cyclesMap_
eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] : cyclesMap φ = h₁.cyclesIso.hom ≫ 
γ.φK ≫ h₂.cyclesIso.inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cyclesMap_comm [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    cyclesMap φ ≫ h₂.cyclesIso.hom = h₁.cyclesIso.hom ≫ γ.φK := by
  simp only [γ.cyclesMap_eq, assoc, Iso.inv_hom_id, comp_id]

end LeftHomologyMapData

section

variable (C)
variable [HasKernels C] [HasCokernels C]

/-- The left homology functor `ShortComplex C ⥤ C`, where the left homology of a
short complex `S` is understood as a cokernel of the obvious map `S.toCycles : S.X₁ ⟶ S.cycles`
where `S.cycles` is a kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.leftHomologyFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ShortComplex`。
形式化陈述：leftHomologyFunctor : ShortComplex C ⥤ C where obj S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left homology functor `ShortComplex C ⥤ C`, where the left homology of a
short complex `S` is understood as a cokernel of the obvious map `S.toCycles : S
.X₁ ⟶ S.cycles`
where `S.cycles` is a kernel of `S.g : S.X₂ ⟶ S.X₃`.
-/
noncomputable def leftHomologyFunctor : ShortComplex C ⥤ C where
  obj S := S.leftHomology
  map := leftHomologyMap

/-- The cycles functor `ShortComplex C ⥤ C` which sends a short complex `S` to `S.cycles`
which is a kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.cyclesFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：cyclesFunctor : ShortComplex C ⥤ C where obj S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cycles functor `ShortComplex C ⥤ C` which sends a short complex `S` to `S.cy
cles`
which is a kernel of `S.g : S.X₂ ⟶ S.X₃`.
-/
noncomputable def cyclesFunctor : ShortComplex C ⥤ C where
  obj S := S.cycles
  map := cyclesMap

/-- The natural transformation `S.cycles ⟶ S.leftHomology` for all short complexes `S`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.leftHomology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：leftHomology : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `S.cycles ⟶ S.leftHomology` for all short complexes `
S`.
-/
noncomputable def leftHomologyπNatTrans : cyclesFunctor C ⟶ leftHomologyFunctor C where
  app S := leftHomologyπ S
  naturality := fun _ _ φ => (leftHomologyπ_naturality φ).symm

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `S.cycles ⟶ S.X₂` for all short complexes `S`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.iCyclesNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：iCyclesNatTrans : cyclesFunctor C ⟶ ShortComplex.π₂ where app S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `S.cycles ⟶ S.X₂` for all short complexes `S`.
-/
noncomputable def iCyclesNatTrans : cyclesFunctor C ⟶ ShortComplex.π₂ where
  app S := S.iCycles

/-- The natural transformation `S.X₁ ⟶ S.cycles` for all short complexes `S`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.toCyclesNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：toCyclesNatTrans : π₁ ⟶ cyclesFunctor C where app S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `S.X₁ ⟶ S.cycles` for all short complexes `S`.
-/
noncomputable def toCyclesNatTrans :
    π₁ ⟶ cyclesFunctor C where
  app S := S.toCycles
  naturality := fun _ _ φ => (toCycles_naturality φ).symm

end

namespace LeftHomologyData

set_option backward.isDefEq.respectTransparency false in
/-- If `φ : S₁ ⟶ S₂` is a morphism of short complexes such that `φ.τ₁` is epi, `φ.τ₂` is an iso
and `φ.τ₃` is mono, then a left homology data for `S₁` induces a left homology data for `S₂` with
the same `K` and `H` fields. The inverse construction is `ofEpiOfIsIsoOfMono'`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofEpiOfIsIsoOfMono** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁) [Epi φ.τ₁] [IsI
so φ.τ₂] [Mono φ.τ₃] : LeftHomologyData S₂
参数：φ : S₁ ⟶ S₂；h : LeftHomologyData S₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…

--- 原说明 ---
If `φ : S₁ ⟶ S₂` is a morphism of short complexes such that `φ.τ₁` is epi, `φ.τ₂
` is an iso
and `φ.τ₃` is mono, then a left homology data for `S₁` induces a left homology d
ata for `S₂` with
the same `K` and `H` fields. The inverse construction is `ofEpiOfIsIsoOfMono'`.
-/
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : LeftHomologyData S₂ := by
  let i : h.K ⟶ S₂.X₂ := h.i ≫ φ.τ₂
  have wi : i ≫ S₂.g = 0 := by simp only [i, assoc, φ.comm₂₃, h.wi_assoc, zero_comp]
  have hi : IsLimit (KernelFork.ofι i wi) := KernelFork.IsLimit.ofι _ _
    (fun x hx => h.liftK (x ≫ inv φ.τ₂) (by rw [assoc, ← cancel_mono φ.τ₃, assoc,
      assoc, ← φ.comm₂₃, IsIso.inv_hom_id_assoc, hx, zero_comp]))
    (fun x hx => by simp [i]) (fun x hx b hb => by
      rw [← cancel_mono h.i, ← cancel_mono φ.τ₂, assoc, assoc, liftK_i_assoc,
        assoc, IsIso.inv_hom_id, comp_id, hb])
  let f' := hi.lift (KernelFork.ofι S₂.f S₂.zero)
  have hf' : φ.τ₁ ≫ f' = h.f' := by
    have eq := @Fork.IsLimit.lift_ι _ _ _ _ _ _ _ ((KernelFork.ofι S₂.f S₂.zero)) hi
    simp only [Fork.ι_ofι] at eq
    rw [← cancel_mono h.i, ← cancel_mono φ.τ₂, assoc, assoc, eq, f'_i, φ.comm₁₂]
  have wπ : f' ≫ h.π = 0 := by
    rw [← cancel_epi φ.τ₁, comp_zero, reassoc_of% hf', h.f'_π]
  have hπ : IsColimit (CokernelCofork.ofπ h.π wπ) := CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => h.descH x (by rw [← hf', assoc, hx, comp_zero]))
    (fun x hx => by simp) (fun x hx b hb => by rw [← cancel_epi h.π, π_descH, hb])
  exact ⟨h.K, h.H, i, h.π, wi, hi, wπ, hπ⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ShortComplex.LeftHomologyData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma τ₁_ofEpiOfIsIsoOfMono_f' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : φ.τ₁ ≫ (ofEpiOfIsIsoOfMono φ h).f' = h.f' := by
  rw [← cancel_mono (ofEpiOfIsIsoOfMono φ h).i, assoc, f'_i,
    ofEpiOfIsIsoOfMono_i, f'_i_assoc, φ.comm₁₂]

set_option backward.isDefEq.respectTransparency false in
/-- If `φ : S₁ ⟶ S₂` is a morphism of short complexes such that `φ.τ₁` is epi, `φ.τ₂` is an iso
and `φ.τ₃` is mono, then a left homology data for `S₂` induces a left homology data for `S₁` with
the same `K` and `H` fields. The inverse construction is `ofEpiOfIsIsoOfMono`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofEpiOfIsIsoOfMono'** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂) [Epi φ.τ₁] [Is
Iso φ.τ₂] [Mono φ.τ₃] : LeftHomologyData S₁
参数：φ : S₁ ⟶ S₂；h : LeftHomologyData S₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…

--- 原说明 ---
If `φ : S₁ ⟶ S₂` is a morphism of short complexes such that `φ.τ₁` is epi, `φ.τ₂
` is an iso
and `φ.τ₃` is mono, then a left homology data for `S₂` induces a left homology d
ata for `S₁` with
the same `K` and `H` fields. The inverse construction is `ofEpiOfIsIsoOfMono`.
-/
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : LeftHomologyData S₁ := by
  let i : h.K ⟶ S₁.X₂ := h.i ≫ inv φ.τ₂
  have wi : i ≫ S₁.g = 0 := by
    rw [assoc, ← cancel_mono φ.τ₃, zero_comp, assoc, assoc, ← φ.comm₂₃,
      IsIso.inv_hom_id_assoc, h.wi]
  have hi : IsLimit (KernelFork.ofι i wi) := KernelFork.IsLimit.ofι _ _
    (fun x hx => h.liftK (x ≫ φ.τ₂)
      (by rw [assoc, φ.comm₂₃, reassoc_of% hx, zero_comp]))
    (fun x hx => by simp [i])
    (fun x hx b hb => by rw [← cancel_mono h.i, ← cancel_mono (inv φ.τ₂), assoc, assoc,
      hb, liftK_i_assoc, assoc, IsIso.hom_inv_id, comp_id])
  let f' := hi.lift (KernelFork.ofι S₁.f S₁.zero)
  have hf' : f' ≫ i = S₁.f := Fork.IsLimit.lift_ι _
  have hf'' : f' = φ.τ₁ ≫ h.f' := by
    rw [← cancel_mono h.i, ← cancel_mono (inv φ.τ₂), assoc, assoc, assoc, hf', f'_i_assoc,
      φ.comm₁₂_assoc, IsIso.hom_inv_id, comp_id]
  have wπ : f' ≫ h.π = 0 := by simp only [hf'', assoc, f'_π, comp_zero]
  have hπ : IsColimit (CokernelCofork.ofπ h.π wπ) := CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => h.descH x (by rw [← cancel_epi φ.τ₁, ← reassoc_of% hf'', hx, comp_zero]))
    (fun x hx => π_descH _ _ _)
    (fun x hx b hx => by rw [← cancel_epi h.π, π_descH, hx])
  exact ⟨h.K, h.H, i, h.π, wi, hi, wπ, hπ⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofEpiOfIsIsoOfMono'_f'** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} (φ : S₁ ⟶ S₂) (h : S₂.LeftHomologyData) [inst_2 : CategoryTheory.Epi φ.τ₁]   
[inst_3 : CategoryTheory.IsIso φ.τ₂] [inst_4 : CategoryTheory.Mono φ.τ₃],   (Cat
egoryTheory.ShortComplex.LeftHomologyData.ofEpiOfIsIsoOfMono' φ h).f' =     Cate
goryTheory.CategoryStruct.comp φ.τ₁ h.f'
参数：φ : S₁ ⟶ S₂；h : S₂.LeftHomologyData；CategoryTheory.ShortComplex.LeftHomologyD
ata.ofEpiOfIsIsoOfMono' φ h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instMonoI`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_i`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.ofEpiOfIsIsoOfMono'_i`：∀ {C
 : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryThe
ory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_i_assoc`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₁₂_assoc`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma ofEpiOfIsIsoOfMono'_f' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : (ofEpiOfIsIsoOfMono' φ h).f' = φ.τ₁ ≫ h.f' := by
  rw [← cancel_mono (ofEpiOfIsIsoOfMono' φ h).i, f'_i, ofEpiOfIsIsoOfMono'_i,
    assoc, f'_i_assoc, φ.comm₁₂_assoc, IsIso.hom_inv_id, comp_id]

/-- If `e : S₁ ≅ S₂` is an isomorphism of short complexes and `h₁ : LeftHomologyData S₁`,
this is the left homology data for `S₂` deduced from the isomorphism. -/
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：ofIso (e : S₁ ≅ S₂) (h₁ : LeftHomologyData S₁) : LeftHomologyData S₂
参数：e : S₁ ≅ S₂；h₁ : LeftHomologyData S₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e : S₁ ≅ S₂` is an isomorphism of short complexes and `h₁ : LeftHomologyData
 S₁`,
this is the left homology data for `S₂` deduced from the isomorphism.
-/
noncomputable def ofIso (e : S₁ ≅ S₂) (h₁ : LeftHomologyData S₁) : LeftHomologyData S₂ :=
  h₁.ofEpiOfIsIsoOfMono e.hom

end LeftHomologyData

/-
**CategoryTheory.ShortComplex.hasLeftHomology_of_epi_of_isIso_of_mono** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：hasLeftHomology_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [HasLeftHomology S₁]
 [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasLeftHomology S₂
参数：φ : S₁ ⟶ S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.HasLeftHomology.mk'`：mk' (h : S.LeftHomology
Data) : HasLeftHomology S
-/
lemma hasLeftHomology_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [HasLeftHomology S₁]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasLeftHomology S₂ :=
  HasLeftHomology.mk' (LeftHomologyData.ofEpiOfIsIsoOfMono φ S₁.leftHomologyData)
/-
**CategoryTheory.ShortComplex.hasLeftHomology_of_epi_of_isIso_of_mono'** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：hasLeftHomology_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [HasLeftHomology S₂
] [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasLeftHomology S₁
参数：φ : S₁ ⟶ S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.HasLeftHomology.mk'`：mk' (h : S.LeftHomology
Data) : HasLeftHomology S
-/
lemma hasLeftHomology_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [HasLeftHomology S₂]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasLeftHomology S₁ :=
  HasLeftHomology.mk' (LeftHomologyData.ofEpiOfIsIsoOfMono' φ S₂.leftHomologyData)
/-
**CategoryTheory.ShortComplex.hasLeftHomology_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：hasLeftHomology_of_iso {S₁ S₂ : ShortComplex C} (e : S₁ ≅ S₂) [HasLeftHomo
logy S₁] : HasLeftHomology S₂
参数：e : S₁ ≅ S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.hasLeftHomology_of_epi_of_isIso_of_mono`：has
LeftHomology_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [HasLeftHomology S₁] [Epi φ.τ
₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasLeftHomology S₂
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoτ₁`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoτ₂`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoτ₃`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory…
-/
lemma hasLeftHomology_of_iso {S₁ S₂ : ShortComplex C} (e : S₁ ≅ S₂) [HasLeftHomology S₁] :
    HasLeftHomology S₂ :=
  hasLeftHomology_of_epi_of_isIso_of_mono e.hom

namespace LeftHomologyMapData

set_option backward.isDefEq.respectTransparency false in
/-- This left homology map data expresses compatibilities of the left homology data
constructed by `LeftHomologyData.ofEpiOfIsIsoOfMono` -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.ofEpiOfIsIsoOfMono** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁) [Epi φ.τ₁] [IsI
so φ.τ₂] [Mono φ.τ₃] : LeftHomologyMapData φ h (LeftHomologyData.ofEpiOfIsIsoOfM
ono φ h) where φK
参数：φ : S₁ ⟶ S₂；h : LeftHomologyData S₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This left homology map data expresses compatibilities of the left homology data
constructed by `LeftHomologyData.ofEpiOfIsIsoOfMono`
-/
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    LeftHomologyMapData φ h (LeftHomologyData.ofEpiOfIsIsoOfMono φ h) where
  φK := 𝟙 _
  φH := 𝟙 _

set_option backward.defeqAttrib.useBackward true in
/-- This left homology map data expresses compatibilities of the left homology data
constructed by `LeftHomologyData.ofEpiOfIsIsoOfMono'` -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.ofEpiOfIsIsoOfMono'** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂) [Epi φ.τ₁] [Is
Iso φ.τ₂] [Mono φ.τ₃] : LeftHomologyMapData φ (LeftHomologyData.ofEpiOfIsIsoOfMo
no' φ h) h where φK
参数：φ : S₁ ⟶ S₂；h : LeftHomologyData S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This left homology map data expresses compatibilities of the left homology data
constructed by `LeftHomologyData.ofEpiOfIsIsoOfMono'`
-/
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    LeftHomologyMapData φ (LeftHomologyData.ofEpiOfIsIsoOfMono' φ h) h where
  φK := 𝟙 _
  φH := 𝟙 _

end LeftHomologyMapData

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (leftHomologyMap' φ h₁ h₂) := by
  let h₂' := LeftHomologyData.ofEpiOfIsIsoOfMono φ h₁
  have : IsIso (leftHomologyMap' φ h₁ h₂') := by
    rw [(LeftHomologyMapData.ofEpiOfIsIsoOfMono φ h₁).leftHomologyMap'_eq]
    dsimp
    infer_instance
  have eq := leftHomologyMap'_comp φ (𝟙 S₂) h₁ h₂' h₂
  rw [comp_id] at eq
  rw [eq]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- If a morphism of short complexes `φ : S₁ ⟶ S₂` is such that `φ.τ₁` is epi, `φ.τ₂` is an iso,
and `φ.τ₃` is mono, then the induced morphism on left homology is an isomorphism. -/
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a morphism of short complexes `φ : S₁ ⟶ S₂` is such that `φ.τ₁` is epi, `φ.τ₂
` is an iso,
and `φ.τ₃` is mono, then the induced morphism on left homology is an isomorphism
.
-/
instance (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (leftHomologyMap φ) := by
  dsimp only [leftHomologyMap]
  infer_instance

section

variable (S) (h : LeftHomologyData S) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  [HasLeftHomology S]

/-- A morphism `k : A ⟶ S.X₂` such that `k ≫ S.g = 0` lifts to a morphism `A ⟶ S.cycles`. -/
/-
**CategoryTheory.ShortComplex.liftCycles** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ShortComplex`。
形式化陈述：liftCycles : A ⟶ S.cycles
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `k : A ⟶ S.X₂` such that `k ≫ S.g = 0` lifts to a morphism `A ⟶ S.cyc
les`.
-/
noncomputable def liftCycles : A ⟶ S.cycles :=
  S.leftHomologyData.liftK k hk

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.liftCycles_i** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：liftCycles_i : S.liftCycles k hk ≫ S.iCycles = k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.liftK_i`：liftK_i (k : A ⟶ S
.X₂) (hk : k ≫ S.g = 0) : h.liftK k hk ≫ h.i = k
-/
lemma liftCycles_i : S.liftCycles k hk ≫ S.iCycles = k :=
  LeftHomologyData.liftK_i _ k hk

@[reassoc]
/-
**CategoryTheory.ShortComplex.comp_liftCycles** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：comp_liftCycles {A' : C} (α : A' ⟶ A) : α ≫ S.liftCycles k hk = S.liftCycl
es (α ≫ k) (by rw [assoc, hk, comp_zero])
参数：α : A' ⟶ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.cycles_ext`：cycles_ext {A : C} (f₁ f₂ : A ⟶ 
S.cycles) (h : f₁ ≫ S.iCycles = f₂ ≫ S.iCycles) : f₁ = f₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ShortComplex.liftCycles_i`：liftCycles_i : S.liftCycles k 
hk ≫ S.iCycles = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_liftCycles {A' : C} (α : A' ⟶ A) :
    α ≫ S.liftCycles k hk = S.liftCycles (α ≫ k) (by rw [assoc, hk, comp_zero]) := by cat_disch

/-- Via `S.iCycles : S.cycles ⟶ S.X₂`, the object `S.cycles` identifies to the
kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
/-
**CategoryTheory.ShortComplex.cyclesIsKernel** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：cyclesIsKernel : IsLimit (KernelFork.ofι S.iCycles S.iCycles_g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Via `S.iCycles : S.cycles ⟶ S.X₂`, the object `S.cycles` identifies to the
kernel of `S.g : S.X₂ ⟶ S.X₃`.
-/
noncomputable def cyclesIsKernel : IsLimit (KernelFork.ofι S.iCycles S.iCycles_g) :=
  S.leftHomologyData.hi

/-- The canonical isomorphism `S.cycles ≅ kernel S.g`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.cyclesIsoKernel** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：cyclesIsoKernel [HasKernel S.g] : S.cycles ≅ kernel S.g where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `S.cycles ≅ kernel S.g`.
-/
noncomputable def cyclesIsoKernel [HasKernel S.g] : S.cycles ≅ kernel S.g where
  hom := kernel.lift S.g S.iCycles (by simp)
  inv := S.liftCycles (kernel.ι S.g) (by simp)

section

variable {kf : KernelFork S.g} (hkf : IsLimit kf)

/-- The isomorphism from the point of a limit kernel fork of `S.g` to `S.cycles`. -/
/-
**CategoryTheory.ShortComplex.isoCyclesOfIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：isoCyclesOfIsLimit : kf.pt ≅ S.cycles
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.iCycles_g`：iCycles_g : S.iCycles ≫ S.g = 0

--- 原说明 ---
The isomorphism from the point of a limit kernel fork of `S.g` to `S.cycles`.
-/
noncomputable def isoCyclesOfIsLimit :
    kf.pt ≅ S.cycles :=
  IsLimit.conePointUniqueUpToIso hkf S.cyclesIsKernel

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.isoCyclesOfIsLimit_inv_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoCyclesOfIsLimit_inv_ι : (S.isoCyclesOfIsLimit hkf).inv ≫ kf.ι = S.iCycles :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingParallelPair.zero

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.isoCyclesOfIsLimit_hom_iCycles** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：isoCyclesOfIsLimit_hom_iCycles : (S.isoCyclesOfIsLimit hkf).hom ≫ S.iCycle
s = kf.ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
· 使用引理 `CategoryTheory.ShortComplex.iCycles_g`：iCycles_g : S.iCycles ≫ S.g = 0
-/
lemma isoCyclesOfIsLimit_hom_iCycles : (S.isoCyclesOfIsLimit hkf).hom ≫ S.iCycles = kf.ι :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

end

/-- The morphism `A ⟶ S.leftHomology` obtained from a morphism `k : A ⟶ S.X₂`
such that `k ≫ S.g = 0.` -/
@[simp]
/-
**CategoryTheory.ShortComplex.liftLeftHomology** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：liftLeftHomology : A ⟶ S.leftHomology
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `A ⟶ S.leftHomology` obtained from a morphism `k : A ⟶ S.X₂`
such that `k ≫ S.g = 0.`
-/
noncomputable def liftLeftHomology : A ⟶ S.leftHomology :=
  S.liftCycles k hk ≫ S.leftHomologyπ

@[reassoc]
/-
**CategoryTheory.ShortComplex.liftCycles_leftHomology** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftCycles_leftHomologyπ_eq_zero_of_boundary (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    S.liftCycles k (by rw [hx, assoc, S.zero, comp_zero]) ≫ S.leftHomologyπ = 0 :=
  LeftHomologyData.liftK_π_eq_zero_of_boundary _ k x hx

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.toCycles_comp_leftHomology** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toCycles_comp_leftHomologyπ : S.toCycles ≫ S.leftHomologyπ = 0 :=
  S.liftCycles_leftHomologyπ_eq_zero_of_boundary S.f (𝟙 _) (by rw [id_comp])

/-- Via `S.leftHomologyπ : S.cycles ⟶ S.leftHomology`, the object `S.leftHomology` identifies
to the cokernel of `S.toCycles : S.X₁ ⟶ S.cycles`. -/
/-
**CategoryTheory.ShortComplex.leftHomologyIsCokernel** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：leftHomologyIsCokernel : IsColimit (CokernelCofork.ofπ S.leftHomologyπ S.t
oCycles_comp_leftHomologyπ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Via `S.leftHomologyπ : S.cycles ⟶ S.leftHomology`, the object `S.leftHomology` i
dentifies
to the cokernel of `S.toCycles : S.X₁ ⟶ S.cycles`.
-/
noncomputable def leftHomologyIsCokernel :
    IsColimit (CokernelCofork.ofπ S.leftHomologyπ S.toCycles_comp_leftHomologyπ) :=
  S.leftHomologyData.hπ

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.liftCycles_comp_cyclesMap** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ShortComplex`。
形式化陈述：liftCycles_comp_cyclesMap (φ : S ⟶ S₁) [S₁.HasLeftHomology] : S.liftCycles
 k hk ≫ cyclesMap φ = S₁.liftCycles (k ≫ φ.τ₂) (by rw [assoc, φ.comm₂₃, reassoc_
of% hk, zero_comp])
参数：φ : S ⟶ S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.cycles_ext`：cycles_ext {A : C} (f₁ f₂ : A ⟶ 
S.cycles) (h : f₁ ≫ S.iCycles = f₂ ≫ S.iCycles) : f₁ = f₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ShortComplex.cyclesMap_i`：cyclesMap_i : cyclesMap φ ≫ S₂.
iCycles = S₁.iCycles ≫ φ.τ₂
· 使用定理 `CategoryTheory.ShortComplex.liftCycles_i_assoc`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   (S : CategoryTheory.Sho…
· 使用引理 `CategoryTheory.ShortComplex.liftCycles_i`：liftCycles_i : S.liftCycles k 
hk ≫ S.iCycles = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftCycles_comp_cyclesMap (φ : S ⟶ S₁) [S₁.HasLeftHomology] :
    S.liftCycles k hk ≫ cyclesMap φ =
      S₁.liftCycles (k ≫ φ.τ₂) (by rw [assoc, φ.comm₂₃, reassoc_of% hk, zero_comp]) := by
  cat_disch

variable {S}

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.liftCycles_comp_cyclesIso_hom** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (
h : S.LeftHomologyData) {A : C} (k : A ⟶ S.X₂)   (hk : CategoryTheory.CategorySt
ruct.comp k S.g = 0) [inst_2 : S.HasLeftHomology],   CategoryTheory.CategoryStru
ct.comp (S.liftCycles k hk) h.cyclesIso.hom = h.liftK k hk
参数：h : S.LeftHomologyData；k : A ⟶ S.X₂；hk : CategoryTheory.CategoryStruct.comp k
 S.g = 0；S.liftCycles k hk。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instMonoI`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i`：cycle
sIso_hom_comp_i : h.cyclesIso.hom ≫ h.i = S.iCycles
· 使用引理 `CategoryTheory.ShortComplex.liftCycles_i`：liftCycles_i : S.liftCycles k 
hk ≫ S.iCycles = k
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.liftK_i`：liftK_i (k : A ⟶ S
.X₂) (hk : k ≫ S.g = 0) : h.liftK k hk ≫ h.i = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LeftHomologyData.liftCycles_comp_cyclesIso_hom :
    S.liftCycles k hk ≫ h.cyclesIso.hom = h.liftK k hk := by
  simp only [← cancel_mono h.i, assoc, LeftHomologyData.cyclesIso_hom_comp_i,
    liftCycles_i, LeftHomologyData.liftK_i]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.LeftHomologyData.lift_K_comp_cyclesIso_inv** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComplex C} (
h : S.LeftHomologyData) {A : C} (k : A ⟶ S.X₂)   (hk : CategoryTheory.CategorySt
ruct.comp k S.g = 0) [inst_2 : S.HasLeftHomology],   CategoryTheory.CategoryStru
ct.comp (h.liftK k hk) h.cyclesIso.inv = S.liftCycles k hk
参数：h : S.LeftHomologyData；k : A ⟶ S.X₂；hk : CategoryTheory.CategoryStruct.comp k
 S.g = 0；h.liftK k hk。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.liftCycles_comp_cyclesIso_h
om`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma LeftHomologyData.lift_K_comp_cyclesIso_inv :
    h.liftK k hk ≫ h.cyclesIso.inv = S.liftCycles k hk := by
  rw [← h.liftCycles_comp_cyclesIso_hom, assoc, Iso.hom_inv_id, comp_id]

end

namespace HasLeftHomology

variable (S)

/-
**CategoryTheory.ShortComplex.HasLeftHomology.hasKernel** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ShortComplex.HasLeftHomology`。
形式化陈述：hasKernel [S.HasLeftHomology] : HasKernel S.g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wi`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
-/
lemma hasKernel [S.HasLeftHomology] : HasKernel S.g :=
  ⟨⟨⟨_, S.leftHomologyData.hi⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.HasLeftHomology.hasCokernel** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ShortComplex.HasLeftHomology`。
形式化陈述：hasCokernel [S.HasLeftHomology] [HasKernel S.g] : HasCokernel (kernel.lift
 S.g S.f S.zero)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_π`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wi`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsLimit.lift_comp_conePointUniqueUpToIso_hom`：lift
_comp_conePointUniqueUpToIso_hom {r s t : Cone F} (P : IsLimit s) (Q : IsLimit t
) : P.lift r ≫ (conePointUniqueUpToIso P Q).hom = Q.lift…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G
-/
lemma hasCokernel [S.HasLeftHomology] [HasKernel S.g] :
    HasCokernel (kernel.lift S.g S.f S.zero) := by
  let h := S.leftHomologyData
  have : HasColimit (parallelPair h.f' 0) := ⟨⟨⟨_, h.hπ'⟩⟩⟩
  let e : parallelPair (kernel.lift S.g S.f S.zero) 0 ≅ parallelPair h.f' 0 :=
    parallelPair.ext (Iso.refl _) (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) h.hi)
      (by cat_disch) (by simp)
  exact hasColimit_of_iso e

end HasLeftHomology

/-- The left homology of a short complex `S` identifies to the cokernel of the canonical
morphism `S.X₁ ⟶ kernel S.g`. -/
/-
**CategoryTheory.ShortComplex.leftHomologyIsoCokernelLift** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.ShortComplex`。
形式化陈述：leftHomologyIsoCokernelLift [S.HasLeftHomology] [HasKernel S.g] [HasCokern
el (kernel.lift S.g S.f S.zero)] : S.leftHomology ≅ cokernel (kernel.lift S.g S.
f S.zero)
参数：kernel.lift S.g S.f S.zero。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…

--- 原说明 ---
The left homology of a short complex `S` identifies to the cokernel of the canon
ical
morphism `S.X₁ ⟶ kernel S.g`.
-/
noncomputable def leftHomologyIsoCokernelLift [S.HasLeftHomology] [HasKernel S.g]
    [HasCokernel (kernel.lift S.g S.f S.zero)] :
    S.leftHomology ≅ cokernel (kernel.lift S.g S.f S.zero) :=
  (LeftHomologyData.ofHasKernelOfHasCokernel S).leftHomologyIso

/-! The following lemmas and instance gives a sufficient condition for a morphism
of short complexes to induce an isomorphism on cycles. -/

/-
**CategoryTheory.ShortComplex.isIso_cyclesMap'_of_isIso_of_mono** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory.ShortComplex 
C} (φ : S₁ ⟶ S₂),   CategoryTheory.IsIso φ.τ₂ →     CategoryTheory.Mono φ.τ₃ →  
     ∀ (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData),         CategoryTh
eory.IsIso (CategoryTheory.ShortComplex.cyclesMap' φ h₁ h₂)
参数：φ : S₁ ⟶ S₂；h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；CategoryTheory.
ShortComplex.cyclesMap' φ h₁ h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₂₃`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.wi`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instMonoI`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.liftK_i`：liftK_i (k : A ⟶ S
.X₂) (hk : k ≫ S.g = 0) : h.liftK k hk ≫ h.i = k
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_i_assoc`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_i`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.liftK_i_assoc`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y

--- 原说明 ---
The following lemmas and instance gives a sufficient condition for a morphism
of short complexes to induce an isomorphism on cycles.
-/
lemma isIso_cyclesMap'_of_isIso_of_mono (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    IsIso (cyclesMap' φ h₁ h₂) := by
  refine ⟨h₁.liftK (h₂.i ≫ inv φ.τ₂) ?_, ?_, ?_⟩
  · simp only [assoc, ← cancel_mono φ.τ₃, zero_comp, ← φ.comm₂₃, IsIso.inv_hom_id_assoc, h₂.wi]
  · simp only [← cancel_mono h₁.i, assoc, h₁.liftK_i, cyclesMap'_i_assoc,
      IsIso.hom_inv_id, comp_id, id_comp]
  · simp only [← cancel_mono h₂.i, assoc, cyclesMap'_i, h₁.liftK_i_assoc,
      IsIso.inv_hom_id, comp_id, id_comp]
/-
**CategoryTheory.ShortComplex.isIso_cyclesMap_of_isIso_of_mono'** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：isIso_cyclesMap_of_isIso_of_mono' (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₃ : Mo
no φ.τ₃) [S₁.HasLeftHomology] [S₂.HasLeftHomology] : IsIso (cyclesMap φ)
参数：φ : S₁ ⟶ S₂；h₂ : IsIso φ.τ₂；h₃ : Mono φ.τ₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.isIso_cyclesMap'_of_isIso_of_mono`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma isIso_cyclesMap_of_isIso_of_mono' (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃)
    [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    IsIso (cyclesMap φ) :=
  isIso_cyclesMap'_of_isIso_of_mono φ h₂ h₃ _ _
/-
**CategoryTheory.ShortComplex.isIso_cyclesMap_of_isIso_of_mono** 是 Mathlib 中的一个实
例，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：isIso_cyclesMap_of_isIso_of_mono (φ : S₁ ⟶ S₂) [IsIso φ.τ₂] [Mono φ.τ₃] [S
₁.HasLeftHomology] [S₂.HasLeftHomology] : IsIso (cyclesMap φ)
参数：φ : S₁ ⟶ S₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.isIso_cyclesMap_of_isIso_of_mono'`：isIso_cyc
lesMap_of_isIso_of_mono' (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃) [S₁.Ha
sLeftHomology] [S₂.HasLeftHomology] : IsIso (cycles…
-/
instance isIso_cyclesMap_of_isIso_of_mono (φ : S₁ ⟶ S₂) [IsIso φ.τ₂] [Mono φ.τ₃]
    [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    IsIso (cyclesMap φ) :=
  isIso_cyclesMap_of_isIso_of_mono' φ inferInstance inferInstance

end ShortComplex

end CategoryTheory

