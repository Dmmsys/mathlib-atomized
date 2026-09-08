/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Subobject.WellPowered
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Subobjects in the category of `R`-modules

We construct an explicit order isomorphism between the categorical subobjects of an `R`-module `M`
and its submodules. This immediately implies that the category of `R`-modules is well-powered.

-/

@[expose] public section

open CategoryTheory Subobject Limits

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R] (M : ModuleCat.{v} R)

/-- The categorical subobjects of a module `M` are in one-to-one correspondence with its
submodules. -/
/-
**ModuleCat.subobjectModule** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：subobjectModule : Subobject M ≃o Submodule R M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.mono_as_hom'_subtype`：∀ {R : Type u} [inst : Ring R] {X : Modu
leCat R} (U : Submodule R ↑X), CategoryTheory.Mono (ModuleCat.ofHom U.subtype)

--- 原说明 ---
The categorical subobjects of a module `M` are in one-to-one correspondence with
 its
submodules.
-/
noncomputable def subobjectModule : Subobject M ≃o Submodule R M :=
  OrderIso.symm
    { invFun := fun S => LinearMap.range S.arrow.hom
      toFun := fun N => Subobject.mk (ofHom N.subtype)
      right_inv := fun S => Eq.symm (by
        fapply eq_mk_of_comm
        · apply LinearEquiv.toModuleIso
          apply LinearEquiv.ofBijective (LinearMap.codRestrict
            (LinearMap.range S.arrow.hom) S.arrow.hom _)
          constructor
          · simp [← LinearMap.ker_eq_bot, ker_eq_bot_of_mono]
          · rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict,
              Submodule.comap_subtype_self]
            exact LinearMap.mem_range_self _
        · ext x
          rfl)
      left_inv := fun N => by
        convert!
          congr_arg LinearMap.range
            (ModuleCat.hom_ext_iff.mp (underlyingIso_arrow (ofHom N.subtype))) using 1
        · have :
            (underlyingIso (ofHom N.subtype)).inv =
              ofHom (underlyingIso (ofHom N.subtype)).symm.toLinearEquiv.toLinearMap := by
              ext x
              rfl
          rw [this, hom_comp, hom_ofHom, LinearEquiv.range_comp]
        · exact (Submodule.range_subtype _).symm
      map_rel_iff' := fun {S T} => by
        refine ⟨fun h => ?_, fun h => mk_le_mk_of_comm (↟(Submodule.inclusion h)) rfl⟩
        convert! LinearMap.range_comp_le_range (ofMkLEMk _ _ h).hom (ofHom T.subtype).hom
        · rw [← hom_comp, ofMkLEMk_comp]
          exact (Submodule.range_subtype _).symm
        · exact (Submodule.range_subtype _).symm }
/-
**ModuleCat.wellPowered_moduleCat** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：wellPowered_moduleCat : WellPowered.{v} (ModuleCat.{v} R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
-/
instance wellPowered_moduleCat : WellPowered.{v} (ModuleCat.{v} R) :=
  ⟨fun M => ⟨⟨_, ⟨(subobjectModule M).toEquiv⟩⟩⟩⟩

attribute [local instance] hasKernels_moduleCat

/-- Bundle an element `m : M` such that `f m = 0` as a term of `kernelSubobject f`. -/
/-
**ModuleCat.toKernelSubobject** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：toKernelSubobject {M N : ModuleCat.{v} R} {f : M ⟶ N} : LinearMap.ker f.ho
m ->ₗ[R] kernelSubobject f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle an element `m : M` such that `f m = 0` as a term of `kernelSubobject f`.
-/
noncomputable def toKernelSubobject {M N : ModuleCat.{v} R} {f : M ⟶ N} :
    LinearMap.ker f.hom →ₗ[R] kernelSubobject f :=
  (kernelSubobjectIso f ≪≫ ModuleCat.kernelIsoKer f).inv.hom

@[simp]
/-
**ModuleCat.toKernelSubobject_arrow** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：toKernelSubobject_arrow {M N : ModuleCat R} {f : M ⟶ N} (x : LinearMap.ker
 f.hom) : (kernelSubobject f).arrow (toKernelSubobject x) = x.1
参数：x : LinearMap.ker f.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `ModuleCat.hasKernels_moduleCat`：hasKernels_moduleCat : HasKernels (Modul
eCat R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow'`：kernelSubobject_arrow' : (
kernelSubobjectIso f).inv ≫ (kernelSubobject f).arrow = kernel.ι f
· 使用定理 `ModuleCat.kernelIsoKer_inv_kernel_ι`：kernelIsoKer_inv_kernel_ι : (kernel
IsoKer f).inv ≫ kernel.ι f = ofHom f.hom.ker.subtype
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toKernelSubobject_arrow {M N : ModuleCat R} {f : M ⟶ N} (x : LinearMap.ker f.hom) :
    (kernelSubobject f).arrow (toKernelSubobject x) = x.1 := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10959): the whole proof was just `simp [toKernelSubobject]`.
  simp [toKernelSubobject, -hom_comp, ← CategoryTheory.comp_apply]

/-- An extensionality lemma showing that two elements of a cokernel by an image
are equal if they differ by an element of the image.

The application is for homology:
two elements in homology are equal if they differ by a boundary.
-/
/-
**ModuleCat.cokernel_** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An extensionality lemma showing that two elements of a cokernel by an image
are equal if they differ by an element of the image.

The application is for homology:
two elements in homology are equal if they differ by a boundary.
-/
theorem cokernel_π_imageSubobject_ext {L M N : ModuleCat.{v} R} (f : L ⟶ M) [HasImage f]
    (g : (imageSubobject f : ModuleCat.{v} R) ⟶ N) [HasCokernel g] {x y : N} (l : L)
    (w : x = y + g (factorThruImageSubobject f l)) : cokernel.π g x = cokernel.π g y := by
  subst w
  simp

end ModuleCat

