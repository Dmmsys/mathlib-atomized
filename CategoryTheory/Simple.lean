/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Order.Atoms

/-!
# Simple objects

We define simple objects in any category with zero morphisms.
A simple object is an object `Y` such that any monomorphism `f : X ⟶ Y`
is either an isomorphism or zero (but not both).

This is formalized as a `Prop`-valued typeclass `Simple X`.

In some contexts, especially representation theory, simple objects are called "irreducibles".

If a morphism `f` out of a simple object is nonzero and has a kernel, then that kernel is zero.
(We state this as `kernel.ι f = 0`, but should add `kernel f ≅ 0`.)

When the category is abelian, being simple is the same as being cosimple (although we do not
state a separate typeclass for this).
As a consequence, any nonzero epimorphism out of a simple object is an isomorphism,
and any nonzero morphism into a simple object has trivial cokernel.

We show that any simple object is indecomposable.
-/

public section


noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

section

variable [HasZeroMorphisms C]

/-- An object is simple if monomorphisms into it are (exclusively) either isomorphisms or zero. -/
/-
**CategoryTheory.Simple** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.Limits.HasZeroMorphisms C] → C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object is simple if monomorphisms into it are (exclusively) either isomorphis
ms or zero.
-/
class Simple (X : C) : Prop where
  mono_isIso_iff_nonzero : ∀ {Y : C} (f : Y ⟶ X) [Mono f], IsIso f ↔ f ≠ 0

/-- A nonzero monomorphism to a simple object is an isomorphism. -/
/-
**CategoryTheory.isIso_of_mono_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：isIso_of_mono_of_nonzero {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : f 
!= 0) : IsIso f
参数：w : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Simple.mono_isIso_iff_nonzero`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C} {X : C}   [self : CategoryTheor…

--- 原说明 ---
A nonzero monomorphism to a simple object is an isomorphism.
-/
theorem isIso_of_mono_of_nonzero {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : f ≠ 0) : IsIso f :=
  (Simple.mono_isIso_iff_nonzero f).mpr w
/-
**CategoryTheory.Functor.simple_of_simple_obj** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {D : Type u_1} [inst_2 : CategoryTheory.Cat
egory.{v_1, u_1} D] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) [F.PreservesMonomorphisms] [F.PreservesZeroMorphisms]
 [F.ReflectsIsomorphisms]   [F.Faithful] (X : C) [CategoryTheory.Simple (F.obj X
)], CategoryTheory.Simple X
参数：F : CategoryTheory.Functor C D；X : C；F.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `CategoryTheory.Simple.mono_isIso_iff_nonzero`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C} {X : C}   [self : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `CategoryTheory.Functor.map_eq_zero_iff`：map_eq_zero_iff (F : C ⥤ D) [Pre
servesZeroMorphisms F] [Faithful F] {X Y : C} {f : X ⟶ Y} : F.map f = 0 ↔ f = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Functor.simple_of_simple_obj {D : Type*} [Category* D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesMonomorphisms] [F.PreservesZeroMorphisms] [F.ReflectsIsomorphisms] [F.Faithful]
    (X : C) [Simple (F.obj X)] : Simple X :=
  .mk fun {Y} g _ ↦ by
    rw [← isIso_iff_of_reflects_iso g F, Simple.mono_isIso_iff_nonzero (F.map g),
      ne_eq, ne_eq, not_iff_not, F.map_eq_zero_iff]
/-
**CategoryTheory.Simple.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Simple`
。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   [CategoryTheory.Simple Y] (i : X 
≅ Y), CategoryTheory.Simple X
参数：i : X ≅ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Simple.mono_isIso_iff_nonzero`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C} {X : C}   [self : CategoryTheor…
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.isIso_of_mono_of_nonzero`：isIso_of_mono_of_nonzero {X Y :
 C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : f != 0) : IsIso f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
theorem Simple.of_iso {X Y : C} [Simple Y] (i : X ≅ Y) : Simple X :=
  { mono_isIso_iff_nonzero := fun f m => by
      constructor
      · intro h w
        have j : IsIso (f ≫ i.hom) := by infer_instance
        rw [Simple.mono_isIso_iff_nonzero] at j
        subst w
        simp at j
      · intro h
        have j : IsIso (f ≫ i.hom) := by
          apply isIso_of_mono_of_nonzero
          intro w
          apply h
          simpa using (cancel_mono i.inv).2 w
        rw [← Category.comp_id f, ← i.hom_inv_id, ← Category.assoc]
        infer_instance }
/-
**CategoryTheory.Simple.iff_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
ple`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   (i : X ≅ Y), CategoryTheory.Simpl
e X ↔ CategoryTheory.Simple Y
参数：i : X ≅ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Simple.of_iso`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y : C}   [
CategoryTheory.Sim…
-/
theorem Simple.iff_of_iso {X Y : C} (i : X ≅ Y) : Simple X ↔ Simple Y :=
  ⟨fun _ => Simple.of_iso i.symm, fun _ => Simple.of_iso i⟩
/-
**CategoryTheory.simple_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：simple_obj {D : Type*} [Category* D] [HasZeroMorphisms D] (F : C ⥤ D) [F.I
sEquivalence] (X : C) [Simple X] : Simple (F.obj X)
参数：F : C ⥤ D；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.asEquivalence_functor`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Simple.of_iso`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y : C}   [
CategoryTheory.Sim…
· 使用定理 `CategoryTheory.Functor.id_obj`：id_obj (X : C) : (𝟭 C).obj X = X
· 使用定理 `CategoryTheory.Functor.comp_obj`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.simple_of_simple_obj`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {D : Type u_1} [inst_2 : Cate…
· 使用定理 `CategoryTheory.Functor.preservesMonomorphisms_of_isRightAdjoint`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_full`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
-/
theorem simple_obj {D : Type*} [Category* D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.IsEquivalence] (X : C) [Simple X] : Simple (F.obj X) := by
  rw [← F.asEquivalence_functor]
  have := F.asEquivalence.counitIso.app (F.asEquivalence.functor.obj X)
  rw [Functor.comp_obj, Functor.id_obj] at this
  have := Simple.of_iso <| Functor.preimageIso _ this
  exact Functor.simple_of_simple_obj F.asEquivalence.inverse _
/-
**CategoryTheory.simple_obj_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：simple_obj_iff {D : Type*} [Category* D] [HasZeroMorphisms D] (F : C ⥤ D) 
[F.IsEquivalence] (X : C) : Simple (F.obj X) ↔ Simple X
参数：F : C ⥤ D；X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.simple_of_simple_obj`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {D : Type u_1} [inst_2 : Cate…
· 使用定理 `CategoryTheory.Functor.preservesMonomorphisms_of_isRightAdjoint`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_full`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.simple_obj`：simple_obj {D : Type*} [Category* D] [HasZero
Morphisms D] (F : C ⥤ D) [F.IsEquivalence] (X : C) [Simple X] : Simple (F.obj X)
-/
theorem simple_obj_iff {D : Type*} [Category* D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.IsEquivalence] (X : C) :
    Simple (F.obj X) ↔ Simple X :=
  ⟨fun _ ↦ Functor.simple_of_simple_obj F X, fun _ ↦ simple_obj F X⟩
/-
**CategoryTheory.kernel_zero_of_nonzero_from_simple** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory`。
形式化陈述：kernel_zero_of_nonzero_from_simple {X Y : C} [Simple X] {f : X ⟶ Y} [HasKe
rnel f] (w : f != 0) : kernel.ι f = 0
参数：w : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `CategoryTheory.isIso_of_mono_of_nonzero`：isIso_of_mono_of_nonzero {X Y :
 C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : f != 0) : IsIso f
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `CategoryTheory.Limits.eq_zero_of_epi_kernel`：eq_zero_of_epi_kernel [Epi 
(kernel.ι f)] : f = 0
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
-/
theorem kernel_zero_of_nonzero_from_simple {X Y : C} [Simple X] {f : X ⟶ Y} [HasKernel f]
    (w : f ≠ 0) : kernel.ι f = 0 := by
  by_contra h
  have := isIso_of_mono_of_nonzero h
  exact w (eq_zero_of_epi_kernel f)

-- See also `mono_of_nonzero_from_simple`, which requires `Preadditive C`.
/-- A nonzero morphism `f` to a simple object is an epimorphism
(assuming `f` has an image, and `C` has equalizers).
-/
/-
**CategoryTheory.epi_of_nonzero_to_simple** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：epi_of_nonzero_to_simple [HasEqualizers C] {X Y : C} [Simple Y] {f : X ⟶ Y
} [HasImage f] (w : f != 0) : Epi f
参数：w : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `CategoryTheory.isIso_of_mono_of_nonzero`：isIso_of_mono_of_nonzero {X Y :
 C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : f != 0) : IsIso f
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `CategoryTheory.Limits.eq_zero_of_image_eq_zero`：eq_zero_of_image_eq_zero
 {X Y : C} {f : X ⟶ Y} [HasImage f] (w : image.ι f = 0) : f = 0
· 使用定理 `CategoryTheory.Limits.instEpiFactorThruImageOfHasLimitWalkingParallelPai
rParallelPair`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C
} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasImage f]   [∀ {Z : C} (g…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…

--- 原说明 ---
A nonzero morphism `f` to a simple object is an epimorphism
(assuming `f` has an image, and `C` has equalizers).
-/
theorem epi_of_nonzero_to_simple [HasEqualizers C] {X Y : C} [Simple Y] {f : X ⟶ Y} [HasImage f]
    (w : f ≠ 0) : Epi f := by
  rw [← image.fac f]
  have : IsIso (image.ι f) := isIso_of_mono_of_nonzero fun h => w (eq_zero_of_image_eq_zero h)
  apply epi_comp
/-
**CategoryTheory.mono_to_simple_zero_of_not_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory`。
形式化陈述：mono_to_simple_zero_of_not_iso {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f] (
w : IsIso f -> False) : f = 0
参数：w : IsIso f -> False。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `CategoryTheory.isIso_of_mono_of_nonzero`：isIso_of_mono_of_nonzero {X Y :
 C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : f != 0) : IsIso f
-/
theorem mono_to_simple_zero_of_not_iso {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f]
    (w : IsIso f → False) : f = 0 := by
  by_contra h
  exact w (isIso_of_mono_of_nonzero h)
/-
**CategoryTheory.id_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：id_nonzero (X : C) [Simple.{v} X] : 𝟙 X != 0
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Simple.mono_isIso_iff_nonzero`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C} {X : C}   [self : CategoryTheor…
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
-/
theorem id_nonzero (X : C) [Simple.{v} X] : 𝟙 X ≠ 0 :=
  (Simple.mono_isIso_iff_nonzero (𝟙 X)).mp (by infer_instance)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) [Simple.{v} X] : Nontrivial (End X) :=
  nontrivial_of_ne 1 _ (id_nonzero X)

section

/-
**CategoryTheory.Simple.not_isZero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
ple`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] (X : C)   [CategoryTheory.Simple X], ¬Categor
yTheory.Limits.IsZero X
参数：X : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.id_nonzero`：id_nonzero (X : C) [Simple.{v} X] : 𝟙 X != 0
-/
theorem Simple.not_isZero (X : C) [Simple X] : ¬IsZero X := by
  simpa [Limits.IsZero.iff_id_eq_zero] using id_nonzero X

variable [HasZeroObject C]

open ZeroObject

variable (C)

/-- We don't want the definition of 'simple' to include the zero object, so we check that here. -/
/-
**CategoryTheory.zero_not_simple** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：zero_not_simple [Simple (0 : C)] : False
参数：0 : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Simple.mono_isIso_iff_nonzero`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C} {X : C}   [self : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instMono`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C] 
{X : C}   (f : 0 ⟶ X), CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.id_zero`：id_zero : 𝟙 (0 : C) = (0 : (0 : C) ⟶ 0)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
We don't want the definition of 'simple' to include the zero object, so we check
 that here.
-/
theorem zero_not_simple [Simple (0 : C)] : False :=
  (Simple.mono_isIso_iff_nonzero (0 : (0 : C) ⟶ (0 : C))).mp ⟨⟨0, by simp⟩⟩ rfl

end

end

-- We next make the dual arguments, but for this we must be in an abelian category.
section Abelian

variable [Abelian C]

/-- In an abelian category, an object satisfying the dual of the definition of a simple object is
simple. -/
/-
**CategoryTheory.simple_of_cosimple** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：simple_of_cosimple (X : C) (h : forall {Z : C} (f : X ⟶ Z) [Epi f], IsIso 
f ↔ f != 0) : Simple X
参数：X : C；h : forall {Z : C} (f : X ⟶ Z) [Epi f], IsIso f ↔ f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.cokernel.π_of_epi`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X
 Y : C}   (f : X ⟶ Y) [Catego…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
· 使用定理 `CategoryTheory.Limits.cokernel.π_zero_isIso`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
] {X Y : C},   CategoryTheory.IsI…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Preadditive.epi_of_cokernel_zero`：epi_of_cokernel_zero {X
 Y : C} {f : X ⟶ Y} [HasColimit (parallelPair f 0)] (w : cokernel.π f = 0) : Epi
 f
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `CategoryTheory.Limits.cokernel_not_iso_of_nonzero`：cokernel_not_iso_of_n
onzero (w : f != 0) : IsIso (cokernel.π f) -> False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
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
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C

--- 原说明 ---
In an abelian category, an object satisfying the dual of the definition of a sim
ple object is
simple.
-/
theorem simple_of_cosimple (X : C) (h : ∀ {Z : C} (f : X ⟶ Z) [Epi f], IsIso f ↔ f ≠ 0) :
    Simple X :=
  ⟨fun {Y} f I => by
    fconstructor
    · intros
      have hx := cokernel.π_of_epi f
      by_contra h
      subst h
      exact (h _).mp inferInstance hx
    · intro hf
      suffices Epi f by exact isIso_of_mono_of_epi _
      apply Preadditive.epi_of_cokernel_zero
      by_contra h'
      exact cokernel_not_iso_of_nonzero hf ((h _).mpr h')⟩

/-- A nonzero epimorphism from a simple object is an isomorphism. -/
/-
**CategoryTheory.isIso_of_epi_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：isIso_of_epi_of_nonzero {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f] (w : f !=
 0) : IsIso f
参数：w : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `CategoryTheory.Preadditive.mono_of_kernel_zero`：mono_of_kernel_zero {X Y
 : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)] (w : kernel.ι f = 0) : Mono f
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.mono_to_simple_zero_of_not_iso`：mono_to_simple_zero_of_no
t_iso {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : IsIso f -> False) : f = 0
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `CategoryTheory.Limits.kernel_not_iso_of_nonzero`：kernel_not_iso_of_nonze
ro (w : f != 0) : IsIso (kernel.ι f) -> False

--- 原说明 ---
A nonzero epimorphism from a simple object is an isomorphism.
-/
theorem isIso_of_epi_of_nonzero {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f] (w : f ≠ 0) : IsIso f :=
  -- `f ≠ 0` means that `kernel.ι f` is not an iso, and hence zero, and hence `f` is a mono.
  haveI : Mono f :=
    Preadditive.mono_of_kernel_zero (mono_to_simple_zero_of_not_iso (kernel_not_iso_of_nonzero w))
  isIso_of_mono_of_epi f
/-
**CategoryTheory.cokernel_zero_of_nonzero_to_simple** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory`。
形式化陈述：cokernel_zero_of_nonzero_to_simple {X Y : C} [Simple Y] {f : X ⟶ Y} (w : f
 != 0) : cokernel.π f = 0
参数：w : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.isIso_of_epi_of_nonzero`：isIso_of_epi_of_nonzero {X Y : C
} [Simple X] {f : X ⟶ Y} [Epi f] (w : f != 0) : IsIso f
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
· 使用定理 `CategoryTheory.Limits.eq_zero_of_mono_cokernel`：eq_zero_of_mono_cokernel
 [Mono (cokernel.π f)] : f = 0
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
-/
theorem cokernel_zero_of_nonzero_to_simple {X Y : C} [Simple Y] {f : X ⟶ Y} (w : f ≠ 0) :
    cokernel.π f = 0 := by
  by_contra h
  have := isIso_of_epi_of_nonzero h
  exact w (eq_zero_of_mono_cokernel f)
/-
**CategoryTheory.epi_from_simple_zero_of_not_iso** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory`。
形式化陈述：epi_from_simple_zero_of_not_iso {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f] (
w : IsIso f -> False) : f = 0
参数：w : IsIso f -> False。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `CategoryTheory.isIso_of_epi_of_nonzero`：isIso_of_epi_of_nonzero {X Y : C
} [Simple X] {f : X ⟶ Y} [Epi f] (w : f != 0) : IsIso f
-/
theorem epi_from_simple_zero_of_not_iso {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f]
    (w : IsIso f → False) : f = 0 := by
  by_contra h
  exact w (isIso_of_epi_of_nonzero h)

end Abelian

section Indecomposable

variable [Preadditive C] [HasBinaryBiproducts C]

-- There are another three potential variations of this lemma,
-- but as any one suffices to prove `indecomposable_of_simple` we will not give them all.
/-
**CategoryTheory.Biprod.isIso_inl_iff_isZero** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasBinaryBiproducts C] 
(X Y : C),   CategoryTheory.IsIso CategoryTheory.Limits.biprod.inl ↔ CategoryThe
ory.Limits.IsZero Y
参数：X Y : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.isIso_inl_iff_id_eq_fst_comp_inl`：∀ {C : Ty
pe uC} [inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Lim
its.HasZeroMorphisms C]   (X Y : C) [inst_2 : Categ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.biprod.total`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [inst_2
 : CategoryTheory.Limits…
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.IsZero.iff_isSplitEpi_eq_zero`：iff_isSplitEpi_eq_z
ero {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] : IsZero Y ↔ f = 0
· 使用定理 `CategoryTheory.Limits.biprod.snd_epi`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
-/
theorem Biprod.isIso_inl_iff_isZero (X Y : C) : IsIso (biprod.inl : X ⟶ X ⊞ Y) ↔ IsZero Y := by
  rw [biprod.isIso_inl_iff_id_eq_fst_comp_inl, ← biprod.total, add_eq_left]
  constructor
  · intro h
    replace h := h =≫ biprod.snd
    simpa [← IsZero.iff_isSplitEpi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] using h
  · intro h
    rw [IsZero.iff_isSplitEpi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] at h
    rw [h, zero_comp]

/-- Any simple object in a preadditive category is indecomposable. -/
/-
**CategoryTheory.indecomposable_of_simple** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：indecomposable_of_simple (X : C) [Simple X] : Indecomposable X
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Simple.not_isZero`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] (X : C)  
 [CategoryTheory.Simpl…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `CategoryTheory.Simple.of_iso`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y : C}   [
CategoryTheory.Sim…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Biprod.isIso_inl_iff_isZero`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [inst_2 :
 CategoryTheory.Limits.HasBinary…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Simple.mono_isIso_iff_nonzero`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C} {X : C}   [self : CategoryTheor…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.Limits.biprod.inl_mono`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.IsZero.iff_isSplitMono_eq_zero`：iff_isSplitMono_eq
_zero {X Y : C} (f : X ⟶ Y) [IsSplitMono f] : IsZero X ↔ f = 0

--- 原说明 ---
Any simple object in a preadditive category is indecomposable.
-/
theorem indecomposable_of_simple (X : C) [Simple X] : Indecomposable X :=
  ⟨Simple.not_isZero X, fun Y Z i => by
    refine or_iff_not_imp_left.mpr fun h => ?_
    rw [IsZero.iff_isSplitMono_eq_zero (biprod.inl : Y ⟶ Y ⊞ Z)] at h
    change biprod.inl ≠ 0 at h
    have : Simple (Y ⊞ Z) := Simple.of_iso i.symm
    rw [← Simple.mono_isIso_iff_nonzero biprod.inl] at h
    rwa [Biprod.isIso_inl_iff_isZero] at h⟩

end Indecomposable

section Subobject

variable [HasZeroMorphisms C] [HasZeroObject C]

open ZeroObject

open Subobject

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} [Simple X] : Nontrivial (Subobject X) :=
  nontrivial_of_not_isZero (Simple.not_isZero X)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} [Simple X] : IsSimpleOrder (Subobject X) where
  eq_bot_or_eq_top a := by
    obtain ⟨Y, i, _, rfl⟩ := Subobject.mk_surjective a
    by_cases h : i = 0
    · exact Or.inl (mk_eq_bot_iff_zero.mpr h)
    · exact Or.inr ((isIso_iff_mk_eq_top _).mp ((Simple.mono_isIso_iff_nonzero i).mpr h))

/-- If `X` has subobject lattice `{⊥, ⊤}`, then `X` is simple. -/
/-
**CategoryTheory.simple_of_isSimpleOrder_subobject** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：simple_of_isSimpleOrder_subobject (X : C) [IsSimpleOrder (Subobject X)] : 
Simple X
参数：X : C；Subobject X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `IsSimpleOrder.bot_ne_top`：IsSimpleOrder.bot_ne_top [LE α] [BoundedOrder 
α] [IsSimpleOrder α] : (⊥ : α) != (⊤ : α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.mk_eq_bot_iff_zero`：mk_eq_bot_iff_zero {f : X ⟶
 Y} [Mono f] : Subobject.mk f = ⊥ ↔ f = 0
· 使用定理 `CategoryTheory.Subobject.isIso_iff_mk_eq_top`：isIso_iff_mk_eq_top {X Y :
 C} (f : X ⟶ Y) [Mono f] : IsIso f ↔ mk f = ⊤
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
If `X` has subobject lattice `{⊥, ⊤}`, then `X` is simple.
-/
theorem simple_of_isSimpleOrder_subobject (X : C) [IsSimpleOrder (Subobject X)] : Simple X := by
  constructor; intro Y f hf; constructor
  · intro i
    rw [Subobject.isIso_iff_mk_eq_top] at i
    intro w
    rw [← Subobject.mk_eq_bot_iff_zero] at w
    exact IsSimpleOrder.bot_ne_top (w.symm.trans i)
  · intro i
    rcases IsSimpleOrder.eq_bot_or_eq_top (Subobject.mk f) with (h | h)
    · rw [Subobject.mk_eq_bot_iff_zero] at h
      exact False.elim (i h)
    · exact (Subobject.isIso_iff_mk_eq_top _).mpr h

/-- `X` is simple iff it has subobject lattice `{⊥, ⊤}`. -/
/-
**CategoryTheory.simple_iff_subobject_isSimpleOrder** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory`。
形式化陈述：simple_iff_subobject_isSimpleOrder (X : C) : Simple X ↔ IsSimpleOrder (Sub
object X)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `CategoryTheory.instIsSimpleOrderSubobjectOfSimple`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `CategoryTheory.simple_of_isSimpleOrder_subobject`：simple_of_isSimpleOrde
r_subobject (X : C) [IsSimpleOrder (Subobject X)] : Simple X

--- 原说明 ---
`X` is simple iff it has subobject lattice `{⊥, ⊤}`.
-/
theorem simple_iff_subobject_isSimpleOrder (X : C) : Simple X ↔ IsSimpleOrder (Subobject X) :=
  ⟨by
    intro h
    infer_instance, by
    intro h
    exact simple_of_isSimpleOrder_subobject X⟩

/-- A subobject is simple iff it is an atom in the subobject lattice. -/
/-
**CategoryTheory.subobject_simple_iff_isAtom** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：subobject_simple_iff_isAtom {X : C} (Y : Subobject X) : Simple (Y : C) ↔ I
sAtom Y
参数：Y : Subobject X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `CategoryTheory.simple_iff_subobject_isSimpleOrder`：simple_iff_subobject_
isSimpleOrder (X : C) : Simple X ↔ IsSimpleOrder (Subobject X)
· 使用定理 `OrderIso.isSimpleOrder_iff`：isSimpleOrder_iff [BoundedOrder α] [BoundedO
rder β] (f : α ≃o β) : IsSimpleOrder α ↔ IsSimpleOrder β
· 使用定理 `Set.isSimpleOrder_Iic_iff_isAtom`：isSimpleOrder_Iic_iff_isAtom [PartialO
rder α] [OrderBot α] {a : α} : IsSimpleOrder (Iic a) ↔ IsAtom a

--- 原说明 ---
A subobject is simple iff it is an atom in the subobject lattice.
-/
theorem subobject_simple_iff_isAtom {X : C} (Y : Subobject X) : Simple (Y : C) ↔ IsAtom Y :=
  (simple_iff_subobject_isSimpleOrder _).trans
    ((OrderIso.isSimpleOrder_iff (subobjectOrderIso Y)).trans Set.isSimpleOrder_Iic_iff_isAtom)

end Subobject

end CategoryTheory

