/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Homology is an additive functor

When `V` is preadditive, `HomologicalComplex V c` is also preadditive,
and `homologyFunctor` is additive.

-/

@[expose] public section


universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

variable {ι : Type*}
variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {W : Type*} [Category* W] [Preadditive W]
variable {W₁ W₂ : Type*} [Category* W₁] [Category* W₂] [HasZeroMorphisms W₁] [HasZeroMorphisms W₂]
variable {c : ComplexShape ι} {C D : HomologicalComplex V c}
variable (f : C ⟶ D) (i : ι)

namespace HomologicalComplex

/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (C ⟶ D) :=
  ⟨{ f := fun _ => 0 }⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (C ⟶ D) :=
  ⟨fun f g => { f := fun i => f.f i + g.f i }⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (C ⟶ D) :=
  ⟨fun f => { f := fun i => -f.f i }⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (C ⟶ D) :=
  ⟨fun f g => { f := fun i => f.f i - g.f i }⟩
/-
**HomologicalComplex.hasNatScalar** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`
。
形式化陈述：hasNatScalar : SMul Nat (C ⟶ D)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasNatScalar : SMul ℕ (C ⟶ D) :=
  ⟨fun n f =>
    { f := fun i => n • f.f i
      comm' := fun i j _ => by simp [Preadditive.nsmul_comp, Preadditive.comp_nsmul] }⟩
/-
**HomologicalComplex.hasIntScalar** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`
。
形式化陈述：hasIntScalar : SMul Int (C ⟶ D)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasIntScalar : SMul ℤ (C ⟶ D) :=
  ⟨fun n f =>
    { f := fun i => n • f.f i
      comm' := fun i j _ => by simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul] }⟩

@[simp]
/-
**HomologicalComplex.zero_f_apply** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`
。
形式化陈述：zero_f_apply (i : ι) : (0 : C ⟶ D).f i = 0
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_f_apply (i : ι) : (0 : C ⟶ D).f i = 0 :=
  rfl

@[simp]
/-
**HomologicalComplex.add_f_apply** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：add_f_apply (f g : C ⟶ D) (i : ι) : (f + g).f i = f.f i + g.f i
参数：f g : C ⟶ D；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_f_apply (f g : C ⟶ D) (i : ι) : (f + g).f i = f.f i + g.f i :=
  rfl

@[simp]
/-
**HomologicalComplex.neg_f_apply** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：neg_f_apply (f : C ⟶ D) (i : ι) : (-f).f i = -f.f i
参数：f : C ⟶ D；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_f_apply (f : C ⟶ D) (i : ι) : (-f).f i = -f.f i :=
  rfl

@[simp]
/-
**HomologicalComplex.sub_f_apply** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：sub_f_apply (f g : C ⟶ D) (i : ι) : (f - g).f i = f.f i - g.f i
参数：f g : C ⟶ D；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_f_apply (f g : C ⟶ D) (i : ι) : (f - g).f i = f.f i - g.f i :=
  rfl

@[simp]
/-
**HomologicalComplex.nsmul_f_apply** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex
`。
形式化陈述：nsmul_f_apply (n : Nat) (f : C ⟶ D) (i : ι) : (n • f).f i = n • f.f i
参数：n : Nat；f : C ⟶ D；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nsmul_f_apply (n : ℕ) (f : C ⟶ D) (i : ι) : (n • f).f i = n • f.f i :=
  rfl

@[simp]
/-
**HomologicalComplex.zsmul_f_apply** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex
`。
形式化陈述：zsmul_f_apply (n : Int) (f : C ⟶ D) (i : ι) : (n • f).f i = n • f.f i
参数：n : Int；f : C ⟶ D；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zsmul_f_apply (n : ℤ) (f : C ⟶ D) (i : ι) : (n • f).f i = n • f.f i :=
  rfl
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (C ⟶ D) :=
  Function.Injective.addCommGroup Hom.f HomologicalComplex.hom_f_injective
    (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (HomologicalComplex V c) where

/-- The `i`-th component of a chain map, as an additive map from chain maps to morphisms. -/
@[simps!]
/-
**HomologicalComplex.Hom.fAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCom
plex.Hom`。
形式化陈述：{ι : Type u_1} →   {V : Type u} →     [inst : CategoryTheory.Category.{v, 
u} V] →       [inst_1 : CategoryTheory.Preadditive V] →         {c : ComplexShap
e ι} → {C₁ C₂ : HomologicalComplex V c} → (i : ι) → (C₁ ⟶ C₂) →+ (C₁.X i ⟶ C₂.X 
i)
参数：i : ι；C₁ ⟶ C₂；C₁.X i ⟶ C₂.X i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`-th component of a chain map, as an additive map from chain maps to morph
isms.
-/
def Hom.fAddMonoidHom {C₁ C₂ : HomologicalComplex V c} (i : ι) : (C₁ ⟶ C₂) →+ (C₁.X i ⟶ C₂.X i) :=
  AddMonoidHom.mk' (fun f => Hom.f f i) fun _ _ => rfl
/-
**HomologicalComplex.eval_additive** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex
`。
形式化陈述：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [i
nst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι} (i : ι), (Homologic
alComplex.eval V c i).Additive
参数：i : ι；HomologicalComplex.eval V c i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance eval_additive (i : ι) : (eval V c i).Additive where

end HomologicalComplex

namespace CategoryTheory

/-- An additive functor induces a functor between homological complexes.
This is sometimes called the "prolongation".
-/
@[simps]
/-
**CategoryTheory.Functor.mapHomologicalComplex** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：{ι : Type u_1} →   {W₁ : Type u_3} →     {W₂ : Type u_4} →       [inst : C
ategoryTheory.Category.{v_2, u_3} W₁] →         [inst_1 : CategoryTheory.Categor
y.{v_3, u_4} W₂] →           [inst_2 : CategoryTheory.Limits.HasZeroMorphisms W₁
] →             [inst_3 : CategoryTheory.Limits.HasZeroMorphisms W₂] →          
     (F : CategoryTheory.Functor W₁ W₂) →                 [F.PreservesZeroMorphi
sms] →                   (c : ComplexShape ι) → CategoryTheory.Functor (Homologi
calComplex W₁ c) (HomologicalComplex W₂ c)
参数：F : CategoryTheory.Functor W₁ W₂；c : ComplexShape ι；HomologicalComplex W₁ c；H
omologicalComplex W₂ c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive functor induces a functor between homological complexes.
This is sometimes called the "prolongation".
-/
def Functor.mapHomologicalComplex (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (c : ComplexShape ι) :
    HomologicalComplex W₁ c ⥤ HomologicalComplex W₂ c where
  obj C :=
    { X := fun i => F.obj (C.X i)
      d := fun i j => F.map (C.d i j)
      shape := fun i j w => by
        rw [C.shape _ _ w, F.map_zero]
      d_comp_d' := fun i j k _ _ => by rw [← F.map_comp, C.d_comp_d, F.map_zero] }
  map f :=
    { f := fun i => F.map (f.f i)
      comm' := fun i j _ => by
        dsimp
        rw [← F.map_comp, ← F.map_comp, f.comm] }
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (c : ComplexShape ι) :
    (F.mapHomologicalComplex c).PreservesZeroMorphisms where
/-
**CategoryTheory.Functor.map_homogical_complex_additive** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [i
nst_1 : CategoryTheory.Preadditive V]   {W : Type u_2} [inst_2 : CategoryTheory.
Category.{v_1, u_2} W] [inst_3 : CategoryTheory.Preadditive W]   (F : CategoryTh
eory.Functor V W) [inst_4 : F.Additive] (c : ComplexShape ι), (F.mapHomologicalC
omplex c).Additive
参数：F : CategoryTheory.Functor V W；c : ComplexShape ι；F.mapHomologicalComplex c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.mapHomologicalComplex_map_f`：∀ {ι : Type u_1} {W₁
 : Type u_3} {W₂ : Type u_4} [inst : CategoryTheory.Category.{v_2, u_3} W₁]   [i
nst_1 : CategoryTheory.Category.{v_3, u_…
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
-/
instance Functor.map_homogical_complex_additive (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    (F.mapHomologicalComplex c).Additive where

variable (W₁)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor on homological complexes induced by the identity functor is
isomorphic to the identity functor. -/
@[simps!]
/-
**CategoryTheory.Functor.mapHomologicalComplexIdIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：{ι : Type u_1} →   (W₁ : Type u_3) →     [inst : CategoryTheory.Category.{
v_2, u_3} W₁] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms W₁] →    
     (c : ComplexShape ι) →           (CategoryTheory.Functor.id W₁).mapHomologi
calComplex c ≅ CategoryTheory.Functor.id (HomologicalComplex W₁ c)
参数：W₁ : Type u_3；c : ComplexShape ι；CategoryTheory.Functor.id W₁；HomologicalComp
lex W₁ c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor on homological complexes induced by the identity functor is
isomorphic to the identity functor.
-/
def Functor.mapHomologicalComplexIdIso (c : ComplexShape ι) :
    (𝟭 W₁).mapHomologicalComplex c ≅ 𝟭 _ :=
  NatIso.ofComponents fun K => Hom.isoOfComponents fun _ => Iso.refl _
/-
**CategoryTheory.Functor.mapHomologicalComplex_reflects_iso** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {ι : Type u_1} (W₁ : Type u_3) {W₂ : Type u_4} [inst : CategoryTheory.Ca
tegory.{v_2, u_3} W₁]   [inst_1 : CategoryTheory.Category.{v_3, u_4} W₂] [inst_2
 : CategoryTheory.Limits.HasZeroMorphisms W₁]   [inst_3 : CategoryTheory.Limits.
HasZeroMorphisms W₂] (F : CategoryTheory.Functor W₁ W₂)   [inst_4 : F.PreservesZ
eroMorphisms] [F.ReflectsIsomorphisms] (c : ComplexShape ι),   (F.mapHomological
Complex c).ReflectsIsomorphisms
参数：W₁ : Type u_3；F : CategoryTheory.Functor W₁ W₂；c : ComplexShape ι；F.mapHomolo
gicalComplex c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
· 使用定理 `HomologicalComplex.Hom.isIso_of_components`：isIso_of_components (f : C₁ 
⟶ C₂) [forall n : ι, IsIso (f.f n)] : IsIso f
-/
instance Functor.mapHomologicalComplex_reflects_iso (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms]
    [ReflectsIsomorphisms F] (c : ComplexShape ι) :
    ReflectsIsomorphisms (F.mapHomologicalComplex c) :=
  ⟨fun f => by
    intro
    have : ∀ n : ι, IsIso (F.map (f.f n)) := fun n =>
        ((HomologicalComplex.eval W₂ c n).mapIso
          (asIso ((F.mapHomologicalComplex c).map f))).isIso_hom
    have := fun n => isIso_of_reflects_iso (f.f n) F
    exact HomologicalComplex.Hom.isIso_of_components f⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) [F.Faithful] :
    (F.mapHomologicalComplex c).Faithful where
  map_injective {K L} f₁ f₂ h := by
    ext
    exact F.map_injective ((HomologicalComplex.eval W c _).congr_map h)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) [F.Faithful] [F.Full] :
    (F.mapHomologicalComplex c).Full where
  map_surjective {X Y} f := ⟨
    { f n := F.preimage (f.f n)
      comm' i j _ := by
        apply F.map_injective
        simp only [Functor.map_comp, Functor.map_preimage]
        exact f.comm i j }, by cat_disch⟩

variable {W₁}

set_option backward.defeqAttrib.useBackward true in
/-- A natural transformation between functors induces a natural transformation
between those functors applied to homological complexes.
-/
@[simps]
/-
**CategoryTheory.NatTrans.mapHomologicalComplex** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.NatTrans`。
形式化陈述：{ι : Type u_1} →   {W₁ : Type u_3} →     {W₂ : Type u_4} →       [inst : C
ategoryTheory.Category.{v_2, u_3} W₁] →         [inst_1 : CategoryTheory.Categor
y.{v_3, u_4} W₂] →           [inst_2 : CategoryTheory.Limits.HasZeroMorphisms W₁
] →             [inst_3 : CategoryTheory.Limits.HasZeroMorphisms W₂] →          
     {F G : CategoryTheory.Functor W₁ W₂} →                 [inst_4 : F.Preserve
sZeroMorphisms] →                   [inst_5 : G.PreservesZeroMorphisms] →       
              (F ⟶ G) → (c : ComplexShape ι) → F.mapHomologicalComplex c ⟶ G.map
HomologicalComplex c
参数：F ⟶ G；c : ComplexShape ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation between functors induces a natural transformation
between those functors applied to homological complexes.
-/
def NatTrans.mapHomologicalComplex {F G : W₁ ⥤ W₂}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (α : F ⟶ G)
    (c : ComplexShape ι) : F.mapHomologicalComplex c ⟶ G.mapHomologicalComplex c where
  app C := { f := fun _ => α.app _ }

@[simp]
/-
**CategoryTheory.NatTrans.mapHomologicalComplex_id** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.NatTrans`。
形式化陈述：∀ {ι : Type u_1} {W₁ : Type u_3} {W₂ : Type u_4} [inst : CategoryTheory.Ca
tegory.{v_2, u_3} W₁]   [inst_1 : CategoryTheory.Category.{v_3, u_4} W₂] [inst_2
 : CategoryTheory.Limits.HasZeroMorphisms W₁]   [inst_3 : CategoryTheory.Limits.
HasZeroMorphisms W₂] (c : ComplexShape ι) (F : CategoryTheory.Functor W₁ W₂)   [
inst_4 : F.PreservesZeroMorphisms],   CategoryTheory.NatTrans.mapHomologicalComp
lex (CategoryTheory.CategoryStruct.id F) c =     CategoryTheory.CategoryStruct.i
d (F.mapHomologicalComplex c)
参数：c : ComplexShape ι；F : CategoryTheory.Functor W₁ W₂；CategoryTheory.CategorySt
ruct.id F；F.mapHomologicalComplex c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NatTrans.mapHomologicalComplex_id
    (c : ComplexShape ι) (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] :
    NatTrans.mapHomologicalComplex (𝟙 F) c = 𝟙 (F.mapHomologicalComplex c) := by cat_disch

@[simp]
/-
**CategoryTheory.NatTrans.mapHomologicalComplex_comp** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.NatTrans`。
形式化陈述：∀ {ι : Type u_1} {W₁ : Type u_3} {W₂ : Type u_4} [inst : CategoryTheory.Ca
tegory.{v_2, u_3} W₁]   [inst_1 : CategoryTheory.Category.{v_3, u_4} W₂] [inst_2
 : CategoryTheory.Limits.HasZeroMorphisms W₁]   [inst_3 : CategoryTheory.Limits.
HasZeroMorphisms W₂] (c : ComplexShape ι) {F G H : CategoryTheory.Functor W₁ W₂}
   [inst_4 : F.PreservesZeroMorphisms] [inst_5 : G.PreservesZeroMorphisms] [inst
_6 : H.PreservesZeroMorphisms]   (α : F ⟶ G) (β : G ⟶ H),   CategoryTheory.NatTr
ans.mapHomologicalComplex (CategoryTheory.CategoryStruct.comp α β) c =     Categ
oryTheory.CategoryStruct.comp (CategoryTheory.NatTrans.mapHomologicalComplex α c
)       (CategoryTheory.NatTrans.mapHomologicalComplex β c)
参数：c : ComplexShape ι；α : F ⟶ G；β : G ⟶ H；CategoryTheory.CategoryStruct.comp α β
；CategoryTheory.NatTrans.mapHomologicalComplex α c；CategoryTheory.NatTrans.mapHo
mologicalComplex β c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NatTrans.mapHomologicalComplex_comp (c : ComplexShape ι) {F G H : W₁ ⥤ W₂}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.mapHomologicalComplex (α ≫ β) c =
      NatTrans.mapHomologicalComplex α c ≫ NatTrans.mapHomologicalComplex β c := by
  cat_disch

@[reassoc]
/-
**CategoryTheory.NatTrans.mapHomologicalComplex_naturality** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.NatTrans`。
形式化陈述：∀ {ι : Type u_1} {W₁ : Type u_3} {W₂ : Type u_4} [inst : CategoryTheory.Ca
tegory.{v_2, u_3} W₁]   [inst_1 : CategoryTheory.Category.{v_3, u_4} W₂] [inst_2
 : CategoryTheory.Limits.HasZeroMorphisms W₁]   [inst_3 : CategoryTheory.Limits.
HasZeroMorphisms W₂] {c : ComplexShape ι} {F G : CategoryTheory.Functor W₁ W₂}  
 [inst_4 : F.PreservesZeroMorphisms] [inst_5 : G.PreservesZeroMorphisms] (α : F 
⟶ G) {C D : HomologicalComplex W₁ c}   (f : C ⟶ D),   CategoryTheory.CategoryStr
uct.comp ((F.mapHomologicalComplex c).map f)       ((CategoryTheory.NatTrans.map
HomologicalComplex α c).app D) =     CategoryTheory.CategoryStruct.comp ((Catego
ryTheory.NatTrans.mapHomologicalComplex α c).app C)       ((G.mapHomologicalComp
lex c).map f)
参数：α : F ⟶ G；f : C ⟶ D；(F.mapHomologicalComplex c).map f；(CategoryTheory.NatTran
s.mapHomologicalComplex α c).app D；(CategoryTheory.NatTrans.mapHomologicalComple
x α c).app C；(G.mapHomologicalComplex c).map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem NatTrans.mapHomologicalComplex_naturality {c : ComplexShape ι} {F G : W₁ ⥤ W₂}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (α : F ⟶ G) {C D : HomologicalComplex W₁ c} (f : C ⟶ D) :
    (F.mapHomologicalComplex c).map f ≫ (NatTrans.mapHomologicalComplex α c).app D =
      (NatTrans.mapHomologicalComplex α c).app C ≫ (G.mapHomologicalComplex c).map f := by
  simp

/-- A natural isomorphism between functors induces a natural isomorphism
between those functors applied to homological complexes.
-/
@[simps!]
/-
**CategoryTheory.NatIso.mapHomologicalComplex** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.NatIso`。
形式化陈述：{ι : Type u_1} →   {W₁ : Type u_3} →     {W₂ : Type u_4} →       [inst : C
ategoryTheory.Category.{v_2, u_3} W₁] →         [inst_1 : CategoryTheory.Categor
y.{v_3, u_4} W₂] →           [inst_2 : CategoryTheory.Limits.HasZeroMorphisms W₁
] →             [inst_3 : CategoryTheory.Limits.HasZeroMorphisms W₂] →          
     {F G : CategoryTheory.Functor W₁ W₂} →                 [inst_4 : F.Preserve
sZeroMorphisms] →                   [inst_5 : G.PreservesZeroMorphisms] →       
              (F ≅ G) → (c : ComplexShape ι) → F.mapHomologicalComplex c ≅ G.map
HomologicalComplex c
参数：F ≅ G；c : ComplexShape ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism between functors induces a natural isomorphism
between those functors applied to homological complexes.
-/
def NatIso.mapHomologicalComplex {F G : W₁ ⥤ W₂} [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (α : F ≅ G) (c : ComplexShape ι) :
    F.mapHomologicalComplex c ≅ G.mapHomologicalComplex c where
  hom := NatTrans.mapHomologicalComplex α.hom c
  inv := NatTrans.mapHomologicalComplex α.inv c
  hom_inv_id := by simp only [← NatTrans.mapHomologicalComplex_comp, α.hom_inv_id,
    NatTrans.mapHomologicalComplex_id]
  inv_hom_id := by simp only [← NatTrans.mapHomologicalComplex_comp, α.inv_hom_id,
    NatTrans.mapHomologicalComplex_id]

/-- If additive functors are related by an isomorphism `F ⋙ G ≅ H`, this is
the corresponding isomorphism for the induced functors on categories
of homological complexes. -/
@[simps!]
/-
**CategoryTheory.Functor.mapHomologicalComplexCompIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：{ι : Type u_1} →   {V : Type u} →     [inst : CategoryTheory.Category.{v, 
u} V] →       [inst_1 : CategoryTheory.Preadditive V] →         {W : Type u_2} →
           [inst_2 : CategoryTheory.Category.{v_1, u_2} W] →             [inst_3
 : CategoryTheory.Preadditive W] →               {W' : Type u_5} →              
   [inst_4 : CategoryTheory.Category.{u_6, u_5} W'] →                   [inst_5 
: CategoryTheory.Preadditive W'] →                     {F : CategoryTheory.Funct
or V W} →                       {G : CategoryTheory.Functor W W'} →             
            {H : CategoryTheory.Functor V W'} →                           (F.com
p G ≅ H) →                             [inst_6 : F.Additive] →                  
             [inst_7 : G.Additive] →                                 [inst_8 : H
.Additive] →                                   (c : ComplexShape ι) →           
                          (F.mapHomologicalComplex c).comp (G.mapHomologicalComp
lex c) ≅                                       H.mapHomologicalComplex c
参数：F.comp G ≅ H；c : ComplexShape ι；F.mapHomologicalComplex c；G.mapHomologicalCom
plex c。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
If additive functors are related by an isomorphism `F ⋙ G ≅ H`, this is
the corresponding isomorphism for the induced functors on categories
of homological complexes.
-/
def Functor.mapHomologicalComplexCompIso {W' : Type*} [Category W'] [Preadditive W']
    {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅ H.mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex e c

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories induces an equivalences between the respective categories
of homological complex.
-/
@[simps]
/-
**CategoryTheory.Equivalence.mapHomologicalComplex** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Equivalence`。
形式化陈述：{ι : Type u_1} →   {W₁ : Type u_3} →     {W₂ : Type u_4} →       [inst : C
ategoryTheory.Category.{v_2, u_3} W₁] →         [inst_1 : CategoryTheory.Categor
y.{v_3, u_4} W₂] →           [inst_2 : CategoryTheory.Limits.HasZeroMorphisms W₁
] →             [inst_3 : CategoryTheory.Limits.HasZeroMorphisms W₂] →          
     (e : W₁ ≌ W₂) →                 [e.functor.PreservesZeroMorphisms] →       
            (c : ComplexShape ι) → HomologicalComplex W₁ c ≌ HomologicalComplex 
W₂ c
参数：e : W₁ ≌ W₂；c : ComplexShape ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of categories induces an equivalences between the respective cate
gories
of homological complex.
-/
def Equivalence.mapHomologicalComplex (e : W₁ ≌ W₂) [e.functor.PreservesZeroMorphisms]
    (c : ComplexShape ι) :
    HomologicalComplex W₁ c ≌ HomologicalComplex W₂ c where
  functor := e.functor.mapHomologicalComplex c
  inverse := e.inverse.mapHomologicalComplex c
  unitIso :=
    (Functor.mapHomologicalComplexIdIso W₁ c).symm ≪≫ NatIso.mapHomologicalComplex e.unitIso c
  counitIso := NatIso.mapHomologicalComplex e.counitIso c ≪≫
  Functor.mapHomologicalComplexIdIso W₂ c

end CategoryTheory

namespace ChainComplex

variable {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**ChainComplex.map_chain_complex_of** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：map_chain_complex_of (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (X : α -> W₁
) (d : forall n, X (n + 1) ⟶ X n) (sq : forall n, d (n + 1) ≫ d n = 0) : (F.mapH
omologicalComplex _).obj (ChainComplex.of X d sq) = ChainComplex.of (fun n => F.
obj (X n)) (fun n => F.map (d n)) fun n => by rw [← F.map_comp]; rw [sq n]; rw [
Functor.map_zero]
参数：F : W₁ ⥤ W₂；X : α -> W₁；d : forall n, X (n + 1) ⟶ X n；sq : forall n, d (n + 1
) ≫ d n = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.ext`：ext {C₁ C₂ : HomologicalComplex V c} (h_X : C₁.X
 = C₂.X) (h_d : forall i j : ι, c.Rel i j -> C₁.d i j ≫ eqToHom (congr_fun h_X j
) = eqToHom …
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ChainComplex.of_d`：of_d (j : α) : of.d X d (j + 1) j = d j
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_chain_complex_of (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (X : α → W₁)
    (d : ∀ n, X (n + 1) ⟶ X n) (sq : ∀ n, d (n + 1) ≫ d n = 0) :
    (F.mapHomologicalComplex _).obj (ChainComplex.of X d sq) =
      ChainComplex.of (fun n => F.obj (X n)) (fun n => F.map (d n)) fun n => by
        rw [← F.map_comp, sq n, Functor.map_zero] := by
  refine HomologicalComplex.ext rfl ?_
  rintro i j (rfl : j + 1 = i)
  simp

end ChainComplex

variable [HasZeroObject W₁] [HasZeroObject W₂]

namespace HomologicalComplex

set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (W : Type*) [Category* W] [Preadditive W] [HasZeroObject W] [DecidableEq ι] (j : ι) :
    (single W c j).Additive where
  map_add {_ _ f g} := by ext; simp [single]

variable (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms]
    (c : ComplexShape ι) [DecidableEq ι]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Turning an object into a complex supported at `j` then applying a functor is
the same as applying the functor then forming the complex.
-/
/-
**HomologicalComplex.singleMapHomologicalComplex** 是 Mathlib 中的一个定义，位于命名空间 `Homo
logicalComplex`。
形式化陈述：singleMapHomologicalComplex (j : ι) : single W₁ c j ⋙ F.mapHomologicalComp
lex _ ≅ F ⋙ single W₂ c j
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turning an object into a complex supported at `j` then applying a functor is
the same as applying the functor then forming the complex.
-/
noncomputable def singleMapHomologicalComplex (j : ι) :
    single W₁ c j ⋙ F.mapHomologicalComplex _ ≅ F ⋙ single W₂ c j :=
  NatIso.ofComponents
    (fun X =>
      { hom := { f := fun i => if h : i = j then eqToHom (by simp [h]) else 0 }
        inv := { f := fun i => if h : i = j then eqToHom (by simp [h]) else 0 }
        hom_inv_id := by
          ext i
          dsimp
          split_ifs with h
          · simp
          · rw [zero_comp, ← F.map_id,
              (isZero_single_obj_X c j X _ h).eq_of_src (𝟙 _) 0, F.map_zero]
        inv_hom_id := by
          ext i
          dsimp
          split_ifs with h
          · simp
          · apply (isZero_single_obj_X c j _ _ h).eq_of_src })
    fun f => by
      ext i
      dsimp
      split_ifs with h
      · subst h
        simp [single_map_f_self, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]
      · apply (isZero_single_obj_X c j _ _ h).eq_of_tgt

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**HomologicalComplex.singleMapHomologicalComplex_hom_app_self** 是 Mathlib 中的一个定理
，位于命名空间 `HomologicalComplex`。
形式化陈述：singleMapHomologicalComplex_hom_app_self (j : ι) (X : W₁) : ((singleMapHom
ologicalComplex F c j).hom.app X).f j = F.map (singleObjXSelf c j X).hom ≫ (sing
leObjXSelf c j (F.obj X)).inv
参数：j : ι；X : W₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
-/
theorem singleMapHomologicalComplex_hom_app_self (j : ι) (X : W₁) :
    ((singleMapHomologicalComplex F c j).hom.app X).f j =
      F.map (singleObjXSelf c j X).hom ≫ (singleObjXSelf c j (F.obj X)).inv := by
  simp [singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]

@[simp]
/-
**HomologicalComplex.singleMapHomologicalComplex_hom_app_ne** 是 Mathlib 中的一个定理，位
于命名空间 `HomologicalComplex`。
形式化陈述：singleMapHomologicalComplex_hom_app_ne {i j : ι} (h : i != j) (X : W₁) : (
(singleMapHomologicalComplex F c j).hom.app X).f i = 0
参数：h : i != j；X : W₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `HomologicalComplex.Hom.mk.congr_simp`：∀ {ι : Type u_1} {V : Type u} [ins
t : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms V] {c : ComplexSh…
· 使用定理 `CategoryTheory.Iso.mk.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (hom hom_1 : X ⟶ Y) (e_hom : hom = hom_1)   (inv in
v_1 : Y ⟶ X) (e_inv : …
· 使用定理 `CategoryTheory.NatIso.ofComponents.congr_simp`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleMapHomologicalComplex_hom_app_ne {i j : ι} (h : i ≠ j) (X : W₁) :
    ((singleMapHomologicalComplex F c j).hom.app X).f i = 0 := by
  simp [singleMapHomologicalComplex, h]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**HomologicalComplex.singleMapHomologicalComplex_inv_app_self** 是 Mathlib 中的一个定理
，位于命名空间 `HomologicalComplex`。
形式化陈述：singleMapHomologicalComplex_inv_app_self (j : ι) (X : W₁) : ((singleMapHom
ologicalComplex F c j).inv.app X).f j = (singleObjXSelf c j (F.obj X)).hom ≫ F.m
ap (singleObjXSelf c j X).inv
参数：j : ι；X : W₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
-/
theorem singleMapHomologicalComplex_inv_app_self (j : ι) (X : W₁) :
    ((singleMapHomologicalComplex F c j).inv.app X).f j =
      (singleObjXSelf c j (F.obj X)).hom ≫ F.map (singleObjXSelf c j X).inv := by
  simp [singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]

@[simp]
/-
**HomologicalComplex.singleMapHomologicalComplex_inv_app_ne** 是 Mathlib 中的一个定理，位
于命名空间 `HomologicalComplex`。
形式化陈述：singleMapHomologicalComplex_inv_app_ne {i j : ι} (h : i != j) (X : W₁) : (
(singleMapHomologicalComplex F c j).inv.app X).f i = 0
参数：h : i != j；X : W₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `HomologicalComplex.Hom.mk.congr_simp`：∀ {ι : Type u_1} {V : Type u} [ins
t : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms V] {c : ComplexSh…
· 使用定理 `CategoryTheory.Iso.mk.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (hom hom_1 : X ⟶ Y) (e_hom : hom = hom_1)   (inv in
v_1 : Y ⟶ X) (e_inv : …
· 使用定理 `CategoryTheory.NatIso.ofComponents.congr_simp`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleMapHomologicalComplex_inv_app_ne {i j : ι} (h : i ≠ j) (X : W₁) :
    ((singleMapHomologicalComplex F c j).inv.app X).f i = 0 := by
  simp [singleMapHomologicalComplex, h]

end HomologicalComplex

