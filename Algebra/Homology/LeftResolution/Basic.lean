/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Left resolutions

Given a fully faithful functor `ι : C ⥤ A` to an abelian category,
we introduce a structure `Abelian.LeftResolution ι` which gives
a functor `F : A ⥤ C` and a natural epimorphism
`π.app X : ι.obj (F.obj X) ⟶ X` for all `X : A`.
This is used in order to construct a resolution functor
`LeftResolution.chainComplexFunctor : A ⥤ ChainComplex C ℕ`.

This shall be used in order to construct functorial flat resolutions.

-/

@[expose] public section

namespace CategoryTheory.Abelian

open Category Limits Preadditive ZeroObject

variable {A C : Type*} [Category* C] [Category* A] (ι : C ⥤ A)

/-- Given a fully faithful functor `ι : C ⥤ A`, this structure contains the data
of a functor `F : A ⥤ C` and a functorial epimorphism
`π.app X : ι.obj (F.obj X) ⟶ X` for all `X : A`. -/
/-
**CategoryTheory.Abelian.LeftResolution** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheor
y.Abelian`。
形式化陈述：LeftResolution where /-- a functor which sends `X : A` to an object `F.obj
 X` with an epimorphism `π.app X : ι.obj (F.obj X) ⟶ X` -/ F : A ⥤ C /-- the nat
ural epimorphism -/ π : F ⋙ ι ⟶ 𝟭 A epi_π_app (X : A) : Epi (π.app X)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a fully faithful functor `ι : C ⥤ A`, this structure contains the data
of a functor `F : A ⥤ C` and a functorial epimorphism
`π.app X : ι.obj (F.obj X) ⟶ X` for all `X : A`.
-/
structure LeftResolution where
  /-- a functor which sends `X : A` to an object `F.obj X` with an epimorphism
    `π.app X : ι.obj (F.obj X) ⟶ X` -/
  F : A ⥤ C
  /-- the natural epimorphism -/
  π : F ⋙ ι ⟶ 𝟭 A
  epi_π_app (X : A) : Epi (π.app X) := by infer_instance

namespace LeftResolution

attribute [instance] epi_π_app

variable {ι} (Λ : LeftResolution ι) (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.LeftResolution.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.LeftResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_naturality : ι.map (Λ.F.map f) ≫ Λ.π.app Y = Λ.π.app X ≫ f :=
  Λ.π.naturality f

variable [ι.Full] [ι.Faithful] [HasZeroMorphisms C] [Abelian A]

/-- Given `ι : C ⥤ A`, `Λ : LeftResolution ι`, `X : A`, this is a chain complex
which is a (functorial) resolution of `A` that is obtained inductively by using
the epimorphisms given by `Λ`. -/
/-
**CategoryTheory.Abelian.LeftResolution.chainComplex** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Abelian.LeftResolution`。
形式化陈述：chainComplex : ChainComplex C Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `ι : C ⥤ A`, `Λ : LeftResolution ι`, `X : A`, this is a chain complex
which is a (functorial) resolution of `A` that is obtained inductively by using
the epimorphisms given by `Λ`.
-/
noncomputable def chainComplex : ChainComplex C ℕ :=
  ChainComplex.mk' _ _ (ι.preimage (Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _))
    (fun f => ⟨_, ι.preimage (Λ.π.app (kernel (ι.map f)) ≫ kernel.ι _),
      ι.map_injective (by simp)⟩)

/-- Given `Λ : LeftResolution ι`, the chain complex `Λ.chainComplex X`
identifies in degree `0` to `Λ.F.obj X`. -/
/-
**CategoryTheory.Abelian.LeftResolution.chainComplexXZeroIso** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Abelian.LeftResolution`。
形式化陈述：chainComplexXZeroIso : (Λ.chainComplex X).X 0 ≅ Λ.F.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Λ : LeftResolution ι`, the chain complex `Λ.chainComplex X`
identifies in degree `0` to `Λ.F.obj X`.
-/
noncomputable def chainComplexXZeroIso :
    (Λ.chainComplex X).X 0 ≅ Λ.F.obj X := Iso.refl _

/-- Given `Λ : LeftResolution ι`, the chain complex `Λ.chainComplex X`
identifies in degree `1` to `Λ.F.obj (kernel (Λ.π.app X))`. -/
/-
**CategoryTheory.Abelian.LeftResolution.chainComplexXOneIso** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Abelian.LeftResolution`。
形式化陈述：chainComplexXOneIso : (Λ.chainComplex X).X 1 ≅ Λ.F.obj (kernel (Λ.π.app X)
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Λ : LeftResolution ι`, the chain complex `Λ.chainComplex X`
identifies in degree `1` to `Λ.F.obj (kernel (Λ.π.app X))`.
-/
noncomputable def chainComplexXOneIso :
    (Λ.chainComplex X).X 1 ≅ Λ.F.obj (kernel (Λ.π.app X)) := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Abelian.LeftResolution.map_chainComplex_d_1_0** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Abelian.LeftResolution`。
形式化陈述：map_chainComplex_d_1_0 : ι.map ((Λ.chainComplex X).d 1 0) = ι.map (Λ.chain
ComplexXOneIso X).hom ≫ Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _ ≫ ι.map (Λ.cha
inComplexXZeroIso X).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ChainComplex.mk'_d_1_0`：∀ {V : Type u} [inst : CategoryTheory.Category.{
v, u} V] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] (X₀ X₁ : V)   (d₀ :
 X₁ ⟶ X₀)   …
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_chainComplex_d_1_0 :
    ι.map ((Λ.chainComplex X).d 1 0) =
      ι.map (Λ.chainComplexXOneIso X).hom ≫ Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _ ≫
      ι.map (Λ.chainComplexXZeroIso X).inv := by
  simp [chainComplexXOneIso, chainComplexXZeroIso, chainComplex]

/-- The isomorphism which gives the inductive step of the construction of `Λ.chainComplex X`. -/
/-
**CategoryTheory.Abelian.LeftResolution.chainComplexXIso** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Abelian.LeftResolution`。
形式化陈述：chainComplexXIso (n : Nat) : (Λ.chainComplex X).X (n + 2) ≅ Λ.F.obj (kerne
l (ι.map ((Λ.chainComplex X).d (n + 1) n)))
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism which gives the inductive step of the construction of `Λ.chainCo
mplex X`.
-/
noncomputable def chainComplexXIso (n : ℕ) :
    (Λ.chainComplex X).X (n + 2) ≅ Λ.F.obj (kernel (ι.map ((Λ.chainComplex X).d (n + 1) n))) := by
  apply ChainComplex.mk'XIso
/-
**CategoryTheory.Abelian.LeftResolution.map_chainComplex_d** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Abelian.LeftResolution`。
形式化陈述：map_chainComplex_d (n : Nat) : ι.map ((Λ.chainComplex X).d (n + 2) (n + 1)
) = ι.map (Λ.chainComplexXIso X n).hom ≫ Λ.π.app (kernel (ι.map ((Λ.chainComplex
 X).d (n + 1) n))) ≫ kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n))
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `ChainComplex.mk'_d`：∀ {V : Type u} [inst : CategoryTheory.Category.{v, u
} V] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] (X₀ X₁ : V)   (d₀ : X₁ 
⟶ X₀)   …
-/
lemma map_chainComplex_d (n : ℕ) :
    ι.map ((Λ.chainComplex X).d (n + 2) (n + 1)) =
    ι.map (Λ.chainComplexXIso X n).hom ≫ Λ.π.app (kernel (ι.map ((Λ.chainComplex X).d (n + 1) n))) ≫
      kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n)) := by
  have := ι.map_preimage (Λ.π.app _ ≫ kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n)))
  dsimp at this
  rw [← this, ← Functor.map_comp]
  congr 1
  apply ChainComplex.mk'_d

attribute [irreducible] chainComplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.LeftResolution.exactAt_map_chainComplex_succ** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Abelian.LeftResolution`。
形式化陈述：exactAt_map_chainComplex_succ (n : Nat) : ((ι.mapHomologicalComplex _).obj
 (Λ.chainComplex X)).ExactAt (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_full`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.exactAt_iff'`：exactAt_iff' (hi : c.prev j = i) (hk : 
c.next j = k) : K.ExactAt j ↔ (K.sc' i j k).Exact
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ChainComplex.next_nat_succ`：next_nat_succ (i : Nat) : (ComplexShape.down
 Nat).next (i + 1) = i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_epi_kernel_lift`：exact_iff_epi_ker
nel_lift [S.HasHomology] [HasKernel S.g] : S.Exact ↔ Epi (kernel.lift S.g S.f S.
zero)
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Abelian.LeftResolution.map_chainComplex_d`：map_chainCompl
ex_d (n : Nat) : ι.map ((Λ.chainComplex X).d (n + 2) (n + 1)) = ι.map (Λ.chainCo
mplexXIso X n).hom ≫ Λ.π.app (kernel (ι.map ((…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Abelian.LeftResolution.epi_π_app`：∀ {A : Type u_1} {C : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_2} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_1} A] {ι : Categor…
-/
lemma exactAt_map_chainComplex_succ (n : ℕ) :
    ((ι.mapHomologicalComplex _).obj (Λ.chainComplex X)).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n
    (ComplexShape.prev_eq' _ (by dsimp; lia)) (by simp),
    ShortComplex.exact_iff_epi_kernel_lift]
  convert! epi_comp (ι.map (Λ.chainComplexXIso X n).hom) (Λ.π.app _)
  rw [← cancel_mono (kernel.ι _), kernel.lift_ι]
  simp [map_chainComplex_d]

variable {X Y Z}

set_option backward.defeqAttrib.useBackward true in
/-- The morphism `Λ.chainComplex X ⟶ Λ.chainComplex Y` of chain complexes
induced by `f : X ⟶ Y`. -/
/-
**CategoryTheory.Abelian.LeftResolution.chainComplexMap** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Abelian.LeftResolution`。
形式化陈述：chainComplexMap : Λ.chainComplex X ⟶ Λ.chainComplex Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `Λ.chainComplex X ⟶ Λ.chainComplex Y` of chain complexes
induced by `f : X ⟶ Y`.
-/
noncomputable def chainComplexMap : Λ.chainComplex X ⟶ Λ.chainComplex Y :=
  ChainComplex.mkHom _ _
    ((Λ.chainComplexXZeroIso X).hom ≫ Λ.F.map f ≫ (Λ.chainComplexXZeroIso Y).inv)
    ((Λ.chainComplexXOneIso X).hom ≫
      Λ.F.map (kernel.map _ _ (ι.map (Λ.F.map f)) f (Λ.π.naturality f).symm) ≫
      (Λ.chainComplexXOneIso Y).inv)
    (ι.map_injective (by
        dsimp
        simp only [Category.assoc, Functor.map_comp, map_chainComplex_d_1_0]
        simp only [← ι.map_comp, ← ι.map_comp_assoc]
        simp))
    (fun n p ↦
      ⟨(Λ.chainComplexXIso X n).hom ≫ (Λ.F.map
        (kernel.map _ _ (ι.map p.2.1) (ι.map p.1) (by
          rw [← ι.map_comp, ← ι.map_comp, p.2.2]))) ≫ (Λ.chainComplexXIso Y n).inv,
            ι.map_injective (by simp [map_chainComplex_d])⟩)

@[simp]
/-
**CategoryTheory.Abelian.LeftResolution.chainComplexMap_f_0** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Abelian.LeftResolution`。
形式化陈述：chainComplexMap_f_0 : (Λ.chainComplexMap f).f 0 = ((Λ.chainComplexXZeroIso
 X).hom ≫ Λ.F.map f ≫ (Λ.chainComplexXZeroIso Y).inv)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma chainComplexMap_f_0 :
    (Λ.chainComplexMap f).f 0 =
      ((Λ.chainComplexXZeroIso X).hom ≫ Λ.F.map f ≫ (Λ.chainComplexXZeroIso Y).inv) := rfl

@[simp]
/-
**CategoryTheory.Abelian.LeftResolution.chainComplexMap_f_1** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Abelian.LeftResolution`。
形式化陈述：chainComplexMap_f_1 : (Λ.chainComplexMap f).f 1 = (Λ.chainComplexXOneIso X
).hom ≫ Λ.F.map (kernel.map _ _ (ι.map (Λ.F.map f)) f (Λ.π.naturality f).symm) ≫
 (Λ.chainComplexXOneIso Y).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma chainComplexMap_f_1 :
    (Λ.chainComplexMap f).f 1 =
    (Λ.chainComplexXOneIso X).hom ≫
      Λ.F.map (kernel.map _ _ (ι.map (Λ.F.map f)) f (Λ.π.naturality f).symm) ≫
      (Λ.chainComplexXOneIso Y).inv := rfl

@[simp]
/-
**CategoryTheory.Abelian.LeftResolution.chainComplexMap_f_succ_succ** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Abelian.LeftResolution`。
形式化陈述：chainComplexMap_f_succ_succ (n : Nat) : (Λ.chainComplexMap f).f (n + 2) = 
(Λ.chainComplexXIso X n).hom ≫ Λ.F.map (kernel.map _ _ (ι.map ((Λ.chainComplexMa
p f).f (n + 1))) (ι.map ((Λ.chainComplexMap f).f n)) (by rw [← ι.map_comp, ← ι.m
ap_comp, HomologicalComplex.Hom.comm])) ≫ (Λ.chainComplexXIso Y n).inv
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ChainComplex.mkHom_f_succ_succ`：mkHom_f_succ_succ (n : Nat) : (mkHom P Q
 zero one one_zero_comm succ).f (n + 2) = (succ n ⟨(mkHom P Q zero one one_zero_
comm succ).f n, (mkH…
-/
lemma chainComplexMap_f_succ_succ (n : ℕ) :
    (Λ.chainComplexMap f).f (n + 2) =
      (Λ.chainComplexXIso X n).hom ≫
        Λ.F.map (kernel.map _ _ (ι.map ((Λ.chainComplexMap f).f (n + 1)))
          (ι.map ((Λ.chainComplexMap f).f n))
          (by rw [← ι.map_comp, ← ι.map_comp, HomologicalComplex.Hom.comm])) ≫
          (Λ.chainComplexXIso Y n).inv := by
  apply ChainComplex.mkHom_f_succ_succ

set_option backward.defeqAttrib.useBackward true in
variable (X) in
@[simp]
/-
**CategoryTheory.Abelian.LeftResolution.chainComplexMap_id** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Abelian.LeftResolution`。
形式化陈述：chainComplexMap_id : Λ.chainComplexMap (𝟙 X) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.kernel.map.congr_simp`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
] {X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.kernel.map_id`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用引理 `CategoryTheory.Abelian.LeftResolution.chainComplexMap_f_succ_succ`：chain
ComplexMap_f_succ_succ (n : Nat) : (Λ.chainComplexMap f).f (n + 2) = (Λ.chainCom
plexXIso X n).hom ≫ Λ.F.map (kernel.map _ _ (ι.map ((Λ.…
-/
lemma chainComplexMap_id : Λ.chainComplexMap (𝟙 X) = 𝟙 _ := by
  ext n
  induction n with
  | zero => simp
  | succ n hn => obtain _ | n := n <;> simp [hn]

set_option backward.defeqAttrib.useBackward true in
variable (X Y) in
@[simp]
/-
**CategoryTheory.Abelian.LeftResolution.chainComplexMap_zero** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Abelian.LeftResolution`。
形式化陈述：chainComplexMap_zero [Λ.F.PreservesZeroMorphisms] : Λ.chainComplexMap (0 :
 X ⟶ Y) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_full`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Limits.kernel.map.congr_simp`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
] {X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.kernel.map_zero`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {X
 Y X' Y' : C} (f : X ⟶ Y) (…
· 使用引理 `CategoryTheory.Abelian.LeftResolution.chainComplexMap_f_succ_succ`：chain
ComplexMap_f_succ_succ (n : Nat) : (Λ.chainComplexMap f).f (n + 2) = (Λ.chainCom
plexXIso X n).hom ≫ Λ.F.map (kernel.map _ _ (ι.map ((Λ.…
-/
lemma chainComplexMap_zero [Λ.F.PreservesZeroMorphisms] :
    Λ.chainComplexMap (0 : X ⟶ Y) = 0 := by
  ext n
  induction n with
  | zero => simp
  | succ n hn => obtain _ | n := n <;> simp [hn]

set_option backward.defeqAttrib.useBackward true in
@[reassoc, simp]
/-
**CategoryTheory.Abelian.LeftResolution.chainComplexMap_comp** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Abelian.LeftResolution`。
形式化陈述：chainComplexMap_comp : Λ.chainComplexMap (f ≫ g) = Λ.chainComplexMap f ≫ Λ
.chainComplexMap g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.Limits.kernel.map.congr_simp`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
] {X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
{X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用引理 `CategoryTheory.Abelian.LeftResolution.chainComplexMap_f_succ_succ`：chain
ComplexMap_f_succ_succ (n : Nat) : (Λ.chainComplexMap f).f (n + 2) = (Λ.chainCom
plexXIso X n).hom ≫ Λ.F.map (kernel.map _ _ (ι.map ((Λ.…
-/
lemma chainComplexMap_comp :
    Λ.chainComplexMap (f ≫ g) = Λ.chainComplexMap f ≫ Λ.chainComplexMap g := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
    obtain _ | n := n
    all_goals
      dsimp
      simp only [chainComplexMap_f_succ_succ, assoc, Iso.cancel_iso_hom_left,
        Iso.inv_hom_id_assoc, ← Λ.F.map_comp_assoc, Iso.cancel_iso_inv_right_assoc]
      congr 1
      cat_disch

/-- Given `ι : C ⥤ A`, `Λ : LeftResolution ι`, this is a
functor `A ⥤ ChainComplex C ℕ` which sends `X : A` to a resolution consisting
of objects in `C`. -/
/-
**CategoryTheory.Abelian.LeftResolution.chainComplexFunctor** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Abelian.LeftResolution`。
形式化陈述：chainComplexFunctor : A ⥤ ChainComplex C Nat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `ι : C ⥤ A`, `Λ : LeftResolution ι`, this is a
functor `A ⥤ ChainComplex C ℕ` which sends `X : A` to a resolution consisting
of objects in `C`.
-/
noncomputable def chainComplexFunctor : A ⥤ ChainComplex C ℕ where
  obj X := Λ.chainComplex X
  map f := Λ.chainComplexMap f

end LeftResolution

end CategoryTheory.Abelian

