/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jujian Zhang
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Exact functors

In this file, it is shown that additive functors which preserves homology
also preserves finite limits and finite colimits.

## Main results

Let `F : C ⥤ D` be an additive functor:

- `Functor.preservesFiniteLimits_of_preservesHomology`: if `F` preserves homology,
  then `F` preserves finite limits.
- `Functor.preservesFiniteColimits_of_preservesHomology`: if `F` preserves homology, then `F`
  preserves finite colimits.

If we further assume that `C` and `D` are abelian categories, then we have:

- `Functor.preservesFiniteLimits_tfae`: the following are equivalent:
  1. for every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`,
     `0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
  2. for every exact sequence `A ⟶ B ⟶ C` where `A ⟶ B` is mono,
     `F(A) ⟶ F(B) ⟶ F(C)` is exact and `F(A) ⟶ F(B)` is mono.
  3. `F` preserves kernels.
  4. `F` preserves finite limits.

- `Functor.preservesFiniteColimits_tfae`: the following are equivalent:
  1. for every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`,
     `F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
  2. for every exact sequence `A ⟶ B ⟶ C` where `B ⟶ C` is epi,
     `F(A) ⟶ F(B) ⟶ F(C)` is exact and `F(B) ⟶ F(C)` is epi.
  3. `F` preserves cokernels.
  4. `F` preserves finite colimits.

- `Functor.exact_tfae`: the following are equivalent:
  1. for every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`,
     `0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
  2. for every exact sequence `A ⟶ B ⟶ C`, `F(A) ⟶ F(B) ⟶ F(C)` is exact.
  3. `F` preserves homology.
  4. `F` preserves both finite limits and finite colimits.

-/

public section

namespace CategoryTheory

open Limits ZeroObject ShortComplex

namespace Functor

section

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] [HasZeroObject C]

/-- An additive functor which preserves homology preserves finite limits. -/
/-
**CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesFiniteLimits_of_preservesHomology [HasFiniteProducts C] [HasKerne
ls C] : PreservesFiniteLimits F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesKernel`：∀ {C : Type u_
1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadd
itive C]   [CategoryTheory.Limits.HasBinaryProducts …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Preadditive.hasEqualizers_of_hasKernels`：hasEqualizers_of
_hasKernels [HasKernels C] : HasEqualizers C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.id_zero`：id_zero : 𝟙 (0 : C) = (0 : (0 : C) ⟶ 0)
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用引理 `CategoryTheory.Functor.preservesFiniteLimits_of_preservesKernels`：preser
vesFiniteLimits_of_preservesKernels [HasFiniteProducts C] [HasEqualizers C] [Has
ZeroObject C] [HasZeroObject D] [forall {X Y} (f : X ⟶…

--- 原说明 ---
An additive functor which preserves homology preserves finite limits.
-/
lemma preservesFiniteLimits_of_preservesHomology
    [HasFiniteProducts C] [HasKernels C] : PreservesFiniteLimits F := by
  have := fun {X Y : C} (f : X ⟶ Y) ↦ PreservesHomology.preservesKernel F f
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
  have : HasZeroObject D :=
    ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩
  exact preservesFiniteLimits_of_preservesKernels F

/-- An additive which preserves homology preserves finite colimits. -/
/-
**CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesFiniteColimits_of_preservesHomology [HasFiniteCoproducts C] [HasC
okernels C] : PreservesFiniteColimits F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesCokernel`：∀ {C : Type 
u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Ca
tegoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryCoproducts`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Prea
dditive C]   [CategoryTheory.Limits.HasBinaryCoproduct…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Preadditive.hasCoequalizers_of_hasCokernels`：hasCoequaliz
ers_of_hasCokernels [HasCokernels C] : HasCoequalizers C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.id_zero`：id_zero : 𝟙 (0 : C) = (0 : (0 : C) ⟶ 0)
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用引理 `CategoryTheory.Functor.preservesFiniteColimits_of_preservesCokernels`：pr
eservesFiniteColimits_of_preservesCokernels [HasFiniteCoproducts C] [HasCoequali
zers C] [HasZeroObject C] [HasZeroObject D] [forall {X Y} …

--- 原说明 ---
An additive which preserves homology preserves finite colimits.
-/
lemma preservesFiniteColimits_of_preservesHomology
    [HasFiniteCoproducts C] [HasCokernels C] : PreservesFiniteColimits F := by
  have := fun {X Y : C} (f : X ⟶ Y) ↦ PreservesHomology.preservesCokernel F f
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts
  have : HasCoequalizers C := Preadditive.hasCoequalizers_of_hasCokernels
  have : HasZeroObject D :=
    ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩
  exact preservesFiniteColimits_of_preservesCokernels F

end

section

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive]

/--
If a functor `F : C ⥤ D` preserves short exact sequences on the left-hand side, (i.e.
if `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is exact then `0 ⟶ F(A) ⟶ F(B) ⟶ F(C)` is exact)
then it preserves monomorphism.
-/
/-
**CategoryTheory.Functor.preservesMonomorphisms_of_preserves_shortExact_left** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesMonomorphisms_of_preserves_shortExact_left (h : forall (S : Short
Complex C), S.ShortExact -> (S.map F).Exact ∧ Mono (F.map S.f)) : F.PreservesMon
omorphisms where .2 preserves f
参数：h : forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact ∧ Mono (F.ma
p S.f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.ShortComplex.exact_cokernel`：exact_cokernel {X Y : C} (f 
: X ⟶ Y) : (ShortComplex.mk f (cokernel.π f) (by simp)).Exact
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…

--- 原说明 ---
If a functor `F : C ⥤ D` preserves short exact sequences on the left-hand side, 
(i.e.
if `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is exact then `0 ⟶ F(A) ⟶ F(B) ⟶ F(C)` is exact)
then it preserves monomorphism.
-/
lemma preservesMonomorphisms_of_preserves_shortExact_left
    (h : ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Mono (F.map S.f)) :
    F.PreservesMonomorphisms where
  preserves f := h _ { exact := exact_cokernel f } |>.2

set_option backward.isDefEq.respectTransparency false in
/--
For an additive functor `F : C ⥤ D` between abelian categories, the following are equivalent:
- `F` preserves short exact sequences on the left-hand side, i.e. if `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is exact
  then `0 ⟶ F(A) ⟶ F(B) ⟶ F(C)` is exact.
- `F` preserves exact sequences on the left-hand side, i.e. if `A ⟶ B ⟶ C` is exact where `A ⟶ B`
  is mono, then `F(A) ⟶ F(B) ⟶ F(C)` is exact and `F(A) ⟶ F(B)` is mono as well.
- `F` preserves kernels.
- `F` preserves finite limits.
-/
/-
**CategoryTheory.Functor.preservesFiniteLimits_tfae** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：preservesFiniteLimits_tfae : List.TFAE [ forall (S : ShortComplex C), S.Sh
ortExact -> (S.map F).Exact ∧ Mono (F.map S.f), forall (S : ShortComplex C), S.E
xact ∧ Mono S.f -> (S.map F).Exact ∧ Mono (F.map S.f), forall ⦃X Y : C⦄ (f : X ⟶
 Y), PreservesLimit (parallelPair f 0) F, PreservesFiniteLimits F ]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Functor.preservesMonomorphisms_of_preserves_shortExact_le
ft`：preservesMonomorphisms_of_preserves_shortExact_left (h : forall (S : ShortCo
mplex C), S.ShortExact -> (S.map F).Exact ∧ Mono (F.map S.f)) : …
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
· 使用定理 `CategoryTheory.Abelian.comp_coimage_π_eq_zero`：comp_coimage_π_eq_zero {R
 : C} {g : Q ⟶ R} (h : f ≫ g = 0) : f ≫ Abelian.coimage.π g = 0
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.map_f`：∀ {C : Type u_1} {D : Type u_2} [inst
 : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono`：exact_iff
_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : S₁.
Exact ↔ S₂.Exact
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Abelian.instMonoFactorThruCoimage`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {P Q : C}
 (f : P ⟶ Q),   CategoryTheory.Mono (C…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_exact_coimage_π`：exact_iff_exact_c
oimage_π : S.Exact ↔ (ShortComplex.mk S.f (Abelian.coimage.π S.g) (Abelian.comp_
coimage_π_eq_zero S.zero)).Exact
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
For an additive functor `F : C ⥤ D` between abelian categories, the following ar
e equivalent:
- `F` preserves short exact sequences on the left-hand side, i.e. if `0 ⟶ A ⟶ B 
⟶ C ⟶ 0` is exact
  then `0 ⟶ F(A) ⟶ F(B) ⟶ F(C)` is exact.
- `F` preserves exact sequences on the left-hand side, i.e. if `A ⟶ B ⟶ C` is ex
act where `A ⟶ B`
  is mono, then `F(A) ⟶ F(B) ⟶ F(C)` is exact and `F(A) ⟶ F(B)` is mono as well.
- `F` preserves kernels.
- `F` preserves finite limits.
-/
lemma preservesFiniteLimits_tfae : List.TFAE
    [
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Mono (F.map S.f),
      ∀ (S : ShortComplex C), S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f),
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F,
      PreservesFiniteLimits F
    ] := by
  tfae_have 1 → 2
  | hF, S, ⟨hS, hf⟩ => by
    have := preservesMonomorphisms_of_preserves_shortExact_left F hF
    refine ⟨?_, inferInstance⟩
    let T := ShortComplex.mk S.f (Abelian.coimage.π S.g) (Abelian.comp_coimage_π_eq_zero S.zero)
    let φ : T.map F ⟶ S.map F :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := F.map <| Abelian.factorThruCoimage S.g
        comm₂₃ := show 𝟙 _ ≫ F.map _ = F.map (cokernel.π _) ≫ _ by
          rw [Category.id_comp, ← F.map_comp, cokernel.π_desc] }
    exact (exact_iff_of_epi_of_isIso_of_mono φ).1 (hF T ⟨(S.exact_iff_exact_coimage_π).1 hS⟩).1
  tfae_have 2 → 3
  | hF, X, Y, f => by
    refine preservesLimit_of_preserves_limit_cone (kernelIsKernel f) ?_
    apply (KernelFork.isLimitMapConeEquiv _ F).2
    let S := ShortComplex.mk _ _ (kernel.condition f)
    let hS := hF S ⟨exact_kernel f, inferInstance⟩
    have : Mono (S.map F).f := hS.2
    exact hS.1.fIsKernel
  tfae_have 3 → 4
  | hF => by
    exact preservesFiniteLimits_of_preservesKernels F
  tfae_have 4 → 1
  | ⟨_⟩, S, hS =>
    (S.map F).exact_and_mono_f_iff_f_is_kernel |>.2 ⟨KernelFork.mapIsLimit _ hS.fIsKernel F⟩
  tfae_finish
/-
**CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesFiniteLimits_iff_forall_exact_map_and_mono : PreservesFiniteLimit
s F ↔ forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact ∧ Mono (F.map
 S.f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Functor.preservesFiniteLimits_tfae`：preservesFiniteLimits
_tfae : List.TFAE [ forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact
 ∧ Mono (F.map S.f), forall (S : ShortC…
-/
lemma preservesFiniteLimits_iff_forall_exact_map_and_mono :
    PreservesFiniteLimits F ↔
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Mono (F.map S.f) :=
  (Functor.preservesFiniteLimits_tfae F).out 3 0

/--
If a functor `F : C ⥤ D` preserves exact sequences on the right-hand side (i.e.
if `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is exact then `F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact),
then it preserves epimorphisms.
-/
/-
**CategoryTheory.Functor.preservesEpimorphisms_of_preserves_shortExact_right** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesEpimorphisms_of_preserves_shortExact_right (h : forall (S : Short
Complex C), S.ShortExact -> (S.map F).Exact ∧ Epi (F.map S.g)) : F.PreservesEpim
orphisms where .2 preserves f
参数：h : forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact ∧ Epi (F.map
 S.g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.ShortComplex.exact_kernel`：exact_kernel {X Y : C} (f : X 
⟶ Y) : (ShortComplex.mk (kernel.ι f) f (by simp)).Exact
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…

--- 原说明 ---
If a functor `F : C ⥤ D` preserves exact sequences on the right-hand side (i.e.
if `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is exact then `F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact),
then it preserves epimorphisms.
-/
lemma preservesEpimorphisms_of_preserves_shortExact_right
    (h : ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Epi (F.map S.g)) :
    F.PreservesEpimorphisms where
  preserves f := h _ { exact := exact_kernel f } |>.2

set_option backward.isDefEq.respectTransparency false in
/--
For an additive functor `F : C ⥤ D` between abelian categories, the following are equivalent:
- `F` preserves short exact sequences on the right-hand side, i.e. if `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is
  exact then `F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
- `F` preserves exact sequences on the right-hand side, i.e. if `A ⟶ B ⟶ C` is exact where `B ⟶ C`
  is epi, then `F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact and `F(B) ⟶ F(C)` is epi as well.
- `F` preserves cokernels.
- `F` preserves finite colimits.
-/
/-
**CategoryTheory.Functor.preservesFiniteColimits_tfae** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：preservesFiniteColimits_tfae : List.TFAE [ forall (S : ShortComplex C), S.
ShortExact -> (S.map F).Exact ∧ Epi (F.map S.g), forall (S : ShortComplex C), S.
Exact ∧ Epi S.g -> (S.map F).Exact ∧ Epi (F.map S.g), forall ⦃X Y : C⦄ (f : X ⟶ 
Y), PreservesColimit (parallelPair f 0) F, PreservesFiniteColimits F ]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Functor.preservesEpimorphisms_of_preserves_shortExact_rig
ht`：preservesEpimorphisms_of_preserves_shortExact_right (h : forall (S : ShortCo
mplex C), S.ShortExact -> (S.map F).Exact ∧ Epi (F.map S.g)) : F…
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
· 使用定理 `CategoryTheory.Abelian.image_ι_comp_eq_zero`：image_ι_comp_eq_zero {R : C
} {g : Q ⟶ R} (h : f ≫ g = 0) : Abelian.image.ι f ≫ g = 0
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Abelian.image.fac`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {P Q : C}
   (f : P ⟶ Q) [inst_2…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.ShortComplex.map_g`：∀ {C : Type u_1} {D : Type u_2} [inst
 : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono`：exact_iff
_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : S₁.
Exact ↔ S₂.Exact
· 使用定理 `CategoryTheory.Abelian.instEpiFactorThruImage`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {P Q : C} (f
 : P ⟶ Q),   CategoryTheory.Epi (Ca…
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_exact_image_ι`：exact_iff_exact_ima
ge_ι : S.Exact ↔ (ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_com
p_eq_zero S.zero)).Exact
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
For an additive functor `F : C ⥤ D` between abelian categories, the following ar
e equivalent:
- `F` preserves short exact sequences on the right-hand side, i.e. if `0 ⟶ A ⟶ B
 ⟶ C ⟶ 0` is
  exact then `F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
- `F` preserves exact sequences on the right-hand side, i.e. if `A ⟶ B ⟶ C` is e
xact where `B ⟶ C`
  is epi, then `F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact and `F(B) ⟶ F(C)` is epi as wel
l.
- `F` preserves cokernels.
- `F` preserves finite colimits.
-/
lemma preservesFiniteColimits_tfae : List.TFAE
    [
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Epi (F.map S.g),
      ∀ (S : ShortComplex C), S.Exact ∧ Epi S.g → (S.map F).Exact ∧ Epi (F.map S.g),
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F,
      PreservesFiniteColimits F
    ] := by
  tfae_have 1 → 2
  | hF, S, ⟨hS, hf⟩ => by
    have := preservesEpimorphisms_of_preserves_shortExact_right F hF
    refine ⟨?_, inferInstance⟩
    let T := ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_comp_eq_zero S.zero)
    let φ : S.map F ⟶ T.map F :=
      { τ₁ := F.map <| Abelian.factorThruImage S.f
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := show _ ≫ F.map (kernel.ι _) = F.map _ ≫ 𝟙 _ by
          rw [← F.map_comp, Abelian.image.fac, Category.comp_id] }
    exact (exact_iff_of_epi_of_isIso_of_mono φ).2 (hF T ⟨(S.exact_iff_exact_image_ι).1 hS⟩).1
  tfae_have 2 → 3
  | hF, X, Y, f => by
    refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f) ?_
    apply (CokernelCofork.isColimitMapCoconeEquiv _ F).2
    let S := ShortComplex.mk _ _ (cokernel.condition f)
    let hS := hF S ⟨exact_cokernel f, inferInstance⟩
    have : Epi (S.map F).g := hS.2
    exact hS.1.gIsCokernel
  tfae_have 3 → 4
  | hF => by
    exact preservesFiniteColimits_of_preservesCokernels F
  tfae_have 4 → 1
  | ⟨_⟩, S, hS => (S.map F).exact_and_epi_g_iff_g_is_cokernel |>.2
    ⟨CokernelCofork.mapIsColimit _ hS.gIsCokernel F⟩
  tfae_finish

set_option backward.isDefEq.respectTransparency false in
/--
For an additive functor `F : C ⥤ D` between abelian categories, the following are equivalent:
- `F` preserves short exact sequences, i.e. if `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is exact then
  `0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
- `F` preserves exact sequences, i.e. if `A ⟶ B ⟶ C` is exact then `F(A) ⟶ F(B) ⟶ F(C)` is exact.
- `F` preserves homology.
- `F` preserves both finite limits and finite colimits.
-/
/-
**CategoryTheory.Functor.exact_tfae** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：exact_tfae : List.TFAE [ forall (S : ShortComplex C), S.ShortExact -> (S.m
ap F).ShortExact, forall (S : ShortComplex C), S.Exact -> (S.map F).Exact, Prese
rvesHomology F, PreservesFiniteLimits F ∧ PreservesFiniteColimits F ]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `CategoryTheory.Functor.preservesFiniteLimits_tfae`：preservesFiniteLimits
_tfae : List.TFAE [ forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact
 ∧ Mono (F.map S.f), forall (S : ShortC…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用引理 `CategoryTheory.Functor.preservesFiniteColimits_tfae`：preservesFiniteColi
mits_tfae : List.TFAE [ forall (S : ShortComplex C), S.ShortExact -> (S.map F).E
xact ∧ Epi (F.map S.g), forall (S : Short…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_mono`：exact_iff_mono [HasZeroObjec
t C] (hf : S.f = 0) : S.Exact ↔ Mono S.g
· 使用定理 `CategoryTheory.ShortComplex.map_f`：∀ {C : Type u_1} {D : Type u_2} [inst
 : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_epi`：exact_iff_epi [HasZeroObject 
C] (hg : S.g = 0) : S.Exact ↔ Epi S.f
· 使用定理 `CategoryTheory.ShortComplex.map_g`：∀ {C : Type u_1} {D : Type u_2} [inst
 : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology`：prese
rvesFiniteLimits_of_preservesHomology [HasFiniteProducts C] [HasKernels C] : Pre
servesFiniteLimits F
· 使用定理 `CategoryTheory.Abelian.has_finite_products`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory
.Limits.HasFiniteProducts C
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用引理 `CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology`：pre
servesFiniteColimits_of_preservesHomology [HasFiniteCoproducts C] [HasCokernels 
C] : PreservesFiniteColimits F
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.ShortComplex.Exact.map`：∀ {C : Type u_1} {D : Type u_2} [
inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category
.{v_2, u_2} D] [inst_2 : Ca…
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
For an additive functor `F : C ⥤ D` between abelian categories, the following ar
e equivalent:
- `F` preserves short exact sequences, i.e. if `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is exact then
  `0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
- `F` preserves exact sequences, i.e. if `A ⟶ B ⟶ C` is exact then `F(A) ⟶ F(B) 
⟶ F(C)` is exact.
- `F` preserves homology.
- `F` preserves both finite limits and finite colimits.
-/
lemma exact_tfae : List.TFAE
    [
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).ShortExact,
      ∀ (S : ShortComplex C), S.Exact → (S.map F).Exact,
      PreservesHomology F,
      PreservesFiniteLimits F ∧ PreservesFiniteColimits F
    ] := by
  tfae_have 1 → 3
  | hF => by
    refine ⟨fun {X Y} f ↦ ?_, fun {X Y} f ↦ ?_⟩
    · have h := (preservesFiniteLimits_tfae F |>.out 0 2 |>.1 fun S hS ↦
        And.intro (hF S hS).exact (hF S hS).mono_f)
      exact h f
    · have h := (preservesFiniteColimits_tfae F |>.out 0 2 |>.1 fun S hS ↦
        And.intro (hF S hS).exact (hF S hS).epi_g)
      exact h f
  tfae_have 2 → 1
  | hF, S, hS => by
    have : Mono (S.map F).f := exact_iff_mono _ (by simp) |>.1 <|
      hF (.mk (0 : 0 ⟶ S.X₁) S.f <| by simp) (exact_iff_mono _ (by simp) |>.2 hS.mono_f)
    have : Epi (S.map F).g := exact_iff_epi _ (by simp) |>.1 <|
      hF (.mk S.g (0 : S.X₃ ⟶ 0) <| by simp) (exact_iff_epi _ (by simp) |>.2 hS.epi_g)
    exact ⟨hF S hS.exact⟩
  tfae_have 3 → 4
  | h => ⟨preservesFiniteLimits_of_preservesHomology F,
      preservesFiniteColimits_of_preservesHomology F⟩
  tfae_have 4 → 2
  | ⟨h1, h2⟩, _, h => h.map F
  tfae_finish
/-
**CategoryTheory.Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesFiniteColimits_iff_forall_exact_map_and_epi : PreservesFiniteColi
mits F ↔ forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact ∧ Epi (F.m
ap S.g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Functor.preservesFiniteColimits_tfae`：preservesFiniteColi
mits_tfae : List.TFAE [ forall (S : ShortComplex C), S.ShortExact -> (S.map F).E
xact ∧ Epi (F.map S.g), forall (S : Short…
-/
lemma preservesFiniteColimits_iff_forall_exact_map_and_epi :
    PreservesFiniteColimits F ↔
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Epi (F.map S.g) :=
  (Functor.preservesFiniteColimits_tfae F).out 3 0

end

end Functor

end CategoryTheory

