/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# Tensoring with a flat module is an exact functor

In this file we prove that tensoring with a flat module is an exact functor.

## Main results

- `Module.Flat.iff_lTensor_preserves_shortComplex_exact`: an `R`-module `M` is flat if and only if
  for every exact sequence `A ⟶ B ⟶ C`, `M ⊗ A ⟶ M ⊗ B ⟶ M ⊗ C` is also exact.

- `Module.Flat.iff_rTensor_preserves_shortComplex_exact`: an `R`-module `M` is flat if and only if
  for every short exact sequence `A ⟶ B ⟶ C`, `A ⊗ M ⟶ B ⊗ M ⟶ C ⊗ M` is also exact.

## TODO

- Relate flatness with `Tor`

-/

public section

universe u

open CategoryTheory MonoidalCategory ShortComplex.ShortExact

namespace Module.Flat

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

/-
**Module.Flat.lTensor_shortComplex_exact** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`
。
形式化陈述：lTensor_shortComplex_exact [Flat R M] (C : ShortComplex <| ModuleCat R) (h
C : C.Exact) : .Exact
参数：C : ShortComplex <| ModuleCat R；hC : C.Exact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.tensoringLeft_additive`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [inst_2 
: CategoryTheory.MonoidalCa…
· 使用定理 `ModuleCat.instMonoidalPreadditive`：∀ {R : Type u} [inst : CommRing R], C
ategoryTheory.MonoidalPreadditive (ModuleCat R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exac
t`：∀ {R : Type u} [inst : Ring R] (S : CategoryTheory.ShortComplex (ModuleCat R)
),   S.Exact ↔ Function.Exact ⇑(CategoryTheory.ConcreteCategory…
· 使用引理 `Module.Flat.lTensor_exact`：lTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄ [
AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] 
[Module R N''] …
-/
lemma lTensor_shortComplex_exact [Flat R M] (C : ShortComplex <| ModuleCat R) (hC : C.Exact) :
    C.map (tensorLeft M) |>.Exact := by
  rw [moduleCat_exact_iff_function_exact] at hC ⊢
  exact lTensor_exact M hC
/-
**Module.Flat.rTensor_shortComplex_exact** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`
。
形式化陈述：rTensor_shortComplex_exact [Flat R M] (C : ShortComplex <| ModuleCat R) (h
C : C.Exact) : .Exact
参数：C : ShortComplex <| ModuleCat R；hC : C.Exact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instPreservesZeroMorphismsObjFlip`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.MonoidalPreadditive.instAdditiveFunctorCurriedTensor`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Preadditive C]   [inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `ModuleCat.instMonoidalPreadditive`：∀ {R : Type u} [inst : CommRing R], C
ategoryTheory.MonoidalPreadditive (ModuleCat R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exac
t`：∀ {R : Type u} [inst : Ring R] (S : CategoryTheory.ShortComplex (ModuleCat R)
),   S.Exact ↔ Function.Exact ⇑(CategoryTheory.ConcreteCategory…
· 使用引理 `Module.Flat.rTensor_exact`：rTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄ [
AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] 
[Module R N''] …
-/
lemma rTensor_shortComplex_exact [Flat R M] (C : ShortComplex <| ModuleCat R) (hC : C.Exact) :
    C.map (tensorRight M) |>.Exact := by
  rw [moduleCat_exact_iff_function_exact] at hC ⊢
  exact rTensor_exact M hC
/-
**Module.Flat.iff_lTensor_preserves_shortComplex_exact** 是 Mathlib 中的一个引理，位于命名空间
 `Module.Flat`。
形式化陈述：iff_lTensor_preserves_shortComplex_exact : Flat R M ↔ forall (C : ShortCom
plex <| ModuleCat R) (_ : C.Exact), (C.map (tensorLeft M) |>.Exact)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.tensoringLeft_additive`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [inst_2 
: CategoryTheory.MonoidalCa…
· 使用定理 `ModuleCat.instMonoidalPreadditive`：∀ {R : Type u} [inst : CommRing R], C
ategoryTheory.MonoidalPreadditive (ModuleCat R)
· 使用引理 `Module.Flat.lTensor_shortComplex_exact`：lTensor_shortComplex_exact [Flat
 R M] (C : ShortComplex <| ModuleCat R) (hC : C.Exact) : .Exact
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Flat.iff_lTensor_exact`：iff_lTensor_exact : Flat R M ↔ forall ⦃N 
N' N'' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [
Module R N] [Module…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `Function.Exact.apply_apply_eq_zero`：∀ {M : Type u_2} {N : Type u_4} {P :
 Type u_6} {f : M → N} {g : N → P} [inst : Zero P],   Function.Exact f g → ∀ (x 
: M), g (f x) = 0
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exac
t`：∀ {R : Type u} [inst : Ring R] (S : CategoryTheory.ShortComplex (ModuleCat R)
),   S.Exact ↔ Function.Exact ⇑(CategoryTheory.ConcreteCategory…
-/
lemma iff_lTensor_preserves_shortComplex_exact :
    Flat R M ↔
    ∀ (C : ShortComplex <| ModuleCat R) (_ : C.Exact), (C.map (tensorLeft M) |>.Exact) :=
  ⟨fun _ _ ↦ lTensor_shortComplex_exact _ _, fun H ↦ iff_lTensor_exact.2
    fun _ _ _ _ _ _ _ _ _ f g h ↦
      moduleCat_exact_iff_function_exact _ |>.1 <|
      H (.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (ModuleCat.hom_ext (DFunLike.ext _ _ h.apply_apply_eq_zero)))
          (moduleCat_exact_iff_function_exact _ |>.2 h)⟩
/-
**Module.Flat.iff_rTensor_preserves_shortComplex_exact** 是 Mathlib 中的一个引理，位于命名空间
 `Module.Flat`。
形式化陈述：iff_rTensor_preserves_shortComplex_exact : Flat R M ↔ forall (C : ShortCom
plex <| ModuleCat R) (_ : C.Exact), (C.map (tensorRight M) |>.Exact)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instPreservesZeroMorphismsObjFlip`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.MonoidalPreadditive.instAdditiveFunctorCurriedTensor`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Preadditive C]   [inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `ModuleCat.instMonoidalPreadditive`：∀ {R : Type u} [inst : CommRing R], C
ategoryTheory.MonoidalPreadditive (ModuleCat R)
· 使用引理 `Module.Flat.rTensor_shortComplex_exact`：rTensor_shortComplex_exact [Flat
 R M] (C : ShortComplex <| ModuleCat R) (hC : C.Exact) : .Exact
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Flat.iff_rTensor_exact`：iff_rTensor_exact : Flat R M ↔ forall ⦃N 
N' N'' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [
Module R N] [Module…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `Function.Exact.apply_apply_eq_zero`：∀ {M : Type u_2} {N : Type u_4} {P :
 Type u_6} {f : M → N} {g : N → P} [inst : Zero P],   Function.Exact f g → ∀ (x 
: M), g (f x) = 0
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exac
t`：∀ {R : Type u} [inst : Ring R] (S : CategoryTheory.ShortComplex (ModuleCat R)
),   S.Exact ↔ Function.Exact ⇑(CategoryTheory.ConcreteCategory…
-/
lemma iff_rTensor_preserves_shortComplex_exact :
    Flat R M ↔
    ∀ (C : ShortComplex <| ModuleCat R) (_ : C.Exact), (C.map (tensorRight M) |>.Exact) :=
  ⟨fun _ _ ↦ rTensor_shortComplex_exact _ _, fun H ↦ iff_rTensor_exact.2
    fun _ _ _ _ _ _ _ _ _ f g h ↦
      moduleCat_exact_iff_function_exact _ |>.1 <|
      H (.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (ModuleCat.hom_ext (DFunLike.ext _ _ h.apply_apply_eq_zero)))
          (moduleCat_exact_iff_function_exact _ |>.2 h)⟩

open Limits
/-
**Module.Flat.iff_preservesFiniteLimits_tensorLeft** 是 Mathlib 中的一个引理，位于命名空间 `Mo
dule.Flat`。
形式化陈述：iff_preservesFiniteLimits_tensorLeft : Flat R M ↔ PreservesFiniteLimits (t
ensorLeft M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.tensoringLeft_additive`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [inst_2 
: CategoryTheory.MonoidalCa…
· 使用定理 `ModuleCat.instMonoidalPreadditive`：∀ {R : Type u} [inst : CommRing R], C
ategoryTheory.MonoidalPreadditive (ModuleCat R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Flat.iff_lTensor_preserves_shortComplex_exact`：iff_lTensor_preser
ves_shortComplex_exact : Flat R M ↔ forall (C : ShortComplex <| ModuleCat R) (_ 
: C.Exact), (C.map (tensorLeft M) |>.Exact…
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `CategoryTheory.Functor.exact_tfae`：exact_tfae : List.TFAE [ forall (S : 
ShortComplex C), S.ShortExact -> (S.map F).ShortExact, forall (S : ShortComplex 
C), S.Exact -> (S.map F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instPreservesColimitsTensorLeft`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] (A
 : C)   [CategoryTheory.Closed A], C…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iff_preservesFiniteLimits_tensorLeft :
    Flat R M ↔ PreservesFiniteLimits (tensorLeft M) := by
  rw [Module.Flat.iff_lTensor_preserves_shortComplex_exact,
    ((Functor.exact_tfae <| tensorLeft M).out 1 3 :)]
  simp [show PreservesFiniteColimits (tensorLeft M) from inferInstance]
/-
**Module.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Flat R M] : PreservesFiniteLimits <| tensorLeft M := by
  rw [← iff_preservesFiniteLimits_tensorLeft]
  infer_instance
/-
**Module.Flat.iff_preservesFiniteLimits_tensorRight** 是 Mathlib 中的一个引理，位于命名空间 `M
odule.Flat`。
形式化陈述：iff_preservesFiniteLimits_tensorRight : Flat R M ↔ PreservesFiniteLimits (
tensorRight M) where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_natIso`：preservesFiniteLi
mits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteLimits F] : PreservesFi
niteLimits G where preservesFiniteLimits _ …
· 使用定理 `Module.Flat.instPreservesFiniteLimitsModuleCatTensorLeftOfCarrier`：∀ {R 
: Type u} [inst : CommRing R] (M : ModuleCat R) [Module.Flat R ↑M],   CategoryTh
eory.Limits.PreservesFiniteLimits (CategoryTheory.Monoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Flat.iff_preservesFiniteLimits_tensorLeft`：iff_preservesFiniteLim
its_tensorLeft : Flat R M ↔ PreservesFiniteLimits (tensorLeft M)
-/
lemma iff_preservesFiniteLimits_tensorRight :
    Flat R M ↔ PreservesFiniteLimits (tensorRight M) where
  mp _ := preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  mpr _ := by
    rw [iff_preservesFiniteLimits_tensorLeft]
    exact preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm
/-
**Module.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Flat R M] : PreservesFiniteLimits (tensorRight M) :=
  preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

end Module.Flat

