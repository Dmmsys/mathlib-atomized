/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Simplicial homology

In this file, we define the homology of simplicial sets.
For any preadditive category `C` with coproducts of size `w` and any
object `R : C`, the simplicial chain complex of a simplicial
set `X` is denoted `X.chainComplex R`, and its homology
in degree `n : ℕ` is `X.homology R n`.

-/

@[expose] public section

open Simplicial CategoryTheory Limits

universe w v u

namespace SSet

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/--
The chain complex associated to a simplicial set, with coefficients in `R : C`.
It computes the simplicial homology of a simplicial sets with coefficients
in `R`. One can recover the ordinary simplicial chain complex when `C := Ab`
and `X := ℤ`.
-/
@[implicit_reducible]
/-
**SSet.chainComplexFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：chainComplexFunctor : C ⥤ SSet.{w} ⥤ ChainComplex C Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The chain complex associated to a simplicial set, with coefficients in `R : C`.
It computes the simplicial homology of a simplicial sets with coefficients
in `R`. One can recover the ordinary simplicial chain complex when `C := Ab`
and `X := ℤ`.
-/
noncomputable def chainComplexFunctor : C ⥤ SSet.{w} ⥤ ChainComplex C ℕ :=
  (Functor.postcompose₂.obj (AlgebraicTopology.alternatingFaceMapComplex _)).obj
    (sigmaConst ⋙ SimplicialObject.whiskering _ _)
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (chainComplexFunctor C).Additive := by
  dsimp [chainComplexFunctor, SimplicialObject.whiskering]
  infer_instance

@[deprecated (since := "2026-04-05")]
alias _root_.AlgebraicTopology.SSet.singularChainComplexFunctor :=
  chainComplexFunctor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] SSet.chainComplexFunctor in
attribute [local simp←] _root_.SSet.yonedaEquiv_symm_comp in
/-- The adjunction `Hom(Cⁿ(-, X), F) ≃ Hom(X, F(Δ[n]))` for `R : C` and `F : SSet ⥤ C`. -/
/-
**SSet.chainComplexFunctorAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：chainComplexFunctorAdjunction (n : Nat) : (Functor.postcompose₂.obj (Homol
ogicalComplex.eval _ _ n)).obj (SSet.chainComplexFunctor C) ⊣ (evaluation _ _).o
bj Δ[n] where unit.app R
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The adjunction `Hom(Cⁿ(-, X), F) ≃ Hom(X, F(Δ[n]))` for `R : C` and `F : SSet ⥤ 
C`.
-/
noncomputable def chainComplexFunctorAdjunction (n : ℕ) :
    (Functor.postcompose₂.obj (HomologicalComplex.eval _ _ n)).obj
      (SSet.chainComplexFunctor C) ⊣ (evaluation _ _).obj Δ[n] where
  unit.app R := Sigma.ι (fun _ : Δ[n] _⦋n⦌ ↦ R) (SSet.stdSimplex.objEquiv (n := ⦋n⦌).symm (𝟙 ⦋n⦌))
  counit.app F := { app S := Sigma.desc fun α ↦ F.map (SSet.yonedaEquiv.symm α) }
  right_triangle_components F := by dsimp; simp

@[deprecated (since := "2026-04-05")]
alias _root_.SSet.singularChainComplexFunctorAdjunction :=
  SSet.chainComplexFunctorAdjunction

variable {C} (X Y Z : SSet.{w}) (f : X ⟶ Y) (g : Y ⟶ Z) (R : C)

/-- The (simplicial) chain complex of a simplicial set `X` with
coefficients in `R : C`. Its homology is the simplicial homology
of `X`. -/
/-
**SSet.chainComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：chainComplex : ChainComplex C Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (simplicial) chain complex of a simplicial set `X` with
coefficients in `R : C`. Its homology is the simplicial homology
of `X`.
-/
noncomputable abbrev chainComplex : ChainComplex C ℕ :=
  ((SSet.chainComplexFunctor C).obj R).obj X

variable {X Y} in
/-- The morphism of simplicial chain complexes induces by a morphism
of simplicial sets. -/
/-
**SSet.chainComplexMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：chainComplexMap : X.chainComplex R ⟶ Y.chainComplex R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism of simplicial chain complexes induces by a morphism
of simplicial sets.
-/
noncomputable abbrev chainComplexMap : X.chainComplex R ⟶ Y.chainComplex R :=
  ((SSet.chainComplexFunctor C).obj R).map f

variable {R} in
/-- The inclusion `R ⟶ (X.chainComplex R).X n` of the summand
corresponding to a `n`-simplex `x : X _⦋n⦌`. -/
/-
**SSet.** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `R ⟶ (X.chainComplex R).X n` of the summand
corresponding to a `n`-simplex `x : X _⦋n⦌`.
-/
noncomputable def ιChainComplex {n : ℕ} (x : X _⦋n⦌) : R ⟶ (X.chainComplex R).X n :=
  Sigma.ι (fun (_ : X _⦋n⦌) ↦ R) x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιChainComplex_d {n : ℕ} (x : X _⦋n + 1⦌) :
    X.ιChainComplex x ≫ (X.chainComplex R).d (n + 1) n =
      ∑ (i : Fin (n + 2)), (-1) ^ i.val • X.ιChainComplex (X.δ i x) := by
  simp [ιChainComplex, chainComplex, chainComplexFunctor, Preadditive.comp_sum]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_chainComplexMap_f {n : ℕ} (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (chainComplexMap f R).f n =
      Y.ιChainComplex (f.app _ x) := by
  dsimp [chainComplexMap, chainComplexFunctor, ιChainComplex, Sigma.map',
    chainComplex, chainComplexFunctor]
  simp

/-- The colimit cofan which defines the simplicial `n`-chains
`(X.chainComplex R).X n`. -/
/-
**SSet.chainComplexXCofan** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：chainComplexXCofan (n : Nat) : Cofan (fun (_ : X _⦋n⦌) => R)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cofan which defines the simplicial `n`-chains
`(X.chainComplex R).X n`.
-/
noncomputable def chainComplexXCofan (n : ℕ) : Cofan (fun (_ : X _⦋n⦌) ↦ R) :=
  Cofan.mk _ X.ιChainComplex

/-- Simplicial `n`-chains `(X.chainComplex R).X n` of a simplicial set `X`
with coefficients in `R` identify to a coproduct of copies of `R`
indexed by `X _⦋n⦌`. -/
/-
**SSet.isColimitChainComplexXCofan** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：isColimitChainComplexXCofan (n : Nat) : IsColimit (X.chainComplexXCofan R 
n)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Simplicial `n`-chains `(X.chainComplex R).X n` of a simplicial set `X`
with coefficients in `R` identify to a coproduct of copies of `R`
indexed by `X _⦋n⦌`.
-/
noncomputable def isColimitChainComplexXCofan (n : ℕ) : IsColimit (X.chainComplexXCofan R n) :=
  coproductIsCoproduct _

variable {X R} in
@[ext]
/-
**SSet.chainComplex_hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：chainComplex_hom_ext {n : Nat} {T : C} {f g : (X.chainComplex R).X n ⟶ T} 
(h : forall (x : X _⦋n⦌), X.ιChainComplex x ≫ f = X.ιChainComplex x ≫ g) : f = g
参数：X.chainComplex R；h : forall (x : X _⦋n⦌), X.ιChainComplex x ≫ f = X.ιChainCom
plex x ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
-/
lemma chainComplex_hom_ext {n : ℕ} {T : C} {f g : (X.chainComplex R).X n ⟶ T}
    (h : ∀ (x : X _⦋n⦌), X.ιChainComplex x ≫ f = X.ιChainComplex x ≫ g) :
    f = g :=
  (X.isColimitChainComplexXCofan R n).hom_ext (fun _ ↦ h _)

variable [CategoryWithHomology C]

/-- The simplicial homology with coefficients in `R : C` in degree `n`
of a simplicial set `X`. -/
/-
**SSet.homology** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasCoproducts C] →       [inst_2 : CategoryTheory.Preadditive C] →
 _root_.SSet → C → [CategoryTheory.CategoryWithHomology C] → ℕ → C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The simplicial homology with coefficients in `R : C` in degree `n`
of a simplicial set `X`.
-/
protected noncomputable abbrev homology (n : ℕ) : C := (X.chainComplex R).homology n

variable {X Y} in
/-- The morphism in simplicial homology that is induced by a morphism
of simplicial sets. -/
/-
**SSet.homologyMap** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasCoproducts C] →       [inst_2 : CategoryTheory.Preaddi
tive C] →         {X Y : _root_.SSet} →           (X ⟶ Y) →             (R : C) 
→ [inst_3 : CategoryTheory.CategoryWithHomology C] → (n : ℕ) → X.homology R n ⟶ 
Y.homology R n
参数：X ⟶ Y；R : C；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism in simplicial homology that is induced by a morphism
of simplicial sets.
-/
protected noncomputable abbrev homologyMap (n : ℕ) : X.homology R n ⟶ Y.homology R n :=
  HomologicalComplex.homologyMap (chainComplexMap f R) n

@[simp]
/-
**SSet.homologyMap_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：homologyMap_id (n : Nat) : SSet.homologyMap (𝟙 X) R n = 𝟙 _
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `HomologicalComplex.homologyMap_id`：homologyMap_id : homologyMap (𝟙 K) i 
= 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homologyMap_id (n : ℕ) : SSet.homologyMap (𝟙 X) R n = 𝟙 _ := by
  simp [SSet.homologyMap]

@[reassoc]
/-
**SSet.homologyMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：homologyMap_comp (n : Nat) : SSet.homologyMap (f ≫ g) R n = SSet.homologyM
ap f R n ≫ SSet.homologyMap g R n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `HomologicalComplex.homologyMap_comp`：homologyMap_comp : homologyMap (φ ≫
 ψ) i = homologyMap φ i ≫ homologyMap ψ i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homologyMap_comp (n : ℕ) :
    SSet.homologyMap (f ≫ g) R n = SSet.homologyMap f R n ≫ SSet.homologyMap g R n := by
  simp [SSet.homologyMap, HomologicalComplex.homologyMap_comp]

attribute [local simp] homologyMap_comp in
/-- The simplicial homology functor in degree `n` with coefficients in `R : C`. -/
@[simps]
/-
**SSet.homologyFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：homologyFunctor (n : Nat) : SSet.{w} ⥤ C where obj X
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The simplicial homology functor in degree `n` with coefficients in `R : C`.
-/
noncomputable def homologyFunctor (n : ℕ) : SSet.{w} ⥤ C where
  obj X := X.homology R n
  map f := SSet.homologyMap f R n

end SSet

