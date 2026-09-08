/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.VanKampen
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes

/-!
# The sheaf condition and universal coproducts

In this file we show that if `{ fᵢ : Yᵢ ⟶ X }` is a family of morphisms and `∐ᵢ Yᵢ` is a universal
coproduct, then any presheaf `F` that preserves products is a sheaf for the single object covering
`{ ∐ᵢ Yᵢ ⟶ X }` if and only if it is a sheaf for `{ fᵢ : Yᵢ ⟶ X }ᵢ`.

We provide both a version for a general coefficient category and one for type values presheafs.
-/

universe w

@[expose] public section

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category* C] {A : Type*} [Category* A] {S : C}

set_option backward.isDefEq.respectTransparency false in
/--
Let `E` be a pre-`0`-hypercover with pairwise pullbacks. If `∐ᵢ Eᵢ` is a universal coproduct
and the presheaf `F` preserves products, then the multifork associated to the single object
`0`-hypercover `{ ∐ᵢ Eᵢ ⟶ S }` is exact if and only if the multifork for `E` is exact.
-/
noncomputable
/-
**CategoryTheory.PreZeroHypercover.isLimitSigmaOfIsColimitEquiv** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.PreZeroHypercover`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {A 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} A] →         {S
 : C} →           (E : CategoryTheory.PreZeroHypercover S) →             [inst_2
 : E.HasPullbacks] →               {c : CategoryTheory.Limits.Cofan E.X} →      
           (hc : CategoryTheory.Limits.IsColimit c) →                   Category
Theory.IsUniversalColimit c →                     [inst_3 : (E.sigmaOfIsColimit 
hc).HasPullbacks] →                       [∀ (i : E.I₀), CategoryTheory.Limits.H
asPullback (E.f i) ((E.sigmaOfIsColimit hc).f PUnit.unit)] →                    
     (F : CategoryTheory.Functor Cᵒᵖ A) →                           [CategoryThe
ory.Limits.PreservesLimit                                 (CategoryTheory.Discre
te.functor fun i => Opposite.op (E.toPreOneHypercover.X i)) F] →                
             [CategoryTheory.Limits.PreservesLimit                              
     (CategoryTheory.Discrete.functor fun i => Opposite.op (E.toPreOneHypercover
.Y' i))                                   F] →                               Cat
egoryTheory.Limits.IsLimit ((E.sigmaOfIsColimit hc).toPreOneHypercover.multifork
 F) ≃                                 CategoryTheory.Limits.IsLimit (E.toPreOneH
ypercover.multifork F)
参数：E : CategoryTheory.PreZeroHypercover S；hc : CategoryTheory.Limits.IsColimit c
；E.sigmaOfIsColimit hc；i : E.I₀；E.f i；(E.sigmaOfIsColimit hc).f PUnit.unit；F : C
ategoryTheory.Functor Cᵒᵖ A；CategoryTheory.Discrete.functor fun i => Opposite.op
 (E.toPreOneHypercover.X i)；CategoryTheory.Discrete.functor fun i => Opposite.op
 (E.toPreOneHypercover.Y' i)；(E.sigmaOfIsColimit hc).toPreOneHypercover.multifor
k F；E.toPreOneHypercover.multifork F。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
def PreZeroHypercover.isLimitSigmaOfIsColimitEquiv (E : PreZeroHypercover.{w} S)
    [E.HasPullbacks] {c : Cofan E.X} (hc : IsColimit c) (huniv : IsUniversalColimit c)
    [(E.sigmaOfIsColimit hc).HasPullbacks]
    [∀ i, HasPullback (E.f i) ((E.sigmaOfIsColimit hc).f PUnit.unit)]
    (F : Cᵒᵖ ⥤ A)
    [PreservesLimit (Discrete.functor fun i ↦ op (E.toPreOneHypercover.X i)) F]
    [PreservesLimit (Discrete.functor fun i ↦ op (E.toPreOneHypercover.Y' i)) F] :
    IsLimit ((E.sigmaOfIsColimit hc).toPreOneHypercover.multifork F) ≃
      IsLimit (E.toPreOneHypercover.multifork F) := by
  let c' : Cofan E.toPreOneHypercover.Y' :=
    Cofan.mk
      ((E.sigmaOfIsColimit hc).toPreOneHypercover.Y (i₁ := ⟨⟩) (i₂ := ⟨⟩) ⟨⟩)
      fun b ↦ pullback.map _ _ _ _ (c.inj _) (c.inj _) (𝟙 _) (by simp) (by simp)
  let equiv : E.toPreOneHypercover.I₁' ≃ E.I₀ × E.I₀ :=
    Equiv.sigmaPUnit (E.toPreOneHypercover.I₀ × E.toPreOneHypercover.I₀)
  have hc' : IsColimit c' := by
    refine (c'.isColimitEquivOfEquiv equiv.symm).symm (Nonempty.some ?_)
    exact IsUniversalColimit.nonempty_isColimit_prod_of_isPullback
      huniv huniv E.f E.f ((E.sigmaOfIsColimit hc).f ⟨⟩) ((E.sigmaOfIsColimit hc).f ⟨⟩)
      (fun i j ↦ .of_hasPullback _ _) (.of_hasPullback _ _) (.refl _) (by simp) (by simp)
      (by simp [c', equiv, Equiv.sigmaPUnit]) (by simp [c', equiv, Equiv.sigmaPUnit])
  refine .trans ?_ (E.toPreOneHypercover.isLimitSigmaOfIsColimitEquiv hc hc' F)
  apply PreOneHypercover.isLimitEquivOfIso
  refine PreOneHypercover.isoMk (.refl _) (fun _ ↦ .refl _) (fun _ _ ↦ .refl _)
      (fun _ _ _ ↦ Iso.refl _) (by cat_disch) ?_ ?_
  · intro ⟨⟩ ⟨⟩ k
    refine Cofan.IsColimit.hom_ext hc' _ _ fun k ↦ ?_
    congr 1
    exact Cofan.IsColimit.hom_ext hc' _ _ fun a ↦ by simp; simp [c']
  · intro ⟨⟩ ⟨⟩ k
    exact Cofan.IsColimit.hom_ext hc' _ _ fun a ↦ by simp; simp [c']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open PreZeroHypercover in
/--
Let `{ fᵢ : Xᵢ ⟶ S }` be a family of morphisms. If `∐ᵢ Xᵢ` is a universal coproduct
and the presheaf `F` preserves products, then `F` is a sheaf for the single object covering
`{ ∐ᵢ Xᵢ ⟶ S }` if and only if it is a sheaf for `{ fᵢ : Xᵢ ⟶ S }ᵢ`.
-/
/-
**CategoryTheory.Presieve.isSheafFor_sigmaDesc_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Presieve`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {S : C} {ι 
: Type u_3} {X : ι → C}   (f : (i : ι) → X i ⟶ S) [inst_1 : (CategoryTheory.Pres
ieve.ofArrows X f).HasPairwisePullbacks]   {c : CategoryTheory.Limits.Cofan X} (
hc : CategoryTheory.Limits.IsColimit c),   CategoryTheory.IsUniversalColimit c →
     ∀       [CategoryTheory.Limits.HasPullback (CategoryTheory.Limits.Cofan.IsC
olimit.desc hc f)           (CategoryTheory.Limits.Cofan.IsColimit.desc hc f)]  
     [∀ (i : ι), CategoryTheory.Limits.HasPullback (f i) (CategoryTheory.Limits.
Cofan.IsColimit.desc hc f)]       (F : CategoryTheory.Functor Cᵒᵖ (Type u_4))   
    [CategoryTheory.Limits.PreservesLimit (CategoryTheory.Discrete.functor fun i
 => Opposite.op (X i)) F]       [CategoryTheory.Limits.PreservesLimit           
(CategoryTheory.Discrete.functor fun ij => Opposite.op (CategoryTheory.Limits.pu
llback (f ij.1) (f ij.2))) F],       CategoryTheory.Presieve.IsSheafFor F       
    (CategoryTheory.Presieve.singleton (CategoryTheory.Limits.Cofan.IsColimit.de
sc hc f)) ↔         CategoryTheory.Presieve.IsSheafFor F (CategoryTheory.Presiev
e.ofArrows X f)
参数：f : (i : ι) → X i ⟶ S；CategoryTheory.Presieve.ofArrows X f；hc : CategoryTheor
y.Limits.IsColimit c；CategoryTheory.Limits.Cofan.IsColimit.desc hc f；CategoryThe
ory.Limits.Cofan.IsColimit.desc hc f；i : ι；f i；CategoryTheory.Limits.Cofan.IsCol
imit.desc hc f；F : CategoryTheory.Functor Cᵒᵖ (Type u_4)；CategoryTheory.Discrete
.functor fun i => Opposite.op (X i)；CategoryTheory.Discrete.functor fun ij => Op
posite.op (CategoryTheory.Limits.pullback (f ij.1) (f ij.2))；CategoryTheory.Pres
ieve.singleton (CategoryTheory.Limits.Cofan.IsColimit.desc hc f)；CategoryTheory.
Presieve.ofArrows X f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.instHasPullbackOfHasPairwisePullbacksOfArrows`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type v₂} {X : α 
→ C} {B : C} (π : (a : α) → X a ⟶ B)   [(CategoryTheory.Pre…
· 使用定理 `CategoryTheory.Functor.Initial.preservesLimit_of_comp`：preservesLimit_of
_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B} [PreservesLimit (F ⋙ G) H] : P
reservesLimit G H where preserves {c} hc
· 使用定理 `CategoryTheory.Functor.initial_of_isLeftAdjoint`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.PreZeroHypercover.presieve₀_sigmaOfIsColimit`：presieve₀_s
igmaOfIsColimit (E : PreZeroHypercover.{w} S) {c : Cofan E.X} (hc : IsColimit c)
 : (E.sigmaOfIsColimit hc).presieve₀ = Presieve.s…
· 使用引理 `CategoryTheory.PreZeroHypercover.isLimit_toPreOneHypercover_type_iff`：is
Limit_toPreOneHypercover_type_iff (E : PreZeroHypercover.{w} S) [E.HasPullbacks]
 (F : Cᵒᵖ ⥤ Type*) : Nonempty (IsLimit <| E.toPreOneHyperc…

--- 原说明 ---
Let `{ fᵢ : Xᵢ ⟶ S }` be a family of morphisms. If `∐ᵢ Xᵢ` is a universal coprod
uct
and the presheaf `F` preserves products, then `F` is a sheaf for the single obje
ct covering
`{ ∐ᵢ Xᵢ ⟶ S }` if and only if it is a sheaf for `{ fᵢ : Xᵢ ⟶ S }ᵢ`.
-/
lemma Presieve.isSheafFor_sigmaDesc_iff {ι : Type*} {X : ι → C} (f : ∀ i, X i ⟶ S)
    [(ofArrows X f).HasPairwisePullbacks] {c : Cofan X} (hc : IsColimit c)
    (hc' : IsUniversalColimit c)
    [HasPullback (Cofan.IsColimit.desc hc f) (Cofan.IsColimit.desc hc f)]
    [∀ i, HasPullback (f i) (Cofan.IsColimit.desc hc f)]
    (F : Cᵒᵖ ⥤ Type*)
    [PreservesLimit (Discrete.functor <| fun i ↦ op (X i)) F]
    [PreservesLimit (Discrete.functor fun (ij : ι × ι) ↦
      op (Limits.pullback (f ij.1) (f ij.2))) F] :
    Presieve.IsSheafFor F (.singleton <| Cofan.IsColimit.desc hc f) ↔
      Presieve.IsSheafFor F (.ofArrows X f) := by
  let E := PreZeroHypercover.mk _ _ f
  have : (E.sigmaOfIsColimit hc).HasPullbacks :=
    fun i j ↦ by dsimp [sigmaOfIsColimit]; infer_instance
  have (i : E.I₀) : HasPullback (E.f i) ((E.sigmaOfIsColimit hc).f PUnit.unit) := by
    dsimp [sigmaOfIsColimit_f]; infer_instance
  have : PreservesLimit (Discrete.functor fun i ↦ op (E.toPreOneHypercover.X i)) F := by
    dsimp [E]; infer_instance
  have : PreservesLimit (Discrete.functor fun i ↦ op (E.toPreOneHypercover.Y' i)) F := by
    convert! Functor.Initial.preservesLimit_of_comp (Discrete.equivalence <| .sigmaPUnit _).inverse
    · infer_instance
    · assumption
  let equiv := (E.isLimitSigmaOfIsColimitEquiv hc hc' F).nonempty_congr
  rwa [isLimit_toPreOneHypercover_type_iff, isLimit_toPreOneHypercover_type_iff,
    presieve₀_sigmaOfIsColimit] at equiv

end CategoryTheory

