/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
public import Mathlib.CategoryTheory.MorphismProperty.Local

/-!
# Covers in subcanonical topologies

In this file we provide API related to covers in subcanonical topologies.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace GrothendieckTopology.OneHypercover

variable {J : GrothendieckTopology C} [J.Subcanonical]

/-- Glue a family of morphisms along a `1`-hypercover for a subcanonical topology. -/
/-
**CategoryTheory.GrothendieckTopology.OneHypercover.glueMorphisms** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.OneHypercover`。
形式化陈述：glueMorphisms {S T : C} (E : J.OneHypercover S) (f : forall i, E.X i ⟶ T) 
(h : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j), E.p₁ k ≫ f i = E.p₂ k ≫ f j) : S ⟶ T
参数：E : J.OneHypercover S；f : forall i, E.X i ⟶ T；h : forall ⦃i j : E.I₀⦄ (k : E.
I₁ i j), E.p₁ k ≫ f i = E.p₂ k ≫ f j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Glue a family of morphisms along a `1`-hypercover for a subcanonical topology.
-/
noncomputable def glueMorphisms {S T : C} (E : J.OneHypercover S) (f : ∀ i, E.X i ⟶ T)
    (h : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), E.p₁ k ≫ f i = E.p₂ k ≫ f j) :
    S ⟶ T :=
  (E.isStronglySheafFor
    (Subcanonical.isSheaf_of_isRepresentable (CategoryTheory.yoneda.obj T))).amalgamate f h

variable {S T : C} (E : J.OneHypercover S) (f : ∀ i, E.X i ⟶ T)
  (h : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), E.p₁ k ≫ f i = E.p₂ k ≫ f j)

@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.OneHypercover.f_glueMorphisms** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.OneHypercover`。
形式化陈述：f_glueMorphisms (i : E.I₀) : E.f i ≫ E.glueMorphisms f h = f i
参数：i : E.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.PreOneHypercover.IsStronglySheafFor.map_amalgamate`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} {E : CategoryT
heory.PreOneHypercover X}   {F : CategoryTheory.Functor…
· 使用引理 `CategoryTheory.GrothendieckTopology.OneHypercover.isStronglySheafFor`：is
StronglySheafFor (hf : Presieve.IsSheaf J F) : E.IsStronglySheafFor F where isSh
eafFor_presieve₀
· 使用定理 `CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresenta
ble`：isSheaf_of_isRepresentable {J : GrothendieckTopology C} [Subcanonical J] (P
 : Cᵒᵖ ⥤ Type w) [P.IsRepresentable] : Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.Functor.instIsRepresentableObjOppositeTypeYoneda`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C}, (CategoryTheory.yo
neda.obj X).IsRepresentable
-/
lemma f_glueMorphisms (i : E.I₀) : E.f i ≫ E.glueMorphisms f h = f i :=
  (E.isStronglySheafFor
    (Subcanonical.isSheaf_of_isRepresentable (CategoryTheory.yoneda.obj T))).map_amalgamate _ _ i

end GrothendieckTopology.OneHypercover

namespace Precoverage.ZeroHypercover

variable {J : Precoverage C} [J.toGrothendieck.Subcanonical]

/-
**CategoryTheory.Precoverage.ZeroHypercover.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Precoverage.ZeroHypercover`。
形式化陈述：hom_ext {X Y : C} (𝒰 : J.ZeroHypercover X) {f g : X ⟶ Y} (h : forall i, 𝒰.
f i ≫ f = 𝒰.f i ≫ g) : f = g
参数：𝒰 : J.ZeroHypercover X；h : forall i, 𝒰.f i ≫ f = 𝒰.f i ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSheaf.isSheafFor_of_mem_precoverage`：∀ {C : Ty
pe u_3} [inst : CategoryTheory.Category.{u_2, u_3} C] {J : CategoryTheory.Precov
erage C}   {P : CategoryTheory.Functor Cᵒᵖ (Type u_…
· 使用定理 `CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresenta
ble`：isSheaf_of_isRepresentable {J : GrothendieckTopology C} [Subcanonical J] (P
 : Cᵒᵖ ⥤ Type w) [P.IsRepresentable] : Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.Functor.instIsRepresentableObjOppositeTypeYoneda`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C}, (CategoryTheory.yo
neda.obj X).IsRepresentable
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
· 使用定理 `CategoryTheory.PreZeroHypercover.ext_of_isSeparatedFor`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Functor Cᵒᵖ (Type u
_2)} {S : C}   (E : CategoryTheory.PreZeroHy…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_ext {X Y : C} (𝒰 : J.ZeroHypercover X) {f g : X ⟶ Y}
    (h : ∀ i, 𝒰.f i ≫ f = 𝒰.f i ≫ g) : f = g := by
  have hs : 𝒰.presieve₀.IsSheafFor (yoneda.obj Y) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor_of_mem_precoverage
      𝒰.mem₀
  exact 𝒰.ext_of_isSeparatedFor hs.isSeparatedFor fun i ↦ by simp [h i]

/-- Glue morphisms along a `0`-hypercover. -/
/-
**CategoryTheory.Precoverage.ZeroHypercover.glueMorphisms** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Precoverage.ZeroHypercover`。
形式化陈述：glueMorphisms {S T : C} (𝒰 : J.ZeroHypercover S) [𝒰.HasPullbacks] (f : for
all i, 𝒰.X i ⟶ T) (hf : forall i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullbac
k.snd (𝒰.f i) (𝒰.f j) ≫ f j) : S ⟶ T
参数：𝒰 : J.ZeroHypercover S；f : forall i, 𝒰.X i ⟶ T；hf : forall i j, pullback.fst 
(𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ f j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Glue morphisms along a `0`-hypercover.
-/
noncomputable def glueMorphisms {S T : C} (𝒰 : J.ZeroHypercover S) [𝒰.HasPullbacks]
    (f : ∀ i, 𝒰.X i ⟶ T)
    (hf : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ f j) :
    S ⟶ T :=
  𝒰.toOneHypercover.glueMorphisms f fun i j _ ↦ hf i j

@[reassoc (attr := simp)]
/-
**CategoryTheory.Precoverage.ZeroHypercover.f_glueMorphisms** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Precoverage.ZeroHypercover`。
形式化陈述：f_glueMorphisms {S T : C} (𝒰 : J.ZeroHypercover S) [𝒰.HasPullbacks] (f : f
orall i, 𝒰.X i ⟶ T) (hf : forall i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullb
ack.snd (𝒰.f i) (𝒰.f j) ≫ f j) (i : 𝒰.I₀) : 𝒰.f i ≫ 𝒰.glueMorphisms f hf = f i
参数：𝒰 : J.ZeroHypercover S；f : forall i, 𝒰.X i ⟶ T；hf : forall i j, pullback.fst 
(𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ f j；i : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.OneHypercover.f_glueMorphisms`：f_glu
eMorphisms (i : E.I₀) : E.f i ≫ E.glueMorphisms f h = f i
-/
lemma f_glueMorphisms {S T : C} (𝒰 : J.ZeroHypercover S) [𝒰.HasPullbacks]
    (f : ∀ i, 𝒰.X i ⟶ T)
    (hf : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ f j)
    (i : 𝒰.I₀) :
    𝒰.f i ≫ 𝒰.glueMorphisms f hf = f i :=
  𝒰.toOneHypercover.f_glueMorphisms _ _ _

open MorphismProperty

variable [Limits.HasPullbacks C] [J.IsStableUnderBaseChange]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `J` is a subcanonical precoverage, isomorphisms are local on the target for `J`. -/
/-
**CategoryTheory.Precoverage.ZeroHypercover.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Precoverage.ZeroHypercover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `J` is a subcanonical precoverage, isomorphisms are local on the target for `
J`.
-/
instance : (isomorphisms C).IsLocalAtTarget J := by
  refine .mk_of_isStableUnderBaseChange fun {X Y} f 𝒰 (H : ∀ i, IsIso _) ↦ ⟨?_, ?_, ?_⟩
  · refine 𝒰.glueMorphisms (fun i ↦ inv (pullback.snd f (𝒰.f i)) ≫ pullback.fst _ _) fun i j ↦ ?_
    let f := pullback.map (pullback.fst f (𝒰.f i) ≫ f) (𝒰.f j) (𝒰.f i) (𝒰.f j) (pullback.snd _ _)
      (𝟙 _) (𝟙 _) (by simp [pullback.condition]) (by simp)
    rw [← cancel_epi ((pullbackRightPullbackFstIso _ _ _).hom ≫ f)]
    simp [pullback.condition, f]
  · exact (𝒰.pullback₁ f).hom_ext fun i ↦ by simp [pullback.condition_assoc]
  · exact 𝒰.hom_ext fun i ↦ by simp [pullback.condition]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
To show that
```
P ---> X
|      |
v      v
Y ---> Z
```
is a pullback square, it suffices to check that
```
P ×[X] Uᵢ ---> Uᵢ
   |           |
   v           v
   Y --------> Z
```
is a pullback square for all `Uᵢ` in a cover of `X` for some subcanonical topology.
-/
/-
**CategoryTheory.Precoverage.ZeroHypercover.isPullback_of_forall_isPullback** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Precoverage.ZeroHypercover`。
形式化陈述：isPullback_of_forall_isPullback {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) 
(f : X ⟶ Z) (g : Y ⟶ Z) -- TODO: after refactoring `MorphismProperty.IsLocalAtTa
rget` to allow covers -- in an arbitrary universe, replace `v` by an arbitrary u
niverse (𝒰 : Precoverage.ZeroHypercover.{v} J X) (H : forall i, IsPullback (pull
back.snd fst _) (pullback.fst fst (𝒰.f i) ≫ snd) (𝒰.f i ≫ f) g) : IsPullback fst
 snd f g
参数：fst : P ⟶ X；snd : P ⟶ Y；f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用定理 `CategoryTheory.Precoverage.instHasPullbacksOfHasPullbacks`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Precoverage C)  
 [CategoryTheory.Limits.HasPullbacks C], J.HasP…
· 使用引理 `CategoryTheory.Precoverage.ZeroHypercover.hom_ext`：hom_ext {X Y : C} (𝒰 
: J.ZeroHypercover X) {f g : X ⟶ Y} (h : forall i, 𝒰.f i ≫ f = 𝒰.f i ≫ g) : f = 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (E
 : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.iff_of_zeroHypercover`：i
ff_of_zeroHypercover [K.HasPullbacks] : P f ↔ forall i, P (pullback.snd f (𝒰.f i
))
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instIsLocalAtTargetIsomorphism
s`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.
Precoverage C}   [J.toGrothendieck.Subcanonical] [CategoryTheor…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPullback.paste_vert_iff`：paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂
₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ 
⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ …
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Presieve.instHasPullbackOfHasPairwisePullbacksOfArrows`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type v₂} {X : α 
→ C} {B : C} (π : (a : α) → X a ⟶ B)   [(CategoryTheory.Pre…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
To show that
```
P ---> X
|      |
v      v
Y ---> Z
```
is a pullback square, it suffices to check that
```
P ×[X] Uᵢ ---> Uᵢ
   |           |
   v           v
   Y --------> Z
```
is a pullback square for all `Uᵢ` in a cover of `X` for some subcanonical topolo
gy.
-/
lemma isPullback_of_forall_isPullback {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z)
    (g : Y ⟶ Z)
    -- TODO: after refactoring `MorphismProperty.IsLocalAtTarget` to allow covers
    -- in an arbitrary universe, replace `v` by an arbitrary universe
    (𝒰 : Precoverage.ZeroHypercover.{v} J X)
    (H : ∀ i, IsPullback (pullback.snd fst _) (pullback.fst fst (𝒰.f i) ≫ snd) (𝒰.f i ≫ f) g) :
    IsPullback fst snd f g := by
  have h : fst ≫ f = snd ≫ g := (𝒰.pullback₁ fst).hom_ext fun i ↦ by
    simpa [pullback.condition_assoc] using (H i).w
  suffices IsIso (pullback.lift fst snd h) from
    .of_iso_pullback ⟨h⟩ (asIso (pullback.lift _ _ h)) (by simp) (by simp)
  simp_rw [← isomorphisms.iff, IsLocalAtTarget.iff_of_zeroHypercover (P := isomorphisms C)
    (𝒰.pullbackCoverOfLeft f g), isomorphisms.iff]
  intro i
  let m := pullback.map (𝒰.f i ≫ f) g f g (𝒰.f i) (𝟙 Y) (𝟙 Z) (by simp) (by simp)
  have : IsPullback (pullback.fst (𝒰.f i ≫ f) g) m (𝒰.f i) (pullback.fst _ _) := by
    simpa [← IsPullback.paste_vert_iff (.of_hasPullback _ _), m] using .of_hasPullback _ _
  have H' : IsPullback (pullback.fst fst (𝒰.f i))
      (pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ snd)
        (by simp [← h, pullback.condition_assoc]))
      (pullback.lift fst snd h) m := by
    rw [← IsPullback.paste_vert_iff this.flip (by ext <;> simp [m, pullback.condition])]
    simpa using .of_hasPullback _ _
  have heq : pullback.snd (pullback.lift fst snd h) ((𝒰.pullbackCoverOfLeft f g).f i) =
      H'.isoPullback.inv ≫ (H i).isoPullback.hom := by
    rw [Iso.eq_inv_comp]
    cat_disch
  rw [heq]
  infer_instance

end Precoverage.ZeroHypercover

end CategoryTheory

