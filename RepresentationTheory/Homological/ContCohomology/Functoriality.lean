/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Richard Hill
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Functoriality of continuous cohomology

Given topological groups `G` and `H`, a continuous group homomorphism `φ : H →ₜ* G`, a topological
representation `X` of `G`, a topological representation `Y` of `H`, and a morphism of topological
`H`-representations `f : res φ X ⟶ Y`, we construct a cochain map
`homogeneousCochains X ⟶ homogeneousCochains Y` and hence maps on continuous cohomology
`Hⁿ(G, X) ⟶ Hⁿ(H, Y)`.

## Main definitions

* `ContinuousCohomology.cochainsMap φ f` : the cochain map
  `homogeneousCochains X ⟶ homogeneousCochains Y` induced by `φ : H →ₜ* G` and
  `f : res φ X ⟶ Y`, sending an invariant function `σ : C(G, C(G, ⋯))` to `f ∘ σ ∘ φ`.
* `ContinuousCohomology.map φ f n` : the induced map `Hⁿ(G, X) ⟶ Hⁿ(H, Y)` on continuous
  cohomology.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace ContinuousCohomology

open TopRep ContRepresentation

variable {k : Type u} {G H K : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  {X : TopRep k G} {Y : TopRep k H} {Z : TopRep k K}

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

/-- The morphisms between the levels of the standard resolutions of `X` and `Y` induced by a
continuous group homomorphism `φ : H →ₜ* G` and a morphism `f : res φ X ⟶ Y`, given by
`F ↦ f ∘ F ∘ φ`. -/
/-
**ContinuousCohomology.resolutionMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousCohomo
logy`。
形式化陈述：{k : Type u} →   {G H : Type v} →     [inst : Ring k] →       [inst_1 : To
pologicalSpace k] →         [inst_2 : Group G] →           [inst_3 : Topological
Space G] →             [inst_4 : IsTopologicalGroup G] →               [inst_5 :
 Group H] →                 [inst_6 : TopologicalSpace H] →                   [i
nst_7 : IsTopologicalGroup H] →                     {X : TopRep k G} →          
             {Y : TopRep k H} →                         (φ : H →ₜ* G) →         
                  (TopRep.res (↑φ) X ⟶ Y) → (i : ℕ) → TopRep.res (↑φ) (X.resolut
ionX i) ⟶ Y.resolutionX i
参数：φ : H →ₜ* G；TopRep.res (↑φ) X ⟶ Y；i : ℕ；↑φ；X.resolutionX i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphisms between the levels of the standard resolutions of `X` and `Y` indu
ced by a
continuous group homomorphism `φ : H →ₜ* G` and a morphism `f : res φ X ⟶ Y`, gi
ven by
`F ↦ f ∘ F ∘ φ`.
-/
def resolutionMap (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    (i : ℕ) → res φ (resolutionX X i) ⟶ resolutionX Y i
  | 0 => f
  | i + 1 => ofHom (coind₁ResMap φ (resolutionMap φ f i).hom)

@[simp]
/-
**ContinuousCohomology.resolutionMap_zero** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousC
ohomology`。
形式化陈述：resolutionMap_zero (φ : H ->ₜ* G) (f : res φ X ⟶ Y) : resolutionMap φ f 0 
= f
参数：φ : H ->ₜ* G；f : res φ X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma resolutionMap_zero (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    resolutionMap φ f 0 = f := rfl
/-
**ContinuousCohomology.resolutionMap_succ** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousC
ohomology`。
形式化陈述：resolutionMap_succ (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (i : Nat) : resolution
Map φ f (i + 1) = ofHom (coind₁ResMap φ (resolutionMap φ f i).hom)
参数：φ : H ->ₜ* G；f : res φ X ⟶ Y；i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma resolutionMap_succ (φ : H →ₜ* G) (f : res φ X ⟶ Y) (i : ℕ) :
    resolutionMap φ f (i + 1) = ofHom (coind₁ResMap φ (resolutionMap φ f i).hom) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ContinuousCohomology.resolutionMap_id** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousCoh
omology`。
形式化陈述：resolutionMap_id (X : TopRep k G) (i : Nat) : resolutionMap (ContinuousMon
oidHom.id G) (𝟙 X) i = 𝟙 (resolutionX X i)
参数：X : TopRep k G；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `TopRep.hV5`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   ContinuousSMul k ↑self
· 使用定理 `ContinuousMap.instIsTopologicalAddGroup`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : AddCommGrou
p β]   [inst_3 : IsTopologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousCohomology.resolutionMap_succ`：resolutionMap_succ (φ : H ->ₜ* 
G) (f : res φ X ⟶ Y) (i : Nat) : resolutionMap φ f (i + 1) = ofHom (coind₁ResMap
 φ (resolutionMap φ f i).hom)
· 使用定理 `TopRep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : TopologicalSpace k] 
[inst_1 : Ring k] [inst_2 : Monoid G] {A B : TopRep k G}   {f g : A ⟶ B}, TopRep
.Hom…
· 使用引理 `ContIntertwiningMap.ext`：ext {π₁ : ContRepresentation R G V} {π₂ : ContR
epresentation R G W} {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toConti
nuousLinearMa…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
-/
lemma resolutionMap_id (X : TopRep k G) (i : ℕ) :
    resolutionMap (ContinuousMonoidHom.id G) (𝟙 X) i = 𝟙 (resolutionX X i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ, ih]
    ext F x
    rfl
/-
**ContinuousCohomology.resolutionMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousC
ohomology`。
形式化陈述：resolutionMap_comp (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : re
s ψ Y ⟶ Z) (i : Nat) : resolutionMap (φ.comp ψ) (X
参数：φ : H ->ₜ* G；ψ : K ->ₜ* H；f : res φ X ⟶ Y；g : res ψ Y ⟶ Z；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `TopRep.hV5`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   ContinuousSMul k ↑self
· 使用定理 `ContinuousMap.instIsTopologicalAddGroup`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : AddCommGrou
p β]   [inst_3 : IsTopologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousCohomology.resolutionMap_succ`：resolutionMap_succ (φ : H ->ₜ* 
G) (f : res φ X ⟶ Y) (i : Nat) : resolutionMap φ f (i + 1) = ofHom (coind₁ResMap
 φ (resolutionMap φ f i).hom)
· 使用定理 `TopRep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : TopologicalSpace k] 
[inst_1 : Ring k] [inst_2 : Monoid G] {A B : TopRep k G}   {f g : A ⟶ B}, TopRep
.Hom…
· 使用引理 `ContIntertwiningMap.ext`：ext {π₁ : ContRepresentation R G V} {π₂ : ContR
epresentation R G W} {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toConti
nuousLinearMa…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
-/
lemma resolutionMap_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
    (i : ℕ) :
    resolutionMap (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) i =
      (resFunctor (ψ : K →* H)).map (resolutionMap φ f i) ≫ resolutionMap ψ g i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ, resolutionMap_succ, resolutionMap_succ, ih]
    ext F x
    rfl

/-- The maps `resolutionMap φ f` commute with the differentials of the resolutions. -/
/-
**ContinuousCohomology.resolutionMap_comp_d** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sCohomology`。
形式化陈述：resolutionMap_comp_d (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (i : Nat) : resoluti
onMap φ f i ≫ d Y i = (resFunctor (φ : H ->* G)).map (d X i) ≫ resolutionMap φ f
 (i + 1)
参数：φ : H ->ₜ* G；f : res φ X ⟶ Y；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : TopologicalSpace k] 
[inst_1 : Ring k] [inst_2 : Monoid G] {A B : TopRep k G}   {f g : A ⟶ B}, TopRep
.Hom…
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.instContinuousSMul`：∀ {α : Type u_1} [inst : TopologicalSp
ace α] {R : Type u_3} {M : Type u_5} [inst_1 : TopologicalSpace M]   [inst_2 : T
opologicalSpace R] [in…
· 使用定理 `TopRep.hV5`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   ContinuousSMul k ↑self
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ContIntertwiningMap.sub_comp`：sub_comp (f g : π₂ ->ⁱL π₃) (h : π₁ ->ⁱL π
₂) : (f - g).comp h = f.comp h - g.comp h
· 使用引理 `ContIntertwiningMap.comp_sub`：comp_sub (f : π₂ ->ⁱL π₃) (g h : π₁ ->ⁱL π
₂) : f.comp (g - h) = f.comp g - f.comp h
· 使用定理 `ContinuousMap.instIsTopologicalAddGroup`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : AddCommGrou
p β]   [inst_3 : IsTopologica…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContRepresentation.coind₁ResMap_comp_coind₁ι_restrict`：coind₁ResMap_comp
_coind₁ι_restrict (φ : H ->ₜ* G) (f : π.restrict (φ : H ->* G) ->ⁱL π') : (coind
₁ResMap φ f).comp (π.coind₁ι.restrict (φ : …

--- 原说明 ---
The maps `resolutionMap φ f` commute with the differentials of the resolutions.
-/
lemma resolutionMap_comp_d (φ : H →ₜ* G) (f : res φ X ⟶ Y) (i : ℕ) :
    resolutionMap φ f i ≫ d Y i =
      (resFunctor (φ : H →* G)).map (d X i) ≫ resolutionMap φ f (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    ext : 1
    replace ih := congr($(ih).hom)
    simp only [TopRep.hom_comp, resolutionMap_succ, TopRep.hom_ofHom, hom_d_succ,
      ContIntertwiningMap.restrict_sub, ContIntertwiningMap.sub_comp,
      ContIntertwiningMap.comp_sub, coind₁Map_comp_coind₁ResMap,
      coind₁ResMap_comp_coind₁Map_restrict] at ih ⊢
    rw [ih, ← coind₁ResMap_comp_coind₁ι_restrict]

/-- The cochain map `homogeneousCochains X ⟶ homogeneousCochains Y` induced by a continuous
group homomorphism `φ : H →ₜ* G` and a morphism of topological `H`-representations
`f : res φ X ⟶ Y`, sending an invariant function `σ : C(G, C(G, ⋯))` to `f ∘ σ ∘ φ`. -/
@[simps! -isSimp f f_hom]
/-
**ContinuousCohomology.cochainsMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousCohomolo
gy`。
形式化陈述：cochainsMap (φ : H ->ₜ* G) (f : res φ X ⟶ Y) : homogeneousCochains X ⟶ hom
ogeneousCochains Y where f i
参数：φ : H ->ₜ* G；f : res φ X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cochain map `homogeneousCochains X ⟶ homogeneousCochains Y` induced by a con
tinuous
group homomorphism `φ : H →ₜ* G` and a morphism of topological `H`-representatio
ns
`f : res φ X ⟶ Y`, sending an invariant function `σ : C(G, C(G, ⋯))` to `f ∘ σ ∘
 φ`.
-/
def cochainsMap (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    homogeneousCochains X ⟶ homogeneousCochains Y where
  f i := invariantsResMap φ (resolutionMap φ f (i + 1))
  comm' i j (hij : _ = _) := by
    subst hij
    rw [homogeneousCochains.d_eq, homogeneousCochains.d_eq, ← invariantsResMap_comp,
      resolutionMap_comp_d, invariantsResMap_map_comp]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ContinuousCohomology.cochainsMap_id** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousCohom
ology`。
形式化陈述：cochainsMap_id (X : TopRep k G) : cochainsMap (ContinuousMonoidHom.id G) (
𝟙 X) = 𝟙 (homogeneousCochains X)
参数：X : TopRep k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousCohomology.cochainsMap_f`：∀ {k : Type u} {G H : Type v} [inst 
: Ring k] [inst_1 : TopologicalSpace k] [inst_2 : Group G]   [inst_3 : Topologic
alSpace G] [inst_4 : IsT…
· 使用引理 `ContinuousCohomology.resolutionMap_id`：resolutionMap_id (X : TopRep k G)
 (i : Nat) : resolutionMap (ContinuousMonoidHom.id G) (𝟙 X) i = 𝟙 (resolutionX X
 i)
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
-/
lemma cochainsMap_id (X : TopRep k G) :
    cochainsMap (ContinuousMonoidHom.id G) (𝟙 X) = 𝟙 (homogeneousCochains X) := by
  ext i : 1
  rw [cochainsMap_f, resolutionMap_id]
  ext v
  rfl

@[reassoc]
/-
**ContinuousCohomology.cochainsMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousCoh
omology`。
形式化陈述：cochainsMap_comp (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res 
ψ Y ⟶ Z) : cochainsMap (φ.comp ψ) (X
参数：φ : H ->ₜ* G；ψ : K ->ₜ* H；f : res φ X ⟶ Y；g : res ψ Y ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
· 使用引理 `ContinuousCohomology.resolutionMap_comp`：resolutionMap_comp (φ : H ->ₜ* 
G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z) (i : Nat) : resolutionMap 
(φ.comp ψ) (X
-/
lemma cochainsMap_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z) :
    cochainsMap (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) =
      cochainsMap φ f ≫ cochainsMap ψ g := by
  ext i v x
  exact congr($(resolutionMap_comp φ ψ f g (i + 1)).hom v.1 x)

/-- The map `Zⁿ(G, X) ⟶ Zⁿ(H, Y)` on cocycles induced by a continuous group homomorphism
`φ : H →ₜ* G` and a morphism of topological `H`-representations `f : res φ X ⟶ Y`. -/
/-
**ContinuousCohomology.cocyclesMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `ContinuousCohomo
logy`。
形式化陈述：cocyclesMap (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (n : Nat) : cocycles X n ⟶ co
cycles Y n
参数：φ : H ->ₜ* G；f : res φ X ⟶ Y；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Zⁿ(G, X) ⟶ Zⁿ(H, Y)` on cocycles induced by a continuous group homomorp
hism
`φ : H →ₜ* G` and a morphism of topological `H`-representations `f : res φ X ⟶ Y
`.
-/
noncomputable abbrev cocyclesMap (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    cocycles X n ⟶ cocycles Y n :=
  HomologicalComplex.cyclesMap (cochainsMap φ f) n

@[simp]
/-
**ContinuousCohomology.cocyclesMap_id** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousCohom
ology`。
形式化陈述：cocyclesMap_id (X : TopRep k G) (n : Nat) : cocyclesMap (ContinuousMonoidH
om.id G) (𝟙 X) n = 𝟙 _
参数：X : TopRep k G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ContinuousCohomology.cochainsMap_id`：cochainsMap_id (X : TopRep k G) : c
ochainsMap (ContinuousMonoidHom.id G) (𝟙 X) = 𝟙 (homogeneousCochains X)
· 使用引理 `HomologicalComplex.cyclesMap_id`：cyclesMap_id : cyclesMap (𝟙 K) i = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cocyclesMap_id (X : TopRep k G) (n : ℕ) :
    cocyclesMap (ContinuousMonoidHom.id G) (𝟙 X) n = 𝟙 _ := by
  simp [cocyclesMap]

@[reassoc]
/-
**ContinuousCohomology.cocyclesMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousCoh
omology`。
形式化陈述：cocyclesMap_comp (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res 
ψ Y ⟶ Z) (n : Nat) : cocyclesMap (φ.comp ψ) (X
参数：φ : H ->ₜ* G；ψ : K ->ₜ* H；f : res φ X ⟶ Y；g : res ψ Y ⟶ Z；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cocyclesMap_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
    (n : ℕ) :
    cocyclesMap (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) n =
      cocyclesMap φ f n ≫ cocyclesMap ψ g n := by
  simp [cocyclesMap, ← HomologicalComplex.cyclesMap_comp, ← cochainsMap_comp]

/-- The map `Hⁿ(G, X) ⟶ Hⁿ(H, Y)` on continuous cohomology induced by a continuous group
homomorphism `φ : H →ₜ* G` and a morphism of topological `H`-representations
`f : res φ X ⟶ Y`. -/
/-
**ContinuousCohomology.map** 是 Mathlib 中的一个缩写定义，位于命名空间 `ContinuousCohomology`。
形式化陈述：map (φ : H ->ₜ* G) (f : res φ X ⟶ Y) (n : Nat) : continuousCohomology n X 
⟶ continuousCohomology n Y
参数：φ : H ->ₜ* G；f : res φ X ⟶ Y；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Hⁿ(G, X) ⟶ Hⁿ(H, Y)` on continuous cohomology induced by a continuous g
roup
homomorphism `φ : H →ₜ* G` and a morphism of topological `H`-representations
`f : res φ X ⟶ Y`.
-/
noncomputable abbrev map (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    continuousCohomology n X ⟶ continuousCohomology n Y :=
  HomologicalComplex.homologyMap (cochainsMap φ f) n

@[reassoc]
/-
**ContinuousCohomology.** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_map (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    π X n ≫ map φ f n = cocyclesMap φ f n ≫ π Y n := by
  simp [map, cocyclesMap]

@[simp]
/-
**ContinuousCohomology.map_id** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousCohomology`。
形式化陈述：map_id (X : TopRep k G) (n : Nat) : map (ContinuousMonoidHom.id G) (𝟙 X) n
 = 𝟙 _
参数：X : TopRep k G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ContinuousCohomology.cochainsMap_id`：cochainsMap_id (X : TopRep k G) : c
ochainsMap (ContinuousMonoidHom.id G) (𝟙 X) = 𝟙 (homogeneousCochains X)
· 使用引理 `HomologicalComplex.homologyMap_id`：homologyMap_id : homologyMap (𝟙 K) i 
= 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id (X : TopRep k G) (n : ℕ) :
    map (ContinuousMonoidHom.id G) (𝟙 X) n = 𝟙 _ := by
  simp [map]

@[reassoc]
/-
**ContinuousCohomology.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousCohomology`
。
形式化陈述：map_comp (φ : H ->ₜ* G) (ψ : K ->ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
 (n : Nat) : map (φ.comp ψ) (X
参数：φ : H ->ₜ* G；ψ : K ->ₜ* H；f : res φ X ⟶ Y；g : res ψ Y ⟶ Z；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z) (n : ℕ) :
    map (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) n = map φ f n ≫ map ψ g n := by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← cochainsMap_comp]

end ContinuousCohomology

