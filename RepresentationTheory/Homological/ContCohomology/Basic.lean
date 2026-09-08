/-
Copyright (c) 2026 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill, Andrew Yang, Edison Xie
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.RepresentationTheory.Continuous.TopRep

/-!

# Continuous cohomology

We define continuous cohomology as the homology of the homogeneous cochain complex.

## Implementation details

We define homogeneous cochains as `g`-invariant continuous function in `C(G, C(G,...,C(G, M)))`
instead of the usual `C(Gⁿ, M)` to allow more general topological groups other than locally compact
ones. For this to work, we also work in `TopRep k G`, where the `G` action on `M`
is only continuous on `M`, and not necessarily continuous in both variables, because the `G` action
on `C(G, M)` might not be continuous on both variables even if it is on `M`.

For the differential map, instead of a finite sum we use the inductive definition
`d₋₁ : M → C(G, M) := const : m ↦ g ↦ m` and
`dₙ₊₁ : C(G, _) → C(G, C(G, _)) := const - C(G, dₙ) : f ↦ g ↦ f - dₙ (f (g))`
See `TopRep.d`.

## Main definition
- `TopRep.homogeneousCochains`:
  The functor taking an `R`-linear `G`-representation to the complex of homogeneous cochains.
- `continuousCohomology`:
  The functor taking an `R`-linear `G`-representation to its `n`-th continuous cohomology.

## TODO
- Show that it coincides with `groupCohomology` for discrete groups.
- Give the usual description of cochains in terms of `n`-ary functions for locally compact groups.
- Show that short exact sequences induce long exact sequences in certain scenarios.
-/

@[expose] public section

variable {k G : Type*} [Ring k] [Group G] [TopologicalSpace k]
  [TopologicalSpace G] [IsTopologicalGroup G]

open CategoryTheory ContRepresentation Limits

namespace TopRep

/-- The `n`-th term in the resolution of a topological representation induced by `TopRep.coind₁`. -/
/-
**TopRep.resolutionX** 是 Mathlib 中的一个定义，位于命名空间 `TopRep`。
形式化陈述：{k : Type u_1} →   {G : Type u_2} →     [inst : Ring k] →       [inst_1 : 
Group G] →         [inst_2 : TopologicalSpace k] →           [inst_3 : Topologic
alSpace G] → [IsTopologicalGroup G] → TopRep k G → ℕ → TopRep k G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-th term in the resolution of a topological representation induced by `To
pRep.coind₁`.
-/
abbrev resolutionX (X : TopRep k G) : ℕ → TopRep k G
  | 0 => X
  | n + 1 => (resolutionX X n).coind₁

/-- The boundary map in the resolution of a topological representation induced
by `TopRep.coind₁Functor`. -/
/-
**TopRep.d** 是 Mathlib 中的一个定义，位于命名空间 `TopRep`。
形式化陈述：{k : Type u_1} →   {G : Type u_2} →     [inst : Ring k] →       [inst_1 : 
Group G] →         [inst_2 : TopologicalSpace k] →           [inst_3 : Topologic
alSpace G] →             [inst_4 : IsTopologicalGroup G] → (X : TopRep k G) → (n
 : ℕ) → X.resolutionX n ⟶ X.resolutionX (n + 1)
参数：X : TopRep k G；n : ℕ；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The boundary map in the resolution of a topological representation induced
by `TopRep.coind₁Functor`.
-/
def d (X : TopRep k G) : (n : ℕ) → resolutionX X n ⟶ resolutionX X (n + 1)
  | 0 => ofHom X.ρ.coind₁ι
  | n + 1 => ofHom (resolutionX X (n + 1)).ρ.coind₁ι - (coind₁Functor k G).map (d X n)
/-
**TopRep.d_zero** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：d_zero (X : TopRep k G) : d X 0 = ofHom X.ρ.coind₁ι
参数：X : TopRep k G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d_zero (X : TopRep k G) : d X 0 = ofHom X.ρ.coind₁ι := rfl
/-
**TopRep.d_succ** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：d_succ (X : TopRep k G) (n : Nat) : d X (n + 1) = ofHom (resolutionX X (n 
+ 1)).ρ.coind₁ι - (coind₁Functor k G).map (d X n)
参数：X : TopRep k G；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d_succ (X : TopRep k G) (n : ℕ) :
    d X (n + 1) = ofHom (resolutionX X (n + 1)).ρ.coind₁ι - (coind₁Functor k G).map (d X n) :=
  rfl
/-
**TopRep.hom_d_succ** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：hom_d_succ (X : TopRep k G) (n : Nat) : (d X (n + 1)).hom = (resolutionX X
 (n + 1)).ρ.coind₁ι - ContRepresentation.coind₁Map (d X n).hom
参数：X : TopRep k G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
-/
lemma hom_d_succ (X : TopRep k G) (n : ℕ) :
    (d X (n + 1)).hom = (resolutionX X (n + 1)).ρ.coind₁ι -
      ContRepresentation.coind₁Map (d X n).hom :=
  rfl

@[reassoc (attr := simp)]
/-
**TopRep.d_comp_d** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：d_comp_d (X : TopRep k G) (n : Nat) : d X n ≫ d X (n + 1) = 0
参数：X : TopRep k G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : TopologicalSpace k] 
[inst_1 : Ring k] [inst_2 : Monoid G] {A B : TopRep k G}   {f g : A ⟶ B}, TopRep
.Hom…
· 使用引理 `ContIntertwiningMap.ext`：ext {π₁ : ContRepresentation R G V} {π₂ : ContR
epresentation R G W} {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toConti
nuousLinearMa…
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousMap.instIsTopologicalAddGroup`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : AddCommGrou
p β]   [inst_3 : IsTopologica…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `ContinuousMap.instContinuousSMul`：∀ {α : Type u_1} [inst : TopologicalSp
ace α] {R : Type u_3} {M : Type u_5} [inst_1 : TopologicalSpace M]   [inst_2 : T
opologicalSpace R] [in…
· 使用定理 `TopRep.hV5`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   ContinuousSMul k ↑self
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `ContRepresentation.coind₁ι_toFun`：∀ {R : Type u_1} {V : Type u_3} [inst 
: Ring R] [inst_1 : AddCommGroup V] [inst_2 : TopologicalSpace V]   [inst_3 : Is
TopologicalAddGroup V]…
· 使用定理 `ContRepresentation.coind₁Map_toFun`：∀ {R : Type u_1} {V : Type u_3} {W :
 Type u_4} [inst : Ring R] [inst_1 : AddCommGroup V] [inst_2 : TopologicalSpace 
V]   [inst_3 : IsTopolog…
· 使用定理 `ContinuousMap.comp_const`：comp_const (f : C(β, γ)) (b : β) : f.comp (con
st α b) = const α (f b)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `TopRep.d_succ`：d_succ (X : TopRep k G) (n : Nat) : d X (n + 1) = ofHom (
resolutionX X (n + 1)).ρ.coind₁ι - (coind₁Functor k G).map (d X n)
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 36 条，此处仅展示前 30 条）
-/
lemma d_comp_d (X : TopRep k G) (n : ℕ) : d X n ≫ d X (n + 1) = 0 := by
  induction n with
  | zero =>
    ext
    simp [d_succ, ContIntertwiningMap.toContinuousLinearMap_apply, d_zero, hom_sub]
  | succ n ih =>
    rw [d_succ _ (n + 1), Preadditive.comp_sub]
    nth_rw 2 [d_succ]
    rw [Preadditive.sub_comp, ← Functor.map_comp, ih, Functor.map_zero, sub_zero, sub_eq_zero]
    rfl

/-- The complex of functors whose behaviour pointwise takes an `R`-linear `G`-representation `M`
to the complex `M → C(G, M) → ⋯ → C(G, C(G,...,C(G, M))) → ⋯`
The `G`-invariant submodules of it is the homogeneous cochains (shifted by one). -/
/-
**TopRep.resolution** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopRep`。
形式化陈述：resolution (X : TopRep k G) : CochainComplex (TopRep k G) Nat
参数：X : TopRep k G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `TopRep.d_comp_d`：d_comp_d (X : TopRep k G) (n : Nat) : d X n ≫ d X (n + 
1) = 0

--- 原说明 ---
The complex of functors whose behaviour pointwise takes an `R`-linear `G`-repres
entation `M`
to the complex `M → C(G, M) → ⋯ → C(G, C(G,...,C(G, M))) → ⋯`
The `G`-invariant submodules of it is the homogeneous cochains (shifted by one).
-/
abbrev resolution (X : TopRep k G) : CochainComplex (TopRep k G) ℕ :=
  CochainComplex.of (resolutionX X) (d X) (d_comp_d X)

/-- The shifted object in resolution by `1` degree. -/
/-
**TopRep.resolution'X** 是 Mathlib 中的一个定义，位于命名空间 `TopRep`。
形式化陈述：{k : Type u_1} →   {G : Type u_2} →     [inst : Ring k] →       [inst_1 : 
Group G] →         [inst_2 : TopologicalSpace k] →           [inst_3 : Topologic
alSpace G] → [IsTopologicalGroup G] → TopRep k G → ℕ → TopRep k G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shifted object in resolution by `1` degree.
-/
abbrev resolution'X (X : TopRep k G) (n : ℕ) : TopRep k G := resolutionX X (n + 1)

/-- The shifted boundary map of the resolution. -/
@[implicit_reducible]
/-
**TopRep.resolution'd** 是 Mathlib 中的一个定义，位于命名空间 `TopRep`。
形式化陈述：{k : Type u_1} →   {G : Type u_2} →     [inst : Ring k] →       [inst_1 : 
Group G] →         [inst_2 : TopologicalSpace k] →           [inst_3 : Topologic
alSpace G] →             [inst_4 : IsTopologicalGroup G] → (X : TopRep k G) → (n
 : ℕ) → X.resolution'X n ⟶ X.resolution'X (n + 1)
参数：X : TopRep k G；n : ℕ；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shifted boundary map of the resolution.
-/
def resolution'd (X : TopRep k G) (n : ℕ) :
    resolution'X X n ⟶ resolution'X X (n + 1) := d X (n + 1)
/-
**TopRep.resolution'd_eq** 是 Mathlib 中的一个定理，位于命名空间 `TopRep`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : Ring k] [inst_1 : Group G] [inst_2
 : TopologicalSpace k]   [inst_3 : TopologicalSpace G] [inst_4 : IsTopologicalGr
oup G] (X : TopRep k G) (n : ℕ), X.resolution'd n = X.d (n + 1)
参数：X : TopRep k G；n : ℕ；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma resolution'd_eq (X : TopRep k G) (n : ℕ) :
    resolution'd X n = d X (n + 1) := rfl

/-- The shifted resolution of a topological representation by `1` degree. -/
/-
**TopRep.resolution'** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopRep`。
形式化陈述：resolution'X (X : TopRep k G) (n : Nat) : TopRep k G
参数：X : TopRep k G；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shifted resolution of a topological representation by `1` degree.
-/
abbrev resolution' (X : TopRep k G) : CochainComplex (TopRep k G) ℕ :=
  CochainComplex.of (resolution'X X)
    (resolution'd X) (fun n ↦ d_comp_d X (n + 1))

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

/-- The homogeneous cochains of a topological representation. -/
/-
**TopRep.homogeneousCochains** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopRep`。
形式化陈述：homogeneousCochains (X : TopRep k G) : CochainComplex (TopModuleCat k) Nat
参数：X : TopRep k G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homogeneous cochains of a topological representation.
-/
abbrev homogeneousCochains (X : TopRep k G) :
    CochainComplex (TopModuleCat k) ℕ :=
  ((invariantsFunctor k G).mapHomologicalComplex _).obj (resolution' X)
/-
**TopRep.homogeneousCochains.d_eq** 是 Mathlib 中的一个定理，位于命名空间 `TopRep.homogeneousC
ochains`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : Ring k] [inst_1 : Group G] [inst_2
 : TopologicalSpace k]   [inst_3 : TopologicalSpace G] [inst_4 : IsTopologicalGr
oup G] (X : TopRep k G) (i : ℕ),   X.homogeneousCochains.d i (i + 1) = (TopRep.i
nvariantsFunctor k G).map (X.d (i + 1))
参数：X : TopRep k G；i : ℕ；i + 1；TopRep.invariantsFunctor k G；X.d (i + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopRep.resolution'd_eq`：∀ {k : Type u_1} {G : Type u_2} [inst : Ring k] 
[inst_1 : Group G] [inst_2 : TopologicalSpace k]   [inst_3 : TopologicalSpace G]
 [inst_4 : I…
· 使用定理 `CochainComplex.of_d`：of_d (j : α) : of.d X d j (j + 1) = d j
-/
lemma homogeneousCochains.d_eq (X : TopRep k G) (i : ℕ) :
    (homogeneousCochains X).d i (i + 1) =
      (invariantsFunctor k G).map (d X (i + 1)) := by
  dsimp only
  rw [← resolution'd_eq, CochainComplex.of_d]
/-
**TopRep.homogeneousCochains.d_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopRep.homogeneo
usCochains`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : Ring k] [inst_1 : Group G] [inst_2
 : TopologicalSpace k]   [inst_3 : TopologicalSpace G] [inst_4 : IsTopologicalGr
oup G] (X : TopRep k G) (i : ℕ)   (σ : ↑(X.homogeneousCochains.X i).toModuleCat)
,   ↑((TopModuleCat.Hom.hom (X.homogeneousCochains.d i (i + 1))) σ) = (TopRep.Ho
m.hom (X.d (i + 1))) ↑σ
参数：X : TopRep k G；i : ℕ；σ : ↑(X.homogeneousCochains.X i).toModuleCat；(TopModuleC
at.Hom.hom (X.homogeneousCochains.d i (i + 1))) σ；TopRep.Hom.hom (X.d (i + 1))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopRep.homogeneousCochains.d_eq`：∀ {k : Type u_1} {G : Type u_2} [inst :
 Ring k] [inst_1 : Group G] [inst_2 : TopologicalSpace k]   [inst_3 : Topologica
lSpace G] [inst_4 : I…
-/
lemma homogeneousCochains.d_apply (X : TopRep k G) (i : ℕ)
    (σ : (homogeneousCochains X).X i) :
    ((homogeneousCochains X).d i (i + 1)).hom σ = (d X (i + 1)).hom σ := by
  rw [homogeneousCochains.d_eq]
  dsimp [ContIntertwiningMap.mapInvariants_apply]

/-- The continuous cohomology of a continuous representation defined by taking homology
of the homogeneous cochains. -/
/-
**TopRep._root_.continuousCohomology** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous cohomology of a continuous representation defined by taking homol
ogy
of the homogeneous cochains.
-/
noncomputable abbrev _root_.continuousCohomology (n : ℕ) (A : TopRep k G) :
    TopModuleCat k := (homogeneousCochains A).homology n

end TopRep

namespace ContinuousCohomology

open TopRep

/-- The `n`-cocycles `Zⁿ(G, A)` of a `k`-linear `G`-representation `A`, i.e. the kernel of the
`n`th differential in the complex of homogeneous cochains. -/
/-
**ContinuousCohomology.cocycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `ContinuousCohomolog
y`。
形式化陈述：cocycles (A : TopRep k G) (n : Nat) : TopModuleCat k
参数：A : TopRep k G；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-cocycles `Zⁿ(G, A)` of a `k`-linear `G`-representation `A`, i.e. the ker
nel of the
`n`th differential in the complex of homogeneous cochains.
-/
noncomputable abbrev cocycles (A : TopRep k G) (n : ℕ) :
    TopModuleCat k := (homogeneousCochains A).cycles n

/-- The natural map from `n`-cocycles to `n`th continuous cohomology for a `k`-linear
`G`-representation `A`. -/
/-
**ContinuousCohomology.** 是 Mathlib 中的一个缩写定义，位于命名空间 `ContinuousCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map from `n`-cocycles to `n`th continuous cohomology for a `k`-linea
r
`G`-representation `A`.
-/
noncomputable abbrev π (A : TopRep k G) (n : ℕ) := (homogeneousCochains A).homologyπ n

end ContinuousCohomology

