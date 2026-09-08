/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.RepresentationTheory.Rep.Iso

/-!
# The standard and bar resolutions of `k` as a trivial `k`-linear `G`-representation

Given a commutative ring `k` and a group `G`, this file defines two projective resolutions of `k`
as a trivial `k`-linear `G`-representation.

The first one, the standard resolution, has objects `k[Gⁿ⁺¹]` equipped with the diagonal
representation, and differential defined by `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`.

We define this as the alternating face map complex associated to an appropriate simplicial
`k`-linear `G`-representation. This simplicial object is the `linearization` of the simplicial
`G`-set given by the universal cover of the classifying space of `G`, `EG`. We prove this
simplicial `G`-set `EG` is isomorphic to the Čech nerve of the natural arrow of `G`-sets
`G ⟶ {pt}`.

We then use this isomorphism to deduce that as a complex of `k`-modules, the standard resolution
of `k` as a trivial `G`-representation is homotopy equivalent to the complex with `k` at 0 and 0
elsewhere.

Putting this material together allows us to define `Rep.standardResolution`, the
standard projective resolution of `k` as a trivial `k`-linear `G`-representation.

We then construct the bar resolution. The `n`th object in this complex is the representation on
`Gⁿ →₀ k[G]` defined pointwise by the left regular representation on `k[G]`. The differentials are
defined by sending `(g₀, ..., gₙ)` to
`g₀·(g₁, ..., gₙ) + ∑ (-1)ʲ⁺¹·(g₀, ..., gⱼgⱼ₊₁, ..., gₙ) + (-1)ⁿ⁺¹·(g₀, ..., gₙ₋₁)` for
`j = 0, ..., n - 1`.

In `RepresentationTheory.Rep` we define an isomorphism `Rep.diagonalSuccIsoFree` between
`k[Gⁿ⁺¹] ≅ (Gⁿ →₀ k[G])` sending `(g₀, ..., gₙ) ↦ g₀·(g₀⁻¹g₁, ..., gₙ₋₁⁻¹gₙ)`.
We show that this isomorphism defines a commutative square with the bar resolution differential and
the standard resolution differential, and thus conclude that the bar resolution differential
squares to zero and that `Rep.diagonalSuccIsoFree` defines an isomorphism between the two
complexes. We carry the exactness properties across this isomorphism to conclude the bar resolution
is a projective resolution too, in `Rep.barResolution`.

In `Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean` and
`Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`, we then use
`Rep.barResolution` to define the inhomogeneous (co)chains of a representation, useful for
computing group (co)homology.

## Main definitions

* `groupCohomology.resolution.ofMulActionBasis`
* `classifyingSpaceUniversalCover`
* `Rep.standardComplex.forget₂ToModuleCatHomotopyEquiv`
* `Rep.standardResolution`

TODO: There's bad DefEq abuses in `Action` and the way we do `Rep.standardComplex` should be
  unified with continuous cohomology, therefore we should remove the use of `Action` in `Rep` which
  would remove all the unification hints in this file.
-/

@[expose] public noncomputable section

suppress_compilation

open CategoryTheory Finsupp
open scoped MonoidAlgebra

universe u v w

variable {k G : Type u} [CommRing k] {n : ℕ}

local notation "Gⁿ" => Fin n → G

set_option quotPrecheck false
local notation "Gⁿ⁺¹" => Fin (n + 1) → G

variable (G)

/-- The simplicial `G`-set sending `[n]` to `Gⁿ⁺¹` equipped with the diagonal action of `G`. -/
@[simps obj map]
/-
**classifyingSpaceUniversalCover** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：classifyingSpaceUniversalCover [Monoid G] : SimplicialObject (Action (Type
 u) G) where obj n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The simplicial `G`-set sending `[n]` to `Gⁿ⁺¹` equipped with the diagonal action
 of `G`.
-/
def classifyingSpaceUniversalCover [Monoid G] :
    SimplicialObject (Action (Type u) G) where
  obj n := Action.ofMulAction G (Fin (n.unop.len + 1) → G)
  map f :=
    { hom := ↾fun x => x ∘ f.unop.toOrderHom
      comm := fun _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

namespace classifyingSpaceUniversalCover

open CategoryTheory.Limits

variable [Monoid G]

set_option backward.isDefEq.respectTransparency false in
/-- When the category is `G`-Set, `cechNerveTerminalFrom` of `G` with the left regular action is
isomorphic to `EG`, the universal cover of the classifying space of `G` as a simplicial `G`-set. -/
/-
**classifyingSpaceUniversalCover.cechNerveTerminalFromIso** 是 Mathlib 中的一个定义，位于命
名空间 `classifyingSpaceUniversalCover`。
形式化陈述：cechNerveTerminalFromIso : cechNerveTerminalFrom (Action.ofMulAction G (G)
) ≅ classifyingSpaceUniversalCover G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the category is `G`-Set, `cechNerveTerminalFrom` of `G` with the left regul
ar action is
isomorphic to `EG`, the universal cover of the classifying space of `G` as a sim
plicial `G`-set.
-/
def cechNerveTerminalFromIso : cechNerveTerminalFrom (Action.ofMulAction G (G)) ≅
    classifyingSpaceUniversalCover G :=
  NatIso.ofComponents (fun _ => limit.isoLimitCone (Action.ofMulActionLimitCone _ _)) fun f => by
    refine IsLimit.hom_ext (Action.ofMulActionLimitCone.{u, 0} G fun _ => G).2 fun j => ?_
    dsimp only [cechNerveTerminalFrom, Pi.lift]
    rw [Category.assoc, limit.isoLimitCone_hom_π, limit.lift_π, Category.assoc]
    exact (limit.isoLimitCone_hom_π _ _).symm

/-- As a simplicial set, `cechNerveTerminalFrom` of a monoid `G` is isomorphic to the universal
cover of the classifying space of `G` as a simplicial set. -/
/-
**classifyingSpaceUniversalCover.cechNerveTerminalFromIsoCompForget** 是 Mathlib 
中的一个定义，位于命名空间 `classifyingSpaceUniversalCover`。
形式化陈述：cechNerveTerminalFromIsoCompForget : cechNerveTerminalFrom G ≅ classifying
SpaceUniversalCover G ⋙ forget _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…

--- 原说明 ---
As a simplicial set, `cechNerveTerminalFrom` of a monoid `G` is isomorphic to th
e universal
cover of the classifying space of `G` as a simplicial set.
-/
def cechNerveTerminalFromIsoCompForget :
    cechNerveTerminalFrom G ≅ classifyingSpaceUniversalCover G ⋙ forget _ := by
  refine NatIso.ofComponents (fun _ => Types.productIso _) fun _ => ?_
  ext : 2
  exact Matrix.ext fun _ _ => Pi.lift_π_apply (f := fun _ ↦ G) _ _ _

variable (k)

open AlgebraicTopology SimplicialObject.Augmented SimplicialObject CategoryTheory.Arrow

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `Fin 1 → G` to the terminal object in `Type u`. -/
/-
**classifyingSpaceUniversalCover.compForgetAugmented** 是 Mathlib 中的一个定义，位于命名空间 `
classifyingSpaceUniversalCover`。
形式化陈述：compForgetAugmented : SimplicialObject.Augmented (Type u)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal cover of the classifying space of `G` as a simplicial set, augment
ed by the map
from `Fin 1 → G` to the terminal object in `Type u`.
-/
def compForgetAugmented : SimplicialObject.Augmented (Type u) :=
  SimplicialObject.augment (classifyingSpaceUniversalCover G ⋙ forget _) (terminal _)
    (terminal.from _) fun _ _ _ => Subsingleton.elim _ _

set_option backward.defeqAttrib.useBackward true in
/-- The augmented Čech nerve of the map from `Fin 1 → G` to the terminal object in `Type u` has an
extra degeneracy. -/
/-
**classifyingSpaceUniversalCover.extraDegeneracyAugmentedCechNerve** 是 Mathlib 中
的一个定义，位于命名空间 `classifyingSpaceUniversalCover`。
形式化陈述：extraDegeneracyAugmentedCechNerve : ExtraDegeneracy (Arrow.mk <| terminal.
from G).augmentedCechNerve
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The augmented Čech nerve of the map from `Fin 1 → G` to the terminal object in `
Type u` has an
extra degeneracy.
-/
def extraDegeneracyAugmentedCechNerve :
    ExtraDegeneracy (Arrow.mk <| terminal.from G).augmentedCechNerve :=
  AugmentedCechNerve.extraDegeneracy (Arrow.mk <| terminal.from G)
    ⟨↾fun _ => (1 : G), by cat_disch⟩

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `Fin 1 → G` to the terminal object in `Type u`, has an extra degeneracy. -/
/-
**classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmented** 是 Mathlib 
中的一个定义，位于命名空间 `classifyingSpaceUniversalCover`。
形式化陈述：extraDegeneracyCompForgetAugmented : ExtraDegeneracy (compForgetAugmented 
G)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…

--- 原说明 ---
The universal cover of the classifying space of `G` as a simplicial set, augment
ed by the map
from `Fin 1 → G` to the terminal object in `Type u`, has an extra degeneracy.
-/
def extraDegeneracyCompForgetAugmented : ExtraDegeneracy (compForgetAugmented G) := by
  refine
    ExtraDegeneracy.ofIso (?_ : (Arrow.mk <| terminal.from G).augmentedCechNerve ≅ _)
      (extraDegeneracyAugmentedCechNerve G)
  exact
    Comma.isoMk (CechNerveTerminalFrom.iso G ≪≫ cechNerveTerminalFromIsoCompForget G)
      (Iso.refl _) (by ext : 1; exact IsTerminal.hom_ext terminalIsTerminal _ _)

/-- The free functor `Type u ⥤ ModuleCat.{u} k` applied to the universal cover of the classifying
space of `G` as a simplicial set, augmented by the map from `Fin 1 → G` to the terminal object
in `Type u`. -/
/-
**classifyingSpaceUniversalCover.compForgetAugmented.toModule** 是 Mathlib 中的一个定义
，位于命名空间 `classifyingSpaceUniversalCover.compForgetAugmented`。
形式化陈述：(k G : Type u) → [inst : CommRing k] → [Monoid G] → CategoryTheory.Simplic
ialObject.Augmented (ModuleCat k)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free functor `Type u ⥤ ModuleCat.{u} k` applied to the universal cover of th
e classifying
space of `G` as a simplicial set, augmented by the map from `Fin 1 → G` to the t
erminal object
in `Type u`.
-/
def compForgetAugmented.toModule : SimplicialObject.Augmented (ModuleCat.{u} k) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.monoidAlgebraFree k)).obj
    (compForgetAugmented G)

/-- If we augment the universal cover of the classifying space of `G` as a simplicial set by the
map from `Fin 1 → G` to the terminal object in `Type u`, then apply the free functor
`Type u ⥤ ModuleCat.{u} k`, the resulting augmented simplicial `k`-module has an extra
degeneracy. -/
/-
**classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmentedToModule** 是 
Mathlib 中的一个定义，位于命名空间 `classifyingSpaceUniversalCover`。
形式化陈述：extraDegeneracyCompForgetAugmentedToModule : ExtraDegeneracy (compForgetAu
gmented.toModule k G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we augment the universal cover of the classifying space of `G` as a simplicia
l set by the
map from `Fin 1 → G` to the terminal object in `Type u`, then apply the free fun
ctor
`Type u ⥤ ModuleCat.{u} k`, the resulting augmented simplicial `k`-module has an
 extra
degeneracy.
-/
def extraDegeneracyCompForgetAugmentedToModule :
    ExtraDegeneracy (compForgetAugmented.toModule k G) :=
  .map (extraDegeneracyCompForgetAugmented G) (ModuleCat.monoidAlgebraFree k)

end classifyingSpaceUniversalCover

variable (k)

/-- The standard resolution of `k` as a trivial representation, defined as the alternating
face map complex of a simplicial `k`-linear `G`-representation. -/
/-
**Rep.standardComplex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Rep.standardComplex [Monoid G]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard resolution of `k` as a trivial representation, defined as the alter
nating
face map complex of a simplicial `k`-linear `G`-representation.
-/
def Rep.standardComplex [Monoid G] :=
  (AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).obj
    (classifyingSpaceUniversalCover G ⋙ linearization k G)

namespace Rep.standardComplex

open classifyingSpaceUniversalCover AlgebraicTopology CategoryTheory.Limits

/-- The `k`-linear map underlying the differential in the standard resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`. -/
/-
**Rep.standardComplex.d** 是 Mathlib 中的一个定义，位于命名空间 `Rep.standardComplex`。
形式化陈述：d (G : Type u) (n : Nat) : k[Fin (n + 1) -> G] ->ₗ[k] k[Fin n -> G]
参数：G : Type u；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `k`-linear map underlying the differential in the standard resolution of `k`
 as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ,
 ..., gₙ)`.
-/
def d (G : Type u) (n : ℕ) : k[Fin (n + 1) → G] →ₗ[k] k[Fin n → G] :=
  (Finsupp.lift k[Fin n → G] k (Fin (n + 1) → G) fun g =>
    (@Finset.univ (Fin (n + 1)) _).sum fun p =>
      .single (g ∘ p.succAbove) ((-1 : k) ^ (p : ℕ))) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

variable {k G}

@[simp]
/-
**Rep.standardComplex.d_of** 是 Mathlib 中的一个定理，位于命名空间 `Rep.standardComplex`。
形式化陈述：d_of {n : Nat} (c : Fin (n + 1) -> G) : d k G n (.single c 1) = ∑ p : Fin 
(n + 1), .single (c ∘ p.succAbove) ((-1 : k) ^ p.val)
参数：c : Fin (n + 1) -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem d_of {n : ℕ} (c : Fin (n + 1) → G) :
    d k G n (.single c 1) = ∑ p : Fin (n + 1), .single (c ∘ p.succAbove) ((-1 : k) ^ p.val) := by
  simp [d]
/-
**Rep.standardComplex.d_single** 是 Mathlib 中的一个引理，位于命名空间 `Rep.standardComplex`。
形式化陈述：d_single {n : Nat} (c : Fin (n + 1) -> G) (r : k) : d k G n (.single c r) 
= ∑ p : Fin (n + 1), .single (c ∘ p.succAbove) (r * (-1 : k) ^ p.val)
参数：c : Fin (n + 1) -> G；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `MonoidAlgebra.smul_single`：smul_single (a : A) (m : M) (r : R) : a • sin
gle m r = single m (a • r)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Rep.standardComplex.d_of`：d_of {n : Nat} (c : Fin (n + 1) -> G) : d k G 
n (.single c 1) = ∑ p : Fin (n + 1), .single (c ∘ p.succAbove) ((-1 : k) ^ p.val
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma d_single {n : ℕ} (c : Fin (n + 1) → G) (r : k) :
    d k G n (.single c r) =
      ∑ p : Fin (n + 1), .single (c ∘ p.succAbove) (r * (-1 : k) ^ p.val) := by
  rw [← mul_one r, ← smul_eq_mul, ← MonoidAlgebra.smul_single, map_smul, d_of]
  simp [Finset.smul_sum]

variable (k G) [Monoid G]

/-- The `n`th object of the standard resolution of `k` is definitionally isomorphic to `k[Gⁿ⁺¹]`
equipped with the representation induced by the diagonal action of `G`. -/
/-
**Rep.standardComplex.xIso** 是 Mathlib 中的一个定义，位于命名空间 `Rep.standardComplex`。
形式化陈述：xIso (n : Nat) : (standardComplex k G).X n ≅ Rep.ofMulAction k G (Fin (n +
 1) -> G)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th object of the standard resolution of `k` is definitionally isomorphic 
to `k[Gⁿ⁺¹]`
equipped with the representation induced by the diagonal action of `G`.
-/
def xIso (n : ℕ) : (standardComplex k G).X n ≅ Rep.ofMulAction k G (Fin (n + 1) → G) :=
  Iso.refl _
/-
**Rep.standardComplex.x_projective** 是 Mathlib 中的一个实例，位于命名空间 `Rep.standardComple
x`。
形式化陈述：x_projective (G : Type u) [Group G] (n : Nat) : Projective ((standardCompl
ex k G).X n)
参数：G : Type u；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance x_projective (G : Type u) [Group G] (n : ℕ) :
    Projective ((standardComplex k G).X n) := by
  exact inferInstanceAs <| Projective (Rep.diagonal k G (n + 1))

set_option backward.defeqAttrib.useBackward true in
unif_hint where ⊢ Action.V (Action.ofMulAction G (Fin (n + 1) → G)) ≟ Fin (n + 1) → G in
set_option backward.isDefEq.respectTransparency false in
/-- Simpler expression for the differential in the standard resolution of `k` as a
`G`-representation. It sends `(g₀, ..., gₙ₊₁) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ₊₁)`. -/
/-
**Rep.standardComplex.d_eq** 是 Mathlib 中的一个定理，位于命名空间 `Rep.standardComplex`。
形式化陈述：d_eq (n : Nat) : ((standardComplex k G).d (n + 1) n).hom.toLinearMap = d k
 G (n + 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.lhom_ext'`：lhom_ext' {N : Type*} [Semiring R] [AddCommMono
id N] [Module R N] [Module R S] ⦃f g : S[M] ->ₗ[R] N⦄ (H : forall (x : M), Linea
rMap.comp f (…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.strictMono_succAbove`：strictMono_succAbove (p : Fin (n + 1)) : Stric
tMono (succAbove p)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `AlgebraicTopology.alternatingFaceMapComplex_obj_d`：alternatingFaceMapCom
plex_obj_d (X : SimplicialObject C) (n : Nat) : ((alternatingFaceMapComplex C).o
bj X).d (n + 1) n = AlternatingFaceMapC…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用引理 `Representation.IntertwiningMap.sum_apply`：sum_apply {ι : Type*} (s : Fin
set ι) (f : ι -> IntertwiningMap ρ σ) (v : V) : (∑ i in s, f i) v = ∑ i in s, f 
i v
· 使用引理 `Representation.linearizeMap_single`：linearizeMap_single (f : X ⟶ Y) (x :
 X.V) (r : k) : (linearizeMap f) (.single x r) = .single (f.hom x) r
· 使用引理 `MonoidAlgebra.smul_single`：smul_single (a : A) (m : M) (r : R) : a • sin
gle m r = single m (a • r)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Rep.standardComplex.d_of`：d_of {n : Nat} (c : Fin (n + 1) -> G) : d k G 
n (.single c 1) = ∑ p : Fin (n + 1), .single (c ∘ p.succAbove) ((-1 : k) ^ p.val
)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Simpler expression for the differential in the standard resolution of `k` as a
`G`-representation. It sends `(g₀, ..., gₙ₊₁) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ₊
₁)`.
-/
theorem d_eq (n : ℕ) : ((standardComplex k G).d (n + 1) n).hom.toLinearMap =
    d k G (n + 1) := by
  refine MonoidAlgebra.lhom_ext' fun (x : Fin (n + 2) → G) => LinearMap.ext_ring ?_
  simp [standardComplex, Action.ofMulAction_V, SimplicialObject.δ, SimplexCategory.δ,
    Fin.succAboveOrderEmb, ← Int.cast_smul_eq_zsmul k ((-1) ^ _ : ℤ), ← ofHom_smul, ← ofHom_sum,
    Representation.IntertwiningMap.coe_toLinearMap, Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.smul_apply, (Representation.linearizeMap_single),
    smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Rep.standardComplex.d_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep.standardComplex`。
形式化陈述：d_apply {n : Nat} (f : k[Fin (n + 1 + 1) -> G]) : ((standardComplex k G).d
 (n + 1) n).hom f = d k G (n + 1) f
参数：f : k[Fin (n + 1 + 1) -> G]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Representation.IntertwiningMap.toLinearMap_apply`：toLinearMap_apply (f :
 IntertwiningMap ρ σ) (v : V) : f.toLinearMap v = f v
· 使用定理 `Rep.standardComplex.d_eq`：d_eq (n : Nat) : ((standardComplex k G).d (n +
 1) n).hom.toLinearMap = d k G (n + 1)
-/
lemma d_apply {n : ℕ} (f : k[Fin (n + 1 + 1) → G]) :
    ((standardComplex k G).d (n + 1) n).hom f = d k G (n + 1) f := by
  rw [← Representation.IntertwiningMap.toLinearMap_apply, d_eq]; rfl

section Exactness

/-- The standard resolution of `k` as a trivial representation as a complex of `k`-modules. -/
/-
**Rep.standardComplex.forget** 是 Mathlib 中的一个定义，位于命名空间 `Rep.standardComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard resolution of `k` as a trivial representation as a complex of `k`-m
odules.
-/
def forget₂ToModuleCat :=
  ((forget₂ (Rep k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj (standardComplex k G)

/-- If we apply the free functor `Type u ⥤ ModuleCat.{u} k` to the universal cover of the
classifying space of `G` as a simplicial set, then take the alternating face map complex, the result
is isomorphic to the standard resolution of the trivial `G`-representation `k` as a complex of
`k`-modules. -/
/-
**Rep.standardComplex.compForgetAugmentedIso** 是 Mathlib 中的一个定义，位于命名空间 `Rep.stan
dardComplex`。
形式化陈述：compForgetAugmentedIso : AlternatingFaceMapComplex.obj (SimplicialObject.A
ugmented.drop.obj (compForgetAugmented.toModule k G)) ≅ standardComplex.forget₂T
oModuleCat k G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we apply the free functor `Type u ⥤ ModuleCat.{u} k` to the universal cover o
f the
classifying space of `G` as a simplicial set, then take the alternating face map
 complex, the result
is isomorphic to the standard resolution of the trivial `G`-representation `k` a
s a complex of
`k`-modules.
-/
def compForgetAugmentedIso :
    AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj (compForgetAugmented.toModule k G)) ≅
      standardComplex.forget₂ToModuleCat k G :=
  eqToIso
    (Functor.congr_obj (map_alternatingFaceMapComplex (forget₂ (Rep k G) (ModuleCat.{u} k))).symm
      (classifyingSpaceUniversalCover G ⋙ linearization k G))

/-- As a complex of `k`-modules, the standard resolution of the trivial `G`-representation `k` is
homotopy equivalent to the complex which is `k` at 0 and 0 elsewhere. -/
/-
**Rep.standardComplex.forget** 是 Mathlib 中的一个定义，位于命名空间 `Rep.standardComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As a complex of `k`-modules, the standard resolution of the trivial `G`-represen
tation `k` is
homotopy equivalent to the complex which is `k` at 0 and 0 elsewhere.
-/
def forget₂ToModuleCatHomotopyEquiv :
    HomotopyEquiv (standardComplex.forget₂ToModuleCat k G)
      ((ChainComplex.single₀ (ModuleCat k)).obj ((forget₂ (Rep k G) _).obj <| Rep.trivial k G k)) :=
  (HomotopyEquiv.ofIso (compForgetAugmentedIso k G).symm).trans <|
    (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
          (extraDegeneracyCompForgetAugmentedToModule k G)).trans
      (HomotopyEquiv.ofIso <|
        (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
          (letI : Unique (⊤_ Type u) := Types.terminalIso.toEquiv.unique
           ((MonoidAlgebra.coeffLinearEquiv k (M := ⊤_ Type u)).trans
             (Finsupp.uniqueLinearEquiv k k default)).toModuleIso))

/-- The hom of `k`-linear `G`-representations `k[G¹] → k` sending `∑ nᵢgᵢ ↦ ∑ nᵢ`. -/
/-
**Rep.standardComplex.** 是 Mathlib 中的一个定义，位于命名空间 `Rep.standardComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The hom of `k`-linear `G`-representations `k[G¹] → k` sending `∑ nᵢgᵢ ↦ ∑ nᵢ`.
-/
def ε : Rep.ofMulAction k G (Fin 1 → G) ⟶ Rep.trivial k G k := ofHom
  ⟨(Finsupp.linearCombination _ fun _ ↦ (1 : k)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap,
    fun _ ↦ MonoidAlgebra.lhom_ext' fun _ => LinearMap.ext_ring <| by simp⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homotopy equivalence of complexes of `k`-modules between the standard resolution of `k` as
a trivial `G`-representation, and the complex which is `k` at 0 and 0 everywhere else, acts as
`∑ nᵢgᵢ ↦ ∑ nᵢ : k[G¹] → k` at 0. -/
/-
**Rep.standardComplex.forget** 是 Mathlib 中的一个定理，位于命名空间 `Rep.standardComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy equivalence of complexes of `k`-modules between the standard resolu
tion of `k` as
a trivial `G`-representation, and the complex which is `k` at 0 and 0 everywhere
 else, acts as
`∑ nᵢgᵢ ↦ ∑ nᵢ : k[G¹] → k` at 0.
-/
theorem forget₂ToModuleCatHomotopyEquiv_f_0_eq :
    (forget₂ToModuleCatHomotopyEquiv k G).1.f 0 = (forget₂ (Rep k G) _).map (ε k G) := by
  refine ModuleCat.hom_ext <| MonoidAlgebra.lhom_ext' fun (x : Fin 1 → G) => LinearMap.ext_ring ?_
  simp [forget₂ToModuleCatHomotopyEquiv, HomotopyEquiv.ofIso, HomotopyEquiv.trans,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv, ChainComplex.single₀_map_f_zero,
    AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero, compForgetAugmentedIso, eqToIso.inv,
    HomologicalComplex.eqToHom_f, compForgetAugmented, compForgetAugmented.toModule, ε,
    SimplicialObject.augment, Unique.eq_default (terminal.from _), MonoidAlgebra.coeff_single,
    Finsupp.single_apply, if_pos (Subsingleton.elim _ _)]

set_option backward.isDefEq.respectTransparency false in
/-
**Rep.standardComplex.d_comp_** 是 Mathlib 中的一个定理，位于命名空间 `Rep.standardComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem d_comp_ε : (standardComplex k G).d 1 0 ≫ ε k G = 0 := by
  ext : 3
  have : (forget₂ToModuleCat k G).d 1 0
      ≫ (forget₂ (Rep k G) (ModuleCat.{u} k)).map (ε k G) = 0 := by
    rw [← forget₂ToModuleCatHomotopyEquiv_f_0_eq,
      ← (forget₂ToModuleCatHomotopyEquiv k G).1.2 1 0 rfl]
    exact comp_zero
  exact LinearMap.ext_iff.1 (ModuleCat.hom_ext_iff.mp this) _

/-- The chain map from the standard resolution of `k` to `k[0]` given by `∑ nᵢgᵢ ↦ ∑ nᵢ` in
degree zero. -/
/-
**Rep.standardComplex.** 是 Mathlib 中的一个定义，位于命名空间 `Rep.standardComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The chain map from the standard resolution of `k` to `k[0]` given by `∑ nᵢgᵢ ↦ ∑
 nᵢ` in
degree zero.
-/
def εToSingle₀ :
    standardComplex k G ⟶ (ChainComplex.single₀ _).obj (Rep.trivial k G k) :=
  ((standardComplex k G).toSingle₀Equiv _).symm ⟨ε k G, d_comp_ε k G⟩

set_option backward.defeqAttrib.useBackward true in
/-
**Rep.standardComplex.** 是 Mathlib 中的一个定理，位于命名空间 `Rep.standardComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem εToSingle₀_comp_eq :
    ((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G) ≫
        (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _ =
      (forget₂ToModuleCatHomotopyEquiv k G).hom := by
  dsimp
  ext1
  simpa using! (forget₂ToModuleCatHomotopyEquiv_f_0_eq k G).symm
/-
**Rep.standardComplex.quasiIso_forget** 是 Mathlib 中的一个定理，位于命名空间 `Rep.standardCom
plex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quasiIso_forget₂_εToSingle₀ :
    QuasiIso (((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G)) := by
  have h : QuasiIso (forget₂ToModuleCatHomotopyEquiv k G).hom := inferInstance
  rw [← εToSingle₀_comp_eq k G] at h
  exact quasiIso_of_comp_right (hφφ' := h)
/-
**Rep.standardComplex.** 是 Mathlib 中的一个实例，位于命名空间 `Rep.standardComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : QuasiIso (εToSingle₀ k G) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat.{u} k))]
  apply quasiIso_forget₂_εToSingle₀

end Exactness
end standardComplex

open HomologicalComplex.Hom standardComplex

variable [Group G]

/-- The standard projective resolution of `k` as a trivial `k`-linear `G`-representation. -/
/-
**Rep.standardResolution** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：(k G : Type u) → [inst : CommRing k] → [inst_1 : Group G] → CategoryTheory
.ProjectiveResolution (Rep.trivial k G k)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard projective resolution of `k` as a trivial `k`-linear `G`-representa
tion.
-/
def standardResolution : ProjectiveResolution (Rep.trivial k G k) where
  complex := standardComplex k G
  π := εToSingle₀ k G

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is a trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
standard resolution of `k` called `standardComplex k G`. -/
/-
**Rep.standardResolution.extIso** 是 Mathlib 中的一个定义，位于命名空间 `Rep.standardResolutio
n`。
形式化陈述：(k G : Type u) →   [inst : CommRing k] →     [inst_1 : Group G] →       (V
 : Rep.{u, u, u} k G) →         (n : ℕ) →           ((Ext k (Rep.{u, u, u} k G) 
n).obj (Opposite.op (Rep.trivial k G k))).obj V ≅             HomologicalComplex
.homology ((Rep.standardComplex k G).linearYonedaObj k V) n
参数：Ext k (Rep.{u, u, u} k G) n；Opposite.op (Rep.trivial k G k)；Rep.standardCompl
ex k G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is a trivial 
`k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, 
where `P` is the
standard resolution of `k` called `standardComplex k G`.
-/
def standardResolution.extIso (V : Rep k G) (n : ℕ) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      ((standardComplex k G).linearYonedaObj k V).homology n :=
  (standardResolution k G).isoExt n V

namespace barComplex

open Rep Finsupp

variable (n)

/-- The differential from `Gⁿ⁺¹ →₀ k[G]` to `Gⁿ →₀ k[G]` in the bar resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ)` to
`g₀·(g₁, ..., gₙ) + ∑ (-1)ʲ⁺¹·(g₀, ..., gⱼgⱼ₊₁, ..., gₙ) + (-1)ⁿ⁺¹·(g₀, ..., gₙ₋₁)` for
`j = 0, ..., n - 1`. -/
/-
**Rep.barComplex.d** 是 Mathlib 中的一个定义，位于命名空间 `Rep.barComplex`。
形式化陈述：(k G : Type u) →   [inst : CommRing k] → (n : ℕ) → [inst_1 : Group G] → Re
p.free k G (Fin (n + 1) → G) ⟶ Rep.free k G (Fin n → G)
参数：n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differential from `Gⁿ⁺¹ →₀ k[G]` to `Gⁿ →₀ k[G]` in the bar resolution of `k
` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ)` to
`g₀·(g₁, ..., gₙ) + ∑ (-1)ʲ⁺¹·(g₀, ..., gⱼgⱼ₊₁, ..., gₙ) + (-1)ⁿ⁺¹·(g₀, ..., gₙ₋
₁)` for
`j = 0, ..., n - 1`.
-/
def d : free k G Gⁿ⁺¹ ⟶ free k G Gⁿ :=
  freeLift k G _ fun g => single (fun i => g i.succ) (.single (g 0) 1) +
    ∑ j : Fin (n + 1), single (j.contractNth (· * ·) g) (.single (1 : G) ((-1 : k) ^ (j.val + 1)))

variable {k G} in
/-
**Rep.barComplex.d_single** 是 Mathlib 中的一个定理，位于命名空间 `Rep.barComplex`。
形式化陈述：∀ {k G : Type u} [inst : CommRing k] (n : ℕ) [inst_1 : Group G] (x : Fin (
n + 1) → G),   ((Rep.Hom.hom (Rep.barComplex.d k G n)) fun₀ | x => MonoidAlgebra
.single 1 1) =     (fun₀ | fun i => x i.succ => MonoidAlgebra.single (x 0) 1) + 
      ∑ j, fun₀ | j.contractNth (fun x1 x2 => x1 * x2) x => MonoidAlgebra.single
 1 ((-1) ^ (↑j + 1))
参数：n : ℕ；x : Fin (n + 1) → G；(Rep.Hom.hom (Rep.barComplex.d k G n)) fun₀ | x => 
MonoidAlgebra.single 1 1；fun₀ | fun i => x i.succ => MonoidAlgebra.single (x 0) 
1；fun x1 x2 => x1 * x2；(-1) ^ (↑j + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Representation.freeLift_toLinearMap`：∀ {G : Type v} [inst : Monoid G] {V
 : Type v'} [inst_1 : AddCommMonoid V] {k : Type u} [inst_2 : CommSemiring k]   
[inst_3 : _root_.Module k…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Representation.finsupp_single`：finsupp_single (g : G) (x : α) (a : A) : 
ρ.finsupp α g (single x a) = single x (ρ g a)
· 使用定理 `Representation.ofMulAction_single`：ofMulAction_single (g : G) (x : H) (r
 : k) : ofMulAction k G H g (single x r) = single (g • x) r
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `Finsupp.curryLinearEquiv_symm_apply`：∀ {α : Type u_9} {β : Type u_10} (R
 : Type u_11) {M : Type u_12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [
inst_2 : _root_.Module R …
· 使用引理 `Finsupp.uncurry_single`：uncurry_single (a : α) (b : β) (m : M) : (single
 a (single b m)).uncurry = single (a, b) m
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
（共 31 条，此处仅展示前 30 条）
-/
lemma d_single (x : Gⁿ⁺¹) :
    (d k G n).hom (single x (.single 1 1)) = single (fun i => x i.succ) (.single (x 0) 1) +
      ∑ j : Fin (n + 1),
        single (j.contractNth (· * ·) x) (.single (1 : G) ((-1 : k) ^ (j.val + 1))) := by
  simp [d, ← Representation.IntertwiningMap.toLinearMap_apply]

set_option backward.defeqAttrib.useBackward true in
unif_hint (X : Type*) where ⊢ Action.V (Action.trivial G X) ≟ X in
unif_hint where ⊢ (HomologicalComplex.X (standardComplex k G) n).V ≟ k[Fin (n + 1) → G] in
set_option backward.isDefEq.respectTransparency false in
/-
**Rep.barComplex.d_comp_diagonalSuccIsoFree_inv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Re
p.barComplex`。
形式化陈述：∀ (k G : Type u) [inst : CommRing k] (n : ℕ) [inst_1 : Group G],   Categor
yTheory.CategoryStruct.comp (Rep.barComplex.d k G n) (Rep.diagonalSuccIsoFree k 
G n).inv =     CategoryTheory.CategoryStruct.comp (Rep.diagonalSuccIsoFree k G (
n + 1)).inv ((Rep.standardComplex k G).d (n + 1) n)
参数：k G : Type u；n : ℕ；Rep.barComplex.d k G n；Rep.diagonalSuccIsoFree k G n；Rep.d
iagonalSuccIsoFree k G (n + 1)；(Rep.standardComplex k G).d (n + 1) n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rep.free_ext`：free_ext (f g : free k G α ⟶ A) (h : forall i : α, f.hom (
single i (.single 1 1)) = g.hom (single i (.single 1 1))) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.partialProd_succ'`：partialProd_succ' (f : Fin (n + 1) -> M) (j : Fin
 (n + 1)) : partialProd f j.succ = f 0 * partialProd (Fin.tail f) j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rep.barComplex.d_single`：∀ {k G : Type u} [inst : CommRing k] (n : ℕ) [i
nst_1 : Group G] (x : Fin (n + 1) → G),   ((Rep.Hom.hom (Rep.barComplex.d k G n)
) fun₀ | x =>…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Representation.IntertwiningMap.instLinearMapClass`：∀ {A : Type u_1} {G :
 Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]
   [inst_2 : AddCommMonoid V] [inst_3 :…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single`
：leftRegularTensorTrivialIsoFree_symm_apply_single_single {α : Type w'} (i : α) 
(g : G) (r : k) : (leftRegularTensorTrivialIsoFree α).symm (.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearEquiv.isIntertwining_symm_isIntertwining`：∀ {A : Type u_1} {G : Ty
pe u_2} {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   
[inst_2 : AddCommMonoid V] [inst_3 :…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用引理 `Representation.linearizeMap_single`：linearizeMap_single (f : X ⟶ Y) (x :
 X.V) (r : k) : (linearizeMap f) (.single x r) = .single (f.hom x) r
· 使用引理 `Representation.LinearizeMonoidal.μ_apply_single_single`：μ_apply_single_s
ingle (x : X.V) (y : Y.V) (r s : k) : μ (k
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Action.diagonalSuccIsoTensorTrivial_inv_hom_apply`：diagonalSuccIsoTensor
Trivial_inv_hom_apply {n : Nat} (g : G) (f : Fin n -> G) : dsimp% (diagonalSuccI
soTensorTrivial G n).inv.hom (g, f) = (…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `Fin.partialProd_contractNth`：partialProd_contractNth {G : Type*} [Monoid
 G] {n : Nat} (g : Fin (n + 1) -> G) (a : Fin (n + 1)) : partialProd (contractNt
h a (· * ·) g) = …
（共 37 条，此处仅展示前 30 条）
-/
lemma d_comp_diagonalSuccIsoFree_inv_eq :
    d k G n ≫ (diagonalSuccIsoFree k G n).inv =
      (diagonalSuccIsoFree k G (n + 1)).inv ≫ (standardComplex k G).d (n + 1) n :=
  free_ext k G _ _ _ fun i ↦ by
    have eq3 : MonoidAlgebra.single (i 0 • Fin.partialProd fun i_1 ↦ i i_1.succ) (1 : k) =
        MonoidAlgebra.single (Fin.partialProd i ∘ Fin.succ) 1 := by
      congr; exact funext fun j ↦ Fin.partialProd_succ' i j |>.symm
    simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
    rw [d_single (k := k), map_add, map_sum]
    -- in-context `have`: at `Action` carriers, only locally re-elaborated statements key-match
    have H : ∀ (m : ℕ) (f : Fin m → G) (g : G) (r : k),
        (diagonalSuccIsoFree k G m).inv.hom (single f (MonoidAlgebra.single g r)) =
          MonoidAlgebra.single (g • Fin.partialProd f) r := by
      intro m f g r
      simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
        Representation.IntertwiningMap.comp_apply]
      have step1 : (Hom.hom (leftRegularTensorTrivialIsoFree k G (Fin m → G)).inv)
          (single f (.single g r)) = .single g 1 ⊗ₜ[k] .single f r :=
        Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
      rw [step1]
      simp only [mkIso_inv, Representation.linearizeOfMulActionIso, Representation.Equiv.mk_symm,
        LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom, Action.tensorObj_V, Action.trivial_V,
        Functor.mapIso_inv, tensor_V, tensor_ρ, Iso.symm_inv, Functor.Monoidal.μIso_hom, μ_hom,
        MonoidalCategory.tensorIso_inv, Representation.linearizeTrivialIso, hom_tensorHom,
        Representation.IntertwiningMap.tensor_apply, Representation.Equiv.coe_toIntertwiningMap,
        Representation.Equiv.mk_apply, LinearEquiv.refl_apply]
      have key₁ := Representation.linearizeMap_single (k := k)
        (Action.diagonalSuccIsoTensorTrivial G m).inv (g, f) ((1 : k) * r)
      have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
        (X := Action.leftRegular G) (Y := Action.trivial G (Fin m → G)) g f 1 r
      exact ((congrArg (fun z => (Representation.linearizeMap
        (Action.diagonalSuccIsoTensorTrivial G m).inv) z) key₂).trans key₁).trans (by simp)
    simp only [H, one_smul]
    simp [d_apply (k := k), Fin.partialProd_contractNth, Fin.sum_univ_succ, eq3]

end barComplex

open barComplex

set_option backward.isDefEq.respectTransparency false in
/-- The projective resolution of `k` as a trivial `k`-linear `G`-representation with `n`th
differential `(Gⁿ⁺¹ →₀ k[G]) → (Gⁿ →₀ k[G])` sending `(g₀, ..., gₙ)` to
`g₀·(g₁, ..., gₙ) + ∑ (-1)ʲ⁺¹·(g₀, ..., gⱼgⱼ₊₁, ..., gₙ) + (-1)ⁿ⁺¹·(g₀, ..., gₙ₋₁)` for
`j = 0, ..., n - 1`. -/
/-
**Rep.barComplex** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：(k G : Type u) → [inst : CommRing k] → [inst_1 : Group G] → ChainComplex (
Rep.{u, u, u} k G) ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projective resolution of `k` as a trivial `k`-linear `G`-representation with
 `n`th
differential `(Gⁿ⁺¹ →₀ k[G]) → (Gⁿ →₀ k[G])` sending `(g₀, ..., gₙ)` to
`g₀·(g₁, ..., gₙ) + ∑ (-1)ʲ⁺¹·(g₀, ..., gⱼgⱼ₊₁, ..., gₙ) + (-1)ⁿ⁺¹·(g₀, ..., gₙ₋
₁)` for
`j = 0, ..., n - 1`.
-/
noncomputable abbrev barComplex : ChainComplex (Rep k G) ℕ :=
  ChainComplex.of (fun n => free k G (Fin n → G)) (fun n => d k G n) fun m => by
    have key : (d k G (m + 1) ≫ d k G m) ≫ (diagonalSuccIsoFree k G m).inv = 0 := by
      rw [Category.assoc, d_comp_diagonalSuccIsoFree_inv_eq, ← Category.assoc,
        d_comp_diagonalSuccIsoFree_inv_eq, Category.assoc, HomologicalComplex.d_comp_d,
        Limits.comp_zero]
    exact (cancel_mono (diagonalSuccIsoFree k G m).inv).mp (by simpa using key)

namespace barComplex

/-
**Rep.barComplex.d_def** 是 Mathlib 中的一个定理，位于命名空间 `Rep.barComplex`。
形式化陈述：∀ (k G : Type u) [inst : CommRing k] {n : ℕ} [inst_1 : Group G],   (Rep.ba
rComplex k G).d (n + 1) n = Rep.barComplex.d k G n
参数：k G : Type u；Rep.barComplex k G；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ChainComplex.of_d`：of_d (j : α) : of.d X d (j + 1) j = d j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem d_def : (barComplex k G).d (n + 1) n = d k G n := by simp

set_option backward.isDefEq.respectTransparency false in
/-- Isomorphism between the bar resolution and standard resolution, with `n`th map
`(Gⁿ →₀ k[G]) → k[Gⁿ⁺¹]` sending `(g₁, ..., gₙ) ↦ (1, g₁, g₁g₂, ..., g₁...gₙ)`. -/
/-
**Rep.barComplex.isoStandardComplex** 是 Mathlib 中的一个定义，位于命名空间 `Rep.barComplex`。
形式化陈述：(k G : Type u) → [inst : CommRing k] → [inst_1 : Group G] → Rep.barComplex
 k G ≅ Rep.standardComplex k G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphism between the bar resolution and standard resolution, with `n`th map
`(Gⁿ →₀ k[G]) → k[Gⁿ⁺¹]` sending `(g₁, ..., gₙ) ↦ (1, g₁, g₁g₂, ..., g₁...gₙ)`.
-/
def isoStandardComplex : barComplex k G ≅ standardComplex k G :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (diagonalSuccIsoFree k G i).symm) fun i j => by
    rintro (rfl : j + 1 = i)
    rw [d_def, Iso.symm_hom, Iso.symm_hom, d_comp_diagonalSuccIsoFree_inv_eq]

end barComplex

/-- The chain complex `barComplex k G` as a projective resolution of `k` as a trivial
`k`-linear `G`-representation. -/
@[simps complex]
/-
**Rep.barResolution** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：(k G : Type u) → [inst : CommRing k] → [inst_1 : Group G] → CategoryTheory
.ProjectiveResolution (Rep.trivial k G k)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The chain complex `barComplex k G` as a projective resolution of `k` as a trivia
l
`k`-linear `G`-representation.
-/
def barResolution : ProjectiveResolution (Rep.trivial k G k) where
  complex := barComplex k G
  projective n := (inferInstance : Projective (free k G (Fin n → G)))
  π := (isoStandardComplex k G).hom ≫ standardComplex.εToSingle₀ k G

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is the trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
bar resolution of `k`. -/
/-
**Rep.barResolution.extIso** 是 Mathlib 中的一个定义，位于命名空间 `Rep.barResolution`。
形式化陈述：(k G : Type u) →   [inst : CommRing k] →     [inst_1 : Group G] →       (V
 : Rep.{u, u, u} k G) →         (n : ℕ) →           ((Ext k (Rep.{u, u, u} k G) 
n).obj (Opposite.op (Rep.trivial k G k))).obj V ≅             HomologicalComplex
.homology ((Rep.barComplex k G).linearYonedaObj k V) n
参数：Ext k (Rep.{u, u, u} k G) n；Opposite.op (Rep.trivial k G k)；Rep.barComplex k 
G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is the trivia
l `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, 
where `P` is the
bar resolution of `k`.
-/
def barResolution.extIso (V : Rep k G) (n : ℕ) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      ((barComplex k G).linearYonedaObj k V).homology n :=
  (barResolution k G).isoExt n V

end Rep

