/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.LocallyFinsupp.Pushforward
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Algebraic Cycles

In this file we define algebraic cycles on a scheme `X` with coefficients in a type `R` and provide
some basic API for working with them. We define an algebraic cycle on a scheme `X` with
coefficients in a type `R` to be functions `c : X → R` whose support is locally finite.

## Implementation notes

Here we're making use of the equivalence between irreducible closed subsets of a scheme and their
generic points in order to reuse the API in `Function.locallyFinsupp`, hence the slightly
nonstandard definition.
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u v
variable {X Y : Scheme.{u}} {R : Type*}

/--
Algebraic cycle on a scheme `X` with coefficients in a type `Z` is just a function from `X` to `Z`
with locally finite support (see the module docstring for more details).

Note: currently this is an abbrev to save some effort in duplicating API. This seems fine for now,
but be aware of this if there is ever an instance clash involving algebraic cycles.
-/
@[stacks 02QR]
/-
**AlgebraicGeometry.AlgebraicCycle** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGeometr
y`。
形式化陈述：AlgebraicCycle (X : Scheme.{u}) (R : Type*) [Zero R]
参数：X : Scheme.{u}；R : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebraic cycle on a scheme `X` with coefficients in a type `Z` is just a functi
on from `X` to `Z`
with locally finite support (see the module docstring for more details).

Note: currently this is an abbrev to save some effort in duplicating API. This s
eems fine for now,
but be aware of this if there is ever an instance clash involving algebraic cycl
es.
-/
abbrev AlgebraicCycle (X : Scheme.{u}) (R : Type*) [Zero R] :=
  Function.locallyFinsupp X R

variable (f : X ⟶ Y) [Semiring R] (c : AlgebraicCycle X R) (x : X) (z : Y)
namespace AlgebraicCycle

/--
Implementation detail for `AlgebraicCycle.map`: function used to define the coefficient of the
pushforward of a cycle `c` at a point `z = f x`.
-/
@[stacks 02R3]
/-
**AlgebraicGeometry.AlgebraicCycle.mapCoeff** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.AlgebraicCycle`。
形式化陈述：mapCoeff {N : Type*} [DecidableEq N] {Y : Scheme} (f : X ⟶ Y) (wx : X -> N
) (wy : Y -> N) (x : X) : Nat
参数：f : X ⟶ Y；wx : X -> N；wy : Y -> N；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation detail for `AlgebraicCycle.map`: function used to define the coef
ficient of the
pushforward of a cycle `c` at a point `z = f x`.
-/
noncomputable def mapCoeff {N : Type*} [DecidableEq N] {Y : Scheme} (f : X ⟶ Y) (wx : X → N)
    (wy : Y → N) (x : X) : ℕ := if wx x = wy (f.base x) then f.residueDegree x else 0

/--
The pushforward of algebraic cycles with respect to a quasicompact morphism of schemes. The
arguments `wx` and `wy` are certain weight functions used to calculate how the weights of the
algebraic cycle should be adjusted to make the pushforward operation functorial. Typically in
applications these will be some notions of dimension or codimension. The most common notion of
dimension is `Order.height`, and the most common notion of codimension is `Order.coheight`, though
more sophisticated notions exist in the literature which are useful when sufficient
equidimensionality hypotheses cannot be assumed.
-/
@[stacks 02R3]
noncomputable
/-
**AlgebraicGeometry.AlgebraicCycle.map** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.AlgebraicCycle`。
形式化陈述：map [QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X -> N) (wy : Y -> 
N) (c : AlgebraicCycle X R) : AlgebraicCycle Y R
参数：wx : X -> N；wy : Y -> N；c : AlgebraicCycle X R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instPrespectralSpaceCarrierCarrierCommRingCat`：∀ {X : 
AlgebraicGeometry.Scheme}, PrespectralSpace ↥X
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isSpectralMap`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f], IsSpectralMap ⇑f
-/
def map [QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)
    (c : AlgebraicCycle X R) : AlgebraicCycle Y R :=
  Function.locallyFinsupp.map f (Nat.cast (R := R) <| mapCoeff f wx wy ·) f.isSpectralMap c

@[simp]
/-
**AlgebraicGeometry.AlgebraicCycle.map_id** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.AlgebraicCycle`。
形式化陈述：map_id {N : Type*} [DecidableEq N] (wx : X -> N) (c : AlgebraicCycle X R) 
: map (𝟙 _) wx wx c = c
参数：wx : X -> N；c : AlgebraicCycle X R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsupp.map_id`：map_id [PrespectralSpace X] (hw : forall
 z : X, w z = 1) : map id w isSpectralMap_id c = c
· 使用定理 `AlgebraicGeometry.instPrespectralSpaceCarrierCarrierCommRingCat`：∀ {X : 
AlgebraicGeometry.Scheme}, PrespectralSpace ↥X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.Scheme.Hom.residueDegree_id`：∀ {X : AlgebraicGeometry.
Scheme} (x : ↥X),   AlgebraicGeometry.Scheme.Hom.residueDegree (CategoryTheory.C
ategoryStruct.id X) x = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma map_id {N : Type*} [DecidableEq N] (wx : X → N) (c : AlgebraicCycle X R) :
    map (𝟙 _) wx wx c = c := by
  apply Function.locallyFinsupp.map_id
  simp [mapCoeff]

end AlgebraicGeometry.AlgebraicCycle

