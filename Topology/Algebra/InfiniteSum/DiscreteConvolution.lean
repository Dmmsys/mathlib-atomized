/-
Copyright (c) 2026 Fengyang Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fengyang Wang
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Data.Set.MulAntidiagonal

/-!
# Discrete Convolution

Discrete convolution over monoids: `(f ⋆[L] g) x = ∑' (a, b) : mulFiber x, L (f a) (g b)`
where `mulFiber x = {(a, b) | a * b = x}`. Additive monoids are also supported.

## Design

Uses a bilinear map `L : E →ₗ[S] E' →ₗ[S] F` to combine values, following
`MeasureTheory.convolution`.

The index monoid `M` can be non-commutative (group algebras R[G] with non-abelian G).

`@[to_additive]` generates multiplicative and additive versions from a single definition.
The `mul/add` distinction refers to the index monoid `M`: multiplicative sums over
`mulFiber x = {(a,b) | a * b = x}`, additive sums over `addFiber x = {(a,b) | a + b = x}`.

## Main Definitions

* `mulFiber x`: the fiber of multiplication at `x`, all pairs `(a, b)` with `a * b = x`.
* `convolution L f g`: the discrete convolution
  `(f ⋆[L] g) x = ∑' ab : mulFiber x, L (f ab.1) (g ab.2)`.
* `ConvolutionExistsAt L f g x`: the convolution sum is summable at `x`.
* `ConvolutionExists L f g`: the convolution sum is summable at every point.

## Main Results

* `convolution_indicator_one_left`, `convolution_indicator_one_right`: identity element
  (`Set.indicator {1} (fun _ => e)` where `L e` is the identity map)
* `ConvolutionExists.distrib_add`, `ConvolutionExists.add_distrib`: distributivity over addition
* `ConvolutionExistsAt.smul_convolution`, `ConvolutionExistsAt.convolution_smul`:
  scalar multiplication
* `convolution_comm`: commutativity for symmetric bilinear maps over commutative monoids

## Notation

| Notation | Operation |
|--------------|-------------------------------------------------|
| `f ⋆[L] g` | `∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)` |
| `f ⋆₊[L] g` | `∑' ab : addFiber x, L (f ab.1.1) (g ab.1.2)` |

Precedence design: `f:68` and `g:67` gives right associativity (`f ⋆ g ⋆ h` parses as
`f ⋆ (g ⋆ h)`), matching function composition `∘` and `MeasureTheory.convolution`.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace DiscreteConvolution

variable {M S E E' E'' F F' G R : Type*}

/-! ### Multiplication Fiber -/

section Fiber

variable [Monoid M]

/-- The fiber of multiplication at `x`: all pairs `(a, b)` with `a * b = x`. -/
@[to_additive /-- The fiber of addition at `x`: all pairs `(a, b)` with `a + b = x`. -/]
/--
Definition of `mulFiber` / `mulFiber` 的定义

English:
definition mulFiber
  signature: (x : M)
  body: Set.mulAntidiagonal Set.univ Set.univ x

@[to_additive (attr := grind =)]

中文:
定义 mulFiber
  签名: (x : M)
  定义体: Set.mulAntidiagonal Set.univ Set.univ x

@[to_additive (attr := grind =)]

Depends on / 依赖: Set.mulAntidiagonal, Set.univ, mulAntidiagonal
-/
def mulFiber (x : M) : Set (M × M) := Set.mulAntidiagonal Set.univ Set.univ x

@[to_additive (attr := grind =)]
/--
lemma `mem_mulFiber` / 引理 `mem_mulFiber`

English:
lemma mem_mulFiber
  given: {x : M} {ab : M × M}
  statement: ab in mulFiber x ↔ ab.1 * ab.2 = x
  proof: by simp [mulFiber]

@[to_additive]

中文:
引理 mem_mulFiber
  条件: {x : M} {ab : M × M}
  结论: ab in mulFiber x ↔ ab.1 * ab.2 = x
  证明: by simp [mulFiber]

@[to_additive]

Depends on / 依赖: mulFiber
-/
lemma mem_mulFiber {x : M} {ab : M × M} : ab in mulFiber x ↔ ab.1 * ab.2 = x := by simp [mulFiber]

@[to_additive]
/--
lemma `mulFiber_one_mem` / 引理 `mulFiber_one_mem`

English:
lemma mulFiber_one_mem
  statement: (1, 1) in mulFiber (1 : M)
  proof: by simp [mulFiber]

中文:
引理 mulFiber_one_mem
  结论: (1, 1) in mulFiber (1 : M)
  证明: by simp [mulFiber]

Depends on / 依赖: mulFiber
-/
lemma mulFiber_one_mem : (1, 1) in mulFiber (1 : M) := by simp [mulFiber]

end Fiber

/-! ### Convolution Definition and Existence -/

section Definition

variable [Monoid M] [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F]
variable [TopologicalSpace F]

/-- The discrete convolution of `f` and `g` using bilinear map `L`:
`(f ⋆[L] g) x = ∑' (a, b) : mulFiber x, L (f a) (g b)`. -/
@[to_additive (dont_translate := S E E' F) addConvolution
  /-- Additive convolution: `(f ⋆₊[L] g) x = ∑' ab : addFiber x, L (f ab.1) (g ab.2)`. -/]
/--
Definition of `convolution` / `convolution` 的定义

English:
definition convolution
  signature: (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E) (g : M -> E')
  body: fun x => ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)

中文:
定义 convolution
  签名: (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E) (g : M -> E')
  定义体: fun x => ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)

Depends on / 依赖: mulFiber
-/
def convolution (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E) (g : M -> E') : M -> F :=
  fun x => ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)

/-- Notation for discrete convolution with explicit bilinear map:
`(f ⋆[L] g) x = ∑' ab : mulFiber x, L (f ab.1) (g ab.2)`. -/
scoped notation:67 f:68 " ⋆[" L "] " g:67 => convolution L f g

/-- Notation for additive convolution with explicit bilinear map:
`(f ⋆₊[L] g) x = ∑' ab : addFiber x, L (f ab.1) (g ab.2)`. -/
scoped notation:67 f:68 " ⋆₊[" L "] " g:67 => addConvolution L f g

end Definition

section BasicProperties

variable [Monoid M] [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F]
variable [TopologicalSpace F]

@[to_additive (dont_translate := S E E' F) (attr := simp) zero_addConvolution]
/--
lemma `zero_convolution` / 引理 `zero_convolution`

English:
lemma zero_convolution
  given: (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E')
  proof: by
  ext; simp [convolution]

@[to_additive (dont_translate := S E E' F) (attr := simp) addConvolution_zero]

中文:
引理 zero_convolution
  条件: (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E')
  证明: by
  ext; simp [convolution]

@[to_additive (dont_translate := S E E' F) (attr := simp) addConvolution_zero]

Depends on / 依赖: convolution
-/
lemma zero_convolution (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E') :
    (0 : M -> E) ⋆[L] f = 0 := by
  ext; simp [convolution]

@[to_additive (dont_translate := S E E' F) (attr := simp) addConvolution_zero]
/--
lemma `convolution_zero` / 引理 `convolution_zero`

English:
lemma convolution_zero
  given: (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E)
  proof: by
  ext; simp [convolution]

@[to_additive (dont_translate := S E F) (attr := simp) addConvolution_indicator_zero_left]

中文:
引理 convolution_zero
  条件: (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E)
  证明: by
  ext; simp [convolution]

@[to_additive (dont_translate := S E F) (attr := simp) addConvolution_indicator_zero_left]

Depends on / 依赖: convolution
-/
lemma convolution_zero (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E) :
    f ⋆[L] (0 : M -> E') = 0 := by
  ext; simp [convolution]

@[to_additive (dont_translate := S E F) (attr := simp) addConvolution_indicator_zero_left]
/--
lemma `convolution_indicator_one_left` / 引理 `convolution_indicator_one_left`

English:
lemma convolution_indicator_one_left
  statement: (L : E ->ₗ[S] F ->ₗ[S] F) (e : E) (f : M -> F)
  proof: by
  classical
  ext x; simp only [convolution, Set.indicator_apply]
  rw [tsum_eq_single (⟨(1]; rw [x)]; rw [by grind⟩ : mulFiber x) (by grind [LinearMap.zero_apply])]
  simp [hL]

@[to_additive (dont_translate := S E F) (attr := simp) addConvolution_indicator_zero_right]

中文:
引理 convolution_indicator_one_left
  结论: (L : E ->ₗ[S] F ->ₗ[S] F) (e : E) (f : M -> F)
  证明: by
  classical
  ext x; simp only [convolution, Set.indicator_apply]
  rw [tsum_eq_single (⟨(1]; rw [x)]; rw [by grind⟩ : mulFiber x) (by grind [LinearMap.zero_apply])]
  simp [hL]

@[to_additive (dont_translate := S E F) (attr := simp) addConvolution_indicator_zero_right]

Depends on / 依赖: LinearMap, LinearMap.zero_apply, Set.indicator_apply, classical, convolution, indicator_apply, mulFiber, tsum_eq_single, zero_apply
-/
lemma convolution_indicator_one_left (L : E ->ₗ[S] F ->ₗ[S] F) (e : E) (f : M -> F)
    (hL : forall y, L e y = y) :
    Set.indicator {1} (fun _ => e) ⋆[L] f = f := by
  classical
  ext x; simp only [convolution, Set.indicator_apply]
  rw [tsum_eq_single (⟨(1]; rw [x)]; rw [by grind⟩ : mulFiber x) (by grind [LinearMap.zero_apply])]
  simp [hL]

@[to_additive (dont_translate := S E F) (attr := simp) addConvolution_indicator_zero_right]
/--
lemma `convolution_indicator_one_right` / 引理 `convolution_indicator_one_right`

English:
lemma convolution_indicator_one_right
  statement: (L : F ->ₗ[S] E ->ₗ[S] F) (f : M -> F) (e : E)
  proof: by
  classical
  ext x; simp only [convolution, Set.indicator_apply]
  rw [tsum_eq_single (⟨(x]; rw [1)]; rw [by grind⟩ : mulFiber x) (by grind [LinearMap.zero_apply])]
  simp [hL]

中文:
引理 convolution_indicator_one_right
  结论: (L : F ->ₗ[S] E ->ₗ[S] F) (f : M -> F) (e : E)
  证明: by
  classical
  ext x; simp only [convolution, Set.indicator_apply]
  rw [tsum_eq_single (⟨(x]; rw [1)]; rw [by grind⟩ : mulFiber x) (by grind [LinearMap.zero_apply])]
  simp [hL]

Depends on / 依赖: LinearMap, LinearMap.zero_apply, Set.indicator_apply, classical, convolution, indicator_apply, mulFiber, tsum_eq_single, zero_apply
-/
lemma convolution_indicator_one_right (L : F ->ₗ[S] E ->ₗ[S] F) (f : M -> F) (e : E)
    (hL : forall y, L y e = y) :
    f ⋆[L] Set.indicator {1} (fun _ => e) = f := by
  classical
  ext x; simp only [convolution, Set.indicator_apply]
  rw [tsum_eq_single (⟨(x]; rw [1)]; rw [by grind⟩ : mulFiber x) (by grind [LinearMap.zero_apply])]
  simp [hL]

end BasicProperties

section ExistenceProperties

variable [Monoid M] [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F]
variable [TopologicalSpace F]

/-- The convolution of `f` and `g` with bilinear map `L` exists at `x` when the sum over
the fiber is summable. -/
@[to_additive (dont_translate := S E E' F) AddConvolutionExistsAt
  /-- Additive convolution exists at `x` when the fiber sum is summable. -/]
/--
Definition of `ConvolutionExistsAt` / `ConvolutionExistsAt` 的定义

English:
definition ConvolutionExistsAt
  signature: (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E) (g : M -> E') (x : M)
  body: Summable fun ab : mulFiber x => L (f ab.1.1) (g ab.1.2)

中文:
定义 ConvolutionExistsAt
  签名: (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E) (g : M -> E') (x : M)
  定义体: Summable fun ab : mulFiber x => L (f ab.1.1) (g ab.1.2)

Depends on / 依赖: Summable, mulFiber
-/
def ConvolutionExistsAt (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E) (g : M -> E') (x : M) : Prop :=
  Summable fun ab : mulFiber x => L (f ab.1.1) (g ab.1.2)

/-- The convolution of `f` and `g` with bilinear map `L` exists when it exists at every point. -/
@[to_additive (dont_translate := S E E' F) AddConvolutionExists
  /-- Additive convolution exists when it exists at every point. -/]
/--
Definition of `ConvolutionExists` / `ConvolutionExists` 的定义

English:
definition ConvolutionExists
  signature: (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E) (g : M -> E')
  body: forall x, ConvolutionExistsAt L f g x

中文:
定义 ConvolutionExists
  签名: (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E) (g : M -> E')
  定义体: forall x, ConvolutionExistsAt L f g x

Depends on / 依赖: ConvolutionExistsAt
-/
def ConvolutionExists (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E) (g : M -> E') : Prop :=
  forall x, ConvolutionExistsAt L f g x

variable [T2Space F] [ContinuousAdd F]

@[to_additive (dont_translate := S E E' F)]
/--
lemma `ConvolutionExistsAt.distrib_add` / 引理 `ConvolutionExistsAt.distrib_add`

English:
lemma ConvolutionExistsAt.distrib_add
  statement: {f : M -> E} {g g' : M -> E'} {x : M}
  proof: by
  simpa [convolution] using hfg.tsum_add hfg'

@[to_additive (dont_translate := S E E' F)]

中文:
引理 ConvolutionExistsAt.distrib_add
  结论: {f : M -> E} {g g' : M -> E'} {x : M}
  证明: by
  simpa [convolution] using hfg.tsum_add hfg'

@[to_additive (dont_translate := S E E' F)]
-/
lemma ConvolutionExistsAt.distrib_add {f : M -> E} {g g' : M -> E'} {x : M}
    (L : E ->ₗ[S] E' ->ₗ[S] F) (hfg : ConvolutionExistsAt L f g x)
    (hfg' : ConvolutionExistsAt L f g' x) :
    (f ⋆[L] (g + g')) x = (f ⋆[L] g) x + (f ⋆[L] g') x := by
  simpa [convolution] using hfg.tsum_add hfg'

@[to_additive (dont_translate := S E E' F)]
/--
lemma `ConvolutionExists.distrib_add` / 引理 `ConvolutionExists.distrib_add`

English:
lemma ConvolutionExists.distrib_add
  statement: {f : M -> E} {g g' : M -> E'} (L : E ->ₗ[S] E' ->ₗ[S] F)
  proof: by
  ext x; exact (hfg x).distrib_add L (hfg' x)

@[to_additive (dont_translate := S E E' F)]

中文:
引理 ConvolutionExists.distrib_add
  结论: {f : M -> E} {g g' : M -> E'} (L : E ->ₗ[S] E' ->ₗ[S] F)
  证明: by
  ext x; exact (hfg x).distrib_add L (hfg' x)

@[to_additive (dont_translate := S E E' F)]
-/
lemma ConvolutionExists.distrib_add {f : M -> E} {g g' : M -> E'} (L : E ->ₗ[S] E' ->ₗ[S] F)
    (hfg : ConvolutionExists L f g) (hfg' : ConvolutionExists L f g') :
    f ⋆[L] (g + g') = f ⋆[L] g + f ⋆[L] g' := by
  ext x; exact (hfg x).distrib_add L (hfg' x)

@[to_additive (dont_translate := S E E' F)]
/--
lemma `ConvolutionExistsAt.add_distrib` / 引理 `ConvolutionExistsAt.add_distrib`

English:
lemma ConvolutionExistsAt.add_distrib
  statement: {f f' : M -> E} {g : M -> E'} {x : M}
  proof: by
  simpa [convolution] using hfg.tsum_add hfg'

@[to_additive (dont_translate := S E E' F)]

中文:
引理 ConvolutionExistsAt.add_distrib
  结论: {f f' : M -> E} {g : M -> E'} {x : M}
  证明: by
  simpa [convolution] using hfg.tsum_add hfg'

@[to_additive (dont_translate := S E E' F)]
-/
lemma ConvolutionExistsAt.add_distrib {f f' : M -> E} {g : M -> E'} {x : M}
    (L : E ->ₗ[S] E' ->ₗ[S] F) (hfg : ConvolutionExistsAt L f g x)
    (hfg' : ConvolutionExistsAt L f' g x) :
    ((f + f') ⋆[L] g) x = (f ⋆[L] g) x + (f' ⋆[L] g) x := by
  simpa [convolution] using hfg.tsum_add hfg'

@[to_additive (dont_translate := S E E' F)]
/--
lemma `ConvolutionExists.add_distrib` / 引理 `ConvolutionExists.add_distrib`

English:
lemma ConvolutionExists.add_distrib
  statement: {f f' : M -> E} {g : M -> E'} (L : E ->ₗ[S] E' ->ₗ[S] F)
  proof: by
  ext x; exact (hfg x).add_distrib L (hfg' x)

中文:
引理 ConvolutionExists.add_distrib
  结论: {f f' : M -> E} {g : M -> E'} (L : E ->ₗ[S] E' ->ₗ[S] F)
  证明: by
  ext x; exact (hfg x).add_distrib L (hfg' x)
-/
lemma ConvolutionExists.add_distrib {f f' : M -> E} {g : M -> E'} (L : E ->ₗ[S] E' ->ₗ[S] F)
    (hfg : ConvolutionExists L f g) (hfg' : ConvolutionExists L f' g) :
    (f + f') ⋆[L] g = f ⋆[L] g + f' ⋆[L] g := by
  ext x; exact (hfg x).add_distrib L (hfg' x)

variable {F : Type*}
variable [AddCommMonoid F] [Module S F] [TopologicalSpace F] [ContinuousConstSMul S F] [T2Space F]

@[to_additive (dont_translate := S E E' F)]
/--
lemma `ConvolutionExistsAt.smul_convolution` / 引理 `ConvolutionExistsAt.smul_convolution`

English:
lemma ConvolutionExistsAt.smul_convolution
  statement: {c : S} {f : M -> E} {g : M -> E'} {x : M}
  proof: by
  simpa [convolution] using hfg.tsum_const_smul c

@[to_additive (dont_translate := S E E' F)]

中文:
引理 ConvolutionExistsAt.smul_convolution
  结论: {c : S} {f : M -> E} {g : M -> E'} {x : M}
  证明: by
  simpa [convolution] using hfg.tsum_const_smul c

@[to_additive (dont_translate := S E E' F)]

Depends on / 依赖: convolution, hfg.tsum_const_smul, tsum_const_smul
-/
lemma ConvolutionExistsAt.smul_convolution {c : S} {f : M -> E} {g : M -> E'} {x : M}
    (L : E ->ₗ[S] E' ->ₗ[S] F) (hfg : ConvolutionExistsAt L f g x) :
    ((c • f) ⋆[L] g) x = c • ((f ⋆[L] g) x) := by
  simpa [convolution] using hfg.tsum_const_smul c

@[to_additive (dont_translate := S E E' F)]
/--
lemma `ConvolutionExistsAt.convolution_smul` / 引理 `ConvolutionExistsAt.convolution_smul`

English:
lemma ConvolutionExistsAt.convolution_smul
  statement: {c : S} {f : M -> E} {g : M -> E'} {x : M}
  proof: by
  simpa [convolution] using hfg.tsum_const_smul c

中文:
引理 ConvolutionExistsAt.convolution_smul
  结论: {c : S} {f : M -> E} {g : M -> E'} {x : M}
  证明: by
  simpa [convolution] using hfg.tsum_const_smul c

Depends on / 依赖: convolution, hfg.tsum_const_smul, tsum_const_smul
-/
lemma ConvolutionExistsAt.convolution_smul {c : S} {f : M -> E} {g : M -> E'} {x : M}
    (L : E ->ₗ[S] E' ->ₗ[S] F) (hfg : ConvolutionExistsAt L f g x) :
    (f ⋆[L] (c • g)) x = c • ((f ⋆[L] g) x) := by
  simpa [convolution] using hfg.tsum_const_smul c

end ExistenceProperties

/-! ### Commutativity -/

section CommMonoid

variable [CommMonoid M] [CommSemiring S] [AddCommMonoid E] [Module S E] [TopologicalSpace E]

@[to_additive]
/--
Definition of `mulFiber_swapEquiv` / `mulFiber_swapEquiv` 的定义

English:
definition mulFiber_swapEquiv
  signature: (x : M)
  body: fun ⟨p, h⟩ => ⟨p.swap, by simp_all [mem_mulFiber, mul_comm]⟩
  invFun := fun ⟨p, h⟩ => ⟨p.swap, by simp_all [mem_mulFiber, mul_comm]⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl

@[to_additive (dont_translate := S E) addConvolution_comm]

中文:
定义 mulFiber_swapEquiv
  签名: (x : M)
  定义体: fun ⟨p, h⟩ => ⟨p.swap, by simp_all [mem_mulFiber, mul_comm]⟩
  invFun := fun ⟨p, h⟩ => ⟨p.swap, by simp_all [mem_mulFiber, mul_comm]⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl

@[to_additive (dont_translate := S E) addConvolution_comm]
-/
private def mulFiber_swapEquiv (x : M) : mulFiber x ≃ mulFiber x where
  toFun := fun ⟨p, h⟩ => ⟨p.swap, by simp_all [mem_mulFiber, mul_comm]⟩
  invFun := fun ⟨p, h⟩ => ⟨p.swap, by simp_all [mem_mulFiber, mul_comm]⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl

@[to_additive (dont_translate := S E) addConvolution_comm]
/--
theorem `convolution_comm` / 定理 `convolution_comm`

English:
theorem convolution_comm
  given: (L : E ->ₗ[S] E ->ₗ[S] E) (f g : M -> E) (hL : forall x y, L x y = L y x)
  proof: by
  unfold convolution; ext x
  rw [← (mulFiber_swapEquiv x).tsum_eq]
  congr 1; funext ⟨⟨a, b⟩, _⟩; exact hL (f b) (g a)

中文:
定理 convolution_comm
  条件: (L : E ->ₗ[S] E ->ₗ[S] E) (f g : M -> E) (hL : 对任意 x y, L x y = L y x)
  证明: by
  unfold convolution; ext x
  rw [← (mulFiber_swapEquiv x).tsum_eq]
  congr 1; funext ⟨⟨a, b⟩, _⟩; exact hL (f b) (g a)

Depends on / 依赖: convolution, mulFiber_swapEquiv, tsum_eq
-/
theorem convolution_comm (L : E ->ₗ[S] E ->ₗ[S] E) (f g : M -> E) (hL : forall x y, L x y = L y x) :
    f ⋆[L] g = g ⋆[L] f := by
  unfold convolution; ext x
  rw [← (mulFiber_swapEquiv x).tsum_eq]
  congr 1; funext ⟨⟨a, b⟩, _⟩; exact hL (f b) (g a)

end CommMonoid

end DiscreteConvolution

end
