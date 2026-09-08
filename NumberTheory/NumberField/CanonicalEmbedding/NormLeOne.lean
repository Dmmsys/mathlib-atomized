/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.PolarCoord
public import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Fundamental Cone: set of elements of norm ≤ 1

In this file, we study the subset `NormLeOne` of the `fundamentalCone` of elements `x` with
`mixedEmbedding.norm x ≤ 1`.

Mainly, we prove that it is bounded, its frontier has volume zero and compute its volume.

## Strategy of proof

The proof is loosely based on the strategy given in [D. Marcus, *Number Fields*][marcus1977number].

1. since `NormLeOne K` is norm-stable, in the sense that
  `normLeOne K = normAtAllPlaces⁻¹' (normAtAllPlaces '' (normLeOne K))`,
  see `normLeOne_eq_preimage_image`, it's enough to study the subset
  `normAtAllPlaces '' (normLeOne K)` of `realSpace K`.

2. A description of `normAtAllPlaces '' (normLeOne K)` is given by `normAtAllPlaces_normLeOne`, it
  is the set of `x : realSpace K`, nonnegative at all places, whose norm is nonzero and `≤ 1` and
  such that `logMap x` is in the `fundamentalDomain` of `basisUnitLattice K`.
  Note that, here and elsewhere, we identify `x` with its image in `mixedSpace K` given
  by `mixedSpaceOfRealSpace x`.

3. In order to describe the inverse image in `realSpace K` of the `fundamentalDomain` of
  `basisUnitLattice K`, we define the map `expMap : realSpace K → realSpace K` that is, in
  some way, the right inverse of `logMap`, see `logMap_expMap`.

4. Denote by `ηᵢ` (with `i ≠ w₀` where `w₀` is the distinguished infinite place,
  see the description of `logSpace` below) the fundamental system of units given by
  `fundSystem` and let `|ηᵢ|` denote `normAtAllPlaces (mixedEmbedding ηᵢ)`, that is the vector
  `(w (ηᵢ))_w` in `realSpace K`. Then, the image of `|ηᵢ|` by `expMap.symm` form a basis of the
  subspace `{x : realSpace K | ∑ w, x w = 0}`. We complete by adding the vector `(mult w)_w` to
  get a basis, called `completeBasis`, of `realSpace K`. The basis `completeBasis K` has
  the property that, for `i ≠ w₀`, the image of `completeBasis K i` by the
  natural restriction map `realSpace K → logSpace K` is `basisUnitLattice K`.

5. At this point, we can construct the map `expMapBasis` that plays a crucial part in the proof.
  It is the map that sends `x : realSpace K` to `Real.exp (x w₀) * ∏_{i ≠ w₀} |ηᵢ| ^ x i`, see
  `expMapBasis_apply'`. Then, we prove a change of variable formula for `expMapBasis`, see
  `setLIntegral_expMapBasis_image`.

6. We define a set `paramSet` in `realSpace K` and prove that
  `normAtAllPlaces '' (normLeOne K) = expMapBasis (paramSet K)`, see
  `normAtAllPlaces_normLeOne_eq_image`. Using this, `setLIntegral_expMapBasis_image` and the results
  from `mixedEmbedding.polarCoord`, we can then compute the volume of `normLeOne K`, see
  `volume_normLeOne`.

7. Finally, we need to prove that the frontier of `normLeOne K` has zero-volume (we will prove
  in passing that `normLeOne K` is bounded.) For that we prove that
  `volume (interior (normLeOne K)) = volume (closure (normLeOne K))`, see
  `volume_interior_eq_volume_closure`. Since we know that the volume of `interior (normLeOne K)` is
  finite since it is bounded by the volume of `normLeOne K`, the result follows, see
  `volume_frontier_normLeOne`. We proceed in several steps.

  7.1. We prove first that
    `normAtAllPlaces⁻¹' (expMapBasis '' interior (paramSet K)) ⊆ interior (normLeOne K)`, see
    `subset_interior_normLeOne` (Note that here again we identify `realSpace K` with its image
    in `mixedSpace K`). The main argument is that `expMapBasis` is an open partial homeomorphism
    and that `interior (paramSet K)` is a subset of its source, so its image by `expMapBasis`
    is still open.

  7.2. The same kind of argument does not work with `closure (paramSet)` since it is not contained
    in the source of `expMapBasis`. So we define a compact set, called `compactSet K`, such that
    `closure (normLeOne K) ⊆ normAtAllPlaces⁻¹' (compactSet K)`, see `closure_normLeOne_subset`,
    and it is almost equal to `expMapBasis '' closure (paramSet K)`, see `compactSet_ae`.

  7.3. We get from the above that `normLeOne K ⊆ normAtAllPlaces⁻¹' (compactSet K)`, from which
    it follows easily that `normLeOne K` is bounded, see `isBounded_normLeOne`.

  7.4. Finally, we prove that `volume (normAtAllPlaces ⁻¹' compactSet K) =
    volume (normAtAllPlaces ⁻¹' (expMapBasis '' interior (paramSet K)))`, which implies that
    `volume (interior (normLeOne K)) = volume (closure (normLeOne K))` by the above and the fact
    that `volume (interior (normLeOne K)) ≤ volume (closure (normLeOne K))`, which boils down to
    the fact that the interior and closure of `paramSet K` are almost equal, see
    `closure_paramSet_ae_interior`.

## Spaces and maps

To help understand the proof, we make a list of (almost) all the spaces and maps used and
their connections (as hinted above, we do not mention the map `mixedSpaceOfRealSpace` since we
identify `realSpace K` with its image in `mixedSpace K`).

* `mixedSpace`: the set `({w // IsReal w} → ℝ) × (w // IsComplex w → ℂ)` where `w` denote the
  infinite places of `K`.

* `realSpace`: the set `w → ℝ` where `w` denote the infinite places of `K`

* `logSpace`: the set `{w // w ≠ w₀} → ℝ` where `w₀` is a distinguished place of `K`. It is the set
  used in the proof of Dirichlet Unit Theorem.

* `mixedEmbedding : K → mixedSpace K`: the map that sends `x : K` to `φ_w(x)` where, for all
  infinite place `w`, `φ_w : K → ℝ` or `ℂ`, resp. if `w` is real or if `w` is complex, denote a
  complex embedding associated to `w`.

* `logEmbedding : (𝓞 K)ˣ → logSpace K`: the map that sends the unit `u : (𝓞 K)ˣ` to
  `(mult w * log (w u))_w` for `w ≠ w₀`. Its image is `unitLattice K`, a `ℤ`-lattice of
  `logSpace K`, that admits `basisUnitLattice K` as a basis.

* `logMap : mixedSpace K → logSpace K`: this map is defined such that it factors `logEmbedding`,
  that is, for `u : (𝓞 K)ˣ`, `logMap (mixedEmbedding x) = logEmbedding x`, and that
  `logMap (c • x) = logMap x` for `c ≠ 0` and `norm x ≠ 0`. The inverse image of the fundamental
  domain of `basisUnitLattice K` by `logMap` (minus the elements of norm zero) is
  `fundamentalCone K`.

* `expMap : realSpace K → realSpace K`: the right inverse of `logMap` in the sense that
  `logMap (expMap x) = (x_w)_{w ≠ w₀}`.

* `expMapBasis : realSpace K → realSpace K`: the map that sends `x : realSpace K` to
  `Real.exp (x w₀) * ∏_{i ≠ w₀} |ηᵢ| ^ x i` where `|ηᵢ|` denote the vector of `realSpace K` given
  by `w (ηᵢ)` and `ηᵢ` denote the units in `fundSystem K`.

-/

@[expose] public section

variable (K : Type*) [Field K]

open Finset Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units dirichletUnitTheorem

namespace NumberField.mixedEmbedding.fundamentalCone

section normAtAllPlaces

variable [NumberField K]

variable {K}

/-
**NumberField.mixedEmbedding.fundamentalCone.logMap_normAtAllPlaces** 是 Mathlib 
中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：logMap_normAtAllPlaces (x : mixedSpace K) : logMap (mixedSpaceOfRealSpace 
(normAtAllPlaces x)) = logMap x
参数：x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.mixedEmbedding.logMap_eq_of_normAtPlace_eq`：logMap_eq_of_nor
mAtPlace_eq (h : forall w, normAtPlace w x = normAtPlace w y) : logMap x = logMa
p y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_mixedSpaceOfRealSpace`：normAtPlac
e_mixedSpaceOfRealSpace {x : realSpace K} {w : InfinitePlace K} (hx : 0 <= x w) 
: normAtPlace w (mixedSpaceOfRealSpace x) = x w
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_nonneg`：normAtPlace_nonneg (w : I
nfinitePlace K) (x : mixedSpace K) : 0 <= normAtPlace w x
-/
theorem logMap_normAtAllPlaces (x : mixedSpace K) :
    logMap (mixedSpaceOfRealSpace (normAtAllPlaces x)) = logMap x :=
  logMap_eq_of_normAtPlace_eq
    fun w ↦ by rw [normAtPlace_mixedSpaceOfRealSpace (normAtPlace_nonneg w x)]
/-
**NumberField.mixedEmbedding.fundamentalCone.norm_normAtAllPlaces** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：norm_normAtAllPlaces (x : mixedSpace K) : mixedEmbedding.norm (mixedSpaceO
fRealSpace (normAtAllPlaces x)) = mixedEmbedding.norm x
参数：x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_mixedSpaceOfRealSpace`：normAtPlac
e_mixedSpaceOfRealSpace {x : realSpace K} {w : InfinitePlace K} (hx : 0 <= x w) 
: normAtPlace w (mixedSpaceOfRealSpace x) = x w
· 使用定理 `NumberField.mixedEmbedding.normAtAllPlaces_nonneg`：normAtAllPlaces_nonne
g (x : mixedSpace K) (w : InfinitePlace K) : 0 <= normAtAllPlaces x w
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_normAtAllPlaces (x : mixedSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (normAtAllPlaces x)) = mixedEmbedding.norm x := by
  simp_rw [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (normAtAllPlaces_nonneg _ _)]
/-
**NumberField.mixedEmbedding.fundamentalCone.normAtAllPlaces_mem_fundamentalCone
_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：normAtAllPlaces_mem_fundamentalCone_iff {x : mixedSpace K} : mixedSpaceOfR
ealSpace (normAtAllPlaces x) in fundamentalCone K ↔ x in fundamentalCone K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.logMap_normAtAllPlaces`：logMa
p_normAtAllPlaces (x : mixedSpace K) : logMap (mixedSpaceOfRealSpace (normAtAllP
laces x)) = logMap x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.norm_normAtAllPlaces`：norm_no
rmAtAllPlaces (x : mixedSpace K) : mixedEmbedding.norm (mixedSpaceOfRealSpace (n
ormAtAllPlaces x)) = mixedEmbedding.norm x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem normAtAllPlaces_mem_fundamentalCone_iff {x : mixedSpace K} :
    mixedSpaceOfRealSpace (normAtAllPlaces x) ∈ fundamentalCone K ↔ x ∈ fundamentalCone K := by
  simp_rw [fundamentalCone, Set.mem_sdiff, Set.mem_preimage, logMap_normAtAllPlaces,
    Set.mem_ofPred_eq, norm_normAtAllPlaces]

end normAtAllPlaces

section normLeOne_def

variable [NumberField K]

/--
The set of elements of the `fundamentalCone` of `norm ≤ 1`.
-/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**NumberField.mixedEmbedding.fundamentalCone.normLeOne** 是 Mathlib 中的一个缩写定义，位于命名
空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：normLeOne : Set (mixedSpace K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev normLeOne : Set (mixedSpace K) :=
  fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ 1}

variable {K} in
/-
**NumberField.mixedEmbedding.fundamentalCone.mem_normLeOne** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：mem_normLeOne {x : mixedSpace K} : x in normLeOne K ↔ x in fundamentalCone
 K ∧ mixedEmbedding.norm x <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_sep_iff`：mem_sep_iff : x in { x in s | p x } ↔ x in s ∧ p x
-/
theorem mem_normLeOne {x : mixedSpace K} :
    x ∈ normLeOne K ↔ x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1 := Set.mem_sep_iff
/-
**NumberField.mixedEmbedding.fundamentalCone.measurableSet_normLeOne** 是 Mathlib
 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：measurableSet_normLeOne : MeasurableSet (normLeOne K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `NumberField.mixedEmbedding.measurableSet_fundamentalCone`：measurableSet_
fundamentalCone : MeasurableSet (fundamentalCone K)
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `NumberField.mixedEmbedding.continuous_norm`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], Continuous ⇑NumberField.mixedEmbedding.norm
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem measurableSet_normLeOne :
    MeasurableSet (normLeOne K) :=
  (measurableSet_fundamentalCone K).inter <|
    measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const
/-
**NumberField.mixedEmbedding.fundamentalCone.normLeOne_eq_preimage_image** 是 Mat
hlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：normLeOne_eq_preimage_image : normLeOne K = normAtAllPlaces ⁻¹' normAtAllP
laces '' (normLeOne K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.mem_normLeOne`：mem_normLeOne 
{x : mixedSpace K} : x in normLeOne K ↔ x in fundamentalCone K ∧ mixedEmbedding.
norm x <= 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.normAtAllPlaces_mem_fundament
alCone_iff`：normAtAllPlaces_mem_fundamentalCone_iff {x : mixedSpace K} : mixedSp
aceOfRealSpace (normAtAllPlaces x) in fundamentalCone K ↔ x in fundament…
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.norm_normAtAllPlaces`：norm_no
rmAtAllPlaces (x : mixedSpace K) : mixedEmbedding.norm (mixedSpaceOfRealSpace (n
ormAtAllPlaces x)) = mixedEmbedding.norm x
-/
theorem normLeOne_eq_preimage_image :
    normLeOne K = normAtAllPlaces ⁻¹' normAtAllPlaces '' (normLeOne K) := by
  refine subset_antisymm (Set.subset_preimage_image _ _) ?_
  rintro x ⟨y, hy₁, hy₂⟩
  rw [mem_normLeOne, ← normAtAllPlaces_mem_fundamentalCone_iff, ← norm_normAtAllPlaces,
    ← mem_normLeOne] at hy₁ ⊢
  rwa [← hy₂]

open scoped Classical in
/-
**NumberField.mixedEmbedding.fundamentalCone.normAtAllPlaces_normLeOne** 是 Mathl
ib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：normAtAllPlaces_normLeOne : normAtAllPlaces '' (normLeOne K) = mixedSpaceO
fRealSpace ⁻¹' (logMap ⁻¹' ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatt
iceBasis Real (unitLattice K))) inter {x | (forall w, 0 <= x w)} inter {x | mixe
dEmbedding.norm (mixedSpaceOfRealSpace x) != 0} inter {x | mixedEmbedding.norm (
mixedSpaceOfRealSpace x) <= 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.logMap_normAtAllPlaces`：logMa
p_normAtAllPlaces (x : mixedSpace K) : logMap (mixedSpaceOfRealSpace (normAtAllP
laces x)) = logMap x
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_nonneg`：normAtPlace_nonneg (w : I
nfinitePlace K) (x : mixedSpace K) : 0 <= normAtPlace w x
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.norm_normAtAllPlaces`：norm_no
rmAtAllPlaces (x : mixedSpace K) : mixedEmbedding.norm (mixedSpaceOfRealSpace (n
ormAtAllPlaces x)) = mixedEmbedding.norm x
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `NumberField.mixedEmbedding.normAtAllPlaces_mixedSpaceOfRealSpace`：normAt
AllPlaces_mixedSpaceOfRealSpace {x : realSpace K} (hx : forall w, 0 <= x w) : no
rmAtAllPlaces (mixedSpaceOfRealSpace x) = x
-/
theorem normAtAllPlaces_normLeOne :
    normAtAllPlaces '' (normLeOne K) =
    mixedSpaceOfRealSpace ⁻¹'
      (logMap ⁻¹'
          ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K))) ∩
      {x | (∀ w, 0 ≤ x w)} ∩
      {x | mixedEmbedding.norm (mixedSpaceOfRealSpace x) ≠ 0} ∩
      {x | mixedEmbedding.norm (mixedSpaceOfRealSpace x) ≤ 1} := by
  ext x
  refine ⟨?_, fun ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ ↦ ?_⟩
  · rintro ⟨y, ⟨⟨h₁, h₂⟩, h₃⟩, rfl⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rwa [Set.mem_preimage, ← logMap_normAtAllPlaces] at h₁
    · exact fun w ↦ normAtPlace_nonneg w y
    · rwa [Set.mem_ofPred_eq, ← norm_normAtAllPlaces] at h₂
    · rwa [Set.mem_ofPred_eq, ← norm_normAtAllPlaces] at h₃
  · exact ⟨mixedSpaceOfRealSpace x, ⟨⟨h₁, h₃⟩, h₄⟩, normAtAllPlaces_mixedSpaceOfRealSpace h₂⟩

end normLeOne_def

noncomputable section expMap

variable {K}

/--
The component of `expMap` at the place `w`.
-/
@[simps]
/-
**NumberField.mixedEmbedding.fundamentalCone.expMap_single** 是 Mathlib 中的一个定义，位于
命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMap_single (w : InfinitePlace K) : OpenPartialHomeomorph Real Real wher
e toFun
参数：w : InfinitePlace K。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
The component of `expMap` at the place `w`.
-/
def expMap_single (w : InfinitePlace K) : OpenPartialHomeomorph ℝ ℝ where
  toFun := fun x ↦ Real.exp ((w.mult : ℝ)⁻¹ * x)
  invFun := fun x ↦ w.mult * Real.log x
  source := Set.univ
  target := Set.Ioi 0
  open_source := isOpen_univ
  open_target := isOpen_Ioi
  map_source' _ _ := Real.exp_pos _
  map_target' _ _ := trivial
  left_inv' _ _ := by simp only [Real.log_exp, mul_inv_cancel_left₀ mult_coe_ne_zero]
  right_inv' _ h := by simp only [inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log h]
  continuousOn_toFun := (continuousOn_const.mul continuousOn_id).rexp
  continuousOn_invFun := continuousOn_const.mul (Real.continuousOn_log.mono (by simp))

/--
The derivative of `expMap_single`, see `hasDerivAt_expMap_single`.
-/
/-
**NumberField.mixedEmbedding.fundamentalCone.deriv_expMap_single** 是 Mathlib 中的一
个缩写定义，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：deriv_expMap_single (w : InfinitePlace K) (x : Real) : Real
参数：w : InfinitePlace K；x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivative of `expMap_single`, see `hasDerivAt_expMap_single`.
-/
abbrev deriv_expMap_single (w : InfinitePlace K) (x : ℝ) : ℝ :=
  (expMap_single w x) * (w.mult : ℝ)⁻¹
/-
**NumberField.mixedEmbedding.fundamentalCone.hasDerivAt_expMap_single** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：hasDerivAt_expMap_single (w : InfinitePlace K) (x : Real) : HasDerivAt (ex
pMap_single w) (deriv_expMap_single w x) x
参数：w : InfinitePlace K；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `trivial`：True
· 使用定理 `PartialEquiv.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} (toFun toFun
_1 : α → β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : 
invFun = invFun_…
· 使用定理 `PartialHomeomorph.mk.congr_simp`：∀ {X : Type u_7} {Y : Type u_8} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (toPartialEquiv toPartialEq
uiv_1 : PartialEquiv …
· 使用定理 `OpenPartialHomeomorph.mk.congr_simp`：∀ {X : Type u_7} {Y : Type u_8} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (toPartialHomeomorph to
PartialHomeomorph_1 : Par…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `Real.hasDerivAt_exp`：hasDerivAt_exp (x : Real) : HasDerivAt exp (exp x) 
x
· 使用定理 `hasDerivAt_mul_const`：hasDerivAt_mul_const (c : 𝕜) : HasDerivAt (fun x =
> x * c) c x
-/
theorem hasDerivAt_expMap_single (w : InfinitePlace K) (x : ℝ) :
    HasDerivAt (expMap_single w) (deriv_expMap_single w x) x := by
  simpa [expMap_single, mul_comm] using!
    (HasDerivAt.comp x (Real.hasDerivAt_exp _) (hasDerivAt_mul_const (w.mult : ℝ)⁻¹))


variable [NumberField K]

/--
The map from `realSpace K → realSpace K` whose components is given by `expMap_single`. It is, in
some respect, a right inverse of `logMap`, see `logMap_expMap`.
-/
/-
**NumberField.mixedEmbedding.fundamentalCone.expMap** 是 Mathlib 中的一个定义，位于命名空间 `N
umberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMap : OpenPartialHomeomorph (realSpace K) (realSpace K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from `realSpace K → realSpace K` whose components is given by `expMap_si
ngle`. It is, in
some respect, a right inverse of `logMap`, see `logMap_expMap`.
-/
def expMap : OpenPartialHomeomorph (realSpace K) (realSpace K) :=
  OpenPartialHomeomorph.pi fun w ↦ expMap_single w

variable (K)
/-
**NumberField.mixedEmbedding.fundamentalCone.expMap_source** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMap_source : expMap.source = (Set.univ : Set (realSpace K))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.pi_toPartialHomeomorph`：∀ {ι : Type u_7} [inst : F
inite ι] {X : ι → Type u_8} {Y : ι → Type u_9} [inst_1 : (i : ι) → TopologicalSp
ace (X i)]   [inst_2 : (i : ι) → T…
· 使用定理 `PartialEquiv.pi_source`：∀ {ι : Type u_5} {αi : ι → Type u_6} {βi : ι → T
ype u_7} (ei : (i : ι) → PartialEquiv (αi i) (βi i)),   (PartialEquiv.pi ei).sou
rce = Set.un…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.pi_univ`：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = 
univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expMap_source :
    expMap.source = (Set.univ : Set (realSpace K)) := by
  simp_rw [expMap, OpenPartialHomeomorph.pi_toPartialHomeomorph,
    PartialEquiv.pi_source, expMap_single, Set.pi_univ Set.univ]
/-
**NumberField.mixedEmbedding.fundamentalCone.expMap_target** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMap_target : expMap.target = Set.univ.pi fun (_ : InfinitePlace K) => S
et.Ioi 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.pi_toPartialHomeomorph`：∀ {ι : Type u_7} [inst : F
inite ι] {X : ι → Type u_8} {Y : ι → Type u_9} [inst_1 : (i : ι) → TopologicalSp
ace (X i)]   [inst_2 : (i : ι) → T…
· 使用定理 `PartialEquiv.pi_target`：∀ {ι : Type u_5} {αi : ι → Type u_6} {βi : ι → T
ype u_7} (ei : (i : ι) → PartialEquiv (αi i) (βi i)),   (PartialEquiv.pi ei).tar
get = Set.un…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expMap_target :
    expMap.target = Set.univ.pi fun (_ : InfinitePlace K) ↦ Set.Ioi 0 := by
  simp_rw [expMap, OpenPartialHomeomorph.pi_toPartialHomeomorph,
    PartialEquiv.pi_target, expMap_single]
/-
**NumberField.mixedEmbedding.fundamentalCone.injective_expMap** 是 Mathlib 中的一个定理
，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：injective_expMap : Function.Injective (expMap : realSpace K -> realSpace K
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.injOn_univ`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Set.InjOn f
 Set.univ ↔ Function.Injective f
· 使用定理 `OpenPartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InjOn (↑e) …
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMap_source`：expMap_source 
: expMap.source = (Set.univ : Set (realSpace K))
-/
theorem injective_expMap :
    Function.Injective (expMap : realSpace K → realSpace K) :=
  Set.injOn_univ.1 (expMap_source K ▸ expMap.injOn)
/-
**NumberField.mixedEmbedding.fundamentalCone.continuous_expMap** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：continuous_expMap : Continuous (expMap : realSpace K -> realSpace K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `OpenPartialHomeomorph.continuousOn`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y), ContinuousOn (↑…
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMap_source`：expMap_source 
: expMap.source = (Set.univ : Set (realSpace K))
-/
theorem continuous_expMap :
    Continuous (expMap : realSpace K → realSpace K) :=
  continuousOn_univ.mp <| (expMap_source K) ▸ expMap.continuousOn

variable {K}

@[simp]
/-
**NumberField.mixedEmbedding.fundamentalCone.expMap_apply** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMap_apply (x : realSpace K) (w : InfinitePlace K) : expMap x w = Real.e
xp ((↑w.mult)⁻¹ * x w)
参数：x : realSpace K；w : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem expMap_apply (x : realSpace K) (w : InfinitePlace K) :
    expMap x w = Real.exp ((↑w.mult)⁻¹ * x w) := rfl
/-
**NumberField.mixedEmbedding.fundamentalCone.expMap_pos** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMap_pos (x : realSpace K) (w : InfinitePlace K) : 0 < expMap x w
参数：x : realSpace K；w : InfinitePlace K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
-/
theorem expMap_pos (x : realSpace K) (w : InfinitePlace K) :
    0 < expMap x w := Real.exp_pos _
/-
**NumberField.mixedEmbedding.fundamentalCone.expMap_smul** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMap_smul (c : Real) (x : realSpace K) : expMap (c • x) = (expMap x) ^ c
参数：c : Real；x : realSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.exp_mul`：exp_mul (x y : Real) : exp (x * y) = exp x ^ y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expMap_smul (c : ℝ) (x : realSpace K) :
    expMap (c • x) = (expMap x) ^ c := by
  ext
  simp [mul_comm c _, ← mul_assoc, Real.exp_mul]
/-
**NumberField.mixedEmbedding.fundamentalCone.expMap_add** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMap_add (x y : realSpace K) : expMap (x + y) = expMap x * expMap y
参数：x y : realSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expMap_add (x y : realSpace K) :
    expMap (x + y) = expMap x * expMap y := by
  ext
  simp [mul_add, Real.exp_add]
/-
**NumberField.mixedEmbedding.fundamentalCone.expMap_sum** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMap_sum {ι : Type*} (s : Finset ι) (f : ι -> realSpace K) : expMap (∑ i
 in s, f i) = ∏ i in s, expMap (f i)
参数：s : Finset ι；f : ι -> realSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expMap_sum {ι : Type*} (s : Finset ι) (f : ι → realSpace K) :
    expMap (∑ i ∈ s, f i) = ∏ i ∈ s, expMap (f i) := by
  ext
  simp [← Real.exp_sum, ← mul_sum]

@[simp]
/-
**NumberField.mixedEmbedding.fundamentalCone.expMap_symm_apply** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMap_symm_apply (x : realSpace K) (w : InfinitePlace K) : expMap.symm x 
w = ↑w.mult * Real.log (x w)
参数：x : realSpace K；w : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem expMap_symm_apply (x : realSpace K) (w : InfinitePlace K) :
    expMap.symm x w = ↑w.mult * Real.log (x w) := rfl
/-
**NumberField.mixedEmbedding.fundamentalCone.logMap_expMap** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：logMap_expMap {x : realSpace K} (hx : mixedEmbedding.norm (mixedSpaceOfRea
lSpace (expMap x)) = 1) : logMap (mixedSpaceOfRealSpace (expMap x)) = fun w => x
 w.1
参数：hx : mixedEmbedding.norm (mixedSpaceOfRealSpace (expMap x)) = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.logMap.eq_1`：∀ {K : Type u_1} [inst : Field K
] [inst_1 : NumberField K] (x : NumberField.mixedEmbedding.mixedSpace K)   (w : 
{ w // w ≠ NumberField.Units…
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_mixedSpaceOfRealSpace`：normAtPlac
e_mixedSpaceOfRealSpace {x : realSpace K} {w : InfinitePlace K} (hx : 0 <= x w) 
: normAtPlace w (mixedSpaceOfRealSpace x) = x w
· 使用引理 `Real.exp_nonneg`：exp_nonneg (x : Real) : 0 <= exp x
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMap_apply`：expMap_apply (x
 : realSpace K) (w : InfinitePlace K) : expMap x w = Real.exp ((↑w.mult)⁻¹ * x w
)
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `NumberField.InfinitePlace.mult_coe_ne_zero`：mult_coe_ne_zero {w : Infini
tePlace K} : (mult w : Real) != 0
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem logMap_expMap {x : realSpace K}
    (hx : mixedEmbedding.norm (mixedSpaceOfRealSpace (expMap x)) = 1) :
    logMap (mixedSpaceOfRealSpace (expMap x)) = fun w ↦ x w.1 := by
  ext
  rw [logMap, normAtPlace_mixedSpaceOfRealSpace (Real.exp_nonneg _), expMap_apply, Real.log_exp,
    mul_sub, mul_inv_cancel_left₀ mult_coe_ne_zero, hx, Real.log_one, zero_mul, mul_zero, sub_zero]
/-
**NumberField.mixedEmbedding.fundamentalCone.sum_expMap_symm_apply** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：sum_expMap_symm_apply {x : K} (hx : x != 0) : ∑ w : InfinitePlace K, expMa
p.symm ((normAtAllPlaces (mixedEmbedding K x))) w = Real.log (|Algebra.norm Rat 
x| : Rat)
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_prod`：log_prod {α : Type*} {s : Finset α} {f : α -> Real} (hf :
 forall x in s, f x != 0) : log (∏ i in s, f i) = ∑ i in s, log (f i)
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `NumberField.InfinitePlace.instMonoidWithZeroHomClassReal`：∀ {K : Type u_
1} [inst : Field K], MonoidWithZeroHomClass (NumberField.InfinitePlace K) K ℝ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Real.log_pow`：log_pow (x : Real) (n : Nat) : log (x ^ n) = n * log x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.mixedEmbedding.normAtAllPlaces_mixedEmbedding`：normAtAllPlac
es_mixedEmbedding (x : K) (w : InfinitePlace K) : normAtAllPlaces (mixedEmbeddin
g K x) w = w x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_expMap_symm_apply {x : K} (hx : x ≠ 0) :
    ∑ w : InfinitePlace K, expMap.symm ((normAtAllPlaces (mixedEmbedding K x))) w =
      Real.log (|Algebra.norm ℚ x| : ℚ) := by
  simp_rw [← prod_eq_abs_norm, Real.log_prod (fun _ _ ↦ pow_ne_zero _ ((map_ne_zero _).mpr hx)),
    Real.log_pow, expMap_symm_apply, normAtAllPlaces_mixedEmbedding]

/--
The derivative of `expMap`, see `hasFDerivAt_expMap`.
-/
/-
**NumberField.mixedEmbedding.fundamentalCone.fderiv_expMap** 是 Mathlib 中的一个缩写定义，
位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：fderiv_expMap (x : realSpace K) : realSpace K ->L[Real] realSpace K
参数：x : realSpace K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivative of `expMap`, see `hasFDerivAt_expMap`.
-/
abbrev fderiv_expMap (x : realSpace K) : realSpace K →L[ℝ] realSpace K :=
  .pi fun w ↦ (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv_expMap_single w (x w))).comp
    (.proj w)
/-
**NumberField.mixedEmbedding.fundamentalCone.hasFDerivAt_expMap** 是 Mathlib 中的一个
定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：hasFDerivAt_expMap (x : realSpace K) : HasFDerivAt expMap (fderiv_expMap x
) x
参数：x : realSpace K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OpenPartialHomeomorph.pi_apply`：∀ {ι : Type u_7} [inst : Finite ι] {X : 
ι → Type u_8} {Y : ι → Type u_9} [inst_1 : (i : ι) → TopologicalSpace (X i)]   [
inst_2 : (i : ι) → T…
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMap_single_apply`：∀ {K : T
ype u_1} [inst : Field K] (w : NumberField.InfinitePlace K) (x : ℝ),   ↑(NumberF
ield.mixedEmbedding.fundamentalCone.expMap_single w)…
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.hasDerivAt_expMap_single`：has
DerivAt_expMap_single (w : InfinitePlace K) (x : Real) : HasDerivAt (expMap_sing
le w) (deriv_expMap_single w x) x
· 使用定理 `hasFDerivAt_apply`：hasFDerivAt_apply (i : ι) (f : forall i, F' i) : HasF
DerivAt (𝕜
-/
theorem hasFDerivAt_expMap (x : realSpace K) : HasFDerivAt expMap (fderiv_expMap x) x := by
  simpa [expMap, fderiv_expMap, hasFDerivAt_pi', OpenPartialHomeomorph.pi_apply,
    ContinuousLinearMap.proj_pi] using!
    fun w ↦ (hasDerivAt_expMap_single w _).hasFDerivAt.comp x (hasFDerivAt_apply w x)

end expMap

noncomputable section completeBasis

variable [NumberField K]

variable {K}

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
A fixed equiv between `Fin (rank K)` and `{w : InfinitePlace K // w ≠ w₀}`.
-/
/-
**NumberField.mixedEmbedding.fundamentalCone.equivFinRank** 是 Mathlib 中的一个定义，位于命
名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w != w₀}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fixed equiv between `Fin (rank K)` and `{w : InfinitePlace K // w ≠ w₀}`.
-/
def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} :=
  Fintype.equivOfCardEq <| by
    rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

open scoped Classical in
variable (K) in
/--
A family of elements in the `realSpace K` formed of the image of the fundamental units
and the vector `(mult w)_w`. This family is in fact a basis of `realSpace K`, see `completeBasis`.
-/
/-
**NumberField.mixedEmbedding.fundamentalCone.completeFamily** 是 Mathlib 中的一个定义，位
于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：completeFamily : InfinitePlace K -> realSpace K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A family of elements in the `realSpace K` formed of the image of the fundamental
 units
and the vector `(mult w)_w`. This family is in fact a basis of `realSpace K`, se
e `completeBasis`.
-/
def completeFamily : InfinitePlace K → realSpace K :=
  fun i ↦ if hi : i = w₀ then fun w ↦ mult w else
    expMap.symm <| normAtAllPlaces <| mixedEmbedding K <| fundSystem K <| equivFinRank.symm ⟨i, hi⟩

/--
An auxiliary map from `realSpace K` to `logSpace K` used to prove that `completeFamily` is
linearly independent, see `linearIndependent_completeFamily`.
-/
/-
**NumberField.mixedEmbedding.fundamentalCone.realSpaceToLogSpace** 是 Mathlib 中的一
个定义，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：realSpaceToLogSpace : realSpace K ->ₗ[Real] {w : InfinitePlace K // w != w
₀} -> Real where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K

--- 原说明 ---
An auxiliary map from `realSpace K` to `logSpace K` used to prove that `complete
Family` is
linearly independent, see `linearIndependent_completeFamily`.
-/
def realSpaceToLogSpace : realSpace K →ₗ[ℝ] {w : InfinitePlace K // w ≠ w₀} → ℝ where
  toFun := fun x w ↦ x w.1 - w.1.mult * (∑ w', x w') * (Module.finrank ℚ K : ℝ)⁻¹
  map_add' := fun _ _ ↦ funext fun _ ↦ by simp [sum_add_distrib]; ring
  map_smul' := fun _ _ ↦ funext fun _ ↦ by simp [← mul_sum]; ring
/-
**NumberField.mixedEmbedding.fundamentalCone.realSpaceToLogSpace_apply** 是 Mathl
ib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：realSpaceToLogSpace_apply (x : realSpace K) (w : {w : InfinitePlace K // w
 != w₀}) : realSpaceToLogSpace x w = x w - w.1.mult * (∑ w', x w') * (Module.fin
rank Rat K : Real)⁻¹
参数：x : realSpace K；w : {w : InfinitePlace K // w != w₀}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem realSpaceToLogSpace_apply (x : realSpace K) (w : {w : InfinitePlace K // w ≠ w₀}) :
    realSpaceToLogSpace x w = x w - w.1.mult * (∑ w', x w') * (Module.finrank ℚ K : ℝ)⁻¹ := rfl
/-
**NumberField.mixedEmbedding.fundamentalCone.realSpaceToLogSpace_expMap_symm** 是
 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：realSpaceToLogSpace_expMap_symm {x : K} (hx : x != 0) : realSpaceToLogSpac
e (expMap.symm (normAtAllPlaces (mixedEmbedding K x))) = logMap (mixedEmbedding 
K x)
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.sum_expMap_symm_apply`：sum_ex
pMap_symm_apply {x : K} (hx : x != 0) : ∑ w : InfinitePlace K, expMap.symm ((nor
mAtAllPlaces (mixedEmbedding K x))) w = Real.log (|Alg…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply`：normAtPlace_apply (w : Inf
initePlace K) (x : K) : normAtPlace w (mixedEmbedding K x) = w x
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.mixedEmbedding.norm_eq_norm`：norm_eq_norm (x : K) : mixedEmb
edding.norm (mixedEmbedding K x) = |Algebra.norm Rat x|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem realSpaceToLogSpace_expMap_symm {x : K} (hx : x ≠ 0) :
    realSpaceToLogSpace (expMap.symm (normAtAllPlaces (mixedEmbedding K x))) =
      logMap (mixedEmbedding K x) := by
  ext w
  simp_rw [realSpaceToLogSpace_apply, sum_expMap_symm_apply hx, expMap_symm_apply,
    logMap, normAtPlace_apply, mul_sub, mul_assoc, norm_eq_norm]
/-
**NumberField.mixedEmbedding.fundamentalCone.realSpaceToLogSpace_completeFamily_
of_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：realSpaceToLogSpace_completeFamily_of_eq : realSpaceToLogSpace (completeFa
mily K w₀) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.realSpaceToLogSpace_apply`：re
alSpaceToLogSpace_apply (x : realSpace K) (w : {w : InfinitePlace K // w != w₀})
 : realSpaceToLogSpace x w = x w - w.1.mult * (∑ w', x w')…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.completeFamily.eq_1`：∀ (K : T
ype u_1) [inst : Field K] [inst_1 : NumberField K] (i : NumberField.InfinitePlac
e K),   NumberField.mixedEmbedding.fundamentalCone.c…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `NumberField.InfinitePlace.sum_mult_eq`：sum_mult_eq [NumberField K] : ∑ w
 : InfinitePlace K, mult w = Module.finrank Rat K
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
-/
theorem realSpaceToLogSpace_completeFamily_of_eq :
    realSpaceToLogSpace (completeFamily K w₀) = 0 := by
  ext
  rw [realSpaceToLogSpace_apply, completeFamily, dif_pos rfl, ← Nat.cast_sum, sum_mult_eq,
    mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne'), sub_self, Pi.zero_apply]
/-
**NumberField.mixedEmbedding.fundamentalCone.realSpaceToLogSpace_completeFamily_
of_ne** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：realSpaceToLogSpace_completeFamily_of_ne (i : {w : InfinitePlace K // w !=
 w₀}) : realSpaceToLogSpace (completeFamily K i) = basisUnitLattice K (equivFinR
ank.symm i)
参数：i : {w : InfinitePlace K // w != w₀}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.Units.logEmbedding_fundSystem`：∀ (K : Type u_1) [inst : Fiel
d K] [inst_1 : NumberField K] (i : Fin (NumberField.Units.rank K)),   (NumberFie
ld.Units.logEmbedding K) (Addit…
· 使用定理 `NumberField.mixedEmbedding.logMap_eq_logEmbedding`：logMap_eq_logEmbeddin
g (u : (𝓞 K)ˣ) : logMap (mixedEmbedding K u) = logEmbedding K (Additive.ofMul u)
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.completeFamily.eq_1`：∀ (K : T
ype u_1) [inst : Field K] [inst_1 : NumberField K] (i : NumberField.InfinitePlac
e K),   NumberField.mixedEmbedding.fundamentalCone.c…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.realSpaceToLogSpace_expMap_sy
mm`：realSpaceToLogSpace_expMap_symm {x : K} (hx : x != 0) : realSpaceToLogSpace 
(expMap.symm (normAtAllPlaces (mixedEmbedding K x))) = logMap (m…
· 使用定理 `NumberField.Units.coe_ne_zero`：coe_ne_zero (x : (𝓞 K)ˣ) : (x : K) != 0
-/
theorem realSpaceToLogSpace_completeFamily_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    realSpaceToLogSpace (completeFamily K i) = basisUnitLattice K (equivFinRank.symm i) := by
  ext
  rw [← logEmbedding_fundSystem, ← logMap_eq_logEmbedding, completeFamily, dif_neg,
    realSpaceToLogSpace_expMap_symm]
  exact coe_ne_zero _
/-
**NumberField.mixedEmbedding.fundamentalCone.sum_eq_zero_of_mem_span_completeFam
ily** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：sum_eq_zero_of_mem_span_completeFamily {x : realSpace K} (hx : x in Submod
ule.span Real (Set.range fun w : {w // w != w₀} => completeFamily K w.1)) : ∑ w,
 x w = 0
参数：hx : x in Submodule.span Real (Set.range fun w : {w // w != w₀} => completeFa
mily K w.1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.sum_expMap_symm_apply`：sum_ex
pMap_symm_apply {x : K} (hx : x != 0) : ∑ w : InfinitePlace K, expMap.symm ((nor
mAtAllPlaces (mixedEmbedding K x))) w = Real.log (|Alg…
· 使用定理 `NumberField.Units.coe_ne_zero`：coe_ne_zero (x : (𝓞 K)ˣ) : (x : K) != 0
· 使用定理 `NumberField.Units.norm`：∀ (K : Type u_1) [inst : Field K] [inst_1 : Numb
erField K] (x : (NumberField.RingOfIntegers K)ˣ),   |(Algebra.norm ℚ) ((algebraM
ap (NumberFi…
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem sum_eq_zero_of_mem_span_completeFamily {x : realSpace K}
    (hx : x ∈ Submodule.span ℝ (Set.range fun w : {w // w ≠ w₀} ↦ completeFamily K w.1)) :
    ∑ w, x w = 0 := by
  induction hx using Submodule.span_induction with
  | mem _ h =>
      obtain ⟨w, rfl⟩ := h
      simp_rw [completeFamily, dif_neg w.prop, sum_expMap_symm_apply (coe_ne_zero _),
        Units.norm, Rat.cast_one, Real.log_one]
  | zero => simp
  | add _ _ _ _ hx hy => simp [sum_add_distrib, hx, hy]
  | smul _ _ _ hx => simp [← mul_sum, hx]

variable (K)
/-
**NumberField.mixedEmbedding.fundamentalCone.linearIndependent_completeFamily** 
是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：linearIndependent_completeFamily : LinearIndependent Real (completeFamily 
K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.realSpaceToLogSpace_completeF
amily_of_ne`：realSpaceToLogSpace_completeFamily_of_ne (i : {w : InfinitePlace K 
// w != w₀}) : realSpaceToLogSpace (completeFamily K i) = basisUnitLattic…
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `Module.Basis.ofZLatticeBasis_apply`：ofZLatticeBasis_apply (i : ι) : b.of
ZLatticeBasis K L i = b i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.sum_eq_zero_of_mem_span_compl
eteFamily`：sum_eq_zero_of_mem_span_completeFamily {x : realSpace K} (hx : x in S
ubmodule.span Real (Set.range fun w : {w // w != w₀} => completeFamily …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
（共 38 条，此处仅展示前 30 条）
-/
theorem linearIndependent_completeFamily :
    LinearIndependent ℝ (completeFamily K) := by
  classical
  have h₁ : LinearIndependent ℝ (fun w : {w // w ≠ w₀} ↦ completeFamily K w.1) := by
    refine LinearIndependent.of_comp realSpaceToLogSpace ?_
    simp_rw [Function.comp_def, realSpaceToLogSpace_completeFamily_of_ne]
    convert! (((basisUnitLattice K).ofZLatticeBasis ℝ _).reindex equivFinRank).linearIndependent
    simp
  have h₂ : completeFamily K w₀ ∉ Submodule.span ℝ
      (Set.range (fun w : {w // w ≠ w₀} ↦ completeFamily K w.1)) := by
    intro h
    have := sum_eq_zero_of_mem_span_completeFamily h
    rw [completeFamily, dif_pos rfl, ← Nat.cast_sum, sum_mult_eq, Nat.cast_eq_zero] at this
    exact Module.finrank_pos.ne' this
  rw [← linearIndependent_equiv (Equiv.optionSubtypeNe w₀), linearIndependent_option]
  exact ⟨h₁, h₂⟩

/--
A basis of `realSpace K` formed by the image of the fundamental units
(which form a basis of a subspace `{x : realSpace K | ∑ w, x w = 0}`) and the vector `(mult w)_w`.
For `i ≠ w₀`, the image of `completeBasis K i` by the natural restriction map
`realSpace K → logSpace K` is `basisUnitLattice K`
-/
/-
**NumberField.mixedEmbedding.fundamentalCone.completeBasis** 是 Mathlib 中的一个定义，位于
命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：completeBasis : Basis (InfinitePlace K) Real (realSpace K)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.linearIndependent_completeFam
ily`：linearIndependent_completeFamily : LinearIndependent Real (completeFamily K
)

--- 原说明 ---
A basis of `realSpace K` formed by the image of the fundamental units
(which form a basis of a subspace `{x : realSpace K | ∑ w, x w = 0}`) and the ve
ctor `(mult w)_w`.
For `i ≠ w₀`, the image of `completeBasis K i` by the natural restriction map
`realSpace K → logSpace K` is `basisUnitLattice K`
-/
def completeBasis : Basis (InfinitePlace K) ℝ (realSpace K) :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_completeFamily K)
    (Module.finrank_fintype_fun_eq_card _).symm
/-
**NumberField.mixedEmbedding.fundamentalCone.completeBasis_apply_of_eq** 是 Mathl
ib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：completeBasis_apply_of_eq : completeBasis K w₀ = fun w => (mult w : Real)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.linearIndependent_completeFam
ily`：linearIndependent_completeFamily : LinearIndependent Real (completeFamily K
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.completeBasis.eq_1`：∀ (K : Ty
pe u_1) [inst : Field K] [inst_1 : NumberField K],   NumberField.mixedEmbedding.
fundamentalCone.completeBasis K = basisOfLinearInde…
· 使用定理 `coe_basisOfLinearIndependentOfCardEqFinrank`：coe_basisOfLinearIndependen
tOfCardEqFinrank [Nonempty ι] {b : ι -> V} (lin_ind : LinearIndependent K b) (ca
rd_eq : Fintype.card ι = finrank …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.completeFamily.eq_1`：∀ (K : T
ype u_1) [inst : Field K] [inst_1 : NumberField K] (i : NumberField.InfinitePlac
e K),   NumberField.mixedEmbedding.fundamentalCone.c…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem completeBasis_apply_of_eq :
    completeBasis K w₀ = fun w ↦ (mult w : ℝ) := by
  rw [completeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, completeFamily, dif_pos rfl]
/-
**NumberField.mixedEmbedding.fundamentalCone.completeBasis_apply_of_ne** 是 Mathl
ib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：completeBasis_apply_of_ne (i : {w : InfinitePlace K // w != w₀}) : complet
eBasis K i = expMap.symm (normAtAllPlaces (mixedEmbedding K (fundSystem K (equiv
FinRank.symm i))))
参数：i : {w : InfinitePlace K // w != w₀}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.linearIndependent_completeFam
ily`：linearIndependent_completeFamily : LinearIndependent Real (completeFamily K
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.completeBasis.eq_1`：∀ (K : Ty
pe u_1) [inst : Field K] [inst_1 : NumberField K],   NumberField.mixedEmbedding.
fundamentalCone.completeBasis K = basisOfLinearInde…
· 使用定理 `coe_basisOfLinearIndependentOfCardEqFinrank`：coe_basisOfLinearIndependen
tOfCardEqFinrank [Nonempty ι] {b : ι -> V} (lin_ind : LinearIndependent K b) (ca
rd_eq : Fintype.card ι = finrank …
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.completeFamily.eq_1`：∀ (K : T
ype u_1) [inst : Field K] [inst_1 : NumberField K] (i : NumberField.InfinitePlac
e K),   NumberField.mixedEmbedding.fundamentalCone.c…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem completeBasis_apply_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    completeBasis K i =
      expMap.symm (normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm i)))) := by
  rw [completeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, completeFamily, dif_neg]
/-
**NumberField.mixedEmbedding.fundamentalCone.expMap_basis_of_eq** 是 Mathlib 中的一个
定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMap_basis_of_eq : expMap (completeBasis K w₀) = fun _ => Real.exp 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.completeBasis_apply_of_eq`：co
mpleteBasis_apply_of_eq : completeBasis K w₀ = fun w => (mult w : Real)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `NumberField.InfinitePlace.mult_coe_ne_zero`：mult_coe_ne_zero {w : Infini
tePlace K} : (mult w : Real) != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expMap_basis_of_eq :
    expMap (completeBasis K w₀) = fun _ ↦ Real.exp 1 := by
  ext
  simp_rw [expMap_apply, completeBasis_apply_of_eq, inv_mul_cancel₀ mult_coe_ne_zero]
/-
**NumberField.mixedEmbedding.fundamentalCone.expMap_basis_of_ne** 是 Mathlib 中的一个
定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMap_basis_of_ne (i : {w : InfinitePlace K // w != w₀}) : expMap (comple
teBasis K i) = normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.sym
m i)))
参数：i : {w : InfinitePlace K // w != w₀}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.completeBasis_apply_of_ne`：co
mpleteBasis_apply_of_ne (i : {w : InfinitePlace K // w != w₀}) : completeBasis K
 i = expMap.symm (normAtAllPlaces (mixedEmbedding K (fundS…
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMap_target`：expMap_target 
: expMap.target = Set.univ.pi fun (_ : InfinitePlace K) => Set.Ioi 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply`：normAtPlace_apply (w : Inf
initePlace K) (x : K) : normAtPlace w (mixedEmbedding K x) = w x
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem expMap_basis_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    expMap (completeBasis K i) =
      normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm i))) := by
  rw [completeBasis_apply_of_ne, expMap.right_inv (by simp [expMap_target, pos_at_place])]
/-
**NumberField.mixedEmbedding.fundamentalCone.abs_det_completeBasis_equivFunL_sym
m** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：abs_det_completeBasis_equivFunL_symm : |((completeBasis K).equivFunL.symm 
: realSpace K ->L[Real] realSpace K).det| = Module.finrank Rat K * regulator K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.det.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {M : 
Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _r
oot_.Module R M] (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `NumberField.Units.regulator_eq_regOfFamily_fundSystem`：regulator_eq_regO
fFamily_fundSystem : regulator K = regOfFamily (fundSystem K)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `NumberField.Units.finrank_mul_regOfFamily_eq_det`：finrank_mul_regOfFamil
y_eq_det (u : Fin (rank K) -> (𝓞 K)ˣ) (w' : InfinitePlace K) (e : {w // w != w'}
 ≃ Fin (rank K)) : finrank Rat K * reg…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Matrix.transpose_apply`：transpose_apply (M : Matrix m n α) (i j) : trans
pose M i j = M j i
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Matrix.of_apply`：of_apply (f : m -> n -> α) (i j) : of f i j = f i j
· 使用定理 `Module.Basis.equivFunL_apply`：∀ {𝕜 : Type u} [hnorm : NontriviallyNormed
Field 𝕜] {E : Type v} [inst : AddCommGroup E] [inst_1 : _root_.Module 𝕜 E]   [in
st_2 : Topological…
· 使用定理 `ContinuousLinearMap.coe_coe`：coe_coe (f : M₁ ->SL[σ₁₂] M₂) : ⇑(f : M₁ ->
ₛₗ[σ₁₂] M₂) = f
· 使用定理 `ContinuousLinearEquiv.coe_apply`：coe_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁)
 : (e : M₁ ->SL[σ₁₂] M₂) b = e b
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
（共 39 条，此处仅展示前 30 条）
-/
theorem abs_det_completeBasis_equivFunL_symm :
    |((completeBasis K).equivFunL.symm : realSpace K →L[ℝ] realSpace K).det| =
      Module.finrank ℚ K * regulator K := by
  classical
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (completeBasis K), ← Matrix.det_transpose,
    regulator_eq_regOfFamily_fundSystem, finrank_mul_regOfFamily_eq_det _ w₀ equivFinRank.symm]
  congr 2 with w i
  rw [Matrix.transpose_apply, LinearMap.toMatrix_apply, Matrix.of_apply, ← Basis.equivFunL_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_apply,
    (completeBasis K).equivFunL.apply_symm_apply]
  split_ifs with hw
  · rw [hw, completeBasis_apply_of_eq]
  · simp_rw [completeBasis_apply_of_ne K ⟨w, hw⟩, expMap_symm_apply, normAtAllPlaces_mixedEmbedding]

end completeBasis

noncomputable section expMapBasis

variable [NumberField K]

variable {K}

/--
The map that sends `x : realSpace K` to
`Real.exp (x w₀) * ∏_{i ≠ w₀} |ηᵢ| ^ x i` where `|ηᵢ|` denote the vector of `realSpace K` given
by `w (ηᵢ)` and `ηᵢ` denote the units in `fundSystem K`, see `expMapBasis_apply'`.
-/
/-
**NumberField.mixedEmbedding.fundamentalCone.expMapBasis** 是 Mathlib 中的一个定义，位于命名
空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMapBasis : OpenPartialHomeomorph (realSpace K) (realSpace K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map that sends `x : realSpace K` to
`Real.exp (x w₀) * ∏_{i ≠ w₀} |ηᵢ| ^ x i` where `|ηᵢ|` denote the vector of `rea
lSpace K` given
by `w (ηᵢ)` and `ηᵢ` denote the units in `fundSystem K`, see `expMapBasis_apply'
`.
-/
def expMapBasis : OpenPartialHomeomorph (realSpace K) (realSpace K) :=
  (completeBasis K).equivFunL.symm.toHomeomorph.transOpenPartialHomeomorph expMap

variable (K)
/-
**NumberField.mixedEmbedding.fundamentalCone.expMapBasis_source** 是 Mathlib 中的一个
定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMapBasis_source : expMapBasis.source = (Set.univ : Set (realSpace K))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.transOpenPartialHomeomorph_source`：∀ {X : Type u_1} {Y : Type
 u_3} {Z : Type u_5} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]  
 [inst_2 : TopologicalSpace Z] (e …
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMap_source`：expMap_source 
: expMap.source = (Set.univ : Set (realSpace K))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expMapBasis_source :
    expMapBasis.source = (Set.univ : Set (realSpace K)) := by
  simp [expMapBasis, expMap_source]
/-
**NumberField.mixedEmbedding.fundamentalCone.injective_expMapBasis** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：injective_expMapBasis : Function.Injective (expMapBasis : realSpace K -> r
ealSpace K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.injective_expMap`：injective_e
xpMap : Function.Injective (expMap : realSpace K -> realSpace K)
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem injective_expMapBasis :
    Function.Injective (expMapBasis : realSpace K → realSpace K) :=
  (injective_expMap K).comp (completeBasis K).equivFun.symm.injective
/-
**NumberField.mixedEmbedding.fundamentalCone.continuous_expMapBasis** 是 Mathlib 
中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：continuous_expMapBasis : Continuous (expMapBasis : realSpace K -> realSpac
e K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.continuous_expMap`：continuous
_expMap : Continuous (expMap : realSpace K -> realSpace K)
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
-/
theorem continuous_expMapBasis :
    Continuous (expMapBasis : realSpace K → realSpace K) :=
  (continuous_expMap K).comp (ContinuousLinearEquiv.continuous _)

variable {K}
/-
**NumberField.mixedEmbedding.fundamentalCone.expMapBasis_pos** 是 Mathlib 中的一个定理，
位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMapBasis_pos (x : realSpace K) (w : InfinitePlace K) : 0 < expMapBasis 
x w
参数：x : realSpace K；w : InfinitePlace K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMap_pos`：expMap_pos (x : r
ealSpace K) (w : InfinitePlace K) : 0 < expMap x w
-/
theorem expMapBasis_pos (x : realSpace K) (w : InfinitePlace K) :
    0 < expMapBasis x w := expMap_pos _ _
/-
**NumberField.mixedEmbedding.fundamentalCone.expMapBasis_nonneg** 是 Mathlib 中的一个
定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMapBasis_nonneg (x : realSpace K) (w : InfinitePlace K) : 0 <= expMapBa
sis x w
参数：x : realSpace K；w : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_pos`：expMapBasis_
pos (x : realSpace K) (w : InfinitePlace K) : 0 < expMapBasis x w
-/
theorem expMapBasis_nonneg (x : realSpace K) (w : InfinitePlace K) :
    0 ≤ expMapBasis x w := (expMapBasis_pos _ _).le
/-
**NumberField.mixedEmbedding.fundamentalCone.expMapBasis_apply** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMapBasis_apply (x : realSpace K) : expMapBasis x = expMap ((completeBas
is K).equivFun.symm x)
参数：x : realSpace K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem expMapBasis_apply (x : realSpace K) :
    expMapBasis x = expMap ((completeBasis K).equivFun.symm x) := rfl

open scoped Classical in
/-
**NumberField.mixedEmbedding.fundamentalCone.expMapBasis_apply'** 是 Mathlib 中的一个
定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMapBasis_apply' (x : realSpace K) : expMapBasis x = Real.exp (x w₀) • f
un w : InfinitePlace K => ∏ i : {w // w != w₀}, w (fundSystem K (equivFinRank.sy
mm i)) ^ x i
参数：x : realSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用定理 `Fintype.sum_eq_add_sum_subtype_ne`：∀ {α : Type u_1} {M : Type u_4} [inst
 : Fintype α] [inst_1 : AddCommMonoid M] [inst_2 : DecidableEq α] (f : α → M)   
(a : α), ∑ i, f i = f a…
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMap_add`：expMap_add (x y :
 realSpace K) : expMap (x + y) = expMap x * expMap y
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMap_smul`：expMap_smul (c :
 Real) (x : realSpace K) : expMap (c • x) = (expMap x) ^ c
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMap_basis_of_eq`：expMap_ba
sis_of_eq : expMap (completeBasis K w₀) = fun _ => Real.exp 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.exp_one_rpow`：exp_one_rpow (x : Real) : exp 1 ^ x = exp x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMap_sum`：expMap_sum {ι : T
ype*} (s : Finset ι) (f : ι -> realSpace K) : expMap (∑ i in s, f i) = ∏ i in s,
 expMap (f i)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMap_basis_of_ne`：expMap_ba
sis_of_ne (i : {w : InfinitePlace K // w != w₀}) : expMap (completeBasis K i) = 
normAtAllPlaces (mixedEmbedding K (fundSystem K (eq…
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.mixedEmbedding.normAtAllPlaces_mixedEmbedding`：normAtAllPlac
es_mixedEmbedding (x : K) (w : InfinitePlace K) : normAtAllPlaces (mixedEmbeddin
g K x) w = w x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expMapBasis_apply' (x : realSpace K) :
    expMapBasis x = Real.exp (x w₀) •
      fun w : InfinitePlace K ↦
         ∏ i : {w // w ≠ w₀}, w (fundSystem K (equivFinRank.symm i)) ^ x i := by
  simp_rw [expMapBasis_apply, Basis.equivFun_symm_apply, Fintype.sum_eq_add_sum_subtype_ne _ w₀,
    expMap_add, expMap_smul, expMap_basis_of_eq, Pi.pow_def, Real.exp_one_rpow, Pi.mul_def,
    expMap_sum, expMap_smul, expMap_basis_of_ne, Pi.smul_def, smul_eq_mul, prod_apply, Pi.pow_apply,
    normAtAllPlaces_mixedEmbedding]

open scoped Classical in
/-
**NumberField.mixedEmbedding.fundamentalCone.expMapBasis_apply''** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMapBasis_apply'' (x : realSpace K) : expMapBasis x = Real.exp (x w₀) • 
expMapBasis (fun i => if i = w₀ then 0 else x i)
参数：x : realSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_apply'`：expMapBas
is_apply' (x : realSpace K) : expMapBasis x = Real.exp (x w₀) • fun w : Infinite
Place K => ∏ i : {w // w != w₀}, w (fundSystem K (e…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem expMapBasis_apply'' (x : realSpace K) :
    expMapBasis x = Real.exp (x w₀) • expMapBasis (fun i ↦ if i = w₀ then 0 else x i) := by
  rw [expMapBasis_apply', expMapBasis_apply', if_pos rfl, smul_smul, ← Real.exp_add, add_zero]
  conv_rhs =>
    enter [2, w, 2, i]
    rw [if_neg i.prop]
/-
**NumberField.mixedEmbedding.fundamentalCone.prod_expMapBasis_pow** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：prod_expMapBasis_pow (x : realSpace K) : ∏ w, (expMapBasis x w) ^ w.mult =
 Real.exp (x w₀) ^ Module.finrank Rat K
参数：x : realSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_apply'`：expMapBas
is_apply' (x : realSpace K) : expMapBasis x = Real.exp (x w₀) • fun w : Infinite
Place K => ∏ i : {w // w != w₀}, w (fundSystem K (e…
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用引理 `Finset.prod_pow_eq_pow_sum`：prod_pow_eq_pow_sum (s : Finset ι) (f : ι ->
 Nat) (a : M) : ∏ i in s, a ^ f i = a ^ ∑ i in s, f i
· 使用定理 `NumberField.InfinitePlace.sum_mult_eq`：sum_mult_eq [NumberField K] : ∑ w
 : InfinitePlace K, mult w = Module.finrank Rat K
· 使用定理 `Finset.prod_comm`：prod_comm {s : Finset γ} {t : Finset α} {f : γ -> α ->
 β} : (∏ x in s, ∏ y in t, f x y) = ∏ y in t, ∏ x in s, f x y
· 使用引理 `Real.rpow_pow_comm`：rpow_pow_comm {x : Real} (hx : 0 <= x) (y : Real) (n
 : Nat) : (x ^ y) ^ n = (x ^ n) ^ y
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `NumberField.InfinitePlace.instNonnegHomClassReal`：∀ {K : Type u_1} [inst
 : Field K], NonnegHomClass (NumberField.InfinitePlace K) K ℝ
· 使用定理 `Real.finsetProd_rpow`：∀ {ι : Type u_1} (s : Finset ι) (f : ι → ℝ), (∀ i 
∈ s, 0 ≤ f i) → ∀ (r : ℝ), ∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NumberField.InfinitePlace.prod_eq_abs_norm`：prod_eq_abs_norm (x : K) : ∏
 w : InfinitePlace K, w x ^ mult w = abs (Algebra.norm Rat x)
· 使用定理 `NumberField.Units.norm`：∀ (K : Type u_1) [inst : Field K] [inst_1 : Numb
erField K] (x : (NumberField.RingOfIntegers K)ˣ),   |(Algebra.norm ℚ) ((algebraM
ap (NumberFi…
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Real.one_rpow`：one_rpow (x : Real) : (1 : Real) ^ x = 1
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_expMapBasis_pow (x : realSpace K) :
    ∏ w, (expMapBasis x w) ^ w.mult = Real.exp (x w₀) ^ Module.finrank ℚ K := by
  simp_rw [expMapBasis_apply', Pi.smul_def, smul_eq_mul, mul_pow, prod_mul_distrib,
    prod_pow_eq_pow_sum, sum_mult_eq, ← prod_pow]
  rw [prod_comm]
  simp_rw [Real.rpow_pow_comm (apply_nonneg _ _), Real.finsetProd_rpow _ _
    fun _ _ ↦ pow_nonneg (apply_nonneg _ _) _, prod_eq_abs_norm, Units.norm, Rat.cast_one,
    Real.one_rpow, prod_const_one, mul_one]
/-
**NumberField.mixedEmbedding.fundamentalCone.norm_expMapBasis** 是 Mathlib 中的一个定理
，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：norm_expMapBasis (x : realSpace K) : mixedEmbedding.norm (mixedSpaceOfReal
Space (expMapBasis x)) = Real.exp (x w₀) ^ Module.finrank Rat K
参数：x : realSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_mixedSpaceOfRealSpace`：normAtPlac
e_mixedSpaceOfRealSpace {x : realSpace K} {w : InfinitePlace K} (hx : 0 <= x w) 
: normAtPlace w (mixedSpaceOfRealSpace x) = x w
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_pos`：expMapBasis_
pos (x : realSpace K) (w : InfinitePlace K) : 0 < expMapBasis x w
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.prod_expMapBasis_pow`：prod_ex
pMapBasis_pow (x : realSpace K) : ∏ w, (expMapBasis x w) ^ w.mult = Real.exp (x 
w₀) ^ Module.finrank Rat K
-/
theorem norm_expMapBasis (x : realSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (expMapBasis x)) =
      Real.exp (x w₀) ^ Module.finrank ℚ K := by
  simpa only [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (expMapBasis_pos _ _).le] using prod_expMapBasis_pow x
/-
**NumberField.mixedEmbedding.fundamentalCone.norm_expMapBasis_ne_zero** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：norm_expMapBasis_ne_zero (x : realSpace K) : mixedEmbedding.norm (mixedSpa
ceOfRealSpace (expMapBasis x)) != 0
参数：x : realSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.exp_ne_zero`：∀ (x : ℝ), Real.exp x ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.norm_expMapBasis`：norm_expMap
Basis (x : realSpace K) : mixedEmbedding.norm (mixedSpaceOfRealSpace (expMapBasi
s x)) = Real.exp (x w₀) ^ Module.finrank Rat K
-/
theorem norm_expMapBasis_ne_zero (x : realSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (expMapBasis x)) ≠ 0 :=
  norm_expMapBasis x ▸ pow_ne_zero _ (Real.exp_ne_zero _)

open scoped Classical in
/-
**NumberField.mixedEmbedding.fundamentalCone.logMap_expMapBasis** 是 Mathlib 中的一个
定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：logMap_expMapBasis (x : realSpace K) : logMap (mixedSpaceOfRealSpace (expM
apBasis x)) in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis Rea
l (unitLattice K)) ↔ forall w, w != w₀ -> x w in Set.Ico 0 1
参数：x : realSpace K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_apply''`：expMapBa
sis_apply'' (x : realSpace K) : expMapBasis x = Real.exp (x w₀) • expMapBasis (f
un i => if i = w₀ then 0 else x i)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `NumberField.mixedEmbedding.logMap_real_smul`：logMap_real_smul (hx : mixe
dEmbedding.norm x != 0) {c : Real} (hc : c != 0) : logMap (c • x) = logMap x
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.norm_expMapBasis_ne_zero`：nor
m_expMapBasis_ne_zero (x : realSpace K) : mixedEmbedding.norm (mixedSpaceOfRealS
pace (expMapBasis x)) != 0
· 使用定理 `Real.exp_ne_zero`：∀ (x : ℝ), Real.exp x ≠ 0
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_apply`：expMapBasi
s_apply (x : realSpace K) : expMapBasis x = expMap ((completeBasis K).equivFun.s
ymm x)
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.logMap_expMap`：logMap_expMap 
{x : realSpace K} (hx : mixedEmbedding.norm (mixedSpaceOfRealSpace (expMap x)) =
 1) : logMap (mixedSpaceOfRealSpace (expMap x)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.norm_expMapBasis`：norm_expMap
Basis (x : realSpace K) : mixedEmbedding.norm (mixedSpaceOfRealSpace (expMapBasi
s x)) = Real.exp (x w₀) ^ Module.finrank Rat K
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用定理 `Fintype.sum_eq_add_sum_subtype_ne`：∀ {α : Type u_1} {M : Type u_4} [inst
 : Fintype α] [inst_1 : AddCommMonoid M] [inst_2 : DecidableEq α] (f : α → M)   
(a : α), ∑ i, f i = f a…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 59 条，此处仅展示前 30 条）
-/
theorem logMap_expMapBasis (x : realSpace K) :
    logMap (mixedSpaceOfRealSpace (expMapBasis x)) ∈
        ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K))
      ↔ ∀ w, w ≠ w₀ → x w ∈ Set.Ico 0 1 := by
  simp_rw [ZSpan.mem_fundamentalDomain, equivFinRank.forall_congr_left, Subtype.forall]
  refine forall₂_congr fun w hw ↦ ?_
  rw [expMapBasis_apply'', map_smul, logMap_real_smul (norm_expMapBasis_ne_zero _)
    (Real.exp_ne_zero _), expMapBasis_apply, logMap_expMap (by rw [← expMapBasis_apply,
    norm_expMapBasis, if_pos rfl, Real.exp_zero, one_pow]), Basis.equivFun_symm_apply,
    Fintype.sum_eq_add_sum_subtype_ne _ w₀, if_pos rfl, zero_smul, zero_add]
  conv_lhs =>
    enter [2, 1, 2, w, 2, i]
    rw [if_neg i.prop]
  simp_rw [Finset.sum_apply, ← sum_fn, map_sum, Pi.smul_apply, ← Pi.smul_def, map_smul,
    completeBasis_apply_of_ne, expMap_symm_apply, normAtAllPlaces_mixedEmbedding,
    ← logEmbedding_component, logEmbedding_fundSystem, Finsupp.coe_finsetSum, Finsupp.coe_smul,
    Finset.sum_apply, Pi.smul_apply, Basis.ofZLatticeBasis_repr_apply, Basis.repr_self,
    Finsupp.single_apply, EmbeddingLike.apply_eq_iff_eq, Int.cast_ite, Int.cast_one, Int.cast_zero,
    smul_ite, smul_eq_mul, mul_one, mul_zero, Fintype.sum_ite_eq']
/-
**NumberField.mixedEmbedding.fundamentalCone.normAtAllPlaces_image_preimage_expM
apBasis** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：normAtAllPlaces_image_preimage_expMapBasis (s : Set (realSpace K)) : normA
tAllPlaces '' normAtAllPlaces ⁻¹' expMapBasis '' s = expMapBasis '' s
参数：s : Set (realSpace K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.mixedEmbedding.normAtAllPlaces_image_preimage_of_nonneg`：nor
mAtAllPlaces_image_preimage_of_nonneg {s : Set (realSpace K)} (hs : forall x in 
s, forall w, 0 <= x w) : normAtAllPlaces '' normAtAllPlac…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_pos`：expMapBasis_
pos (x : realSpace K) (w : InfinitePlace K) : 0 < expMapBasis x w
-/
theorem normAtAllPlaces_image_preimage_expMapBasis (s : Set (realSpace K)) :
    normAtAllPlaces '' normAtAllPlaces ⁻¹' expMapBasis '' s = expMapBasis '' s := by
  apply normAtAllPlaces_image_preimage_of_nonneg
  rintro _ ⟨x, _, rfl⟩ w
  exact (expMapBasis_pos _ _).le

open scoped Classical in
/-
**NumberField.mixedEmbedding.fundamentalCone.prod_deriv_expMap_single** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：prod_deriv_expMap_single (x : realSpace K) : ∏ w, deriv_expMap_single w ((
completeBasis K).equivFun.symm x w) = Real.exp (x w₀) ^ Module.finrank Rat K * (
∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ * (2⁻¹) ^ nrComplexPlaces K
参数：x : realSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMap_single_apply`：∀ {K : T
ype u_1} [inst : Field K] (w : NumberField.InfinitePlace K) (x : ℝ),   ↑(NumberF
ield.mixedEmbedding.fundamentalCone.expMap_single w)…
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NumberField.InfinitePlace.prod_eq_prod_mul_prod`：prod_eq_prod_mul_prod {
α : Type*} [CommMonoid α] [NumberField K] (f : InfinitePlace K -> α) : ∏ w, f w 
= (∏ w : {w // IsReal w}, f w.1) * (∏…
· 使用定理 `NumberField.InfinitePlace.mult_isReal`：mult_isReal (w : {w : InfinitePla
ce K // IsReal w}) : mult w.1 = 1
· 使用定理 `NumberField.InfinitePlace.mult_isComplex`：mult_isComplex (w : {w : Infin
itePlace K // IsComplex w}) : mult w.1 = 2
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Finset.prod_pow`：prod_pow (s : Finset ι) (n : Nat) (f : ι -> M) : ∏ x in
 s, f x ^ n = (∏ x in s, f x) ^ n
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.exp_ne_zero`：∀ (x : ℝ), Real.exp x ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_inv_distrib`：prod_inv_distrib (f : ι -> G) : (∏ x in s, (f x
)⁻¹) = (∏ x in s, f x)⁻¹
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
（共 32 条，此处仅展示前 30 条）
-/
theorem prod_deriv_expMap_single (x : realSpace K) :
    ∏ w, deriv_expMap_single w ((completeBasis K).equivFun.symm x w) =
      Real.exp (x w₀) ^ Module.finrank ℚ K * (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ *
        (2⁻¹) ^ nrComplexPlaces K := by
  simp only [deriv_expMap_single, expMap_single_apply]
  rw [Finset.prod_mul_distrib]
  congr 1
  · simp_rw [← prod_expMapBasis_pow, prod_eq_prod_mul_prod, expMapBasis_apply, expMap_apply,
      mult_isReal, mult_isComplex, pow_one, Finset.prod_pow, pow_two, mul_assoc, mul_inv_cancel₀
      (Finset.prod_ne_zero_iff.mpr <| fun _ _ ↦ Real.exp_ne_zero _), mul_one]
  · simp [prod_eq_prod_mul_prod, mult_isReal, mult_isComplex]

variable (K)

/--
The derivative of `expMapBasis`, see `hasFDerivAt_expMapBasis`.
-/
/-
**NumberField.mixedEmbedding.fundamentalCone.fderiv_expMapBasis** 是 Mathlib 中的一个
缩写定义，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：fderiv_expMapBasis (x : realSpace K) : realSpace K ->L[Real] realSpace K
参数：x : realSpace K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivative of `expMapBasis`, see `hasFDerivAt_expMapBasis`.
-/
abbrev fderiv_expMapBasis (x : realSpace K) : realSpace K →L[ℝ] realSpace K :=
  (fderiv_expMap ((completeBasis K).equivFun.symm x)).comp
    (completeBasis K).equivFunL.symm.toContinuousLinearMap
/-
**NumberField.mixedEmbedding.fundamentalCone.hasFDerivAt_expMapBasis** 是 Mathlib
 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：hasFDerivAt_expMapBasis (x : realSpace K) : HasFDerivAt expMapBasis (fderi
v_expMapBasis K x) x
参数：x : realSpace K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.hasFDerivAt_expMap`：hasFDeriv
At_expMap (x : realSpace K) : HasFDerivAt expMap (fderiv_expMap x) x
· 使用定理 `ContinuousLinearEquiv.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
-/
theorem hasFDerivAt_expMapBasis (x : realSpace K) :
    HasFDerivAt expMapBasis (fderiv_expMapBasis K x) x := by
  change HasFDerivAt (expMap ∘ (completeBasis K).equivFunL.symm) (fderiv_expMapBasis K x) x
  exact (hasFDerivAt_expMap _).comp x (completeBasis K).equivFunL.symm.hasFDerivAt

open Classical ContinuousLinearMap in
/-
**NumberField.mixedEmbedding.fundamentalCone.abs_det_fderiv_expMapBasis** 是 Math
lib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：abs_det_fderiv_expMapBasis (x : realSpace K) : |(fderiv_expMapBasis K x).d
et| = Real.exp (x w₀ * Module.finrank Rat K) * (∏ w : {w // IsComplex w}, expMap
Basis x w.1)⁻¹ * 2⁻¹ ^ nrComplexPlaces K * (Module.finrank Rat K) * regulator K
参数：x : realSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.det_comp`：det_comp (f g : M ->ₗ[A] M) : LinearMap.det (f.comp 
g) = LinearMap.det f * LinearMap.det g
· 使用定理 `LinearMap.det_pi`：det_pi [Module.Free R M] [Module.Finite R M] (f : ι ->
 M ->ₗ[R] M) : (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))).det = ∏ i
, (f i…
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `LinearMap.det_ring`：∀ {R : Type u_1} [inst : CommRing R] (f : R →ₗ[R] R)
, LinearMap.det f = f 1
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.abs_det_completeBasis_equivFu
nL_symm`：abs_det_completeBasis_equivFunL_symm : |((completeBasis K).equivFunL.sy
mm : realSpace K ->L[Real] realSpace K).det| = Module.finrank Rat K *…
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.prod_deriv_expMap_single`：pro
d_deriv_expMap_single (x : realSpace K) : ∏ w, deriv_expMap_single w ((completeB
asis K).equivFun.symm x w) = Real.exp (x w₀) ^ Module.fin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.exp_mul`：exp_mul (x y : Real) : exp (x * y) = exp x ^ y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Real.exp_nonneg`：exp_nonneg (x : Real) : 0 <= exp x
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用引理 `Finset.abs_prod`：abs_prod [CommRing R] [LinearOrder R] [IsStrictOrderedR
ing R] (s : Finset ι) (f : ι -> R) : |∏ x in s, f x| = ∏ x in s, |f x|
（共 64 条，此处仅展示前 30 条）
-/
theorem abs_det_fderiv_expMapBasis (x : realSpace K) :
    |(fderiv_expMapBasis K x).det| =
      Real.exp (x w₀ * Module.finrank ℚ K) *
      (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ * 2⁻¹ ^ nrComplexPlaces K *
        (Module.finrank ℚ K) * regulator K := by
  simp_rw [fderiv_expMapBasis, det, toLinearMap_comp, LinearMap.det_comp, fderiv_expMap, coe_pi,
    toLinearMap_comp, coe_proj, LinearMap.det_pi, LinearMap.det_ring, ContinuousLinearMap.coe_coe,
    smulRight_apply, one_apply_eq_self, one_smul, abs_mul, abs_det_completeBasis_equivFunL_symm,
    prod_deriv_expMap_single]
  simp_rw [abs_mul, Real.exp_mul, abs_pow, Real.rpow_natCast, abs_of_nonneg (Real.exp_nonneg _),
    abs_inv, abs_prod, abs_of_nonneg (expMapBasis_nonneg _ _), Nat.abs_ofNat]
  ring

variable {K}

open ENNReal MeasureTheory

open scoped Classical in
/-
**NumberField.mixedEmbedding.fundamentalCone.setLIntegral_expMapBasis_image** 是 
Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：setLIntegral_expMapBasis_image {s : Set (realSpace K)} (hs : MeasurableSet
 s) {f : (InfinitePlace K -> Real) -> Real>=0∞} (hf : Measurable f) : ∫⁻ x in ex
pMapBasis '' s, f x = (2 : Real>=0∞)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (reg
ulator K) * (Module.finrank Rat K) * ∫⁻ x in s, ENNReal.ofReal (Real.exp (x w₀ *
 Module.finrank Rat K)) * (∏ i : {w : InfinitePlace K // IsComplex w}, .ofReal (
expMapBasis (fun w => x w) i))⁻¹ * f (expMapBasis x)
参数：realSpace K；hs : MeasurableSet s；InfinitePlace K -> Real；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`：lintegral
_image_eq_lintegral_abs_det_fderiv_mul (hs : MeasurableSet s) (hf' : forall x in
 s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfS
igmaFinite`：∀ {ι : Type u_1} [inst : Fintype ι] {G : ι → Type u_4} [inst_1 : (i 
: ι) → AddGroup (G i)]   [inst_2 : (i : ι) → MeasureTheory.MeasureSpace …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.hasFDerivAt_expMapBasis`：hasF
DerivAt_expMapBasis (x : realSpace K) : HasFDerivAt expMapBasis (fderiv_expMapBa
sis K x) x
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.injective_expMapBasis`：inject
ive_expMapBasis : Function.Injective (expMapBasis : realSpace K -> realSpace K)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.abs_det_fderiv_expMapBasis`：a
bs_det_fderiv_expMapBasis (x : realSpace K) : |(fderiv_expMapBasis K x).det| = R
eal.exp (x w₀ * Module.finrank Rat K) * (∏ w : {w // IsComp…
（共 93 条，此处仅展示前 30 条）
-/
theorem setLIntegral_expMapBasis_image {s : Set (realSpace K)} (hs : MeasurableSet s)
    {f : (InfinitePlace K → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in expMapBasis '' s, f x =
      (2 : ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (Module.finrank ℚ K) *
        ∫⁻ x in s, ENNReal.ofReal (Real.exp (x w₀ * Module.finrank ℚ K)) *
          (∏ i : {w : InfinitePlace K // IsComplex w},
            .ofReal (expMapBasis (fun w ↦ x w) i))⁻¹ * f (expMapBasis x) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x _ ↦ (hasFDerivAt_expMapBasis K x).hasFDerivWithinAt) (injective_expMapBasis K).injOn]
  simp_rw [abs_det_fderiv_expMapBasis]
  have : Measurable expMapBasis := (continuous_expMapBasis K).measurable
  rw [← lintegral_const_mul _ (by fun_prop)]
  congr with x
  have : 0 ≤ (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ :=
    inv_nonneg.mpr <| Finset.prod_nonneg fun _ _ ↦ (expMapBasis_pos _ _).le
  rw [ofReal_mul (by positivity), ofReal_mul (by positivity), ofReal_mul (by positivity),
    ofReal_mul (by positivity), ofReal_pow (by positivity), ofReal_inv_of_pos (Finset.prod_pos
    fun _ _ ↦ expMapBasis_pos _ _), ofReal_inv_of_pos zero_lt_two, ofReal_ofNat, ofReal_natCast,
    ofReal_prod_of_nonneg (fun _ _ ↦ (expMapBasis_pos _ _).le)]
  ring

end expMapBasis

section paramSet

variable [NumberField K]

open scoped Classical in
/--
The set that parametrizes `normAtAllPlaces '' (normLeOne K)`, see
`normAtAllPlaces_normLeOne_eq_image`.
-/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**NumberField.mixedEmbedding.fundamentalCone.paramSet** 是 Mathlib 中的一个缩写定义，位于命名空
间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：paramSet : Set (realSpace K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev paramSet : Set (realSpace K) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Iic 0 else Set.Ico 0 1
/-
**NumberField.mixedEmbedding.fundamentalCone.measurableSet_paramSet** 是 Mathlib 
中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：measurableSet_paramSet : MeasurableSet (paramSet K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `measurableSet_Iic`：measurableSet_Iic [ClosedIicTopology α] : MeasurableS
et (Iic a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `measurableSet_Ico`：measurableSet_Ico [ClosedIciTopology α] : MeasurableS
et (Ico a b)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
-/
theorem measurableSet_paramSet :
    MeasurableSet (paramSet K) := by
  refine MeasurableSet.univ_pi fun _ ↦ ?_
  split_ifs
  · exact measurableSet_Iic
  · exact measurableSet_Ico

open scoped Classical in
/-
**NumberField.mixedEmbedding.fundamentalCone.interior_paramSet** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：interior_paramSet : interior (paramSet K) = Set.univ.pi fun w => if w = w₀
 then Set.Iio 0 else Set.Ioo 0 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_pi_set`：interior_pi_set {I : Set ι} (hI : I.Finite) {s : forall
 i, Set (A i)} : interior (pi I s) = I.pi fun i => interior (s i)
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `interior_Iic'`：interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior 
(Iic a) = Iio a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `interior_Ico`：interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b)
 = Ioo a b
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem interior_paramSet :
    interior (paramSet K) = Set.univ.pi fun w ↦ if w = w₀ then Set.Iio 0 else Set.Ioo 0 1 := by
  simp [interior_pi_set Set.finite_univ, apply_ite]

open scoped Classical in
/-
**NumberField.mixedEmbedding.fundamentalCone.closure_paramSet** 是 Mathlib 中的一个定理
，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：closure_paramSet : closure (paramSet K) = Set.univ.pi fun w => if w = w₀ t
hen Set.Iic 0 else Set.Icc 0 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_pi_set`：closure_pi_set {ι : Type*} {α : ι -> Type*} [forall i, T
opologicalSpace (α i)] (I : Set ι) (s : forall i, Set (α i)) : closure (pi I s) 
= pi…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `closure_Iic`：closure_Iic (a : α) : closure (Iic a) = Iic a
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `closure_Ico`：closure_Ico {a b : α} (hab : a != b) : closure (Ico a b) = 
Icc a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closure_paramSet :
    closure (paramSet K) = Set.univ.pi fun w ↦ if w = w₀ then Set.Iic 0 else Set.Icc 0 1 := by
  simp [closure_pi_set, apply_ite]
/-
**NumberField.mixedEmbedding.fundamentalCone.normAtAllPlaces_normLeOne_eq_image*
* 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：normAtAllPlaces_normLeOne_eq_image : normAtAllPlaces '' (normLeOne K) = ex
pMapBasis '' (paramSet K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_univ_pi`：mem_univ_pi : f in pi univ t ↔ forall i, f i in t i
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.injective_expMapBasis`：inject
ive_expMapBasis : Function.Injective (expMapBasis : realSpace K -> realSpace K)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.normAtAllPlaces_normLeOne`：no
rmAtAllPlaces_normLeOne : normAtAllPlaces '' (normLeOne K) = mixedSpaceOfRealSpa
ce ⁻¹' (logMap ⁻¹' ZSpan.fundamentalDomain ((basisUnitLatt…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.norm_expMapBasis`：norm_expMap
Basis (x : realSpace K) : mixedEmbedding.norm (mixedSpaceOfRealSpace (expMapBasi
s x)) = Real.exp (x w₀) ^ Module.finrank Rat K
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `pow_le_one_iff_of_nonneg`：pow_le_one_iff_of_nonneg (ha : 0 <= a) (hn : n
 != 0) : a ^ n <= 1 ↔ a <= 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Real.exp_nonneg`：exp_nonneg (x : Real) : 0 <= exp x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
（共 45 条，此处仅展示前 30 条）
-/
theorem normAtAllPlaces_normLeOne_eq_image :
    normAtAllPlaces '' (normLeOne K) = expMapBasis '' (paramSet K) := by
  ext x
  by_cases hx : ∀ w, 0 < x w
  · rw [← expMapBasis.right_inv (Set.mem_univ_pi.mpr hx), (injective_expMapBasis K).mem_set_image]
    simp only [normAtAllPlaces_normLeOne, Set.mem_inter_iff, Set.mem_ofPred_eq, expMapBasis_nonneg,
      Set.mem_preimage, logMap_expMapBasis, implies_true, and_true, norm_expMapBasis,
      pow_le_one_iff_of_nonneg (Real.exp_nonneg _) Module.finrank_pos.ne', Real.exp_le_one_iff,
      ne_eq, pow_eq_zero_iff', Real.exp_ne_zero, false_and, not_false_eq_true, Set.mem_univ_pi]
    refine ⟨fun ⟨h₁, h₂⟩ w ↦ ?_, fun h ↦ ⟨fun w hw ↦ by simpa [hw] using h w, by simpa using h w₀⟩⟩
    · split_ifs with hw
      · exact hw ▸ h₂
      · exact h₁ w hw
  · refine ⟨?_, ?_⟩
    · rintro ⟨a, ⟨ha, _⟩, rfl⟩
      exact (hx fun w ↦ fundamentalCone.normAtPlace_pos_of_mem ha w).elim
    · rintro ⟨a, _, rfl⟩
      exact (hx fun w ↦ expMapBasis_pos a w).elim
/-
**NumberField.mixedEmbedding.fundamentalCone.normLeOne_eq_preimage** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：normLeOne_eq_preimage : normLeOne K = normAtAllPlaces ⁻¹' expMapBasis '' (
paramSet K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.normLeOne_eq_preimage_image`：
normLeOne_eq_preimage_image : normLeOne K = normAtAllPlaces ⁻¹' normAtAllPlaces 
'' (normLeOne K)
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.normAtAllPlaces_normLeOne_eq_
image`：normAtAllPlaces_normLeOne_eq_image : normAtAllPlaces '' (normLeOne K) = e
xpMapBasis '' (paramSet K)
-/
theorem normLeOne_eq_preimage :
    normLeOne K = normAtAllPlaces ⁻¹' expMapBasis '' (paramSet K) := by
  rw [normLeOne_eq_preimage_image, normAtAllPlaces_normLeOne_eq_image]
/-
**NumberField.mixedEmbedding.fundamentalCone.subset_interior_normLeOne** 是 Mathl
ib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：subset_interior_normLeOne : normAtAllPlaces ⁻¹' expMapBasis '' interior (p
aramSet K) subseteq interior (normLeOne K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.normLeOne_eq_preimage`：normLe
One_eq_preimage : normLeOne K = normAtAllPlaces ⁻¹' expMapBasis '' (paramSet K)
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用引理 `OpenPartialHomeomorph.isOpen_image_of_subset_source`：isOpen_image_of_sub
set_source {s : Set X} (hs : IsOpen s) (hse : s subseteq e.source) : IsOpen (e '
' s)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_source`：expMapBas
is_source : expMapBasis.source = (Set.univ : Set (realSpace K))
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `preimage_interior_subset_interior_preimage`：preimage_interior_subset_int
erior_preimage {t : Set Y} (hf : Continuous f) : f ⁻¹' interior t subseteq inter
ior (f ⁻¹' t)
· 使用定理 `NumberField.mixedEmbedding.continuous_normAtAllPlaces`：continuous_normAt
AllPlaces : Continuous (normAtAllPlaces : mixedSpace K -> realSpace K)
-/
theorem subset_interior_normLeOne :
    normAtAllPlaces ⁻¹' expMapBasis '' interior (paramSet K) ⊆ interior (normLeOne K) := by
  rw [normLeOne_eq_preimage]
  refine subset_trans (Set.preimage_mono ?_) <|
    preimage_interior_subset_interior_preimage (continuous_normAtAllPlaces K)
  have : IsOpen (expMapBasis '' (interior (paramSet K))) :=
    expMapBasis.isOpen_image_of_subset_source isOpen_interior (by simp [expMapBasis_source])
  exact interior_maximal (Set.image_mono interior_subset) this

open ENNReal MeasureTheory
/-
**NumberField.mixedEmbedding.fundamentalCone.closure_paramSet_ae_interior** 是 Ma
thlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：closure_paramSet_ae_interior : closure (paramSet K) =ᵐ[volume] interior (p
aramSet K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.closure_paramSet`：closure_par
amSet : closure (paramSet K) = Set.univ.pi fun w => if w = w₀ then Set.Iic 0 els
e Set.Icc 0 1
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.interior_paramSet`：interior_p
aramSet : interior (paramSet K) = Set.univ.pi fun w => if w = w₀ then Set.Iio 0 
else Set.Ioo 0 1
· 使用定理 `MeasureTheory.volume_pi`：volume_pi [forall i, MeasureSpace (α i)] : (vol
ume : Measure (forall i, α i)) = Measure.pi fun _ => volume
· 使用定理 `MeasureTheory.Measure.ae_eq_set_pi`：ae_eq_set_pi {I : Set ι} {s t : fora
ll i, Set (α i)} (h : forall i in I, s i =ᵐ[μ i] t i) : Set.pi I s =ᵐ[Measure.pi
 μ] Set.pi I t
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Iio_ae_eq_Iic`：Iio_ae_eq_Iic : Iio a =ᵐ[μ] Iic a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.Ioo_ae_eq_Icc`：Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b
-/
theorem closure_paramSet_ae_interior : closure (paramSet K) =ᵐ[volume] interior (paramSet K) := by
  rw [closure_paramSet, interior_paramSet, volume_pi]
  refine Measure.ae_eq_set_pi fun w _ ↦ ?_
  split_ifs
  · exact Iio_ae_eq_Iic.symm
  · exact Ioo_ae_eq_Icc.symm
/-
**NumberField.mixedEmbedding.fundamentalCone.setLIntegral_paramSet_exp** 是 Mathl
ib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：setLIntegral_paramSet_exp {n : Nat} (hn : 0 < n) : ∫⁻ (x : realSpace K) in
 paramSet K, .ofReal (Real.exp (x w₀ * n)) = (n : Real>=0∞)⁻¹
参数：hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.volume_pi`：volume_pi [forall i, MeasureSpace (α i)] : (vol
ume : Measure (forall i, α i)) = Measure.pi fun _ => volume
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.paramSet.eq_1`：∀ (K : Type u_
1) [inst : Field K] [inst_1 : NumberField K],   NumberField.mixedEmbedding.funda
mentalCone.paramSet K =     Set.univ.pi fun w …
· 使用定理 `MeasureTheory.Measure.restrict_pi_pi`：restrict_pi_pi (s : (i : ι) -> Set
 (α i)) : (Measure.pi μ).restrict (Set.univ.pi fun i => s i) = .pi (fun i => (μ 
i).restrict (s i))
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.lintegral_eq_lmarginal_univ`：lintegral_eq_lmarginal_univ [
Fintype δ] {f : (forall i, X i) -> Real>=0∞} (x : forall i, X i) : ∫⁻ x, f x ∂Me
asure.pi μ = (∫⋯∫⁻_univ, f ∂μ) …
· 使用定理 `MeasureTheory.Restrict.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} (μ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ] (s : Set α),  
 MeasureTheory.SigmaFini…
· 使用定理 `MeasureTheory.lmarginal_erase'`：lmarginal_erase' (f : (forall i, X i) ->
 Real>=0∞) (hf : Measurable f) {i : δ} (hi : i in s) : ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_(eras
e s i), (fun x => ∫⁻…
· 使用定理 `Measurable.ennreal_ofReal`：Measurable.ennreal_ofReal {f : α -> Real} (hf
 : Measurable f) : Measurable fun x => ENNReal.ofReal (f x)
· 使用定理 `Measurable.exp`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Me
asurable f → Measurable fun x => Real.exp (f x)
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 58 条，此处仅展示前 30 条）
-/
theorem setLIntegral_paramSet_exp {n : ℕ} (hn : 0 < n) :
    ∫⁻ (x : realSpace K) in paramSet K, .ofReal (Real.exp (x w₀ * n)) = (n : ℝ≥0∞)⁻¹ := by
  classical
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [volume_pi, paramSet, Measure.restrict_pi_pi, lintegral_eq_lmarginal_univ 0,
    lmarginal_erase' _ (by fun_prop) (Finset.mem_univ w₀), if_pos rfl]
  simp_rw [Function.update_self, lmarginal, lintegral_const, Measure.pi_univ, if_neg
    (Finset.ne_of_mem_erase (Subtype.prop _)), Measure.restrict_apply_univ, Real.volume_Ico,
    sub_zero, ofReal_one, prod_const_one, mul_one, mul_comm _ (n : ℝ)]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic hn _), integral_exp_mul_Iic
    hn, mul_zero, Real.exp_zero, ofReal_div_of_pos hn, ofReal_one, ofReal_natCast, one_div]
  filter_upwards with _ using Real.exp_nonneg _

end paramSet

section compactSet

variable [NumberField K]

open scoped Pointwise

open scoped Classical in
/--
A compact set that contains `expMapBasis '' closure (paramSet K)` and furthermore is almost
equal to it, see `compactSet_ae`.
-/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**NumberField.mixedEmbedding.fundamentalCone.compactSet** 是 Mathlib 中的一个缩写定义，位于命
名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：compactSet : Set (realSpace K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev compactSet : Set (realSpace K) :=
  (Set.Icc (0 : ℝ) 1) • (expMapBasis '' Set.univ.pi fun w ↦ if w = w₀ then {0} else Set.Icc 0 1)
/-
**NumberField.mixedEmbedding.fundamentalCone.isCompact_compactSet** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：isCompact_compactSet : IsCompact (compactSet K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompact.smul_set`：IsCompact.smul_set {k : Set M} {u : Set X} (hk : IsC
ompact k) (hu : IsCompact u) : IsCompact (k • u)
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `isCompact_univ_pi`：isCompact_univ_pi {s : forall i, Set (X i)} (h : fora
ll i, IsCompact (s i)) : IsCompact (pi univ s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.continuous_expMapBasis`：conti
nuous_expMapBasis : Continuous (expMapBasis : realSpace K -> realSpace K)
-/
theorem isCompact_compactSet :
    IsCompact (compactSet K) := by
  refine isCompact_Icc.smul_set <| (isCompact_univ_pi fun w ↦ ?_).image_of_continuousOn
    (continuous_expMapBasis K).continuousOn
  split_ifs
  · exact isCompact_singleton
  · exact isCompact_Icc
/-
**NumberField.mixedEmbedding.fundamentalCone.zero_mem_compactSet** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：zero_mem_compactSet : 0 in compactSet K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.zero_mem_smul_iff`：zero_mem_smul_iff : 0 in s • t ↔ 0 in s ∧ t.Nonem
pty ∨ 0 in t ∧ s.Nonempty where mp | ⟨a, ha, b, hb, h⟩ => by obtain rfl | rfl
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `Set.univ_pi_nonempty_iff`：univ_pi_nonempty_iff : (pi univ t).Nonempty ↔ 
forall i, (t i).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem zero_mem_compactSet :
    0 ∈ compactSet K := by
  refine Set.zero_mem_smul_iff.mpr (Or.inl ⟨Set.left_mem_Icc.mpr zero_le_one, ?_⟩)
  exact Set.image_nonempty.mpr (Set.univ_pi_nonempty_iff.mpr (by aesop))
/-
**NumberField.mixedEmbedding.fundamentalCone.nonneg_of_mem_compactSet** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：nonneg_of_mem_compactSet {x : realSpace K} (hx : x in compactSet K) (w : I
nfinitePlace K) : 0 <= x w
参数：hx : x in compactSet K；w : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_pos`：expMapBasis_
pos (x : realSpace K) (w : InfinitePlace K) : 0 < expMapBasis x w
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonneg_of_mem_compactSet {x : realSpace K} (hx : x ∈ compactSet K) (w : InfinitePlace K) :
    0 ≤ x w := by
  obtain ⟨c, hc, ⟨_, ⟨⟨a, ha, rfl⟩, _, rfl⟩⟩⟩ := hx
  exact mul_nonneg hc.1 (expMapBasis_pos _ _).le

variable {K} in
/-
**NumberField.mixedEmbedding.fundamentalCone.compactSet_eq_union_aux** 是 Mathlib
 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compactSet_eq_union_aux₁ {x : realSpace K} (hx₀ : x ≠ 0)
    (hx₁ : x ∈ compactSet K) :
    x ∈ expMapBasis '' closure (paramSet K) := by
  classical
  obtain ⟨c, hc, ⟨_, ⟨y, hy, rfl⟩, rfl⟩⟩ := hx₁
  refine ⟨fun w ↦ if w = w₀ then Real.log c else y w, ?_, ?_⟩
  · rw [closure_paramSet, Set.mem_univ_pi]
    intro w
    split_ifs with h
    · refine Real.log_nonpos hc.1 hc.2
    · simpa [h] using hy w (Set.mem_univ _)
  · have hc' : 0 < c := by
      contrapose! hx₀
      rw [le_antisymm hx₀ hc.1, zero_smul]
    rw [expMapBasis_apply'', if_pos rfl, Real.exp_log hc']
    congr with w
    split_ifs with h
    · simpa [h, eq_comm] using hy w₀
    · rfl

variable {K} in
/-
**NumberField.mixedEmbedding.fundamentalCone.compactSet_eq_union_aux** 是 Mathlib
 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compactSet_eq_union_aux₂ {x : realSpace K} (hx₀ : x ≠ 0)
    (hx₁ : x ∈ expMapBasis '' closure (paramSet K)) :
    x ∈ compactSet K := by
  classical
  simp only [closure_paramSet, Set.mem_image, Set.mem_smul, exists_exists_and_eq_and] at hx₁ ⊢
  obtain ⟨y, hy, rfl⟩ := hx₁
  refine ⟨Real.exp (y w₀), ⟨Real.exp_nonneg _, ?_⟩,
        fun i ↦ if i = w₀ then 0 else y i, Set.mem_univ_pi.mpr fun w ↦ ?_,
        by rw [expMapBasis_apply'' y]⟩
  · exact Real.exp_le_one_iff.mpr (by simpa using hy w₀ (Set.mem_univ _))
  · split_ifs with h
    · rfl
    · simpa [h] using hy w (Set.mem_univ _)
/-
**NumberField.mixedEmbedding.fundamentalCone.compactSet_eq_union** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：compactSet_eq_union : compactSet K = expMapBasis '' closure (paramSet K) u
nion {0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.zero_mem_compactSet`：zero_mem
_compactSet : 0 in compactSet K
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.compactSet_eq_union_aux₁`：com
pactSet_eq_union_aux₁ {x : realSpace K} (hx₀ : x != 0) (hx₁ : x in compactSet K)
 : x in expMapBasis '' closure (paramSet K)
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.compactSet_eq_union_aux₂`：com
pactSet_eq_union_aux₂ {x : realSpace K} (hx₀ : x != 0) (hx₁ : x in expMapBasis '
' closure (paramSet K)) : x in compactSet K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem compactSet_eq_union :
    compactSet K = expMapBasis '' closure (paramSet K) ∪ {0} := by
  ext x
  by_cases hx₀ : x = 0
  · simpa [hx₀] using zero_mem_compactSet K
  · refine ⟨fun hx ↦ Set.mem_union_left _ (compactSet_eq_union_aux₁ hx₀ hx), fun hx ↦ ?_⟩
    simp only [Set.union_singleton, Set.mem_insert_iff, hx₀, false_or] at hx
    exact compactSet_eq_union_aux₂ hx₀ hx
/-
**NumberField.mixedEmbedding.fundamentalCone.expMapBasis_closure_subset_compactS
et** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：expMapBasis_closure_subset_compactSet : expMapBasis '' closure (paramSet K
) subseteq compactSet K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.compactSet_eq_union`：compactS
et_eq_union : compactSet K = expMapBasis '' closure (paramSet K) union {0}
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
theorem expMapBasis_closure_subset_compactSet :
    expMapBasis '' closure (paramSet K) ⊆ compactSet K := by
  rw [compactSet_eq_union]
  exact Set.subset_union_left
/-
**NumberField.mixedEmbedding.fundamentalCone.closure_normLeOne_subset** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：closure_normLeOne_subset : closure (normLeOne K) subseteq normAtAllPlaces 
⁻¹' (compactSet K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.normLeOne_eq_preimage`：normLe
One_eq_preimage : normLeOne K = normAtAllPlaces ⁻¹' expMapBasis '' (paramSet K)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Continuous.closure_preimage_subset`：Continuous.closure_preimage_subset (
hf : Continuous f) (t : Set Y) : closure (f ⁻¹' t) subseteq f ⁻¹' closure t
· 使用定理 `NumberField.mixedEmbedding.continuous_normAtAllPlaces`：continuous_normAt
AllPlaces : Continuous (normAtAllPlaces : mixedSpace K -> realSpace K)
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.isCompact_compactSet`：isCompa
ct_compactSet : IsCompact (compactSet K)
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_closure_subset_co
mpactSet`：expMapBasis_closure_subset_compactSet : expMapBasis '' closure (paramS
et K) subseteq compactSet K
-/
theorem closure_normLeOne_subset :
    closure (normLeOne K) ⊆ normAtAllPlaces ⁻¹' (compactSet K) := by
  rw [normLeOne_eq_preimage]
  refine ((continuous_normAtAllPlaces K).closure_preimage_subset _).trans (Set.preimage_mono ?_)
  refine (isCompact_compactSet K).isClosed.closure_subset_iff.mpr ?_
  exact (Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet _)

open MeasureTheory
/-
**NumberField.mixedEmbedding.fundamentalCone.compactSet_ae** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：compactSet_ae : compactSet K =ᵐ[volume] expMapBasis '' closure (paramSet K
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.compactSet_eq_union`：compactS
et_eq_union : compactSet K = expMapBasis '' closure (paramSet K) union {0}
· 使用定理 `MeasureTheory.union_ae_eq_left_of_ae_eq_empty`：union_ae_eq_left_of_ae_eq
_empty (h : t =ᵐ[μ] (∅ : Set α)) : (s union t : Set α) =ᵐ[μ] s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `MeasureTheory.Measure.instNullSingletonClassForallVolumeOfNonemptyOfSigm
aFinite`：∀ {ι : Type u_1} [inst : Fintype ι] {α : ι → Type u_4} [Nonempty ι]   [
inst_2 : (i : ι) → MeasureTheory.MeasureSpace (α i)] [∀ (i : ι), Meas…
· 使用定理 `NumberField.instNonemptyInfinitePlaceOfRingHomComplex`：∀ (K : Type u_1) 
[inst : Field K] [Nonempty (K →+* ℂ)], Nonempty (NumberField.InfinitePlace K)
· 使用定理 `NumberField.Embeddings.instNonemptyRingHom`：∀ (K : Type u_1) [inst : Fie
ld K] (A : Type u_2) [inst_1 : Field A] [CharZero A] [NumberField K] [IsAlgClose
d A],   Nonempty (K →+* A)
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compactSet_ae :
    compactSet K =ᵐ[volume] expMapBasis '' closure (paramSet K) := by
  rw [compactSet_eq_union]
  exact union_ae_eq_left_of_ae_eq_empty (by simp)

end compactSet

section main_results

variable [NumberField K]

open Bornology ENNReal MeasureTheory

/-
**NumberField.mixedEmbedding.fundamentalCone.isBounded_normLeOne** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：isBounded_normLeOne : IsBounded (normLeOne K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.normLeOne_eq_preimage`：normLe
One_eq_preimage : normLeOne K = normAtAllPlaces ⁻¹' expMapBasis '' (paramSet K)
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.isCompact_compactSet`：isCompa
ct_compactSet : IsCompact (compactSet K)
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_closure_subset_co
mpactSet`：expMapBasis_closure_subset_compactSet : expMapBasis '' closure (paramS
et K) subseteq compactSet K
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isBounded_iff_forall_norm_le`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] {s : Set E}, Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `NumberField.instNonemptyInfinitePlaceOfRingHomComplex`：∀ (K : Type u_1) 
[inst : Field K] [Nonempty (K →+* ℂ)], Nonempty (NumberField.InfinitePlace K)
· 使用定理 `NumberField.Embeddings.instNonemptyRingHom`：∀ (K : Type u_1) [inst : Fie
ld K] (A : Type u_2) [inst_1 : Field A] [CharZero A] [NumberField K] [IsAlgClose
d A],   Nonempty (K →+* A)
· 使用定理 `NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace`：∀ {K : Type u_1} [i
nst : Field K] [inst_1 : NumberField K] (x : NumberField.mixedEmbedding.mixedSpa
ce K),   ‖x‖ = Finset.univ.sup' ⋯ fun w =…
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_nonneg`：normAtPlace_nonneg (w : I
nfinitePlace K) (x : mixedSpace K) : 0 <= normAtPlace w x
· 使用定理 `pi_norm_le_iff_of_nonempty`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : 
Fintype ι] [inst_1 : (i : ι) → SeminormedAddGroup (G i)] (f : (i : ι) → G i)   {
r : ℝ} [Nonempty…
-/
theorem isBounded_normLeOne :
    IsBounded (normLeOne K) := by
  classical
  rw [normLeOne_eq_preimage]
  suffices IsBounded (expMapBasis '' paramSet K) by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp this
    refine isBounded_iff_forall_norm_le.mpr ⟨C, fun x hx ↦ ?_⟩
    rw [norm_eq_sup'_normAtPlace]
    refine sup'_le _ _ fun w _ ↦ ?_
    simpa [normAtAllPlaces_apply, Real.norm_of_nonneg (normAtPlace_nonneg w x)]
      using (pi_norm_le_iff_of_nonempty _).mp (hC _ hx) w
  refine IsBounded.subset ?_ (Set.image_mono subset_closure)
  exact (isCompact_compactSet K).isBounded.subset (expMapBasis_closure_subset_compactSet K)

open scoped Classical in
/-
**NumberField.mixedEmbedding.fundamentalCone.volume_normLeOne** 是 Mathlib 中的一个定理
，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：volume_normLeOne : volume (normLeOne K) = 2 ^ nrRealPlaces K * NNReal.pi ^
 nrComplexPlaces K * .ofReal (regulator K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.volume_eq_two_pow_mul_two_pi_pow_mul_integral
`：volume_eq_two_pow_mul_two_pi_pow_mul_integral [NumberField K] (hA : normAtAllP
laces ⁻¹' normAtAllPlaces '' A = A) (hm : MeasurableSet A) : v…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.normLeOne_eq_preimage_image`：
normLeOne_eq_preimage_image : normLeOne K = normAtAllPlaces ⁻¹' normAtAllPlaces 
'' (normLeOne K)
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.measurableSet_normLeOne`：meas
urableSet_normLeOne : MeasurableSet (normLeOne K)
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.normLeOne_eq_preimage`：normLe
One_eq_preimage : normLeOne K = normAtAllPlaces ⁻¹' expMapBasis '' (paramSet K)
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.normAtAllPlaces_image_preimag
e_expMapBasis`：normAtAllPlaces_image_preimage_expMapBasis (s : Set (realSpace K)
) : normAtAllPlaces '' normAtAllPlaces ⁻¹' expMapBasis '' s = expMapBasis '…
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.setLIntegral_expMapBasis_imag
e`：setLIntegral_expMapBasis_image {s : Set (realSpace K)} (hs : MeasurableSet s)
 {f : (InfinitePlace K -> Real) -> Real>=0∞} (hf : Measurable f…
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.measurableSet_paramSet`：measu
rableSet_paramSet : MeasurableSet (paramSet K)
· 使用定理 `Finset.measurable_prod`：Finset.measurable_prod (s : Finset ι) (hf : fora
ll i in s, Measurable (f i)) : Measurable fun a => ∏ i in s, f i a
· 使用定理 `Measurable.ennreal_ofReal`：Measurable.ennreal_ofReal {f : α -> Real} (hf
 : Measurable f) : Measurable fun x => ENNReal.ofReal (f x)
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.inv_mul_cancel_right`：∀ {a b : ENNReal}, b ≠ 0 → b ≠ ⊤ → a * b⁻¹
 * b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `ENNReal.ofReal_ne_zero_iff`：ofReal_ne_zero_iff {r : Real} : ENNReal.ofRe
al r != 0 ↔ 0 < r
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_pos`：expMapBasis_
pos (x : realSpace K) (w : InfinitePlace K) : 0 < expMapBasis x w
· 使用引理 `ENNReal.prod_ne_top`：prod_ne_top (h : forall a in s, f a != ∞) : ∏ a in 
s, f a != ∞
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.setLIntegral_paramSet_exp`：se
tLIntegral_paramSet_exp {n : Nat} (hn : 0 < n) : ∫⁻ (x : realSpace K) in paramSe
t K, .ofReal (Real.exp (x w₀ * n)) = (n : Real>=0∞)⁻¹
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
（共 55 条，此处仅展示前 30 条）
-/
theorem volume_normLeOne : volume (normLeOne K) =
    2 ^ nrRealPlaces K * NNReal.pi ^ nrComplexPlaces K * .ofReal (regulator K) := by
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral (normLeOne_eq_preimage_image K).symm
    (measurableSet_normLeOne K), normLeOne_eq_preimage,
    normAtAllPlaces_image_preimage_expMapBasis,
    setLIntegral_expMapBasis_image (measurableSet_paramSet K) (by fun_prop)]
  simp_rw [ENNReal.inv_mul_cancel_right
    (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ ofReal_ne_zero_iff.mpr (expMapBasis_pos _ _))
    (prod_ne_top fun _ _ ↦ ofReal_ne_top)]
  rw [setLIntegral_paramSet_exp K Module.finrank_pos, ofReal_mul zero_le_two, mul_pow,
    ofReal_ofNat, ENNReal.mul_inv_cancel_right (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
    (natCast_ne_top _), coe_nnreal_eq, NNReal.coe_real_pi, mul_mul_mul_comm, ← ENNReal.inv_pow,
    ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel_right (pow_ne_zero _ two_ne_zero)
    (pow_ne_top ENNReal.ofNat_ne_top)]

open scoped Classical in
/-
**NumberField.mixedEmbedding.fundamentalCone.volume_interior_eq_volume_closure**
 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：volume_interior_eq_volume_closure : volume (interior (normLeOne K)) = volu
me (closure (normLeOne K))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.isCompact_compactSet`：isCompa
ct_compactSet : IsCompact (compactSet K)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `NumberField.mixedEmbedding.continuous_normAtAllPlaces`：continuous_normAt
AllPlaces : Continuous (normAtAllPlaces : mixedSpace K -> realSpace K)
· 使用定理 `MeasurableSet.image_of_continuousOn_injOn`：MeasurableSet.image_of_contin
uousOn_injOn [OpensMeasurableSpace β] [tγ : TopologicalSpace γ] [PolishSpace γ] 
[MeasurableSpace γ] [BorelSpace…
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.instSeparableSpaceForallOfCountable`：∀ {ι : Type u_2} {
X : ι → Type u_3} [inst : (i : ι) → TopologicalSpace (X i)]   [∀ (i : ι), Topolo
gicalSpace.SeparableSpace (X i)] [Countabl…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `measurableSet_interior`：measurableSet_interior : MeasurableSet (interior
 s)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.continuous_expMapBasis`：conti
nuous_expMapBasis : Continuous (expMapBasis : realSpace K -> realSpace K)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.injective_expMapBasis`：inject
ive_expMapBasis : Function.Injective (expMapBasis : realSpace K -> realSpace K)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
（共 55 条，此处仅展示前 30 条）
-/
theorem volume_interior_eq_volume_closure :
    volume (interior (normLeOne K)) = volume (closure (normLeOne K)) := by
  have h₁ : MeasurableSet (normAtAllPlaces ⁻¹' compactSet K) :=
    (isCompact_compactSet K).measurableSet.preimage (continuous_normAtAllPlaces K).measurable
  have h₂ : MeasurableSet (normAtAllPlaces ⁻¹' expMapBasis '' interior (paramSet K)) := by
    refine MeasurableSet.preimage ?_ (continuous_normAtAllPlaces K).measurable
    refine MeasurableSet.image_of_continuousOn_injOn ?_ (continuous_expMapBasis K).continuousOn
      (injective_expMapBasis K).injOn
    exact measurableSet_interior
  refine le_antisymm (measure_mono interior_subset_closure) ?_
  refine (measure_mono (closure_normLeOne_subset K)).trans ?_
  refine le_of_eq_of_le ?_ (measure_mono (subset_interior_normLeOne K))
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral Set.preimage_image_preimage h₁,
    normAtAllPlaces_image_preimage_of_nonneg (fun x a w ↦ nonneg_of_mem_compactSet K a w),
    volume_eq_two_pow_mul_two_pi_pow_mul_integral Set.preimage_image_preimage h₂,
    normAtAllPlaces_image_preimage_expMapBasis, setLIntegral_congr (compactSet_ae K),
    setLIntegral_expMapBasis_image measurableSet_closure (by fun_prop),
    setLIntegral_expMapBasis_image measurableSet_interior (by fun_prop),
    setLIntegral_congr (closure_paramSet_ae_interior K)]

open scoped Classical in
/-
**NumberField.mixedEmbedding.fundamentalCone.volume_frontier_normLeOne** 是 Mathl
ib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：volume_frontier_normLeOne : volume (frontier (normLeOne K)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), f
rontier s = closure s \ interior s
· 使用定理 `MeasureTheory.measure_sdiff`：measure_sdiff (h : s₂ subseteq s₁) (h₂ : Nu
llMeasurableSet s₂ μ) (h_fin : μ s₂ != ∞) : μ (s₁ \ s₂) = μ s₁ - μ s₂
· 使用定理 `interior_subset_closure`：interior_subset_closure : interior s subseteq c
losure s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `measurableSet_interior`：measurableSet_interior : MeasurableSet (interior
 s)
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.volume_normLeOne`：volume_norm
LeOne : volume (normLeOne K) = 2 ^ nrRealPlaces K * NNReal.pi ^ nrComplexPlaces 
K * .ofReal (regulator K)
· 使用定理 `Batteries.compareOfLessAndEq_eq_lt`：∀ {α : Type u_1} {x y : α} [inst : L
T α] [inst_1 : Decidable (x < y)] [inst_2 : DecidableEq α],   compareOfLessAndEq
 x y = Ordering.lt ↔ x <…
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.volume_interior_eq_volume_clo
sure`：volume_interior_eq_volume_closure : volume (interior (normLeOne K)) = volu
me (closure (normLeOne K))
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
-/
theorem volume_frontier_normLeOne :
     volume (frontier (normLeOne K)) = 0 := by
  rw [frontier, measure_sdiff, volume_interior_eq_volume_closure, tsub_self]
  · exact interior_subset_closure
  · exact measurableSet_interior.nullMeasurableSet
  · refine lt_top_iff_ne_top.mp <| lt_of_le_of_lt (measure_mono interior_subset) ?_
    rw [volume_normLeOne]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl

end main_results

end NumberField.mixedEmbedding.fundamentalCone

