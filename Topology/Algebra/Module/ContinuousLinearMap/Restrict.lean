/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Restrictions of continuous linear maps to submodules

In this file, we collect the various operations of restrictions of `ContinuousLinearMap`s
to subspaces of the domain/codomain.

## Main definitions

* `Submodule.subtypeL S` is the inclusion map `S →L[R] M` when `S : Submodule R M`.
  In other words, it is `Submodule.subtype S` bundled as a `ContinuousLinearMap`.
* `ContinuousLinearMap.domRestrict f S` is the map `S →SL[σ] N` obtained by restricting
  `f : M →SL[σ] N` to a subspace `S` of the *domain*.
  This is the continuous version of `LinearMap.domRestrict`.
* `ContinuousLinearMap.codRestrict f S h` is the map `M →SL[σ] S` obtained by co-restricting
  `f : M →SL[σ] N` to a subspace `S` of the *codomain*; this requires a proof `h` that all values
  of `f` indeed belong to `S`.
  This is the continuous version of `LinearMap.codRestrict`.
* `ContinuousLinearMap.rangeRestrict f` is an abbreviation for
  `f.codRestrict f.range ⋯ : M →SL[σ] f.range`.
  This is the continuous version of `LinearMap.rangeRestrict`.
* `ContinuousLinearMap.restrict f h` is the map `S →SL[σ] T` obtained by restricting from
  `f : M →SL[σ] N` and a proof `h` that `f` maps `S` inside `T`.
  This is the continuous version of `LinearMap.restrict`.
-/

@[expose] public section

open LinearMap (ker range)

namespace Submodule

section Semiring

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]

/--
Definition of `subtypeL` / `subtypeL` 的定义

English:
definition subtypeL
  signature: (p : Submodule R M)
  body: p.subtype

@[simp, norm_cast]

中文:
定义 subtypeL
  签名: (p : Submodule R M)
  定义体: p.subtype

@[simp, norm_cast]

Depends on / 依赖: p.subtype, subtype
-/
def subtypeL (p : Submodule R M) : p ->L[R] M where
  toLinearMap := p.subtype

@[simp, norm_cast]
/--
theorem `toLinearMap_subtypeL` / 定理 `toLinearMap_subtypeL`

English:
theorem toLinearMap_subtypeL
  given: (p : Submodule R M)
  statement: (p.subtypeL : p ->ₗ[R] M) = p.subtype
  proof: rfl

@[simp]

中文:
定理 toLinearMap_subtypeL
  条件: (p : Submodule R M)
  结论: (p.subtypeL : p ->ₗ[R] M) = p.subtype
  证明: rfl

@[simp]
-/
theorem toLinearMap_subtypeL (p : Submodule R M) : (p.subtypeL : p ->ₗ[R] M) = p.subtype := rfl

@[simp]
/--
theorem `coe_subtypeL` / 定理 `coe_subtypeL`

English:
theorem coe_subtypeL
  given: (p : Submodule R M)
  statement: ⇑p.subtypeL = p.subtype
  proof: rfl

@[deprecated (since := "2026-05-06")]
alias coe_subtypeL' := coe_subtypeL

中文:
定理 coe_subtypeL
  条件: (p : Submodule R M)
  结论: ⇑p.subtypeL = p.subtype
  证明: rfl

@[deprecated (since := "2026-05-06")]
alias coe_subtypeL' := coe_subtypeL
-/
theorem coe_subtypeL (p : Submodule R M) : ⇑p.subtypeL = p.subtype := rfl

@[deprecated (since := "2026-05-06")]
alias coe_subtypeL' := coe_subtypeL

/--
theorem `subtypeL_apply` / 定理 `subtypeL_apply`

English:
theorem subtypeL_apply
  given: (p : Submodule R M) (x : p)
  statement: p.subtypeL x = x
  proof: by simp

中文:
定理 subtypeL_apply
  条件: (p : Submodule R M) (x : p)
  结论: p.subtypeL x = x
  证明: by simp
-/
theorem subtypeL_apply (p : Submodule R M) (x : p) : p.subtypeL x = x := by simp

/--
theorem `isEmbedding_subtype` / 定理 `isEmbedding_subtype`

English:
theorem isEmbedding_subtype
  given: (p : Submodule R M)
  statement: Topology.IsEmbedding p.subtype
  proof: .subtypeVal

中文:
定理 isEmbedding_subtype
  条件: (p : Submodule R M)
  结论: Topology.IsEmbedding p.subtype
  证明: .subtypeVal

Depends on / 依赖: subtypeVal
-/
theorem isEmbedding_subtype (p : Submodule R M) : Topology.IsEmbedding p.subtype := .subtypeVal
/--
theorem `isEmbedding_subtypeL` / 定理 `isEmbedding_subtypeL`

English:
theorem isEmbedding_subtypeL
  given: (p : Submodule R M)
  statement: Topology.IsEmbedding p.subtypeL
  proof: .subtypeVal

中文:
定理 isEmbedding_subtypeL
  条件: (p : Submodule R M)
  结论: Topology.IsEmbedding p.subtypeL
  证明: .subtypeVal

Depends on / 依赖: subtypeVal
-/
theorem isEmbedding_subtypeL (p : Submodule R M) : Topology.IsEmbedding p.subtypeL := .subtypeVal

/--
theorem `isClosedEmbedding_subtype` / 定理 `isClosedEmbedding_subtype`

English:
theorem isClosedEmbedding_subtype
  given: (p : Submodule R M) (hp : IsClosed (p : Set M))
  proof: .subtypeVal hp

中文:
定理 isClosedEmbedding_subtype
  条件: (p : Submodule R M) (hp : IsClosed (p : Set M))
  证明: .subtypeVal hp

Depends on / 依赖: subtypeVal
-/
theorem isClosedEmbedding_subtype (p : Submodule R M) (hp : IsClosed (p : Set M)) :
    Topology.IsClosedEmbedding p.subtype := .subtypeVal hp
/--
theorem `isClosedEmbedding_subtypeL` / 定理 `isClosedEmbedding_subtypeL`

English:
theorem isClosedEmbedding_subtypeL
  given: (p : Submodule R M) (hp : IsClosed (p : Set M))
  proof: .subtypeVal hp

@[deprecated range_subtype (since := "2026-05-06")]

中文:
定理 isClosedEmbedding_subtypeL
  条件: (p : Submodule R M) (hp : IsClosed (p : Set M))
  证明: .subtypeVal hp

@[deprecated range_subtype (since := "2026-05-06")]

Depends on / 依赖: subtypeVal
-/
theorem isClosedEmbedding_subtypeL (p : Submodule R M) (hp : IsClosed (p : Set M)) :
    Topology.IsClosedEmbedding p.subtypeL := .subtypeVal hp

@[deprecated range_subtype (since := "2026-05-06")]
/--
theorem `range_subtypeL` / 定理 `range_subtypeL`

English:
theorem range_subtypeL
  given: (p : Submodule R M)
  statement: (p.subtypeL : p ->ₗ[R] M).range = p
  proof: Submodule.range_subtype _

@[deprecated ker_subtype (since := "2026-05-06")]

中文:
定理 range_subtypeL
  条件: (p : Submodule R M)
  结论: (p.subtypeL : p ->ₗ[R] M).range = p
  证明: Submodule.range_subtype _

@[deprecated ker_subtype (since := "2026-05-06")]

Depends on / 依赖: Submodule, Submodule.range_subtype, range_subtype
-/
theorem range_subtypeL (p : Submodule R M) : (p.subtypeL : p ->ₗ[R] M).range = p :=
  Submodule.range_subtype _

@[deprecated ker_subtype (since := "2026-05-06")]
/--
theorem `ker_subtypeL` / 定理 `ker_subtypeL`

English:
theorem ker_subtypeL
  given: (p : Submodule R M)
  statement: (p.subtypeL : p ->ₗ[R] M).ker = ⊥
  proof: Submodule.ker_subtype _

中文:
定理 ker_subtypeL
  条件: (p : Submodule R M)
  结论: (p.subtypeL : p ->ₗ[R] M).ker = ⊥
  证明: Submodule.ker_subtype _

Depends on / 依赖: Submodule, Submodule.ker_subtype, ker_subtype
-/
theorem ker_subtypeL (p : Submodule R M) : (p.subtypeL : p ->ₗ[R] M).ker = ⊥ :=
  Submodule.ker_subtype _

end Semiring

end Submodule

namespace ContinuousLinearMap

section Restrict

variable {R₁ R₂ R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ ->+* R₂} {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R₁ ->+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  {M₁ M₂ M₃ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂]
  [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R₃ M₃]

/-- The restriction of a linear map `f : M → M₂` to a submodule `p ⊆ M` gives a linear map
`p → M₂`. -/
@[simps!]
/--
Definition of `domRestrict` / `domRestrict` 的定义

English:
definition domRestrict
  signature: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₁ M₁)
  body: f ∘SL p.subtypeL

@[simp]

中文:
定义 domRestrict
  签名: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₁ M₁)
  定义体: f ∘SL p.subtypeL

@[simp]

Depends on / 依赖: p.subtypeL, subtypeL
-/
def domRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₁ M₁) : p ->SL[σ₁₂] M₂ :=
  f ∘SL p.subtypeL

@[simp]
/--
theorem `toLinearMap_domRestrict` / 定理 `toLinearMap_domRestrict`

English:
theorem toLinearMap_domRestrict
  given: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₁ M₁)
  proof: rfl

中文:
定理 toLinearMap_domRestrict
  条件: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₁ M₁)
  证明: rfl
-/
theorem toLinearMap_domRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₁ M₁) :
    (f.domRestrict p).toLinearMap = f.toLinearMap.domRestrict p :=
  rfl

/--
lemma `coe_domRestrict` / 引理 `coe_domRestrict`

English:
lemma coe_domRestrict
  given: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₁ M₁)
  proof: rfl

中文:
引理 coe_domRestrict
  条件: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₁ M₁)
  证明: rfl
-/
lemma coe_domRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₁ M₁) :
    ⇑(f.domRestrict p) = Set.domRestrict p f :=
  rfl

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x, f x in p)
  body: f.continuous.subtype_mk _
  toLinearMap := (f : M₁ ->ₛₗ[σ₁₂] M₂).codRestrict p h

@[simp, norm_cast]

中文:
定义 codRestrict
  签名: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : 对任意 x, f x in p)
  定义体: f.continuous.subtype_mk _
  toLinearMap := (f : M₁ ->ₛₗ[σ₁₂] M₂).codRestrict p h

@[simp, norm_cast]

Depends on / 依赖: continuous, f.continuous.subtype_mk, subtype_mk
-/
def codRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x, f x in p) :
    M₁ ->SL[σ₁₂] p where
  cont := f.continuous.subtype_mk _
  toLinearMap := (f : M₁ ->ₛₗ[σ₁₂] M₂).codRestrict p h

@[simp, norm_cast]
/--
theorem `toLinearMap_codRestrict` / 定理 `toLinearMap_codRestrict`

English:
theorem toLinearMap_codRestrict
  given: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x, f x in p)
  proof: rfl

中文:
定理 toLinearMap_codRestrict
  条件: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : 对任意 x, f x in p)
  证明: rfl
-/
theorem toLinearMap_codRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x, f x in p) :
    (f.codRestrict p h).toLinearMap = f.toLinearMap.codRestrict p h :=
  rfl

/--
theorem `coe_codRestrict` / 定理 `coe_codRestrict`

English:
theorem coe_codRestrict
  given: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x, f x in p)
  proof: rfl

@[simp]

中文:
定理 coe_codRestrict
  条件: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : 对任意 x, f x in p)
  证明: rfl

@[simp]
-/
theorem coe_codRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x, f x in p) :
    (f.codRestrict p h : M₁ -> p) = Set.codRestrict (f : M₁ -> M₂) p h :=
  rfl

@[simp]
/--
theorem `coe_codRestrict_apply` / 定理 `coe_codRestrict_apply`

English:
theorem coe_codRestrict_apply
  given: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x, f x in p) (x)
  proof: rfl

中文:
定理 coe_codRestrict_apply
  条件: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : 对任意 x, f x in p) (x)
  证明: rfl
-/
theorem coe_codRestrict_apply (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x, f x in p) (x) :
    (f.codRestrict p h x : M₂) = f x :=
  rfl

/--
theorem `ker_codRestrict` / 定理 `ker_codRestrict`

English:
theorem ker_codRestrict
  given: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x, f x in p)
  proof: f.toLinearMap.ker_codRestrict p h

@[simp]

中文:
定理 ker_codRestrict
  条件: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : 对任意 x, f x in p)
  证明: f.toLinearMap.ker_codRestrict p h

@[simp]

Depends on / 依赖: f.toLinearMap.ker_codRestrict, ker_codRestrict, toLinearMap
-/
theorem ker_codRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x, f x in p) :
    ker (f.codRestrict p h : M₁ ->ₛₗ[σ₁₂] p) = ker (f : M₁ ->ₛₗ[σ₁₂] M₂) :=
  f.toLinearMap.ker_codRestrict p h

@[simp]
/--
theorem `subtypeL_comp_codRestrict` / 定理 `subtypeL_comp_codRestrict`

English:
theorem subtypeL_comp_codRestrict
  given: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x, f x in p)
  proof: rfl

@[simp]

中文:
定理 subtypeL_comp_codRestrict
  条件: (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : 对任意 x, f x in p)
  证明: rfl

@[simp]
-/
theorem subtypeL_comp_codRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x, f x in p) :
    p.subtypeL ∘SL f.codRestrict p h = f :=
  rfl

@[simp]
/--
theorem `domRestrict_comp_codRestrict` / 定理 `domRestrict_comp_codRestrict`

English:
theorem domRestrict_comp_codRestrict
  statement: (g : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂)
  proof: rfl

中文:
定理 domRestrict_comp_codRestrict
  结论: (g : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂)
  证明: rfl
-/
theorem domRestrict_comp_codRestrict (g : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂)
    (p : Submodule R₂ M₂) (h : forall x, f x in p) :
    g.domRestrict p ∘SL f.codRestrict p h = g ∘SL f :=
  rfl

/--
Definition of `rangeRestrict` / `rangeRestrict` 的定义

English:
abbreviation rangeRestrict
  signature: [RingHomSurjective σ₁₂] (f : M₁ ->SL[σ₁₂] M₂)
  body: f.codRestrict (LinearMap.range (f : M₁ ->ₛₗ[σ₁₂] M₂)) (LinearMap.mem_range_self _)

中文:
缩写 rangeRestrict
  签名: [RingHomSurjective σ₁₂] (f : M₁ ->SL[σ₁₂] M₂)
  定义体: f.codRestrict (LinearMap.range (f : M₁ ->ₛₗ[σ₁₂] M₂)) (LinearMap.mem_range_self _)

Depends on / 依赖: LinearMap, LinearMap.mem_range_self, LinearMap.range, codRestrict, f.codRestrict, mem_range_self
-/
abbrev rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ ->SL[σ₁₂] M₂) :=
  f.codRestrict (LinearMap.range (f : M₁ ->ₛₗ[σ₁₂] M₂)) (LinearMap.mem_range_self _)

/--
theorem `toLinearMap_rangeRestrict` / 定理 `toLinearMap_rangeRestrict`

English:
theorem toLinearMap_rangeRestrict
  given: [RingHomSurjective σ₁₂] (f : M₁ ->SL[σ₁₂] M₂)
  proof: by simp

@[simp]

中文:
定理 toLinearMap_rangeRestrict
  条件: [RingHomSurjective σ₁₂] (f : M₁ ->SL[σ₁₂] M₂)
  证明: by simp

@[simp]
-/
theorem toLinearMap_rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ ->SL[σ₁₂] M₂) :
    f.rangeRestrict.toLinearMap = f.toLinearMap.rangeRestrict := by simp

@[simp]
/--
theorem `coe_rangeRestrict` / 定理 `coe_rangeRestrict`

English:
theorem coe_rangeRestrict
  given: [RingHomSurjective σ₁₂] (f : M₁ ->SL[σ₁₂] M₂)
  proof: rfl

中文:
定理 coe_rangeRestrict
  条件: [RingHomSurjective σ₁₂] (f : M₁ ->SL[σ₁₂] M₂)
  证明: rfl
-/
theorem coe_rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ ->SL[σ₁₂] M₂) :
    (f.rangeRestrict : M₁ -> f.range) = Set.rangeFactorization f := rfl

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (f : M₁ ->SL[σ₁₂] M₂) {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
  body: (f.domRestrict p).codRestrict q SetLike.forall.2 h

@[simp, norm_cast]

中文:
定义 restrict
  签名: (f : M₁ ->SL[σ₁₂] M₂) {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
  定义体: (f.domRestrict p).codRestrict q SetLike.forall.2 h

@[simp, norm_cast]

Depends on / 依赖: SetLike, SetLike.forall, codRestrict, domRestrict, f.domRestrict
-/
def restrict (f : M₁ ->SL[σ₁₂] M₂) {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (h : forall x in p, f x in q) : p ->SL[σ₁₂] q :=
(f.domRestrict p).codRestrict q SetLike.forall.2 h

@[simp, norm_cast]
/--
theorem `toLinearMap_restrict` / 定理 `toLinearMap_restrict`

English:
theorem toLinearMap_restrict
  statement: {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
  proof: rfl

@[simp]

中文:
定理 toLinearMap_restrict
  结论: {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
  证明: rfl

@[simp]
-/
theorem toLinearMap_restrict {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (h : forall x in p, f x in q) :
    (f.restrict h).toLinearMap = f.toLinearMap.restrict h :=
  rfl

@[simp]
/--
theorem `coe_restrict_apply` / 定理 `coe_restrict_apply`

English:
theorem coe_restrict_apply
  statement: {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
  proof: rfl

中文:
定理 coe_restrict_apply
  结论: {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
  证明: rfl
-/
theorem coe_restrict_apply {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (hf : forall x in p, f x in q) (x : p) : ↑(f.restrict hf x) = f x :=
  rfl

/--
theorem `restrict_apply` / 定理 `restrict_apply`

English:
theorem restrict_apply
  statement: {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
  proof: rfl

中文:
定理 restrict_apply
  结论: {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
  证明: rfl
-/
theorem restrict_apply {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (hf : forall x in p, f x in q) (x : p) : f.restrict hf x = ⟨f x, hf x.1 x.2⟩ :=
  rfl

open Set in
/--
lemma `restrict_comp` / 引理 `restrict_comp`

English:
lemma restrict_comp
  statement: {p : Submodule R₁ M₁} {p₂ : Submodule R₂ M₂} {p₃ : Submodule R₃ M₃}
  proof: rfl

中文:
引理 restrict_comp
  结论: {p : Submodule R₁ M₁} {p₂ : Submodule R₂ M₂} {p₃ : Submodule R₃ M₃}
  证明: rfl

Depends on / 依赖: hg.comp
-/
lemma restrict_comp {p : Submodule R₁ M₁} {p₂ : Submodule R₂ M₂} {p₃ : Submodule R₃ M₃}
    {f : M₁ ->SL[σ₁₂] M₂} {g : M₂ ->SL[σ₂₃] M₃}
    (hf : MapsTo f p p₂) (hg : MapsTo g p₂ p₃) (hfg : MapsTo (g ∘SL f) p p₃ := hg.comp hf) :
    (g ∘SL f).restrict hfg = (g.restrict hg) ∘SL (f.restrict hf) :=
  rfl

/--
theorem `subtypeL_comp_restrict` / 定理 `subtypeL_comp_restrict`

English:
theorem subtypeL_comp_restrict
  statement: {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
  proof: rfl

中文:
定理 subtypeL_comp_restrict
  结论: {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
  证明: rfl
-/
theorem subtypeL_comp_restrict {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (hf : forall x in p, f x in q) : q.subtypeL ∘SL (f.restrict hf) = f.domRestrict p :=
  rfl

/--
theorem `restrict_eq_codRestrict_domRestrict` / 定理 `restrict_eq_codRestrict_domRestrict`

English:
theorem restrict_eq_codRestrict_domRestrict
  statement: {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁}
  proof: rfl

中文:
定理 restrict_eq_codRestrict_domRestrict
  结论: {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁}
  证明: rfl
-/
theorem restrict_eq_codRestrict_domRestrict {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁}
    {q : Submodule R₂ M₂} (hf : forall x in p, f x in q) :
    f.restrict hf = (f.domRestrict p).codRestrict q fun x => hf x.1 x.2 :=
  rfl

/--
theorem `restrict_eq_domRestrict_codRestrict` / 定理 `restrict_eq_domRestrict_codRestrict`

English:
theorem restrict_eq_domRestrict_codRestrict
  statement: {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁}
  proof: rfl

中文:
定理 restrict_eq_domRestrict_codRestrict
  结论: {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁}
  证明: rfl
-/
theorem restrict_eq_domRestrict_codRestrict {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁}
    {q : Submodule R₂ M₂} (hf : forall x, f x in q) :
    (f.restrict fun x _ => hf x) = (f.codRestrict q hf).domRestrict p :=
  rfl

end Restrict

section

variable {R₁ R₂ R₃ : Type*} [Ring R₁] [Ring R₂]
  {σ₁₂ : R₁ ->+* R₂} {σ₂₁ : R₂ ->+* R₁} [RingHomInvPair σ₁₂ σ₂₁]
  {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [AddCommGroup M₁] [Module R₁ M₁]
  [TopologicalSpace M₂] [AddCommGroup M₂] [Module R₂ M₂]

/--
Definition of `projKerOfRightInverse` / `projKerOfRightInverse` 的定义

English:
definition projKerOfRightInverse
  signature: [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ : M₂ ->SL[σ₂₁] M₁)
  body: (.id R₁ M₁ - f₂ ∘SL f₁).codRestrict (LinearMap.ker f₁.toLinearMap) fun x => by simp [h (f₁ x)]

@[simp]

中文:
定义 projKerOfRightInverse
  签名: [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ : M₂ ->SL[σ₂₁] M₁)
  定义体: (.id R₁ M₁ - f₂ ∘SL f₁).codRestrict (LinearMap.ker f₁.toLinearMap) fun x => by simp [h (f₁ x)]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ker, codRestrict, toLinearMap
-/
def projKerOfRightInverse [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ₁₂] M₂) (f₂ : M₂ ->SL[σ₂₁] M₁)
    (h : Function.RightInverse f₂ f₁) : M₁ ->L[R₁] LinearMap.ker (f₁ : M₁ ->ₛₗ[σ₁₂] M₂) :=
  (.id R₁ M₁ - f₂ ∘SL f₁).codRestrict (LinearMap.ker f₁.toLinearMap) fun x => by simp [h (f₁ x)]

@[simp]
/--
theorem `coe_projKerOfRightInverse_apply` / 定理 `coe_projKerOfRightInverse_apply`

English:
theorem coe_projKerOfRightInverse_apply
  statement: [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ₁₂] M₂)
  proof: rfl

@[simp]

中文:
定理 coe_projKerOfRightInverse_apply
  结论: [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ₁₂] M₂)
  证明: rfl

@[simp]
-/
theorem coe_projKerOfRightInverse_apply [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ₁₂] M₂)
    (f₂ : M₂ ->SL[σ₂₁] M₁) (h : Function.RightInverse f₂ f₁) (x : M₁) :
    (f₁.projKerOfRightInverse f₂ h x : M₁) = x - f₂ (f₁ x) :=
  rfl

@[simp]
/--
theorem `projKerOfRightInverse_apply_idem` / 定理 `projKerOfRightInverse_apply_idem`

English:
theorem projKerOfRightInverse_apply_idem
  statement: [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ₁₂] M₂)
  proof: by
  ext1
  simp

@[simp]

中文:
定理 projKerOfRightInverse_apply_idem
  结论: [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ₁₂] M₂)
  证明: by
  ext1
  simp

@[simp]
-/
theorem projKerOfRightInverse_apply_idem [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ₁₂] M₂)
    (f₂ : M₂ ->SL[σ₂₁] M₁) (h : Function.RightInverse f₂ f₁) (x : f₁.ker) :
    f₁.projKerOfRightInverse f₂ h x = x := by
  ext1
  simp

@[simp]
/--
theorem `projKerOfRightInverse_comp_inv` / 定理 `projKerOfRightInverse_comp_inv`

English:
theorem projKerOfRightInverse_comp_inv
  statement: [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ₁₂] M₂)
  proof: Subtype.ext_iff.2 by simp [h y]

中文:
定理 projKerOfRightInverse_comp_inv
  结论: [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ₁₂] M₂)
  证明: Subtype.ext_iff.2 by simp [h y]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem projKerOfRightInverse_comp_inv [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ₁₂] M₂)
    (f₂ : M₂ ->SL[σ₂₁] M₁) (h : Function.RightInverse f₂ f₁) (y : M₂) :
    f₁.projKerOfRightInverse f₂ h (f₂ y) = 0 :=
Subtype.ext_iff.2 by simp [h y]

end

end ContinuousLinearMap
