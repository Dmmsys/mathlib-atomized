/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig, Pepa Montero
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Cⁿ monoid actions

In this file we define Cⁿ actions (e.g. by Lie groups or monoids) on manifolds: we say
`ContMDiffSMul I I' n G M` if `G` acts multiplicatively on `M` and the action map
`fun p : G × M ↦ p.1 • p.2` is Cⁿ. We also provide API for additive actions using `@[to_additive]`.

We also provide `ContMDiffSMul` instances for scalar multiplication in normed spaces and for
the action of the monoid `E →L[𝕜] E` of continuous linear maps on any normed space `E`.

For a group `G` acting smoothly on `M`, we define `Diffeomorph.smul`, scalar multiplication by a
fixed `g : G` as a diffeomorphism of `M` (in analogy to `Homeomorph.smul`).

See also:
* `ContMDiffMul I n G` for continuous differentiability of multiplication `G × G → G` in a single
  type `G`,
* `ContinuousSMul G M` for continuity of an action `G × M → M`.

Unlike for continuous actions, we do not currently have a class `ContMDiffConstSMul`. If there are
interesting examples satisfying `ContMDiffConstSMul` but not `ContMDiffSMul`, this can be added
later. (Note that such examples may be harder to find: in fact, a continuous action of a
Lie group `G` on a finite-dimensional manifold `M` is `C^n` provided it is `C^n` in the
second variable.)
-/

open scoped Manifold ContDiff

public section

/--
Definition of `ContMDiffVAdd` / `ContMDiffVAdd` 的定义

English:
class ContMDiffVAdd
  parameters: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
  axioms and operations (1):
    - contMDiff_vadd : CMDiff n fun p : G × M => p.1 +ᵥ p.2

中文:
类 ContMDiffVAdd
  参数: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {H : 类型} [TopologicalSpace H]
  公理与运算 (1 个):
    - contMDiff_vadd : CMDiff n fun p : G × M => p.1 +ᵥ p.2
-/
class ContMDiffVAdd {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (I' : ModelWithCorners 𝕜 E' H') (n : Nat∞ω)
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H' M] [VAdd G M] : Prop where
  contMDiff_vadd : CMDiff n fun p : G × M => p.1 +ᵥ p.2

/-- Basic typeclass stating that the action of `G` on `M` is Cⁿ as a function `G × M → M`.
Unlike with `ContMDiffMul` (the class stating that multiplication `G × G → G` within a single type
`G` is Cⁿ), we do not extend `IsManifold` because `ContMDiffSMul` contains more
explicit arguments than `IsManifold` and so `ContMDiffSMul.toIsManifold` could not be an instance
anyway: this means that in order for `ContMDiffSMul` to be meaningful, smoothness of `G` and `M`
have to be required separately. For example, to state that `G` is a Cⁿ Lie group with a Cⁿ action on
a Cⁿ manifold `M`, one can use the typeclasses
`[LieGroup I n G] [IsManifold I' n M] [ContMDiffSMul I I' n G M]`. -/
@[to_additive]
/--
Definition of `ContMDiffSMul` / `ContMDiffSMul` 的定义

English:
class ContMDiffSMul
  parameters: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
  axioms and operations (1):
    - contMDiff_smul : CMDiff n fun p : G × M => p.1 • p.2

中文:
类 ContMDiffSMul
  参数: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {H : 类型} [TopologicalSpace H]
  公理与运算 (1 个):
    - contMDiff_smul : CMDiff n fun p : G × M => p.1 • p.2
-/
class ContMDiffSMul {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (I' : ModelWithCorners 𝕜 E' H') (n : Nat∞ω)
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H' M] [SMul G M] : Prop where
  contMDiff_smul : CMDiff n fun p : G × M => p.1 • p.2

export ContMDiffVAdd (contMDiff_vadd)

export ContMDiffSMul (contMDiff_smul)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'} {H'' : Type*} [TopologicalSpace H''] {E'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]

@[to_additive]
/--
theorem `ContMDiffSMul.of_le` / 定理 `ContMDiffSMul.of_le`

English:
theorem ContMDiffSMul.of_le
  statement: [SMul G M] {n m : Nat∞ω} (h : n <= m)
  proof: ⟨contMDiff_smul.of_le h⟩

@[to_additive]

中文:
定理 ContMDiffSMul.of_le
  结论: [SMul G M] {n m : 自然数∞ω} (h : n <= m)
  证明: ⟨contMDiff_smul.of_le h⟩

@[to_additive]
-/
protected theorem ContMDiffSMul.of_le [SMul G M] {n m : Nat∞ω} (h : n <= m)
    [ContMDiffSMul I I' m G M] : ContMDiffSMul I I' n G M := ⟨contMDiff_smul.of_le h⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: G M] {n
  body: .of_le ENat.LEInfty.out

@[to_additive]

中文:
实例 [SMul
  签名: G M] {n
  定义体: .of_le ENat.LEInfty.out

@[to_additive]

Depends on / 依赖: ENat.LEInfty.out, LEInfty, of_le
-/
instance [SMul G M] {n : Nat∞ω} [ContMDiffSMul I I' ∞ G M] [ENat.LEInfty n] :
    ContMDiffSMul I I' n G M :=
  .of_le ENat.LEInfty.out

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: G M] {n
  body: .of_le le_top

@[to_additive]

中文:
实例 [SMul
  签名: G M] {n
  定义体: .of_le le_top

@[to_additive]

Depends on / 依赖: le_top, of_le
-/
instance [SMul G M] {n : Nat∞ω} [ContMDiffSMul I I' ω G M] : ContMDiffSMul I I' n G M :=
  .of_le le_top

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: G M] [ContinuousSMul G M] : ContMDiffSMul I I' 0 G M
  body: ⟨contMDiff_zero_iff.2 continuous_smul⟩

@[to_additive]

中文:
实例 [SMul
  签名: G M] [ContinuousSMul G M] : ContMDiffSMul I I' 0 G M
  定义体: ⟨contMDiff_zero_iff.2 continuous_smul⟩

@[to_additive]

Depends on / 依赖: contMDiff_zero_iff, continuous_smul
-/
instance [SMul G M] [ContinuousSMul G M] : ContMDiffSMul I I' 0 G M :=
  ⟨contMDiff_zero_iff.2 continuous_smul⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: G M] [ContMDiffSMul I I' 2 G M] : ContMDiffSMul I I' 1 G M
  body: .of_le one_le_two

中文:
实例 [SMul
  签名: G M] [ContMDiffSMul I I' 2 G M] : ContMDiffSMul I I' 1 G M
  定义体: .of_le one_le_two

Depends on / 依赖: of_le, one_le_two
-/
instance [SMul G M] [ContMDiffSMul I I' 2 G M] : ContMDiffSMul I I' 1 G M :=
  .of_le one_le_two

/-- If an action is Cⁿ for some `n`, it is also continuous. This has to be a theorem instead of an
instance because `ContMDiffSMul` depends on parameters `I`, `I'` and `n` that `ContinuousSMul`
doesn't. -/
@[to_additive]
/--
lemma `ContMDiffSMul.continuousSMul` / 引理 `ContMDiffSMul.continuousSMul`

English:
lemma ContMDiffSMul.continuousSMul
  given: [SMul G M] (n : Nat∞ω) [ContMDiffSMul I I' n G M]
  proof: ⟨(contMDiff_smul (I := I) (I' := I') (n := n)).continuous⟩

中文:
引理 ContMDiffSMul.continuousSMul
  条件: [SMul G M] (n : 自然数∞ω) [ContMDiffSMul I I' n G M]
  证明: ⟨(contMDiff_smul (I := I) (I' := I') (n := n)).continuous⟩

Depends on / 依赖: contMDiff_smul, continuous
-/
lemma ContMDiffSMul.continuousSMul [SMul G M] (n : Nat∞ω) [ContMDiffSMul I I' n G M] :
    ContinuousSMul G M :=
  ⟨(contMDiff_smul (I := I) (I' := I') (n := n)).continuous⟩

/--
Instance `ContMDiffMul.contMDiffSMul` / 实例 `ContMDiffMul.contMDiffSMul`

English:
instance ContMDiffMul.contMDiffSMul
  signature: [Mul G] {n : Nat∞ω} [ContMDiffMul I n G]
  body: contMDiff_mul

中文:
实例 ContMDiffMul.contMDiffSMul
  签名: [Mul G] {n : 自然数∞ω} [ContMDiffMul I n G]
  定义体: contMDiff_mul

Depends on / 依赖: contMDiff_mul
-/
instance ContMDiffMul.contMDiffSMul [Mul G] {n : Nat∞ω} [ContMDiffMul I n G] :
    ContMDiffSMul I I n G G where
  contMDiff_smul := contMDiff_mul

section

variable [SMul G M] {n : Nat∞ω} [ContMDiffSMul I I' n G M]
  {f : N -> G} {g : N -> M} {s : Set N} {x : N}

@[to_additive]
/--
theorem `ContMDiffWithinAt.smul` / 定理 `ContMDiffWithinAt.smul`

English:
theorem ContMDiffWithinAt.smul
  given: (hf : CMDiffAt[s] n f x) (hg : CMDiffAt[s] n g x)
  proof: (contMDiff_smul (I := I) (I' := I')).contMDiffAt.comp_contMDiffWithinAt x (hf.prodMk hg)

@[to_additive]
nonrec theorem ContMDiffAt.smul (hf : CMDiffAt n f x) (hg : CMDiffAt n g x) :
    CMDiffAt n (f • g) x :=
  hf.smul hg

@[to_additive]

中文:
定理 ContMDiffWithinAt.smul
  条件: (hf : CMDiffAt[s] n f x) (hg : CMDiffAt[s] n g x)
  证明: (contMDiff_smul (I := I) (I' := I')).contMDiffAt.comp_contMDiffWithinAt x (hf.prodMk hg)

@[to_additive]
nonrec theorem ContMDiffAt.smul (hf : CMDiffAt n f x) (hg : CMDiffAt n g x) :
    CMDiffAt n (f • g) x :=
  hf.smul hg

@[to_additive]

Depends on / 依赖: comp_contMDiffWithinAt, contMDiffAt, contMDiffAt.comp_contMDiffWithinAt, contMDiff_smul, hf.prodMk, prodMk
-/
theorem ContMDiffWithinAt.smul (hf : CMDiffAt[s] n f x) (hg : CMDiffAt[s] n g x) :
    CMDiffAt[s] n (f • g) x :=
  (contMDiff_smul (I := I) (I' := I')).contMDiffAt.comp_contMDiffWithinAt x (hf.prodMk hg)

@[to_additive]
nonrec theorem ContMDiffAt.smul (hf : CMDiffAt n f x) (hg : CMDiffAt n g x) :
    CMDiffAt n (f • g) x :=
  hf.smul hg

@[to_additive]
/--
theorem `ContMDiffOn.smul` / 定理 `ContMDiffOn.smul`

English:
theorem ContMDiffOn.smul
  given: (hf : CMDiff[s] n f) (hg : CMDiff[s] n g)
  proof: fun x hx => (hf x hx).smul (hg x hx)

@[to_additive]

中文:
定理 ContMDiffOn.smul
  条件: (hf : CMDiff[s] n f) (hg : CMDiff[s] n g)
  证明: fun x hx => (hf x hx).smul (hg x hx)

@[to_additive]
-/
theorem ContMDiffOn.smul (hf : CMDiff[s] n f) (hg : CMDiff[s] n g) :
    CMDiff[s] n (f • g) := fun x hx => (hf x hx).smul (hg x hx)

@[to_additive]
/--
theorem `ContMDiff.smul` / 定理 `ContMDiff.smul`

English:
theorem ContMDiff.smul
  given: (hf : CMDiff n f) (hg : CMDiff n g)
  proof: fun x => (hf x).smul (hg x)

中文:
定理 ContMDiff.smul
  条件: (hf : CMDiff n f) (hg : CMDiff n g)
  证明: fun x => (hf x).smul (hg x)
-/
theorem ContMDiff.smul (hf : CMDiff n f) (hg : CMDiff n g) :
    CMDiff n (f • g) := fun x => (hf x).smul (hg x)

-- TODO: after #41534 is merged, weaken the hypothesis to `ContMDiffConstSMul`
@[to_additive]
/--
theorem `ContMDiffSMul.contMDiff_const_smul` / 定理 `ContMDiffSMul.contMDiff_const_smul`

English:
theorem ContMDiffSMul.contMDiff_const_smul
  given: {n : Nat∞ω} [ContMDiffSMul I I' n G M] (g : G)
  proof: contMDiff_const.smul (I := I) contMDiff_id

中文:
定理 ContMDiffSMul.contMDiff_const_smul
  条件: {n : 自然数∞ω} [ContMDiffSMul I I' n G M] (g : G)
  证明: contMDiff_const.smul (I := I) contMDiff_id

Depends on / 依赖: contMDiff_const, contMDiff_const.smul, contMDiff_id
-/
theorem ContMDiffSMul.contMDiff_const_smul {n : Nat∞ω} [ContMDiffSMul I I' n G M] (g : G) :
    CMDiff n fun x : M => g • x :=
  contMDiff_const.smul (I := I) contMDiff_id

end

@[to_additive prod]
/--
Instance `Prod.contMDiffSMul` / 实例 `Prod.contMDiffSMul`

English:
instance Prod.contMDiffSMul
  signature: [SMul G M] [SMul G N] {n : Nat∞ω} [ContMDiffSMul I I' n G M]
  body: (contMDiff_fst.smul <| contMDiff_fst.comp contMDiff_snd).prodMk
contMDiff_fst.smul contMDiff_snd.comp contMDiff_snd

中文:
实例 Prod.contMDiffSMul
  签名: [SMul G M] [SMul G N] {n : 自然数∞ω} [ContMDiffSMul I I' n G M]
  定义体: (contMDiff_fst.smul <| contMDiff_fst.comp contMDiff_snd).prodMk
contMDiff_fst.smul contMDiff_snd.comp contMDiff_snd

Depends on / 依赖: contMDiff_fst, contMDiff_fst.comp, contMDiff_fst.smul, contMDiff_snd, prodMk
-/
instance Prod.contMDiffSMul [SMul G M] [SMul G N] {n : Nat∞ω} [ContMDiffSMul I I' n G M]
    [ContMDiffSMul I I'' n G N] : ContMDiffSMul I (I'.prod I'') n G (M × N) where
contMDiff_smul := (contMDiff_fst.smul <| contMDiff_fst.comp contMDiff_snd).prodMk
contMDiff_fst.smul contMDiff_snd.comp contMDiff_snd

/--
lemma `IsScalarTower.contMDiffSMul` / 引理 `IsScalarTower.contMDiffSMul`

English:
lemma IsScalarTower.contMDiffSMul
  statement: (G' : Type*) [TopologicalSpace G'] [ChartedSpace H'' G']
  proof: by
    suffices CMDiff n (fun p : G × M => (p.1 • (1 : G')) • p.2) by simpa
    exact (contMDiff_fst.smul contMDiff_const).smul (I := I'') contMDiff_snd

中文:
引理 IsScalarTower.contMDiffSMul
  结论: (G' : 类型) [TopologicalSpace G'] [ChartedSpace H'' G']
  证明: by
    suffices CMDiff n (fun p : G × M => (p.1 • (1 : G')) • p.2) by simpa
    exact (contMDiff_fst.smul contMDiff_const).smul (I := I'') contMDiff_snd

Depends on / 依赖: CMDiff, contMDiff_const, contMDiff_fst, contMDiff_fst.smul, contMDiff_snd
-/
lemma IsScalarTower.contMDiffSMul (G' : Type*) [TopologicalSpace G'] [ChartedSpace H'' G']
    [Monoid G'] [SMul G G'] [MulAction G' M] [SMul G M] [IsScalarTower G G' M] {n : Nat∞ω}
    [ContMDiffSMul I I'' n G G'] [ContMDiffSMul I'' I' n G' M] : ContMDiffSMul I I' n G M where
  contMDiff_smul := by
    suffices CMDiff n (fun p : G × M => (p.1 • (1 : G')) • p.2) by simpa
    exact (contMDiff_fst.smul contMDiff_const).smul (I := I'') contMDiff_snd

/-- If an action is continuously differentiable, then post-composing this action with a continuously
differentiable homomorphism gives again a continuously differentiable action. -/
@[to_additive]
/--
theorem `MulAction.contMDiffSMul_compHom` / 定理 `MulAction.contMDiffSMul_compHom`

English:
theorem MulAction.contMDiffSMul_compHom
  statement: [Monoid G] [MulAction G M] {n : Nat∞ω}
  proof: MulAction.compHom _ f
    ContMDiffSMul I'' I' n G' M := by
  let _ : MulAction G' M := MulAction.compHom _ f
  exact ⟨(hf.comp contMDiff_fst).smul contMDiff_snd⟩

中文:
定理 MulAction.contMDiffSMul_compHom
  结论: [Monoid G] [MulAction G M] {n : 自然数∞ω}
  证明: MulAction.compHom _ f
    ContMDiffSMul I'' I' n G' M := by
  let _ : MulAction G' M := MulAction.compHom _ f
  exact ⟨(hf.comp contMDiff_fst).smul contMDiff_snd⟩

Depends on / 依赖: MulAction, MulAction.compHom, compHom
-/
theorem MulAction.contMDiffSMul_compHom [Monoid G] [MulAction G M] {n : Nat∞ω}
    [ContMDiffSMul I I' n G M] {G' : Type*} [TopologicalSpace G'] [ChartedSpace H'' G'] [Monoid G']
    {f : G' ->* G} (hf : CMDiff n f) :
    letI : MulAction G' M := MulAction.compHom _ f
    ContMDiffSMul I'' I' n G' M := by
  let _ : MulAction G' M := MulAction.compHom _ f
  exact ⟨(hf.comp contMDiff_fst).smul contMDiff_snd⟩

/-- The scalar multiplication `𝕜 × E → E` of any normed vector space `E` over `𝕜` is smooth. -/
instance {n : Nat∞ω} : ContMDiffSMul 𝓘(𝕜) 𝓘(𝕜, E) n 𝕜 E where
  contMDiff_smul := by
    have h : ContMDiff (𝓘(𝕜).prod 𝓘(𝕜, E)) 𝓘(𝕜, 𝕜 × E) n (@id (𝕜 × E)) := by
      rw [contMDiff_prod_module_iff]; rw [← contMDiff_prod_iff]; exact contMDiff_id
    exact contDiff_smul.contMDiff.comp h

/-- The monoid `E →L[𝕜] E` of continuous linear endomorphisms of `E` acts smoothly on `E`. -/
instance {n : Nat∞ω} : ContMDiffSMul 𝓘(𝕜, E ->L[𝕜] E) 𝓘(𝕜, E) n (E ->L[𝕜] E) E where
  contMDiff_smul := by
    have h : ContMDiff (𝓘(𝕜, E ->L[𝕜] E).prod 𝓘(𝕜, E)) 𝓘(𝕜, (E ->L[𝕜] E) × E) n
        (@id ((E ->L[𝕜] E) × E)) := by
      rw [contMDiff_prod_module_iff]; rw [← contMDiff_prod_iff]; exact contMDiff_id
    exact isBoundedBilinearMap_apply.contDiff.contMDiff.comp h

section Diffeomorph

variable [Group G] [MulAction G M] {n : Nat∞ω} [ContMDiffSMul I I' n G M] (g : G)

variable (I I' n) in
/-- The diffeomorphism given by scalar multiplication by an element of a group `G` acting
Cⁿ-differentiably on a manifold `M` is a diffeomorphism from `M` to itself. Its inverse is scalar
multiplication by `g⁻¹`. -/
@[expose, to_additive
/-- The diffeomorphism given by affine-addition of an element of an additive group `G` acting
Cⁿ-differentiably on a manifold `M` is a diffeomorphism from `M` to itself. Its inverse is
addition of `-g`. -/]
/--
Definition of `Diffeomorph.smul` / `Diffeomorph.smul` 的定义

English:
definition Diffeomorph.smul
  signature: : M ≃ₘ^n⟮I', I'⟯ M where
  body: MulAction.toPerm g
  contMDiff_toFun := ContMDiffSMul.contMDiff_const_smul (I := I) g
  contMDiff_invFun := ContMDiffSMul.contMDiff_const_smul (I := I) g⁻¹

@[to_additive (attr := simp)]

中文:
定义 Diffeomorph.smul
  签名: : M ≃ₘ^n⟮I', I'⟯ M where
  定义体: MulAction.toPerm g
  contMDiff_toFun := ContMDiffSMul.contMDiff_const_smul (I := I) g
  contMDiff_invFun := ContMDiffSMul.contMDiff_const_smul (I := I) g⁻¹

@[to_additive (attr := simp)]

Depends on / 依赖: MulAction, MulAction.toPerm, toPerm
-/
def Diffeomorph.smul : M ≃ₘ^n⟮I', I'⟯ M where
  toEquiv := MulAction.toPerm g
  contMDiff_toFun := ContMDiffSMul.contMDiff_const_smul (I := I) g
  contMDiff_invFun := ContMDiffSMul.contMDiff_const_smul (I := I) g⁻¹

@[to_additive (attr := simp)]
/--
lemma `Diffeomorph.smul_toHomeomorph` / 引理 `Diffeomorph.smul_toHomeomorph`

English:
lemma Diffeomorph.smul_toHomeomorph
  proof: ContMDiffSMul.continuousSMul (I := I) (I' := I') n
    (Diffeomorph.smul I I' n g).toHomeomorph = Homeomorph.smul (α := M) g :=
  rfl

@[to_additive (attr := simp)]

中文:
引理 Diffeomorph.smul_toHomeomorph
  证明: ContMDiffSMul.continuousSMul (I := I) (I' := I') n
    (Diffeomorph.smul I I' n g).toHomeomorph = Homeomorph.smul (α := M) g :=
  rfl

@[to_additive (attr := simp)]

Depends on / 依赖: ContMDiffSMul, ContMDiffSMul.continuousSMul, continuousSMul
-/
lemma Diffeomorph.smul_toHomeomorph :
    haveI : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := I) (I' := I') n
    (Diffeomorph.smul I I' n g).toHomeomorph = Homeomorph.smul (α := M) g :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `Diffeomorph.smul_apply` / 引理 `Diffeomorph.smul_apply`

English:
lemma Diffeomorph.smul_apply
  given: (x : M)
  statement: Diffeomorph.smul I I' n g x = g • x
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 Diffeomorph.smul_apply
  条件: (x : M)
  结论: Diffeomorph.smul I I' n g x = g • x
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma Diffeomorph.smul_apply (x : M) : Diffeomorph.smul I I' n g x = g • x := rfl

@[to_additive (attr := simp)]
/--
lemma `Diffeomorph.smul_symm_apply` / 引理 `Diffeomorph.smul_symm_apply`

English:
lemma Diffeomorph.smul_symm_apply
  given: (x : M)
  statement: (Diffeomorph.smul I I' n g).symm x = g⁻¹ • x
  proof: rfl

@[to_additive]

中文:
引理 Diffeomorph.smul_symm_apply
  条件: (x : M)
  结论: (Diffeomorph.smul I I' n g).symm x = g⁻¹ • x
  证明: rfl

@[to_additive]
-/
lemma Diffeomorph.smul_symm_apply (x : M) : (Diffeomorph.smul I I' n g).symm x = g⁻¹ • x := rfl

@[to_additive]
/--
lemma `Diffeomorph.smul_symm` / 引理 `Diffeomorph.smul_symm`

English:
lemma Diffeomorph.smul_symm
  proof: Diffeomorph.ext fun _ => rfl

中文:
引理 Diffeomorph.smul_symm
  证明: Diffeomorph.ext fun _ => rfl

Depends on / 依赖: Diffeomorph, Diffeomorph.ext
-/
lemma Diffeomorph.smul_symm :
    (Diffeomorph.smul I I' n g : M ≃ₘ^n⟮I', I'⟯ M).symm = Diffeomorph.smul I I' n g⁻¹ :=
  Diffeomorph.ext fun _ => rfl

end Diffeomorph
