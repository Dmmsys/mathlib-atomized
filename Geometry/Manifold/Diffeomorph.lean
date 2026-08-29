/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Yury Kudryashov
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential

/-!
# Diffeomorphisms

This file implements diffeomorphisms.

## Definitions

* `Diffeomorph I I' M M' n`: `n`-times continuously differentiable diffeomorphism between
  `M` and `M'` with respect to I and I'; we do not introduce a separate definition for the case
  `n = ∞` or `n = ω`; we use notation instead.
* `Diffeomorph.toHomeomorph`: reinterpret a diffeomorphism as a homeomorphism.
* `ContinuousLinearEquiv.toDiffeomorph`: reinterpret a continuous equivalence as
  a diffeomorphism.
* `ModelWithCorners.transContinuousLinearEquiv`: compose a given `ModelWithCorners` with a
  continuous linear equiv between the old and the new target spaces. Useful, e.g, to turn any
  finite-dimensional manifold into a manifold modelled on a Euclidean space.
* `Diffeomorph.toTransContinuousLinearEquiv`: the identity diffeomorphism between `M` with
  model `I` and `M` with model `I.transContinuousLinearEquiv e`.

This file also provides diffeomorphisms related to products and disjoint unions.
* `Diffeomorph.prodCongr`: the product of two diffeomorphisms
* `Diffeomorph.prodComm`: `M × N` is diffeomorphic to `N × M`
* `Diffeomorph.prodAssoc`: `(M × N) × N'` is diffeomorphic to `M × (N × N')`
* `Diffeomorph.sumCongr`: the disjoint union of two diffeomorphisms
* `Diffeomorph.sumComm`: `M ⊕ M'` is diffeomorphic to `M' × M`
* `Diffeomorph.sumAssoc`: `(M ⊕ N) ⊕ P` is diffeomorphic to `M ⊕ (N ⊕ P)`
* `Diffeomorph.sumEmpty`: `M ⊕ ∅` is diffeomorphic to `M`

## Notation

* `M ≃ₘ^n⟮I, I'⟯ M'` := `Diffeomorph I J M N n`
* `M ≃ₘ⟮I, I'⟯ M'` := `Diffeomorph I J M N ∞`
* `E ≃ₘ^n[𝕜] E'` := `E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E'`
* `E ≃ₘ[𝕜] E'` := `E ≃ₘ⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E'`

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

## Keywords

diffeomorphism, manifold
-/

@[expose] public section


open scoped Manifold Topology ContDiff

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type*} [TopologicalSpace H] {H' : Type*}
  [TopologicalSpace H'] {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {J : ModelWithCorners 𝕜 F G}
  {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {M' : Type*} [TopologicalSpace M']
  [ChartedSpace H' M'] {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {N' : Type*}
  [TopologicalSpace N'] [ChartedSpace G' N'] {n : Nat∞ω}

section Defs

variable (I I' M M' n)

/--
Definition of `Diffeomorph` / `Diffeomorph` 的定义

English:
structure Diffeomorph
  parameters: extends M ≃ M'
  extends: M ≃ M'
  axioms and operations (2):
    - contMDiff_toFun : CMDiff n toEquiv
    - contMDiff_invFun : CMDiff n toEquiv.symm

中文:
结构 微分同胚
  参数: extends M ≃ M'
  继承: M ≃ M'
  公理与运算 (2 个):
    - contMDiff_toFun : CMDiff n toEquiv
    - contMDiff_invFun : CMDiff n toEquiv.symm
-/
structure Diffeomorph extends M ≃ M' where
  protected contMDiff_toFun : CMDiff n toEquiv
  protected contMDiff_invFun : CMDiff n toEquiv.symm


end Defs

@[inherit_doc]
scoped[Manifold] notation M " ≃ₘ^" n:1000 "⟮" I ", " J "⟯ " N => Diffeomorph I J M N n

/-- Infinitely differentiable diffeomorphism between `M` and `M'` with respect to `I` and `I'`. -/
scoped[Manifold] notation M " ≃ₘ⟮" I ", " J "⟯ " N => Diffeomorph I J M N ∞

-- Porting note: this notation is broken because `n[𝕜]` gets parsed as `getElem`
/-- `n`-times continuously differentiable diffeomorphism between `E` and `E'`. -/
scoped[Manifold] notation E " ≃ₘ^" n:1000 "[" 𝕜 "] " E' => Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') E E' n

/-- Infinitely differentiable diffeomorphism between `E` and `E'`. -/
scoped[Manifold] notation3 E " ≃ₘ[" 𝕜 "] " E' => Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') E E' ∞

namespace Diffeomorph

/--
theorem `toEquiv_injective` / 定理 `toEquiv_injective`

English:
theorem toEquiv_injective
  statement: Injective (Diffeomorph.toEquiv : (M ≃ₘ^n⟮I, I'⟯ M') -> M ≃ M')

中文:
定理 toEquiv_injective
  结论: 单射 (微分同胚.toEquiv : (M ≃ₘ^n⟮I, I'⟯ M') -> M ≃ M')
-/
theorem toEquiv_injective : Injective (Diffeomorph.toEquiv : (M ≃ₘ^n⟮I, I'⟯ M') -> M ≃ M')
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (M ≃ₘ^n⟮I, I'⟯ M') M M'
  body: Φ.toEquiv
  inv Φ := Φ.toEquiv.symm
  left_inv Φ := Φ.left_inv
  right_inv Φ := Φ.right_inv
coe_injective' _ _ h _ := toEquiv_injective DFunLike.ext' h

中文:
实例 :
  签名: 等价状 (M ≃ₘ^n⟮I, I'⟯ M') M M'
  定义体: Φ.toEquiv
  inv Φ := Φ.toEquiv.symm
  left_inv Φ := Φ.left_inv
  right_inv Φ := Φ.right_inv
coe_injective' _ _ h _ := toEquiv_injective DFunLike.ext' h

Depends on / 依赖: toEquiv
-/
instance : EquivLike (M ≃ₘ^n⟮I, I'⟯ M') M M' where
  coe Φ := Φ.toEquiv
  inv Φ := Φ.toEquiv.symm
  left_inv Φ := Φ.left_inv
  right_inv Φ := Φ.right_inv
coe_injective' _ _ h _ := toEquiv_injective DFunLike.ext' h

/-- Interpret a diffeomorphism as a `ContMDiffMap`. -/
@[coe]
/--
Definition of `toContMDiffMap` / `toContMDiffMap` 的定义

English:
definition toContMDiffMap
  signature: (Φ : M ≃ₘ^n⟮I, I'⟯ M')
  body: ⟨Φ, Φ.contMDiff_toFun⟩

中文:
定义 toContMDiffMap
  签名: (Φ : M ≃ₘ^n⟮I, I'⟯ M')
  定义体: ⟨Φ, Φ.contMDiff_toFun⟩

Depends on / 依赖: contMDiff_toFun
-/
def toContMDiffMap (Φ : M ≃ₘ^n⟮I, I'⟯ M') : C^n⟮I, M; I', M'⟯ :=
  ⟨Φ, Φ.contMDiff_toFun⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (M ≃ₘ^n⟮I, I'⟯ M') C^n⟮I, M; I', M'⟯
  body: ⟨toContMDiffMap⟩

@[continuity]

中文:
实例 :
  签名: Coe (M ≃ₘ^n⟮I, I'⟯ M') C^n⟮I, M; I', M'⟯
  定义体: ⟨toContMDiffMap⟩

@[continuity]

Depends on / 依赖: toContMDiffMap
-/
instance : Coe (M ≃ₘ^n⟮I, I'⟯ M') C^n⟮I, M; I', M'⟯ :=
  ⟨toContMDiffMap⟩

@[continuity]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (h : M ≃ₘ^n⟮I, I'⟯ M')
  statement: Continuous h
  proof: h.contMDiff_toFun.continuous

中文:
定理 continuous
  条件: (h : M ≃ₘ^n⟮I, I'⟯ M')
  结论: 连续 h
  证明: h.contMDiff_toFun.continuous
-/
protected theorem continuous (h : M ≃ₘ^n⟮I, I'⟯ M') : Continuous h :=
  h.contMDiff_toFun.continuous

/--
theorem `contMDiff` / 定理 `contMDiff`

English:
theorem contMDiff
  given: (h : M ≃ₘ^n⟮I, I'⟯ M')
  statement: CMDiff n h
  proof: h.contMDiff_toFun

中文:
定理 contMDiff
  条件: (h : M ≃ₘ^n⟮I, I'⟯ M')
  结论: CMDiff n h
  证明: h.contMDiff_toFun
-/
protected theorem contMDiff (h : M ≃ₘ^n⟮I, I'⟯ M') : CMDiff n h :=
  h.contMDiff_toFun

/--
theorem `contMDiffAt` / 定理 `contMDiffAt`

English:
theorem contMDiffAt
  given: (h : M ≃ₘ^n⟮I, I'⟯ M') {x}
  statement: CMDiffAt n h x
  proof: h.contMDiff.contMDiffAt

中文:
定理 contMDiffAt
  条件: (h : M ≃ₘ^n⟮I, I'⟯ M') {x}
  结论: CMDiffAt n h x
  证明: h.contMDiff.contMDiffAt
-/
protected theorem contMDiffAt (h : M ≃ₘ^n⟮I, I'⟯ M') {x} : CMDiffAt n h x :=
  h.contMDiff.contMDiffAt

/--
theorem `contMDiffWithinAt` / 定理 `contMDiffWithinAt`

English:
theorem contMDiffWithinAt
  given: (h : M ≃ₘ^n⟮I, I'⟯ M') {s x}
  statement: CMDiffAt[s] n h x
  proof: h.contMDiffAt.contMDiffWithinAt

中文:
定理 contMDiffWithinAt
  条件: (h : M ≃ₘ^n⟮I, I'⟯ M') {s x}
  结论: CMDiffAt[s] n h x
  证明: h.contMDiffAt.contMDiffWithinAt
-/
protected theorem contMDiffWithinAt (h : M ≃ₘ^n⟮I, I'⟯ M') {s x} : CMDiffAt[s] n h x :=
  h.contMDiffAt.contMDiffWithinAt

/--
theorem `contDiff` / 定理 `contDiff`

English:
theorem contDiff
  given: (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E')
  statement: ContDiff 𝕜 n h
  proof: h.contMDiff.contDiff

中文:
定理 contDiff
  条件: (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E')
  结论: 连续可微 𝕜 n h
  证明: h.contMDiff.contDiff
-/
protected theorem contDiff (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E') : ContDiff 𝕜 n h :=
  h.contMDiff.contDiff

/--
theorem `mdifferentiable` / 定理 `mdifferentiable`

English:
theorem mdifferentiable
  given: (h : M ≃ₘ^n⟮I, I'⟯ M') (hn : n != 0)
  statement: MDiff h
  proof: h.contMDiff.mdifferentiable hn

中文:
定理 mdifferentiable
  条件: (h : M ≃ₘ^n⟮I, I'⟯ M') (hn : n != 0)
  结论: MDiff h
  证明: h.contMDiff.mdifferentiable hn
-/
protected theorem mdifferentiable (h : M ≃ₘ^n⟮I, I'⟯ M') (hn : n != 0) : MDiff h :=
  h.contMDiff.mdifferentiable hn

/--
theorem `mdifferentiableOn` / 定理 `mdifferentiableOn`

English:
theorem mdifferentiableOn
  given: (h : M ≃ₘ^n⟮I, I'⟯ M') (s : Set M) (hn : n != 0)
  statement: MDiff[s] h
  proof: (h.mdifferentiable hn).mdifferentiableOn

@[simp]

中文:
定理 mdifferentiableOn
  条件: (h : M ≃ₘ^n⟮I, I'⟯ M') (s : 集合 M) (hn : n != 0)
  结论: MDiff[s] h
  证明: (h.mdifferentiable hn).mdifferentiableOn

@[simp]
-/
protected theorem mdifferentiableOn (h : M ≃ₘ^n⟮I, I'⟯ M') (s : Set M) (hn : n != 0) : MDiff[s] h :=
  (h.mdifferentiable hn).mdifferentiableOn

@[simp]
/--
theorem `coe_toEquiv` / 定理 `coe_toEquiv`

English:
theorem coe_toEquiv
  given: (h : M ≃ₘ^n⟮I, I'⟯ M')
  statement: ⇑h.toEquiv = h
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_toEquiv
  条件: (h : M ≃ₘ^n⟮I, I'⟯ M')
  结论: ⇑h.toEquiv = h
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_toEquiv (h : M ≃ₘ^n⟮I, I'⟯ M') : ⇑h.toEquiv = h :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (h : M ≃ₘ^n⟮I, I'⟯ M')
  statement: ⇑(h : C^n⟮I, M; I', M'⟯) = h
  proof: rfl

@[simp]

中文:
定理 coe_coe
  条件: (h : M ≃ₘ^n⟮I, I'⟯ M')
  结论: ⇑(h : C^n⟮I, M; I', M'⟯) = h
  证明: rfl

@[simp]
-/
theorem coe_coe (h : M ≃ₘ^n⟮I, I'⟯ M') : ⇑(h : C^n⟮I, M; I', M'⟯) = h :=
  rfl

@[simp]
/--
theorem `toEquiv_inj` / 定理 `toEquiv_inj`

English:
theorem toEquiv_inj
  given: {h h' : M ≃ₘ^n⟮I, I'⟯ M'}
  statement: h.toEquiv = h'.toEquiv ↔ h = h'
  proof: toEquiv_injective.eq_iff

中文:
定理 toEquiv_inj
  条件: {h h' : M ≃ₘ^n⟮I, I'⟯ M'}
  结论: h.toEquiv = h'.toEquiv ↔ h = h'
  证明: toEquiv_injective.eq_iff

Depends on / 依赖: eq_iff, toEquiv_injective, toEquiv_injective.eq_iff
-/
theorem toEquiv_inj {h h' : M ≃ₘ^n⟮I, I'⟯ M'} : h.toEquiv = h'.toEquiv ↔ h = h' :=
  toEquiv_injective.eq_iff

/--
theorem `coeFn_injective` / 定理 `coeFn_injective`

English:
theorem coeFn_injective
  statement: Injective ((↑) : (M ≃ₘ^n⟮I, I'⟯ M') -> (M -> M'))
  proof: DFunLike.coe_injective

@[ext]

中文:
定理 coeFn_injective
  结论: 单射 ((↑) : (M ≃ₘ^n⟮I, I'⟯ M') -> (M -> M'))
  证明: DFunLike.coe_injective

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coeFn_injective : Injective ((↑) : (M ≃ₘ^n⟮I, I'⟯ M') -> (M -> M')) :=
  DFunLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : forall x, h x = h' x)
  statement: h = h'
  proof: coeFn_injective funext Heq

中文:
定理 ext
  条件: {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : 对任意 x, h x = h' x)
  结论: h = h'
  证明: coeFn_injective funext Heq

Depends on / 依赖: coeFn_injective
-/
theorem ext {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : forall x, h x = h' x) : h = h' :=
coeFn_injective funext Heq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousMapClass (M ≃ₘ⟮I, J⟯ N) M N
  body: f.continuous

中文:
实例 :
  签名: 连续映射类 (M ≃ₘ⟮I, J⟯ N) M N
  定义体: f.continuous

Depends on / 依赖: continuous, f.continuous
-/
instance : ContinuousMapClass (M ≃ₘ⟮I, J⟯ N) M N where
  map_continuous f := f.continuous

section

variable (M I n)

/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : M ≃ₘ^n⟮I, I⟯ M where
  body: contMDiff_id
  contMDiff_invFun := contMDiff_id
  toEquiv := Equiv.refl M

@[simp]

中文:
定义 refl
  签名: : M ≃ₘ^n⟮I, I⟯ M where
  定义体: contMDiff_id
  contMDiff_invFun := contMDiff_id
  toEquiv := Equiv.refl M

@[simp]
-/
protected def refl : M ≃ₘ^n⟮I, I⟯ M where
  contMDiff_toFun := contMDiff_id
  contMDiff_invFun := contMDiff_id
  toEquiv := Equiv.refl M

@[simp]
/--
theorem `refl_toEquiv` / 定理 `refl_toEquiv`

English:
theorem refl_toEquiv
  statement: (Diffeomorph.refl I M n).toEquiv = Equiv.refl _
  proof: rfl

@[simp]

中文:
定理 refl_toEquiv
  结论: (微分同胚.refl I M n).toEquiv = 等价.refl _
  证明: rfl

@[simp]
-/
theorem refl_toEquiv : (Diffeomorph.refl I M n).toEquiv = Equiv.refl _ :=
  rfl

@[simp]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: ⇑(Diffeomorph.refl I M n) = id
  proof: rfl

中文:
定理 coe_refl
  结论: ⇑(微分同胚.refl I M n) = id
  证明: rfl
-/
theorem coe_refl : ⇑(Diffeomorph.refl I M n) = id :=
  rfl

end

/-- Composition of two diffeomorphisms. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N)
  body: h₂.contMDiff.comp h₁.contMDiff
  contMDiff_invFun := h₁.contMDiff_invFun.comp h₂.contMDiff_invFun
  toEquiv := h₁.toEquiv.trans h₂.toEquiv

@[simp]

中文:
定义 trans
  签名: (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N)
  定义体: h₂.contMDiff.comp h₁.contMDiff
  contMDiff_invFun := h₁.contMDiff_invFun.comp h₂.contMDiff_invFun
  toEquiv := h₁.toEquiv.trans h₂.toEquiv

@[simp]
-/
protected def trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) : M ≃ₘ^n⟮I, J⟯ N where
  contMDiff_toFun := h₂.contMDiff.comp h₁.contMDiff
  contMDiff_invFun := h₁.contMDiff_invFun.comp h₂.contMDiff_invFun
  toEquiv := h₁.toEquiv.trans h₂.toEquiv

@[simp]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  given: (h : M ≃ₘ^n⟮I, I'⟯ M')
  statement: h.trans (Diffeomorph.refl I' M' n) = h
  proof: ext fun _ => rfl

@[simp]

中文:
定理 trans_refl
  条件: (h : M ≃ₘ^n⟮I, I'⟯ M')
  结论: h.trans (微分同胚.refl I' M' n) = h
  证明: ext fun _ => rfl

@[simp]
-/
theorem trans_refl (h : M ≃ₘ^n⟮I, I'⟯ M') : h.trans (Diffeomorph.refl I' M' n) = h :=
  ext fun _ => rfl

@[simp]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  given: (h : M ≃ₘ^n⟮I, I'⟯ M')
  statement: (Diffeomorph.refl I M n).trans h = h
  proof: ext fun _ => rfl

@[simp]

中文:
定理 refl_trans
  条件: (h : M ≃ₘ^n⟮I, I'⟯ M')
  结论: (微分同胚.refl I M n).trans h = h
  证明: ext fun _ => rfl

@[simp]
-/
theorem refl_trans (h : M ≃ₘ^n⟮I, I'⟯ M') : (Diffeomorph.refl I M n).trans h = h :=
  ext fun _ => rfl

@[simp]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N)
  statement: ⇑(h₁.trans h₂) = h₂ ∘ h₁
  proof: rfl

中文:
定理 coe_trans
  条件: (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N)
  结论: ⇑(h₁.trans h₂) = h₂ ∘ h₁
  证明: rfl
-/
theorem coe_trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) : ⇑(h₁.trans h₂) = h₂ ∘ h₁ :=
  rfl

/-- Inverse of a diffeomorphism. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (h : M ≃ₘ^n⟮I, J⟯ N)
  body: h.contMDiff_invFun
  contMDiff_invFun := h.contMDiff_toFun
  toEquiv := h.toEquiv.symm

@[simp]

中文:
定义 symm
  签名: (h : M ≃ₘ^n⟮I, J⟯ N)
  定义体: h.contMDiff_invFun
  contMDiff_invFun := h.contMDiff_toFun
  toEquiv := h.toEquiv.symm

@[simp]
-/
protected def symm (h : M ≃ₘ^n⟮I, J⟯ N) : N ≃ₘ^n⟮J, I⟯ M where
  contMDiff_toFun := h.contMDiff_invFun
  contMDiff_invFun := h.contMDiff_toFun
  toEquiv := h.toEquiv.symm

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (h : M ≃ₘ^n⟮I, J⟯ N) (x : N)
  statement: h (h.symm x) = x
  proof: h.toEquiv.apply_symm_apply x

@[simp]

中文:
定理 apply_symm_apply
  条件: (h : M ≃ₘ^n⟮I, J⟯ N) (x : N)
  结论: h (h.symm x) = x
  证明: h.toEquiv.apply_symm_apply x

@[simp]

Depends on / 依赖: apply_symm_apply, h.toEquiv.apply_symm_apply, toEquiv
-/
theorem apply_symm_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x : N) : h (h.symm x) = x :=
  h.toEquiv.apply_symm_apply x

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (h : M ≃ₘ^n⟮I, J⟯ N) (x : M)
  statement: h.symm (h x) = x
  proof: h.toEquiv.symm_apply_apply x

@[simp]

中文:
定理 symm_apply_apply
  条件: (h : M ≃ₘ^n⟮I, J⟯ N) (x : M)
  结论: h.symm (h x) = x
  证明: h.toEquiv.symm_apply_apply x

@[simp]

Depends on / 依赖: h.toEquiv.symm_apply_apply, symm_apply_apply, toEquiv
-/
theorem symm_apply_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x : M) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x

@[simp]
/--
theorem `symm_refl` / 定理 `symm_refl`

English:
theorem symm_refl
  statement: (Diffeomorph.refl I M n).symm = Diffeomorph.refl I M n
  proof: ext fun _ => rfl

@[simp]

中文:
定理 symm_refl
  结论: (微分同胚.refl I M n).symm = 微分同胚.refl I M n
  证明: ext fun _ => rfl

@[simp]
-/
theorem symm_refl : (Diffeomorph.refl I M n).symm = Diffeomorph.refl I M n :=
  ext fun _ => rfl

@[simp]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (h : M ≃ₘ^n⟮I, J⟯ N)
  statement: h.trans h.symm = Diffeomorph.refl I M n
  proof: ext h.symm_apply_apply

@[simp]

中文:
定理 self_trans_symm
  条件: (h : M ≃ₘ^n⟮I, J⟯ N)
  结论: h.trans h.symm = 微分同胚.refl I M n
  证明: ext h.symm_apply_apply

@[simp]

Depends on / 依赖: h.symm_apply_apply, symm_apply_apply
-/
theorem self_trans_symm (h : M ≃ₘ^n⟮I, J⟯ N) : h.trans h.symm = Diffeomorph.refl I M n :=
  ext h.symm_apply_apply

@[simp]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (h : M ≃ₘ^n⟮I, J⟯ N)
  statement: h.symm.trans h = Diffeomorph.refl J N n
  proof: ext h.apply_symm_apply

@[simp]

中文:
定理 symm_trans_self
  条件: (h : M ≃ₘ^n⟮I, J⟯ N)
  结论: h.symm.trans h = 微分同胚.refl J N n
  证明: ext h.apply_symm_apply

@[simp]

Depends on / 依赖: apply_symm_apply, h.apply_symm_apply
-/
theorem symm_trans_self (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.trans h = Diffeomorph.refl J N n :=
  ext h.apply_symm_apply

@[simp]
/--
theorem `symm_trans'` / 定理 `symm_trans'`

English:
theorem symm_trans'
  given: (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N)
  proof: rfl

@[simp]

中文:
定理 symm_trans'
  条件: (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N)
  证明: rfl

@[simp]
-/
theorem symm_trans' (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) :
    (h₁.trans h₂).symm = h₂.symm.trans h₁.symm :=
  rfl

@[simp]
/--
theorem `symm_toEquiv` / 定理 `symm_toEquiv`

English:
theorem symm_toEquiv
  given: (h : M ≃ₘ^n⟮I, J⟯ N)
  statement: h.symm.toEquiv = h.toEquiv.symm
  proof: rfl

@[simp, mfld_simps]

中文:
定理 symm_toEquiv
  条件: (h : M ≃ₘ^n⟮I, J⟯ N)
  结论: h.symm.toEquiv = h.toEquiv.symm
  证明: rfl

@[simp, mfld_simps]
-/
theorem symm_toEquiv (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.toEquiv = h.toEquiv.symm :=
  rfl

@[simp, mfld_simps]
/--
theorem `toEquiv_coe_symm` / 定理 `toEquiv_coe_symm`

English:
theorem toEquiv_coe_symm
  given: (h : M ≃ₘ^n⟮I, J⟯ N)
  statement: ⇑h.toEquiv.symm = h.symm
  proof: rfl

中文:
定理 toEquiv_coe_symm
  条件: (h : M ≃ₘ^n⟮I, J⟯ N)
  结论: ⇑h.toEquiv.symm = h.symm
  证明: rfl
-/
theorem toEquiv_coe_symm (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toEquiv.symm = h.symm :=
  rfl

/--
theorem `image_eq_preimage_symm` / 定理 `image_eq_preimage_symm`

English:
theorem image_eq_preimage_symm
  given: (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set M)
  statement: h '' s = h.symm ⁻¹' s
  proof: h.toEquiv.image_eq_preimage_symm s

中文:
定理 image_eq_preimage_symm
  条件: (h : M ≃ₘ^n⟮I, J⟯ N) (s : 集合 M)
  结论: h '' s = h.symm ⁻¹' s
  证明: h.toEquiv.image_eq_preimage_symm s

Depends on / 依赖: h.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem image_eq_preimage_symm (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) : h '' s = h.symm ⁻¹' s :=
  h.toEquiv.image_eq_preimage_symm s

/--
theorem `symm_image_eq_preimage` / 定理 `symm_image_eq_preimage`

English:
theorem symm_image_eq_preimage
  given: (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set N)
  statement: h.symm '' s = h ⁻¹' s
  proof: h.symm.image_eq_preimage_symm s

@[simp, mfld_simps]
nonrec theorem range_comp {α} (h : M ≃ₘ^n⟮I, J⟯ N) (f : α -> M) :
    range (h ∘ f) = h.symm ⁻¹' range f := by
  rw [range_comp]; rw [image_eq_preimage_symm]

@[simp]

中文:
定理 symm_image_eq_preimage
  条件: (h : M ≃ₘ^n⟮I, J⟯ N) (s : 集合 N)
  结论: h.symm '' s = h ⁻¹' s
  证明: h.symm.image_eq_preimage_symm s

@[simp, mfld_simps]
nonrec theorem range_comp {α} (h : M ≃ₘ^n⟮I, J⟯ N) (f : α -> M) :
    range (h ∘ f) = h.symm ⁻¹' range f := by
  rw [range_comp]; rw [image_eq_preimage_symm]

@[simp]

Depends on / 依赖: h.symm.image_eq_preimage_symm, image_eq_preimage_symm
-/
theorem symm_image_eq_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set N) : h.symm '' s = h ⁻¹' s :=
  h.symm.image_eq_preimage_symm s

@[simp, mfld_simps]
nonrec theorem range_comp {α} (h : M ≃ₘ^n⟮I, J⟯ N) (f : α -> M) :
    range (h ∘ f) = h.symm ⁻¹' range f := by
  rw [range_comp]; rw [image_eq_preimage_symm]

@[simp]
/--
theorem `image_symm_image` / 定理 `image_symm_image`

English:
theorem image_symm_image
  given: (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set N)
  statement: h '' h.symm '' s = s
  proof: h.toEquiv.image_symm_image s

@[simp]

中文:
定理 image_symm_image
  条件: (h : M ≃ₘ^n⟮I, J⟯ N) (s : 集合 N)
  结论: h '' h.symm '' s = s
  证明: h.toEquiv.image_symm_image s

@[simp]

Depends on / 依赖: h.toEquiv.image_symm_image, image_symm_image, toEquiv
-/
theorem image_symm_image (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set N) : h '' h.symm '' s = s :=
  h.toEquiv.image_symm_image s

@[simp]
/--
theorem `symm_image_image` / 定理 `symm_image_image`

English:
theorem symm_image_image
  given: (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set M)
  statement: h.symm '' h '' s = s
  proof: h.toEquiv.symm_image_image s

中文:
定理 symm_image_image
  条件: (h : M ≃ₘ^n⟮I, J⟯ N) (s : 集合 M)
  结论: h.symm '' h '' s = s
  证明: h.toEquiv.symm_image_image s

Depends on / 依赖: h.toEquiv.symm_image_image, symm_image_image, toEquiv
-/
theorem symm_image_image (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) : h.symm '' h '' s = s :=
  h.toEquiv.symm_image_image s

/--
Definition of `toHomeomorph` / `toHomeomorph` 的定义

English:
definition toHomeomorph
  signature: (h : M ≃ₘ^n⟮I, J⟯ N)
  body: ⟨h.toEquiv, h.continuous, h.symm.continuous⟩

@[simp]

中文:
定义 toHomeomorph
  签名: (h : M ≃ₘ^n⟮I, J⟯ N)
  定义体: ⟨h.toEquiv, h.continuous, h.symm.continuous⟩

@[simp]

Depends on / 依赖: continuous, h.continuous, h.symm.continuous, h.toEquiv, toEquiv
-/
def toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : M ≃ₜ N :=
  ⟨h.toEquiv, h.continuous, h.symm.continuous⟩

@[simp]
/--
theorem `toHomeomorph_toEquiv` / 定理 `toHomeomorph_toEquiv`

English:
theorem toHomeomorph_toEquiv
  given: (h : M ≃ₘ^n⟮I, J⟯ N)
  statement: h.toHomeomorph.toEquiv = h.toEquiv
  proof: rfl

@[simp]

中文:
定理 toHomeomorph_toEquiv
  条件: (h : M ≃ₘ^n⟮I, J⟯ N)
  结论: h.toHomeomorph.toEquiv = h.toEquiv
  证明: rfl

@[simp]
-/
theorem toHomeomorph_toEquiv (h : M ≃ₘ^n⟮I, J⟯ N) : h.toHomeomorph.toEquiv = h.toEquiv :=
  rfl

@[simp]
/--
theorem `symm_toHomeomorph` / 定理 `symm_toHomeomorph`

English:
theorem symm_toHomeomorph
  given: (h : M ≃ₘ^n⟮I, J⟯ N)
  statement: h.symm.toHomeomorph = h.toHomeomorph.symm
  proof: rfl

@[simp]

中文:
定理 symm_toHomeomorph
  条件: (h : M ≃ₘ^n⟮I, J⟯ N)
  结论: h.symm.toHomeomorph = h.toHomeomorph.symm
  证明: rfl

@[simp]
-/
theorem symm_toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.toHomeomorph = h.toHomeomorph.symm :=
  rfl

@[simp]
/--
theorem `coe_toHomeomorph` / 定理 `coe_toHomeomorph`

English:
theorem coe_toHomeomorph
  given: (h : M ≃ₘ^n⟮I, J⟯ N)
  statement: ⇑h.toHomeomorph = h
  proof: rfl

@[simp]

中文:
定理 coe_toHomeomorph
  条件: (h : M ≃ₘ^n⟮I, J⟯ N)
  结论: ⇑h.toHomeomorph = h
  证明: rfl

@[simp]
-/
theorem coe_toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toHomeomorph = h :=
  rfl

@[simp]
/--
theorem `coe_toHomeomorph_symm` / 定理 `coe_toHomeomorph_symm`

English:
theorem coe_toHomeomorph_symm
  given: (h : M ≃ₘ^n⟮I, J⟯ N)
  statement: ⇑h.toHomeomorph.symm = h.symm
  proof: rfl

@[simp]

中文:
定理 coe_toHomeomorph_symm
  条件: (h : M ≃ₘ^n⟮I, J⟯ N)
  结论: ⇑h.toHomeomorph.symm = h.symm
  证明: rfl

@[simp]
-/
theorem coe_toHomeomorph_symm (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toHomeomorph.symm = h.symm :=
  rfl

@[simp]
/--
theorem `contMDiffWithinAt_comp_diffeomorph_iff` / 定理 `contMDiffWithinAt_comp_diffeomorph_iff`

English:
theorem contMDiffWithinAt_comp_diffeomorph_iff
  statement: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {s x}
  proof: by
  constructor
  · intro Hfh
    rw [← h.symm_apply_apply x] at Hfh
    simpa only [Function.comp_def, h.apply_symm_apply] using
      Hfh.comp (h x) (h.symm.contMDiffWithinAt.of_le hm) (mapsTo_preimage _ _)
  · rw [← h.image_eq_preimage_symm]
    exact fun hf => hf.comp x (h.contMDiffWithinAt.of_

中文:
定理 contMDiffWithinAt_comp_diffeomorph_iff
  结论: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {s x}
  证明: by
  constructor
  · intro Hfh
    rw [← h.symm_apply_apply x] at Hfh
    simpa only [Function.comp_def, h.apply_symm_apply] using
      Hfh.comp (h x) (h.symm.contMDiffWithinAt.of_le hm) (mapsTo_preimage _ _)
  · rw [← h.image_eq_preimage_symm]
    exact fun hf => hf.comp x (h.contMDiffWithinAt.of_

Depends on / 依赖: Function, Function.comp_def, Hfh.comp, apply_symm_apply, comp_def, contMDiffWithinAt, h.apply_symm_apply, h.contMDiffWithinAt.of_le, h.image_eq_preimage_symm, h.symm.contMDiffWithinAt.of_le, h.symm_apply_apply, hf.comp, image_eq_preimage_symm, mapsTo_image, mapsTo_preimage, of_le, symm_apply_apply
-/
theorem contMDiffWithinAt_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {s x}
    (hm : m <= n) :
    CMDiffAt[s] m (f ∘ h) x ↔ CMDiffAt[h.symm ⁻¹' s] m f (h x) := by
  constructor
  · intro Hfh
    rw [← h.symm_apply_apply x] at Hfh
    simpa only [Function.comp_def, h.apply_symm_apply] using
      Hfh.comp (h x) (h.symm.contMDiffWithinAt.of_le hm) (mapsTo_preimage _ _)
  · rw [← h.image_eq_preimage_symm]
    exact fun hf => hf.comp x (h.contMDiffWithinAt.of_le hm) (mapsTo_image _ _)

@[simp]
/--
theorem `contMDiffOn_comp_diffeomorph_iff` / 定理 `contMDiffOn_comp_diffeomorph_iff`

English:
theorem contMDiffOn_comp_diffeomorph_iff
  given: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {s} (hm : m <= n)
  proof: h.toEquiv.forall_congr fun {_} => by
    simp only [hm, coe_toEquiv, h.symm_apply_apply, contMDiffWithinAt_comp_diffeomorph_iff,
      mem_preimage]

@[simp]

中文:
定理 contMDiffOn_comp_diffeomorph_iff
  条件: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {s} (hm : m <= n)
  证明: h.toEquiv.forall_congr fun {_} => by
    simp only [hm, coe_toEquiv, h.symm_apply_apply, contMDiffWithinAt_comp_diffeomorph_iff,
      mem_preimage]

@[simp]

Depends on / 依赖: coe_toEquiv, contMDiffWithinAt_comp_diffeomorph_iff, forall_congr, h.symm_apply_apply, h.toEquiv.forall_congr, mem_preimage, symm_apply_apply, toEquiv
-/
theorem contMDiffOn_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {s} (hm : m <= n) :
    CMDiff[s] m (f ∘ h) ↔ CMDiff[h.symm ⁻¹' s] m f :=
  h.toEquiv.forall_congr fun {_} => by
    simp only [hm, coe_toEquiv, h.symm_apply_apply, contMDiffWithinAt_comp_diffeomorph_iff,
      mem_preimage]

@[simp]
/--
theorem `contMDiffAt_comp_diffeomorph_iff` / 定理 `contMDiffAt_comp_diffeomorph_iff`

English:
theorem contMDiffAt_comp_diffeomorph_iff
  given: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {x} (hm : m <= n)
  proof: h.contMDiffWithinAt_comp_diffeomorph_iff hm

@[simp]

中文:
定理 contMDiffAt_comp_diffeomorph_iff
  条件: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {x} (hm : m <= n)
  证明: h.contMDiffWithinAt_comp_diffeomorph_iff hm

@[simp]

Depends on / 依赖: contMDiffWithinAt_comp_diffeomorph_iff, h.contMDiffWithinAt_comp_diffeomorph_iff
-/
theorem contMDiffAt_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {x} (hm : m <= n) :
    CMDiffAt m (f ∘ h) x ↔ CMDiffAt m f (h x) :=
  h.contMDiffWithinAt_comp_diffeomorph_iff hm

@[simp]
/--
theorem `contMDiff_comp_diffeomorph_iff` / 定理 `contMDiff_comp_diffeomorph_iff`

English:
theorem contMDiff_comp_diffeomorph_iff
  given: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} (hm : m <= n)
  proof: h.toEquiv.forall_congr fun _ => h.contMDiffAt_comp_diffeomorph_iff hm

@[simp]

中文:
定理 contMDiff_comp_diffeomorph_iff
  条件: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} (hm : m <= n)
  证明: h.toEquiv.forall_congr fun _ => h.contMDiffAt_comp_diffeomorph_iff hm

@[simp]

Depends on / 依赖: contMDiffAt_comp_diffeomorph_iff, forall_congr, h.contMDiffAt_comp_diffeomorph_iff, h.toEquiv.forall_congr, toEquiv
-/
theorem contMDiff_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} (hm : m <= n) :
    CMDiff m (f ∘ h) ↔ CMDiff m f :=
  h.toEquiv.forall_congr fun _ => h.contMDiffAt_comp_diffeomorph_iff hm

@[simp]
/--
theorem `contMDiffWithinAt_diffeomorph_comp_iff` / 定理 `contMDiffWithinAt_diffeomorph_comp_iff`

English:
theorem contMDiffWithinAt_diffeomorph_comp_iff
  statement: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n)
  proof: ⟨fun Hhf => by
    simpa only [Function.comp_def, h.symm_apply_apply] using
      (h.symm.contMDiffAt.of_le hm).comp_contMDiffWithinAt _ Hhf,
    fun Hf => (h.contMDiffAt.of_le hm).comp_contMDiffWithinAt _ Hf⟩

@[simp]

中文:
定理 contMDiffWithinAt_diffeomorph_comp_iff
  结论: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n)
  证明: ⟨fun Hhf => by
    simpa only [Function.comp_def, h.symm_apply_apply] using
      (h.symm.contMDiffAt.of_le hm).comp_contMDiffWithinAt _ Hhf,
    fun Hf => (h.contMDiffAt.of_le hm).comp_contMDiffWithinAt _ Hf⟩

@[simp]

Depends on / 依赖: Function, Function.comp_def, comp_contMDiffWithinAt, comp_def, contMDiffAt, h.contMDiffAt.of_le, h.symm.contMDiffAt.of_le, h.symm_apply_apply, of_le, symm_apply_apply
-/
theorem contMDiffWithinAt_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n)
    {s x} : CMDiffAt[s] m (h ∘ f) x ↔ CMDiffAt[s] m f x :=
  ⟨fun Hhf => by
    simpa only [Function.comp_def, h.symm_apply_apply] using
      (h.symm.contMDiffAt.of_le hm).comp_contMDiffWithinAt _ Hhf,
    fun Hf => (h.contMDiffAt.of_le hm).comp_contMDiffWithinAt _ Hf⟩

@[simp]
/--
theorem `contMDiffAt_diffeomorph_comp_iff` / 定理 `contMDiffAt_diffeomorph_comp_iff`

English:
theorem contMDiffAt_diffeomorph_comp_iff
  given: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n) {x}
  proof: h.contMDiffWithinAt_diffeomorph_comp_iff hm

@[simp]

中文:
定理 contMDiffAt_diffeomorph_comp_iff
  条件: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n) {x}
  证明: h.contMDiffWithinAt_diffeomorph_comp_iff hm

@[simp]

Depends on / 依赖: contMDiffWithinAt_diffeomorph_comp_iff, h.contMDiffWithinAt_diffeomorph_comp_iff
-/
theorem contMDiffAt_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n) {x} :
    CMDiffAt m (h ∘ f) x ↔ CMDiffAt m f x :=
  h.contMDiffWithinAt_diffeomorph_comp_iff hm

@[simp]
/--
theorem `contMDiffOn_diffeomorph_comp_iff` / 定理 `contMDiffOn_diffeomorph_comp_iff`

English:
theorem contMDiffOn_diffeomorph_comp_iff
  given: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n) {s}
  proof: forall₂_congr fun _ _ => h.contMDiffWithinAt_diffeomorph_comp_iff hm

@[simp]

中文:
定理 contMDiffOn_diffeomorph_comp_iff
  条件: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n) {s}
  证明: forall₂_congr fun _ _ => h.contMDiffWithinAt_diffeomorph_comp_iff hm

@[simp]

Depends on / 依赖: contMDiffWithinAt_diffeomorph_comp_iff, h.contMDiffWithinAt_diffeomorph_comp_iff
-/
theorem contMDiffOn_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n) {s} :
    CMDiff[s] m (h ∘ f) ↔ CMDiff[s] m f :=
  forall₂_congr fun _ _ => h.contMDiffWithinAt_diffeomorph_comp_iff hm

@[simp]
/--
theorem `contMDiff_diffeomorph_comp_iff` / 定理 `contMDiff_diffeomorph_comp_iff`

English:
theorem contMDiff_diffeomorph_comp_iff
  given: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n)
  proof: forall_congr' fun _ => h.contMDiffWithinAt_diffeomorph_comp_iff hm

中文:
定理 contMDiff_diffeomorph_comp_iff
  条件: {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n)
  证明: forall_congr' fun _ => h.contMDiffWithinAt_diffeomorph_comp_iff hm

Depends on / 依赖: contMDiffWithinAt_diffeomorph_comp_iff, forall_congr, h.contMDiffWithinAt_diffeomorph_comp_iff
-/
theorem contMDiff_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n) :
    CMDiff m (h ∘ f) ↔ CMDiff m f :=
  forall_congr' fun _ => h.contMDiffWithinAt_diffeomorph_comp_iff hm

/--
theorem `toOpenPartialHomeomorph_mdifferentiable` / 定理 `toOpenPartialHomeomorph_mdifferentiable`

English:
theorem toOpenPartialHomeomorph_mdifferentiable
  given: (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0)
  proof: ⟨h.mdifferentiableOn _ hn, h.symm.mdifferentiableOn _ hn⟩

中文:
定理 toOpenPartialHomeomorph_mdifferentiable
  条件: (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0)
  证明: ⟨h.mdifferentiableOn _ hn, h.symm.mdifferentiableOn _ hn⟩

Depends on / 依赖: h.mdifferentiableOn, h.symm.mdifferentiableOn, mdifferentiableOn
-/
theorem toOpenPartialHomeomorph_mdifferentiable (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) :
    h.toHomeomorph.toOpenPartialHomeomorph.MDifferentiable I J :=
  ⟨h.mdifferentiableOn _ hn, h.symm.mdifferentiableOn _ hn⟩

/--
theorem `uniqueMDiffOn_image_aux` / 定理 `uniqueMDiffOn_image_aux`

English:
theorem uniqueMDiffOn_image_aux
  statement: (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) {s : Set M}
  proof: by
  convert! hs.uniqueMDiffOn_preimage (h.toOpenPartialHomeomorph_mdifferentiable hn)
  simp [h.image_eq_preimage_symm]

@[simp]

中文:
定理 uniqueMDiffOn_image_aux
  结论: (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) {s : 集合 M}
  证明: by
  convert! hs.uniqueMDiffOn_preimage (h.toOpenPartialHomeomorph_mdifferentiable hn)
  simp [h.image_eq_preimage_symm]

@[simp]

Depends on / 依赖: convert, h.image_eq_preimage_symm, h.toOpenPartialHomeomorph_mdifferentiable, hs.uniqueMDiffOn_preimage, image_eq_preimage_symm, toOpenPartialHomeomorph_mdifferentiable, uniqueMDiffOn_preimage
-/
theorem uniqueMDiffOn_image_aux (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) {s : Set M}
    (hs : UniqueMDiff[s]) : UniqueMDiff[h '' s] := by
  convert! hs.uniqueMDiffOn_preimage (h.toOpenPartialHomeomorph_mdifferentiable hn)
  simp [h.image_eq_preimage_symm]

@[simp]
/--
theorem `uniqueMDiffOn_image` / 定理 `uniqueMDiffOn_image`

English:
theorem uniqueMDiffOn_image
  given: (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) {s : Set M}
  proof: ⟨fun hs => h.symm_image_image s ▸ h.symm.uniqueMDiffOn_image_aux hn hs,
    h.uniqueMDiffOn_image_aux hn⟩

@[simp]

中文:
定理 uniqueMDiffOn_image
  条件: (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) {s : 集合 M}
  证明: ⟨fun hs => h.symm_image_image s ▸ h.symm.uniqueMDiffOn_image_aux hn hs,
    h.uniqueMDiffOn_image_aux hn⟩

@[simp]

Depends on / 依赖: h.symm.uniqueMDiffOn_image_aux, h.symm_image_image, h.uniqueMDiffOn_image_aux, symm_image_image, uniqueMDiffOn_image_aux
-/
theorem uniqueMDiffOn_image (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) {s : Set M} :
    UniqueMDiff[h '' s] ↔ UniqueMDiff[s] :=
  ⟨fun hs => h.symm_image_image s ▸ h.symm.uniqueMDiffOn_image_aux hn hs,
    h.uniqueMDiffOn_image_aux hn⟩

@[simp]
/--
theorem `uniqueMDiffOn_preimage` / 定理 `uniqueMDiffOn_preimage`

English:
theorem uniqueMDiffOn_preimage
  given: (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) {s : Set N}
  proof: h.symm_image_eq_preimage s ▸ h.symm.uniqueMDiffOn_image hn

@[simp]

中文:
定理 uniqueMDiffOn_preimage
  条件: (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) {s : 集合 N}
  证明: h.symm_image_eq_preimage s ▸ h.symm.uniqueMDiffOn_image hn

@[simp]

Depends on / 依赖: h.symm.uniqueMDiffOn_image, h.symm_image_eq_preimage, symm_image_eq_preimage, uniqueMDiffOn_image
-/
theorem uniqueMDiffOn_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) {s : Set N} :
    UniqueMDiff[h ⁻¹' s] ↔ UniqueMDiff[s] :=
  h.symm_image_eq_preimage s ▸ h.symm.uniqueMDiffOn_image hn

@[simp]
/--
theorem `uniqueDiffOn_image` / 定理 `uniqueDiffOn_image`

English:
theorem uniqueDiffOn_image
  given: (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (hn : n != 0) {s : Set E}
  proof: by
  simp only [← uniqueMDiffOn_iff_uniqueDiffOn, uniqueMDiffOn_image _ hn]

@[simp]

中文:
定理 uniqueDiffOn_image
  条件: (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (hn : n != 0) {s : 集合 E}
  证明: by
  simp only [← uniqueMDiffOn_iff_uniqueDiffOn, uniqueMDiffOn_image _ hn]

@[simp]

Depends on / 依赖: uniqueMDiffOn_iff_uniqueDiffOn, uniqueMDiffOn_image
-/
theorem uniqueDiffOn_image (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (hn : n != 0) {s : Set E} :
    UniqueDiffOn 𝕜 (h '' s) ↔ UniqueDiffOn 𝕜 s := by
  simp only [← uniqueMDiffOn_iff_uniqueDiffOn, uniqueMDiffOn_image _ hn]

@[simp]
/--
theorem `uniqueDiffOn_preimage` / 定理 `uniqueDiffOn_preimage`

English:
theorem uniqueDiffOn_preimage
  given: (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (hn : n != 0) {s : Set F}
  proof: h.symm_image_eq_preimage s ▸ h.symm.uniqueDiffOn_image hn

中文:
定理 uniqueDiffOn_preimage
  条件: (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (hn : n != 0) {s : 集合 F}
  证明: h.symm_image_eq_preimage s ▸ h.symm.uniqueDiffOn_image hn

Depends on / 依赖: h.symm.uniqueDiffOn_image, h.symm_image_eq_preimage, symm_image_eq_preimage, uniqueDiffOn_image
-/
theorem uniqueDiffOn_preimage (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (hn : n != 0) {s : Set F} :
    UniqueDiffOn 𝕜 (h ⁻¹' s) ↔ UniqueDiffOn 𝕜 s :=
  h.symm_image_eq_preimage s ▸ h.symm.uniqueDiffOn_image hn

end Diffeomorph

namespace ContinuousLinearEquiv

variable (e : E ≃L[𝕜] E')

/--
Definition of `toDiffeomorph` / `toDiffeomorph` 的定义

English:
definition toDiffeomorph
  signature: : E ≃ₘ[𝕜] E' where
  body: e.contDiff.contMDiff
  contMDiff_invFun := e.symm.contDiff.contMDiff
  toEquiv := e.toLinearEquiv.toEquiv

@[simp]

中文:
定义 toDiffeomorph
  签名: : E ≃ₘ[𝕜] E' where
  定义体: e.contDiff.contMDiff
  contMDiff_invFun := e.symm.contDiff.contMDiff
  toEquiv := e.toLinearEquiv.toEquiv

@[simp]

Depends on / 依赖: contDiff, contMDiff, e.contDiff.contMDiff
-/
def toDiffeomorph : E ≃ₘ[𝕜] E' where
  contMDiff_toFun := e.contDiff.contMDiff
  contMDiff_invFun := e.symm.contDiff.contMDiff
  toEquiv := e.toLinearEquiv.toEquiv

@[simp]
/--
theorem `coe_toDiffeomorph` / 定理 `coe_toDiffeomorph`

English:
theorem coe_toDiffeomorph
  statement: ⇑e.toDiffeomorph = e
  proof: rfl

@[simp]

中文:
定理 coe_toDiffeomorph
  结论: ⇑e.toDiffeomorph = e
  证明: rfl

@[simp]
-/
theorem coe_toDiffeomorph : ⇑e.toDiffeomorph = e :=
  rfl

@[simp]
/--
theorem `symm_toDiffeomorph` / 定理 `symm_toDiffeomorph`

English:
theorem symm_toDiffeomorph
  statement: e.symm.toDiffeomorph = e.toDiffeomorph.symm
  proof: rfl

@[simp]

中文:
定理 symm_toDiffeomorph
  结论: e.symm.toDiffeomorph = e.toDiffeomorph.symm
  证明: rfl

@[simp]
-/
theorem symm_toDiffeomorph : e.symm.toDiffeomorph = e.toDiffeomorph.symm :=
  rfl

@[simp]
/--
theorem `coe_toDiffeomorph_symm` / 定理 `coe_toDiffeomorph_symm`

English:
theorem coe_toDiffeomorph_symm
  statement: ⇑e.toDiffeomorph.symm = e.symm
  proof: rfl

中文:
定理 coe_toDiffeomorph_symm
  结论: ⇑e.toDiffeomorph.symm = e.symm
  证明: rfl
-/
theorem coe_toDiffeomorph_symm : ⇑e.toDiffeomorph.symm = e.symm :=
  rfl

end ContinuousLinearEquiv

namespace ModelWithCorners

variable (I) (e : E ≃L[𝕜] E')

/--
Definition of `transContinuousLinearEquiv` / `transContinuousLinearEquiv` 的定义

English:
definition transContinuousLinearEquiv
  signature: : ModelWithCorners 𝕜 E' H where
  body: I.toPartialEquiv.trans e.toEquiv.toPartialEquiv
  source_eq := by simp
  convex_range' := by
    split_ifs with h
    · simp only [PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply, LinearEquiv.coe_toEquiv,
      ContinuousLinearEquiv.coe_toLinearEquiv, toPartialEquiv_coe]
      rw [range_comp]
   

中文:
定义 transContinuousLinearEquiv
  签名: : 带角模型 𝕜 E' H where
  定义体: I.toPartialEquiv.trans e.toEquiv.toPartialEquiv
  source_eq := by simp
  convex_range' := by
    split_ifs with h
    · simp only [PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply, LinearEquiv.coe_toEquiv,
      ContinuousLinearEquiv.coe_toLinearEquiv, toPartialEquiv_coe]
      rw [range_comp]
   

Depends on / 依赖: I.toPartialEquiv.trans, e.toEquiv.toPartialEquiv, toEquiv, toPartialEquiv
-/
def transContinuousLinearEquiv : ModelWithCorners 𝕜 E' H where
  toPartialEquiv := I.toPartialEquiv.trans e.toEquiv.toPartialEquiv
  source_eq := by simp
  convex_range' := by
    split_ifs with h
    · simp only [PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply, LinearEquiv.coe_toEquiv,
      ContinuousLinearEquiv.coe_toLinearEquiv, toPartialEquiv_coe]
      rw [range_comp]
      let := h.rclike
      let := NormedSpace.restrictScalars Real 𝕜 E
      let := NormedSpace.restrictScalars Real 𝕜 E'
      let eR : E ->L[Real] E' := ContinuousLinearMap.restrictScalars Real (e : E ->L[𝕜] E')
      change Convex Real (⇑eR '' range ↑I)
      apply I.convex_range.linear_image
    · simp [range_eq_univ_of_not_isRCLikeNormedField I h, range_comp]
  nonempty_interior' := by
    simp only [PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply, LinearEquiv.coe_toEquiv,
      ContinuousLinearEquiv.coe_toLinearEquiv, toPartialEquiv_coe, range_comp,
      ContinuousLinearEquiv.image_eq_preimage_symm]
    apply Nonempty.mono (preimage_interior_subset_interior_preimage e.symm.continuous)
    rw [← ContinuousLinearEquiv.image_eq_preimage_symm]
    simpa using I.nonempty_interior
  continuous_toFun := e.continuous.comp I.continuous
  continuous_invFun := I.continuous_symm.comp e.symm.continuous

@[simp, mfld_simps]
/--
theorem `coe_transContinuousLinearEquiv` / 定理 `coe_transContinuousLinearEquiv`

English:
theorem coe_transContinuousLinearEquiv
  statement: ⇑(I.transContinuousLinearEquiv e) = e ∘ I
  proof: rfl

@[simp, mfld_simps]

中文:
定理 coe_transContinuousLinearEquiv
  结论: ⇑(I.transContinuousLinearEquiv e) = e ∘ I
  证明: rfl

@[simp, mfld_simps]
-/
theorem coe_transContinuousLinearEquiv : ⇑(I.transContinuousLinearEquiv e) = e ∘ I :=
  rfl

@[simp, mfld_simps]
/--
theorem `coe_transContinuousLinearEquiv_symm` / 定理 `coe_transContinuousLinearEquiv_symm`

English:
theorem coe_transContinuousLinearEquiv_symm
  proof: rfl

中文:
定理 coe_transContinuousLinearEquiv_symm
  证明: rfl
-/
theorem coe_transContinuousLinearEquiv_symm :
    ⇑(I.transContinuousLinearEquiv e).symm = I.symm ∘ e.symm := rfl

/--
theorem `transContinuousLinearEquiv_range` / 定理 `transContinuousLinearEquiv_range`

English:
theorem transContinuousLinearEquiv_range
  statement: range (I.transContinuousLinearEquiv e) = e '' range I
  proof: range_comp e I

中文:
定理 transContinuousLinearEquiv_range
  结论: range (I.transContinuousLinearEquiv e) = e '' range I
  证明: range_comp e I

Depends on / 依赖: range_comp
-/
theorem transContinuousLinearEquiv_range : range (I.transContinuousLinearEquiv e) = e '' range I :=
  range_comp e I

/--
theorem `coe_extChartAt_transContinuousLinearEquiv` / 定理 `coe_extChartAt_transContinuousLinearEquiv`

English:
theorem coe_extChartAt_transContinuousLinearEquiv
  given: (x : M)
  proof: rfl

中文:
定理 coe_extChartAt_transContinuousLinearEquiv
  条件: (x : M)
  证明: rfl
-/
theorem coe_extChartAt_transContinuousLinearEquiv (x : M) :
    ⇑(extChartAt (I.transContinuousLinearEquiv e) x) = e ∘ extChartAt I x :=
  rfl

/--
theorem `coe_extChartAt_transContinuousLinearEquiv_symm` / 定理 `coe_extChartAt_transContinuousLinearEquiv_symm`

English:
theorem coe_extChartAt_transContinuousLinearEquiv_symm
  given: (x : M)
  proof: rfl

中文:
定理 coe_extChartAt_transContinuousLinearEquiv_symm
  条件: (x : M)
  证明: rfl
-/
theorem coe_extChartAt_transContinuousLinearEquiv_symm (x : M) :
    ⇑(extChartAt (I.transContinuousLinearEquiv e) x).symm = (extChartAt I x).symm ∘ e.symm :=
  rfl

/--
theorem `extChartAt_transContinuousLinearEquiv_target` / 定理 `extChartAt_transContinuousLinearEquiv_target`

English:
theorem extChartAt_transContinuousLinearEquiv_target
  given: (x : M)
  proof: by
  simp only [range_comp, preimage_preimage, ContinuousLinearEquiv.image_eq_preimage_symm,
    mfld_simps, ← comp_def]

中文:
定理 extChartAt_transContinuousLinearEquiv_target
  条件: (x : M)
  证明: by
  simp only [range_comp, preimage_preimage, ContinuousLinearEquiv.image_eq_preimage_symm,
    mfld_simps, ← comp_def]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.image_eq_preimage_symm, comp_def, image_eq_preimage_symm, mfld_simps, preimage_preimage, range_comp
-/
theorem extChartAt_transContinuousLinearEquiv_target (x : M) :
    (extChartAt (I.transContinuousLinearEquiv e) x).target
      = e.symm ⁻¹' (extChartAt I x).target := by
  simp only [range_comp, preimage_preimage, ContinuousLinearEquiv.image_eq_preimage_symm,
    mfld_simps, ← comp_def]

end ModelWithCorners

namespace ContinuousLinearEquiv

variable (e : E ≃L[𝕜] F)

/--
Instance `instIsManifoldtransContinuousLinearEquiv` / 实例 `instIsManifoldtransContinuousLinearEquiv`

English:
instance instIsManifoldtransContinuousLinearEquiv
  signature: [IsManifold I n M]
  body: by
  refine isManifold_of_contDiffOn (I.transContinuousLinearEquiv e) n M fun e₁ e₂ h₁ h₂ => ?_
  refine e.contDiff.comp_contDiffOn
      (((contDiffGroupoid n I).compatible h₁ h₂).1.comp e.symm.contDiff.contDiffOn ?_)
  simp [preimage_comp, range_comp, mapsTo_iff_subset_preimage,
    ContinuousLine

中文:
实例 instIsManifoldtransContinuousLinearEquiv
  签名: [是流形 I n M]
  定义体: by
  refine isManifold_of_contDiffOn (I.transContinuousLinearEquiv e) n M fun e₁ e₂ h₁ h₂ => ?_
  refine e.contDiff.comp_contDiffOn
      (((contDiffGroupoid n I).compatible h₁ h₂).1.comp e.symm.contDiff.contDiffOn ?_)
  simp [preimage_comp, range_comp, mapsTo_iff_subset_preimage,
    ContinuousLine

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.image_eq_preimage_symm, I.transContinuousLinearEquiv, comp_contDiffOn, compatible, contDiff, contDiffGroupoid, contDiffOn, e.contDiff.comp_contDiffOn, e.symm.contDiff.contDiffOn, image_eq_preimage_symm, isManifold_of_contDiffOn, mapsTo_iff_subset_preimage, preimage_comp, range_comp, transContinuousLinearEquiv
-/
instance instIsManifoldtransContinuousLinearEquiv [IsManifold I n M] :
    IsManifold (I.transContinuousLinearEquiv e) n M := by
  refine isManifold_of_contDiffOn (I.transContinuousLinearEquiv e) n M fun e₁ e₂ h₁ h₂ => ?_
  refine e.contDiff.comp_contDiffOn
      (((contDiffGroupoid n I).compatible h₁ h₂).1.comp e.symm.contDiff.contDiffOn ?_)
  simp [preimage_comp, range_comp, mapsTo_iff_subset_preimage,
    ContinuousLinearEquiv.image_eq_preimage_symm]

variable (I M)

/--
Definition of `toTransContinuousLinearEquiv` / `toTransContinuousLinearEquiv` 的定义

English:
definition toTransContinuousLinearEquiv
  signature: (e : E ≃L[𝕜] F)
  body: Equiv.refl M
  contMDiff_toFun x := by
    refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    refine e.contDiff.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [Equiv.coe_refl, id, (· ∘ ·), I.coe_extChartAt_transContinuousLinearEquiv,
        (extChartAt I x).right_inv

中文:
定义 toTransContinuousLinearEquiv
  签名: (e : E ≃L[𝕜] F)
  定义体: Equiv.refl M
  contMDiff_toFun x := by
    refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    refine e.contDiff.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [Equiv.coe_refl, id, (· ∘ ·), I.coe_extChartAt_transContinuousLinearEquiv,
        (extChartAt I x).right_inv

Depends on / 依赖: Equiv.refl
-/
def toTransContinuousLinearEquiv (e : E ≃L[𝕜] F) : M ≃ₘ^n⟮I, I.transContinuousLinearEquiv e⟯ M where
  toEquiv := Equiv.refl M
  contMDiff_toFun x := by
    refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    refine e.contDiff.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [Equiv.coe_refl, id, (· ∘ ·), I.coe_extChartAt_transContinuousLinearEquiv,
        (extChartAt I x).right_inv hy.1]
    · exact
      ⟨(extChartAt I x).map_source (mem_extChartAt_source x), trivial, by simp only [mfld_simps]⟩
  contMDiff_invFun x := by
    refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    refine e.symm.contDiff.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [mem_inter_iff, I.extChartAt_transContinuousLinearEquiv_target] at hy
      simp only [Equiv.coe_refl, Equiv.refl_symm, id, (· ∘ ·),
        I.coe_extChartAt_transContinuousLinearEquiv_symm, (extChartAt I x).right_inv hy.1]
    exact ⟨(extChartAt _ x).map_source (mem_extChartAt_source x), trivial, by
      simp only [e.symm_apply_apply, Equiv.refl_symm, Equiv.coe_refl, mfld_simps]⟩

variable {I M}

@[simp]
/--
theorem `contMDiffWithinAt_transContinuousLinearEquiv_right` / 定理 `contMDiffWithinAt_transContinuousLinearEquiv_right`

English:
theorem contMDiffWithinAt_transContinuousLinearEquiv_right
  given: {f : M' -> M} {x s}
  proof: (toTransContinuousLinearEquiv I M e).contMDiffWithinAt_diffeomorph_comp_iff le_rfl

@[simp]

中文:
定理 contMDiffWithinAt_transContinuousLinearEquiv_right
  条件: {f : M' -> M} {x s}
  证明: (toTransContinuousLinearEquiv I M e).contMDiffWithinAt_diffeomorph_comp_iff le_rfl

@[simp]

Depends on / 依赖: contMDiffWithinAt_diffeomorph_comp_iff, le_rfl, toTransContinuousLinearEquiv
-/
theorem contMDiffWithinAt_transContinuousLinearEquiv_right {f : M' -> M} {x s} :
    ContMDiffWithinAt I' (I.transContinuousLinearEquiv e) n f s x
      ↔ CMDiffAt[s] n f x :=
  (toTransContinuousLinearEquiv I M e).contMDiffWithinAt_diffeomorph_comp_iff le_rfl

@[simp]
/--
theorem `contMDiffAt_transContinuousLinearEquiv_right` / 定理 `contMDiffAt_transContinuousLinearEquiv_right`

English:
theorem contMDiffAt_transContinuousLinearEquiv_right
  given: {f : M' -> M} {x}
  proof: (toTransContinuousLinearEquiv I M e).contMDiffAt_diffeomorph_comp_iff le_rfl

@[simp]

中文:
定理 contMDiffAt_transContinuousLinearEquiv_right
  条件: {f : M' -> M} {x}
  证明: (toTransContinuousLinearEquiv I M e).contMDiffAt_diffeomorph_comp_iff le_rfl

@[simp]

Depends on / 依赖: contMDiffAt_diffeomorph_comp_iff, le_rfl, toTransContinuousLinearEquiv
-/
theorem contMDiffAt_transContinuousLinearEquiv_right {f : M' -> M} {x} :
    ContMDiffAt I' (I.transContinuousLinearEquiv e) n f x ↔ CMDiffAt n f x :=
  (toTransContinuousLinearEquiv I M e).contMDiffAt_diffeomorph_comp_iff le_rfl

@[simp]
/--
theorem `contMDiffOn_transContinuousLinearEquiv_right` / 定理 `contMDiffOn_transContinuousLinearEquiv_right`

English:
theorem contMDiffOn_transContinuousLinearEquiv_right
  given: {f : M' -> M} {s}
  proof: (toTransContinuousLinearEquiv I M e).contMDiffOn_diffeomorph_comp_iff le_rfl

@[simp]

中文:
定理 contMDiffOn_transContinuousLinearEquiv_right
  条件: {f : M' -> M} {s}
  证明: (toTransContinuousLinearEquiv I M e).contMDiffOn_diffeomorph_comp_iff le_rfl

@[simp]

Depends on / 依赖: contMDiffOn_diffeomorph_comp_iff, le_rfl, toTransContinuousLinearEquiv
-/
theorem contMDiffOn_transContinuousLinearEquiv_right {f : M' -> M} {s} :
    ContMDiffOn I' (I.transContinuousLinearEquiv e) n f s ↔ CMDiff[s] n f :=
  (toTransContinuousLinearEquiv I M e).contMDiffOn_diffeomorph_comp_iff le_rfl

@[simp]
/--
theorem `contMDiff_transContinuousLinearEquiv_right` / 定理 `contMDiff_transContinuousLinearEquiv_right`

English:
theorem contMDiff_transContinuousLinearEquiv_right
  given: {f : M' -> M}
  proof: (toTransContinuousLinearEquiv I M e).contMDiff_diffeomorph_comp_iff le_rfl

@[simp]

中文:
定理 contMDiff_transContinuousLinearEquiv_right
  条件: {f : M' -> M}
  证明: (toTransContinuousLinearEquiv I M e).contMDiff_diffeomorph_comp_iff le_rfl

@[simp]

Depends on / 依赖: contMDiff_diffeomorph_comp_iff, le_rfl, toTransContinuousLinearEquiv
-/
theorem contMDiff_transContinuousLinearEquiv_right {f : M' -> M} :
    ContMDiff I' (I.transContinuousLinearEquiv e) n f ↔ CMDiff n f :=
  (toTransContinuousLinearEquiv I M e).contMDiff_diffeomorph_comp_iff le_rfl

@[simp]
/--
theorem `contMDiffWithinAt_transContinuousLinearEquiv_left` / 定理 `contMDiffWithinAt_transContinuousLinearEquiv_left`

English:
theorem contMDiffWithinAt_transContinuousLinearEquiv_left
  given: {f : M -> M'} {x s}
  proof: ((toTransContinuousLinearEquiv I M e).contMDiffWithinAt_comp_diffeomorph_iff le_rfl).symm

@[simp]

中文:
定理 contMDiffWithinAt_transContinuousLinearEquiv_left
  条件: {f : M -> M'} {x s}
  证明: ((toTransContinuousLinearEquiv I M e).contMDiffWithinAt_comp_diffeomorph_iff le_rfl).symm

@[simp]

Depends on / 依赖: contMDiffWithinAt_comp_diffeomorph_iff, le_rfl, toTransContinuousLinearEquiv
-/
theorem contMDiffWithinAt_transContinuousLinearEquiv_left {f : M -> M'} {x s} :
    ContMDiffWithinAt (I.transContinuousLinearEquiv e) I' n f s x ↔ CMDiffAt[s] n f x :=
  ((toTransContinuousLinearEquiv I M e).contMDiffWithinAt_comp_diffeomorph_iff le_rfl).symm

@[simp]
/--
theorem `contMDiffAt_transContinuousLinearEquiv_left` / 定理 `contMDiffAt_transContinuousLinearEquiv_left`

English:
theorem contMDiffAt_transContinuousLinearEquiv_left
  given: {f : M -> M'} {x}
  proof: ((toTransContinuousLinearEquiv I M e).contMDiffAt_comp_diffeomorph_iff le_rfl).symm

@[simp]

中文:
定理 contMDiffAt_transContinuousLinearEquiv_left
  条件: {f : M -> M'} {x}
  证明: ((toTransContinuousLinearEquiv I M e).contMDiffAt_comp_diffeomorph_iff le_rfl).symm

@[simp]

Depends on / 依赖: contMDiffAt_comp_diffeomorph_iff, le_rfl, toTransContinuousLinearEquiv
-/
theorem contMDiffAt_transContinuousLinearEquiv_left {f : M -> M'} {x} :
    ContMDiffAt (I.transContinuousLinearEquiv e) I' n f x ↔ CMDiffAt n f x :=
  ((toTransContinuousLinearEquiv I M e).contMDiffAt_comp_diffeomorph_iff le_rfl).symm

@[simp]
/--
theorem `contMDiffOn_transContinuousLinearEquiv_left` / 定理 `contMDiffOn_transContinuousLinearEquiv_left`

English:
theorem contMDiffOn_transContinuousLinearEquiv_left
  given: {f : M -> M'} {s}
  proof: ((toTransContinuousLinearEquiv I M e).contMDiffOn_comp_diffeomorph_iff le_rfl).symm

@[simp]

中文:
定理 contMDiffOn_transContinuousLinearEquiv_left
  条件: {f : M -> M'} {s}
  证明: ((toTransContinuousLinearEquiv I M e).contMDiffOn_comp_diffeomorph_iff le_rfl).symm

@[simp]

Depends on / 依赖: contMDiffOn_comp_diffeomorph_iff, le_rfl, toTransContinuousLinearEquiv
-/
theorem contMDiffOn_transContinuousLinearEquiv_left {f : M -> M'} {s} :
    ContMDiffOn (I.transContinuousLinearEquiv e) I' n f s ↔ CMDiff[s] n f :=
  ((toTransContinuousLinearEquiv I M e).contMDiffOn_comp_diffeomorph_iff le_rfl).symm

@[simp]
/--
theorem `contMDiff_transContinuousLinearEquiv_left` / 定理 `contMDiff_transContinuousLinearEquiv_left`

English:
theorem contMDiff_transContinuousLinearEquiv_left
  given: {f : M -> M'}
  proof: ((toTransContinuousLinearEquiv I M e).contMDiff_comp_diffeomorph_iff le_rfl).symm

中文:
定理 contMDiff_transContinuousLinearEquiv_left
  条件: {f : M -> M'}
  证明: ((toTransContinuousLinearEquiv I M e).contMDiff_comp_diffeomorph_iff le_rfl).symm

Depends on / 依赖: contMDiff_comp_diffeomorph_iff, le_rfl, toTransContinuousLinearEquiv
-/
theorem contMDiff_transContinuousLinearEquiv_left {f : M -> M'} :
    ContMDiff (I.transContinuousLinearEquiv e) I' n f ↔ CMDiff n f :=
  ((toTransContinuousLinearEquiv I M e).contMDiff_comp_diffeomorph_iff le_rfl).symm

end ContinuousLinearEquiv

namespace Diffeomorph

section Constructions

section Product

/--
Definition of `prodCongr` / `prodCongr` 的定义

English:
definition prodCongr
  signature: (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N')
  body: (h₁.contMDiff.comp contMDiff_fst).prodMk (h₂.contMDiff.comp contMDiff_snd)
  contMDiff_invFun :=
    (h₁.symm.contMDiff.comp contMDiff_fst).prodMk (h₂.symm.contMDiff.comp contMDiff_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]

中文:
定义 prodCongr
  签名: (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N')
  定义体: (h₁.contMDiff.comp contMDiff_fst).prodMk (h₂.contMDiff.comp contMDiff_snd)
  contMDiff_invFun :=
    (h₁.symm.contMDiff.comp contMDiff_fst).prodMk (h₂.symm.contMDiff.comp contMDiff_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]

Depends on / 依赖: contMDiff, contMDiff.comp, contMDiff_fst, contMDiff_snd, prodMk
-/
def prodCongr (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') :
    (M × N) ≃ₘ^n⟮I.prod J, I'.prod J'⟯ M' × N' where
  contMDiff_toFun := (h₁.contMDiff.comp contMDiff_fst).prodMk (h₂.contMDiff.comp contMDiff_snd)
  contMDiff_invFun :=
    (h₁.symm.contMDiff.comp contMDiff_fst).prodMk (h₂.symm.contMDiff.comp contMDiff_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]
/--
theorem `prodCongr_symm` / 定理 `prodCongr_symm`

English:
theorem prodCongr_symm
  given: (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N')
  proof: rfl

@[simp]

中文:
定理 prodCongr_symm
  条件: (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N')
  证明: rfl

@[simp]
-/
theorem prodCongr_symm (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl

@[simp]
/--
theorem `coe_prodCongr` / 定理 `coe_prodCongr`

English:
theorem coe_prodCongr
  given: (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N')
  proof: rfl

中文:
定理 coe_prodCongr
  条件: (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N')
  证明: rfl
-/
theorem coe_prodCongr (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') :
    ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl

section

variable (I J J' M N N' n)

/--
Definition of `prodComm` / `prodComm` 的定义

English:
definition prodComm
  signature: : (M × N) ≃ₘ^n⟮I.prod J, J.prod I⟯ N × M where
  body: contMDiff_snd.prodMk contMDiff_fst
  contMDiff_invFun := contMDiff_snd.prodMk contMDiff_fst
  toEquiv := Equiv.prodComm M N

@[simp]

中文:
定义 prodComm
  签名: : (M × N) ≃ₘ^n⟮I.乘积 J, J.乘积 I⟯ N × M where
  定义体: contMDiff_snd.prodMk contMDiff_fst
  contMDiff_invFun := contMDiff_snd.prodMk contMDiff_fst
  toEquiv := Equiv.prodComm M N

@[simp]

Depends on / 依赖: contMDiff_fst, contMDiff_snd, contMDiff_snd.prodMk, prodMk
-/
def prodComm : (M × N) ≃ₘ^n⟮I.prod J, J.prod I⟯ N × M where
  contMDiff_toFun := contMDiff_snd.prodMk contMDiff_fst
  contMDiff_invFun := contMDiff_snd.prodMk contMDiff_fst
  toEquiv := Equiv.prodComm M N

@[simp]
/--
theorem `prodComm_symm` / 定理 `prodComm_symm`

English:
theorem prodComm_symm
  statement: (prodComm I J M N n).symm = prodComm J I N M n
  proof: rfl

@[simp]

中文:
定理 prodComm_symm
  结论: (prodComm I J M N n).symm = prodComm J I N M n
  证明: rfl

@[simp]
-/
theorem prodComm_symm : (prodComm I J M N n).symm = prodComm J I N M n :=
  rfl

@[simp]
/--
theorem `coe_prodComm` / 定理 `coe_prodComm`

English:
theorem coe_prodComm
  statement: ⇑(prodComm I J M N n) = Prod.swap
  proof: rfl

中文:
定理 coe_prodComm
  结论: ⇑(prodComm I J M N n) = 积类型.swap
  证明: rfl
-/
theorem coe_prodComm : ⇑(prodComm I J M N n) = Prod.swap :=
  rfl

/--
Definition of `prodAssoc` / `prodAssoc` 的定义

English:
definition prodAssoc
  signature: : ((M × N) × N') ≃ₘ^n⟮(I.prod J).prod J', I.prod (J.prod J')⟯ M × N × N' where
  body: (contMDiff_fst.comp contMDiff_fst).prodMk
      ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd)
  contMDiff_invFun :=
    (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).prodMk
      (contMDiff_snd.comp contMDiff_snd)
  toEquiv := Equiv.prodAssoc M N N'

中文:
定义 prodAssoc
  签名: : ((M × N) × N') ≃ₘ^n⟮(I.乘积 J).乘积 J', I.乘积 (J.乘积 J')⟯ M × N × N' where
  定义体: (contMDiff_fst.comp contMDiff_fst).prodMk
      ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd)
  contMDiff_invFun :=
    (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).prodMk
      (contMDiff_snd.comp contMDiff_snd)
  toEquiv := Equiv.prodAssoc M N N'

Depends on / 依赖: Equiv.prodAssoc, contMDiff_fst, contMDiff_fst.comp, contMDiff_fst.prodMk, contMDiff_invFun, contMDiff_snd, contMDiff_snd.comp, prodAssoc, prodMk, toEquiv
-/
def prodAssoc : ((M × N) × N') ≃ₘ^n⟮(I.prod J).prod J', I.prod (J.prod J')⟯ M × N × N' where
  contMDiff_toFun :=
    (contMDiff_fst.comp contMDiff_fst).prodMk
      ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd)
  contMDiff_invFun :=
    (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).prodMk
      (contMDiff_snd.comp contMDiff_snd)
  toEquiv := Equiv.prodAssoc M N N'

end

end Product

section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  {N J : Type*} [TopologicalSpace N] [ChartedSpace H N] {J : ModelWithCorners 𝕜 E' H}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace H N']

/--
Definition of `sumCongr` / `sumCongr` 的定义

English:
definition sumCongr
  signature: (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n)
  body: Equiv.sumCongr φ.toEquiv ψ.toEquiv
  contMDiff_toFun := ContMDiff.sumMap φ.contMDiff_toFun ψ.contMDiff_toFun
  contMDiff_invFun := ContMDiff.sumMap φ.contMDiff_invFun ψ.contMDiff_invFun

中文:
定义 sumCongr
  签名: (φ : 微分同胚 I J M N n) (ψ : 微分同胚 I J M' N' n)
  定义体: Equiv.sumCongr φ.toEquiv ψ.toEquiv
  contMDiff_toFun := ContMDiff.sumMap φ.contMDiff_toFun ψ.contMDiff_toFun
  contMDiff_invFun := ContMDiff.sumMap φ.contMDiff_invFun ψ.contMDiff_invFun

Depends on / 依赖: Equiv.sumCongr, sumCongr, toEquiv
-/
def sumCongr (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    Diffeomorph I J (M oplus M') (N oplus N') n where
  toEquiv := Equiv.sumCongr φ.toEquiv ψ.toEquiv
  contMDiff_toFun := ContMDiff.sumMap φ.contMDiff_toFun ψ.contMDiff_toFun
  contMDiff_invFun := ContMDiff.sumMap φ.contMDiff_invFun ψ.contMDiff_invFun

/--
lemma `sumCongr_symm_symm` / 引理 `sumCongr_symm_symm`

English:
lemma sumCongr_symm_symm
  given: (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n)
  proof: rfl

@[simp, mfld_simps]

中文:
引理 sumCongr_symm_symm
  条件: (φ : 微分同胚 I J M N n) (ψ : 微分同胚 I J M' N' n)
  证明: rfl

@[simp, mfld_simps]
-/
lemma sumCongr_symm_symm (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    sumCongr φ.symm ψ.symm = (sumCongr φ ψ).symm := rfl

@[simp, mfld_simps]
/--
lemma `sumCongr_coe` / 引理 `sumCongr_coe`

English:
lemma sumCongr_coe
  given: (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n)
  proof: rfl

中文:
引理 sumCongr_coe
  条件: (φ : 微分同胚 I J M N n) (ψ : 微分同胚 I J M' N' n)
  证明: rfl
-/
lemma sumCongr_coe (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    sumCongr φ ψ = Sum.map φ ψ := rfl

/--
lemma `sumCongr_inl` / 引理 `sumCongr_inl`

English:
lemma sumCongr_inl
  given: (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n)
  proof: rfl

中文:
引理 sumCongr_inl
  条件: (φ : 微分同胚 I J M N n) (ψ : 微分同胚 I J M' N' n)
  证明: rfl
-/
lemma sumCongr_inl (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    (sumCongr φ ψ) ∘ Sum.inl = Sum.inl ∘ φ := rfl

/--
lemma `sumCongr_inr` / 引理 `sumCongr_inr`

English:
lemma sumCongr_inr
  given: (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n)
  proof: rfl

中文:
引理 sumCongr_inr
  条件: (φ : 微分同胚 I J M N n) (ψ : 微分同胚 I J M' N' n)
  证明: rfl
-/
lemma sumCongr_inr (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    (sumCongr φ ψ) ∘ Sum.inr = Sum.inr ∘ ψ := rfl

variable (I M M' n) in
/--
Definition of `sumComm` / `sumComm` 的定义

English:
definition sumComm
  signature: : Diffeomorph I I (M oplus M') (M' oplus M) n where
  body: Equiv.sumComm M M'
  contMDiff_toFun := ContMDiff.swap
  contMDiff_invFun := ContMDiff.swap

@[simp, mfld_simps]

中文:
定义 sumComm
  签名: : 微分同胚 I I (M oplus M') (M' oplus M) n where
  定义体: Equiv.sumComm M M'
  contMDiff_toFun := ContMDiff.swap
  contMDiff_invFun := ContMDiff.swap

@[simp, mfld_simps]

Depends on / 依赖: Equiv.sumComm, sumComm
-/
def sumComm : Diffeomorph I I (M oplus M') (M' oplus M) n where
  toEquiv := Equiv.sumComm M M'
  contMDiff_toFun := ContMDiff.swap
  contMDiff_invFun := ContMDiff.swap

@[simp, mfld_simps]
/--
theorem `sumComm_coe` / 定理 `sumComm_coe`

English:
theorem sumComm_coe
  statement: (Diffeomorph.sumComm I M n M' : (M oplus M') -> (M' oplus M)) = Sum.swap
  proof: rfl

@[simp, mfld_simps]

中文:
定理 sumComm_coe
  结论: (微分同胚.sumComm I M n M' : (M oplus M') -> (M' oplus M)) = 和.swap
  证明: rfl

@[simp, mfld_simps]
-/
theorem sumComm_coe : (Diffeomorph.sumComm I M n M' : (M oplus M') -> (M' oplus M)) = Sum.swap := rfl

@[simp, mfld_simps]
/--
theorem `sumComm_symm` / 定理 `sumComm_symm`

English:
theorem sumComm_symm
  statement: (Diffeomorph.sumComm I M n M').symm = Diffeomorph.sumComm I M' n M
  proof: rfl

中文:
定理 sumComm_symm
  结论: (微分同胚.sumComm I M n M').symm = 微分同胚.sumComm I M' n M
  证明: rfl
-/
theorem sumComm_symm : (Diffeomorph.sumComm I M n M').symm = Diffeomorph.sumComm I M' n M := rfl

variable (I M M' n) in
/--
lemma `sumComm_inl` / 引理 `sumComm_inl`

English:
lemma sumComm_inl
  statement: (Diffeomorph.sumComm I M n M') ∘ Sum.inl = Sum.inr
  proof: by
  ext
  exact Sum.swap_inl

中文:
引理 sumComm_inl
  结论: (微分同胚.sumComm I M n M') ∘ 和.inl = 和.inr
  证明: by
  ext
  exact Sum.swap_inl

Depends on / 依赖: Sum.swap_inl, swap_inl
-/
lemma sumComm_inl : (Diffeomorph.sumComm I M n M') ∘ Sum.inl = Sum.inr := by
  ext
  exact Sum.swap_inl

variable (I M M' n) in
/--
lemma `sumComm_inr` / 引理 `sumComm_inr`

English:
lemma sumComm_inr
  statement: (Diffeomorph.sumComm I M n M') ∘ Sum.inr = Sum.inl
  proof: by
  ext
  exact Sum.swap_inr

中文:
引理 sumComm_inr
  结论: (微分同胚.sumComm I M n M') ∘ 和.inr = 和.inl
  证明: by
  ext
  exact Sum.swap_inr

Depends on / 依赖: Sum.swap_inr, swap_inr
-/
lemma sumComm_inr : (Diffeomorph.sumComm I M n M') ∘ Sum.inr = Sum.inl := by
  ext
  exact Sum.swap_inr

variable (I M M' M'' n) in
/--
Definition of `sumAssoc` / `sumAssoc` 的定义

English:
definition sumAssoc
  signature: : Diffeomorph I I ((M oplus M') oplus M'') (M oplus (M' oplus M'')) n where
  body: Equiv.sumAssoc M M' M''
  contMDiff_toFun := by
    apply ContMDiff.sumElim
    · exact contMDiff_id.sumMap ContMDiff.inl
    · exact ContMDiff.inr.comp ContMDiff.inr
  contMDiff_invFun := by
    apply ContMDiff.sumElim
    · exact ContMDiff.inl.comp ContMDiff.inl
    · exact ContMDiff.inr.sumMap co

中文:
定义 sumAssoc
  签名: : 微分同胚 I I ((M oplus M') oplus M'') (M oplus (M' oplus M'')) n where
  定义体: Equiv.sumAssoc M M' M''
  contMDiff_toFun := by
    apply ContMDiff.sumElim
    · exact contMDiff_id.sumMap ContMDiff.inl
    · exact ContMDiff.inr.comp ContMDiff.inr
  contMDiff_invFun := by
    apply ContMDiff.sumElim
    · exact ContMDiff.inl.comp ContMDiff.inl
    · exact ContMDiff.inr.sumMap co

Depends on / 依赖: Equiv.sumAssoc, sumAssoc
-/
def sumAssoc : Diffeomorph I I ((M oplus M') oplus M'') (M oplus (M' oplus M'')) n where
  toEquiv := Equiv.sumAssoc M M' M''
  contMDiff_toFun := by
    apply ContMDiff.sumElim
    · exact contMDiff_id.sumMap ContMDiff.inl
    · exact ContMDiff.inr.comp ContMDiff.inr
  contMDiff_invFun := by
    apply ContMDiff.sumElim
    · exact ContMDiff.inl.comp ContMDiff.inl
    · exact ContMDiff.inr.sumMap contMDiff_id

@[simp]
/--
theorem `sumAssoc_coe` / 定理 `sumAssoc_coe`

English:
theorem sumAssoc_coe
  proof: rfl

中文:
定理 sumAssoc_coe
  证明: rfl
-/
theorem sumAssoc_coe :
    (sumAssoc I M n M' M'' : (M oplus M') oplus M'' -> M oplus (M' oplus M'')) = Equiv.sumAssoc M M' M'' := rfl

variable (I M n) in
/--
Definition of `sumEmpty` / `sumEmpty` 的定义

English:
definition sumEmpty
  signature: [IsEmpty M']
  body: Equiv.sumEmpty M M'
  contMDiff_toFun := contMDiff_id.sumElim fun x => (IsEmpty.false x).elim
  contMDiff_invFun := ContMDiff.inl

@[simp, mfld_simps]

中文:
定义 sumEmpty
  签名: [是空 M']
  定义体: Equiv.sumEmpty M M'
  contMDiff_toFun := contMDiff_id.sumElim fun x => (IsEmpty.false x).elim
  contMDiff_invFun := ContMDiff.inl

@[simp, mfld_simps]

Depends on / 依赖: Equiv.sumEmpty, sumEmpty
-/
def sumEmpty [IsEmpty M'] : Diffeomorph I I (M oplus M') M n where
  toEquiv := Equiv.sumEmpty M M'
  contMDiff_toFun := contMDiff_id.sumElim fun x => (IsEmpty.false x).elim
  contMDiff_invFun := ContMDiff.inl

@[simp, mfld_simps]
/--
theorem `sumEmpty_toEquiv` / 定理 `sumEmpty_toEquiv`

English:
theorem sumEmpty_toEquiv
  given: [IsEmpty M']
  statement: (sumEmpty I M n).toEquiv = Equiv.sumEmpty M M'
  proof: rfl

@[simp, mfld_simps]

中文:
定理 sumEmpty_toEquiv
  条件: [是空 M']
  结论: (sumEmpty I M n).toEquiv = 等价.sumEmpty M M'
  证明: rfl

@[simp, mfld_simps]
-/
theorem sumEmpty_toEquiv [IsEmpty M'] : (sumEmpty I M n).toEquiv = Equiv.sumEmpty M M' := rfl

@[simp, mfld_simps]
/--
lemma `sumEmpty_apply_inl` / 引理 `sumEmpty_apply_inl`

English:
lemma sumEmpty_apply_inl
  given: [IsEmpty M'] (x : M)
  statement: (sumEmpty I M (M' := M') n) (Sum.inl x) = x
  proof: rfl

中文:
引理 sumEmpty_apply_inl
  条件: [是空 M'] (x : M)
  结论: (sumEmpty I M (M' := M') n) (和.inl x) = x
  证明: rfl

Depends on / 依赖: Sum.inl
-/
lemma sumEmpty_apply_inl [IsEmpty M'] (x : M) : (sumEmpty I M (M' := M') n) (Sum.inl x) = x := rfl

/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: [IsEmpty M] [IsEmpty M']
  body: Equiv.equivOfIsEmpty M M'
  contMDiff_toFun x := (IsEmpty.false x).elim
  contMDiff_invFun x := (IsEmpty.false x).elim

中文:
定义 empty
  签名: [是空 M] [是空 M']
  定义体: Equiv.equivOfIsEmpty M M'
  contMDiff_toFun x := (IsEmpty.false x).elim
  contMDiff_invFun x := (IsEmpty.false x).elim
-/
protected def empty [IsEmpty M] [IsEmpty M'] : Diffeomorph I I M M' n where
  __ := Equiv.equivOfIsEmpty M M'
  contMDiff_toFun x := (IsEmpty.false x).elim
  contMDiff_invFun x := (IsEmpty.false x).elim

end disjointUnion

end Constructions

end Diffeomorph
