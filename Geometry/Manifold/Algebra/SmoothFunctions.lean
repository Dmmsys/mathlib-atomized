/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Algebraic structures over `C^n` functions

In this file, we define instances of algebraic structures over `C^n` functions.
-/

@[expose] public section


noncomputable section

open scoped Manifold ContDiff

open TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N']
  {n : Nat∞ω}

namespace ContMDiffMap

@[to_additive]
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G]
  body: ⟨fun f g => ⟨f * g, f.contMDiff.mul g.contMDiff⟩⟩

@[to_additive (attr := simp)]

中文:
实例 instMul
  签名: {G : 类型} [乘法 G] [拓扑空间 G] [Charted空间 H' G]
  定义体: ⟨fun f g => ⟨f * g, f.contMDiff.mul g.contMDiff⟩⟩

@[to_additive (attr := simp)]
-/
protected instance instMul {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : Mul C^n⟮I, N; I', G⟯ :=
  ⟨fun f g => ⟨f * g, f.contMDiff.mul g.contMDiff⟩⟩

@[to_additive (attr := simp)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  statement: {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffMul I' n G]
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mul
  结论: {G : 类型} [乘法 G] [拓扑空间 G] [Charted空间 H' G] [余ntMDiffMul I' n G]
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mul {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffMul I' n G]
    (f g : C^n⟮I, N; I', G⟯) : ⇑(f * g) = f * g :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mul_comp` / 定理 `mul_comp`

English:
theorem mul_comp
  statement: {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffMul I' n G]
  proof: rfl

@[to_additive]

中文:
定理 mul_comp
  结论: {G : 类型} [乘法 G] [拓扑空间 G] [Charted空间 H' G] [余ntMDiffMul I' n G]
  证明: rfl

@[to_additive]
-/
theorem mul_comp {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffMul I' n G]
    (f g : C^n⟮I'', N'; I', G⟯) (h : C^n⟮I, N; I'', N'⟯) : (f * g).comp h = f.comp h * g.comp h :=
  rfl

@[to_additive]
/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: {G : Type*} [One G] [TopologicalSpace G] [ChartedSpace H' G]
  body: ⟨ContMDiffMap.const (1 : G)⟩

@[to_additive (attr := simp)]

中文:
实例 instOne
  签名: {G : 类型} [幺 G] [拓扑空间 G] [Charted空间 H' G]
  定义体: ⟨ContMDiffMap.const (1 : G)⟩

@[to_additive (attr := simp)]
-/
protected instance instOne {G : Type*} [One G] [TopologicalSpace G] [ChartedSpace H' G] :
    One C^n⟮I, N; I', G⟯ :=
  ⟨ContMDiffMap.const (1 : G)⟩

@[to_additive (attr := simp)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  given: {G : Type*} [One G] [TopologicalSpace G] [ChartedSpace H' G]
  proof: rfl

@[to_additive]

中文:
定理 coe_one
  条件: {G : 类型} [幺 G] [拓扑空间 G] [Charted空间 H' G]
  证明: rfl

@[to_additive]
-/
theorem coe_one {G : Type*} [One G] [TopologicalSpace G] [ChartedSpace H' G] :
    ⇑(1 : C^n⟮I, N; I', G⟯) = 1 :=
  rfl

@[to_additive]
/--
Instance `instPow` / 实例 `instPow`

English:
instance instPow
  signature: {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
  body: ⟨(f : N -> G) ^ n, (contMDiff_pow n).comp f.contMDiff⟩

@[to_additive (attr := simp)]

中文:
实例 instPow
  签名: {G : 类型} [幺半群 G] [拓扑空间 G] [Charted空间 H' G]
  定义体: ⟨(f : N -> G) ^ n, (contMDiff_pow n).comp f.contMDiff⟩

@[to_additive (attr := simp)]

Depends on / 依赖: contMDiff, contMDiff_pow, f.contMDiff
-/
instance instPow {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] :
    Pow C^n⟮I, N; I', G⟯ Nat where
  pow f n := ⟨(f : N -> G) ^ n, (contMDiff_pow n).comp f.contMDiff⟩

@[to_additive (attr := simp)]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  statement: {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
  proof: rfl

中文:
定理 coe_pow
  结论: {G : 类型} [幺半群 G] [拓扑空间 G] [Charted空间 H' G]
  证明: rfl
-/
theorem coe_pow {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] (f : C^n⟮I, N; I', G⟯) (n : Nat) :
    ⇑(f ^ n) = (f : N -> G) ^ n :=
  rfl

section GroupStructure

/-!
### Group structure

In this section we show that `C^n` functions valued in a Lie group inherit a group structure
under pointwise multiplication.
-/

@[to_additive]
/--
Instance `semigroup` / 实例 `semigroup`

English:
instance semigroup
  signature: {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H' G]
  body: DFunLike.coe_injective.semigroup _ coe_mul

@[to_additive]

中文:
实例 semigroup
  签名: {G : 类型} [半群 G] [拓扑空间 G] [Charted空间 H' G]
  定义体: DFunLike.coe_injective.semigroup _ coe_mul

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.semigroup, coe_injective, coe_mul, semigroup
-/
instance semigroup {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : Semigroup C^n⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.semigroup _ coe_mul

@[to_additive]
/--
Instance `monoid` / 实例 `monoid`

English:
instance monoid
  signature: {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
  body: DFunLike.coe_injective.monoid _ coe_one coe_mul coe_pow

中文:
实例 monoid
  签名: {G : 类型} [幺半群 G] [拓扑空间 G] [Charted空间 H' G]
  定义体: DFunLike.coe_injective.monoid _ coe_one coe_mul coe_pow

Depends on / 依赖: DFunLike, DFunLike.coe_injective.monoid, coe_injective, coe_mul, coe_one, coe_pow, monoid
-/
instance monoid {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : Monoid C^n⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.monoid _ coe_one coe_mul coe_pow

/-- Coercion to a function as a `MonoidHom`. Similar to `MonoidHom.coeFn`. -/
@[to_additive (attr := simps) /-- Coercion to a function as an `AddMonoidHom`.
  Similar to `AddMonoidHom.coeFn`. -/]
/--
Definition of `coeFnMonoidHom` / `coeFnMonoidHom` 的定义

English:
definition coeFnMonoidHom
  signature: {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
  body: DFunLike.coe
  map_one' := coe_one
  map_mul' := coe_mul

中文:
定义 coeFnMonoidHom
  签名: {G : 类型} [幺半群 G] [拓扑空间 G] [Charted空间 H' G]
  定义体: DFunLike.coe
  map_one' := coe_one
  map_mul' := coe_mul

Depends on / 依赖: DFunLike, DFunLike.coe
-/
def coeFnMonoidHom {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : C^n⟮I, N; I', G⟯ ->* N -> G where
  toFun := DFunLike.coe
  map_one' := coe_one
  map_mul' := coe_mul

variable (I N)

/-- For a manifold `N` and a `C^n` homomorphism `φ` between Lie groups `G'`, `G''`, the
'left-composition-by-`φ`' group homomorphism from `C^n⟮I, N; I', G'⟯` to `C^n⟮I, N; I'', G''⟯`. -/
@[to_additive /-- For a manifold `N` and a `C^n` homomorphism `φ` between additive Lie groups `G'`,
`G''`, the 'left-composition-by-`φ`' group homomorphism from `C^n⟮I, N; I', G'⟯` to
`C^n⟮I, N; I'', G''⟯`. -/]
/--
Definition of `compLeftMonoidHom` / `compLeftMonoidHom` 的定义

English:
definition compLeftMonoidHom
  signature: {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H' G']
  body: ⟨φ ∘ f, hφ.comp f.contMDiff⟩
  map_one' := by ext; change φ 1 = 1; simp
  map_mul' f g := by ext x; change φ (f x * g x) = φ (f x) * φ (g x); simp

中文:
定义 compLeftMonoidHom
  签名: {G' : 类型} [幺半群 G'] [拓扑空间 G'] [Charted空间 H' G']
  定义体: ⟨φ ∘ f, hφ.comp f.contMDiff⟩
  map_one' := by ext; change φ 1 = 1; simp
  map_mul' f g := by ext x; change φ (f x * g x) = φ (f x) * φ (g x); simp

Depends on / 依赖: contMDiff, f.contMDiff
-/
def compLeftMonoidHom {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H' G']
    [ContMDiffMul I' n G'] {G'' : Type*} [Monoid G''] [TopologicalSpace G''] [ChartedSpace H'' G'']
    [ContMDiffMul I'' n G''] (φ : G' ->* G'') (hφ : CMDiff n φ) :
    C^n⟮I, N; I', G'⟯ ->* C^n⟮I, N; I'', G''⟯ where
  toFun f := ⟨φ ∘ f, hφ.comp f.contMDiff⟩
  map_one' := by ext; change φ 1 = 1; simp
  map_mul' f g := by ext x; change φ (f x * g x) = φ (f x) * φ (g x); simp

variable (I') {N}

-- TODO: generalize to any `C^n` map instead of `Set.inclusion`
/-- For a Lie group `G` and open sets `U ⊆ V` in `N`, the 'restriction' group homomorphism from
`C^n⟮I, V; I', G⟯` to `C^n⟮I, U; I', G⟯`. -/
@[to_additive /-- For an additive Lie group `G` and open sets `U ⊆ V` in `N`, the 'restriction'
group homomorphism from `C^n⟮I, V; I', G⟯` to `C^n⟮I, U; I', G⟯`. -/]
/--
Definition of `restrictMonoidHom` / `restrictMonoidHom` 的定义

English:
definition restrictMonoidHom
  signature: (G : Type*) [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
  body: ⟨f ∘ Set.inclusion h, f.contMDiff.comp (contMDiff_inclusion h)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 restrictMonoidHom
  签名: (G : 类型) [幺半群 G] [拓扑空间 G] [Charted空间 H' G]
  定义体: ⟨f ∘ Set.inclusion h, f.contMDiff.comp (contMDiff_inclusion h)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: Set.inclusion, contMDiff, contMDiff_inclusion, f.contMDiff.comp, inclusion
-/
def restrictMonoidHom (G : Type*) [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] {U V : Opens N} (h : U <= V) : C^n⟮I, V; I', G⟯ ->* C^n⟮I, U; I', G⟯ where
  toFun f := ⟨f ∘ Set.inclusion h, f.contMDiff.comp (contMDiff_inclusion h)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {I I'}

@[to_additive]
/--
Instance `commMonoid` / 实例 `commMonoid`

English:
instance commMonoid
  signature: {G : Type*} [CommMonoid G] [TopologicalSpace G] [ChartedSpace H' G]
  body: DFunLike.coe_injective.commMonoid _ coe_one coe_mul coe_pow

@[to_additive]

中文:
实例 commMonoid
  签名: {G : 类型} [交换幺半群 G] [拓扑空间 G] [Charted空间 H' G]
  定义体: DFunLike.coe_injective.commMonoid _ coe_one coe_mul coe_pow

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.commMonoid, coe_injective, coe_mul, coe_one, coe_pow, commMonoid
-/
instance commMonoid {G : Type*} [CommMonoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : CommMonoid C^n⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.commMonoid _ coe_one coe_mul coe_pow

@[to_additive]
/--
Instance `group` / 实例 `group`

English:
instance group
  signature: {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G]
  body: { ContMDiffMap.monoid with
    inv := fun f => ⟨fun x => (f x)⁻¹, f.contMDiff.inv⟩
    inv_mul_cancel := fun a => by ext; exact inv_mul_cancel _
    div := fun f g => ⟨f / g, f.contMDiff.div g.contMDiff⟩
    div_eq_mul_inv := fun f g => by ext; exact div_eq_mul_inv _ _ }

@[to_additive (attr := simp

中文:
实例 group
  签名: {G : 类型} [群 G] [拓扑空间 G] [Charted空间 H' G] [Lie群 I' n G]
  定义体: { ContMDiffMap.monoid with
    inv := fun f => ⟨fun x => (f x)⁻¹, f.contMDiff.inv⟩
    inv_mul_cancel := fun a => by ext; exact inv_mul_cancel _
    div := fun f g => ⟨f / g, f.contMDiff.div g.contMDiff⟩
    div_eq_mul_inv := fun f g => by ext; exact div_eq_mul_inv _ _ }

@[to_additive (attr := simp

Depends on / 依赖: ContMDiffMap, ContMDiffMap.monoid, contMDiff, div_eq_mul_inv, f.contMDiff.div, f.contMDiff.inv, g.contMDiff, inv_mul_cancel, monoid
-/
instance group {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G] :
    Group C^n⟮I, N; I', G⟯ :=
  { ContMDiffMap.monoid with
    inv := fun f => ⟨fun x => (f x)⁻¹, f.contMDiff.inv⟩
    inv_mul_cancel := fun a => by ext; exact inv_mul_cancel _
    div := fun f g => ⟨f / g, f.contMDiff.div g.contMDiff⟩
    div_eq_mul_inv := fun f g => by ext; exact div_eq_mul_inv _ _ }

@[to_additive (attr := simp)]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  statement: {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G]
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_inv
  结论: {G : 类型} [群 G] [拓扑空间 G] [Charted空间 H' G] [Lie群 I' n G]
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_inv {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G]
    (f : C^n⟮I, N; I', G⟯) : ⇑f⁻¹ = (⇑f)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  statement: {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G]
  proof: rfl

@[to_additive]

中文:
定理 coe_div
  结论: {G : 类型} [群 G] [拓扑空间 G] [Charted空间 H' G] [Lie群 I' n G]
  证明: rfl

@[to_additive]
-/
theorem coe_div {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G]
    (f g : C^n⟮I, N; I', G⟯) : ⇑(f / g) = f / g :=
  rfl

@[to_additive]
/--
Instance `commGroup` / 实例 `commGroup`

English:
instance commGroup
  signature: {G : Type*} [CommGroup G] [TopologicalSpace G] [ChartedSpace H' G]
  body: { ContMDiffMap.group, ContMDiffMap.commMonoid with }

中文:
实例 commGroup
  签名: {G : 类型} [交换群 G] [拓扑空间 G] [Charted空间 H' G]
  定义体: { ContMDiffMap.group, ContMDiffMap.commMonoid with }

Depends on / 依赖: ContMDiffMap, ContMDiffMap.commMonoid, ContMDiffMap.group, commMonoid
-/
instance commGroup {G : Type*} [CommGroup G] [TopologicalSpace G] [ChartedSpace H' G]
    [LieGroup I' n G] : CommGroup C^n⟮I, N; I', G⟯ :=
  { ContMDiffMap.group, ContMDiffMap.commMonoid with }

end GroupStructure

section RingStructure



/--
Instance `semiring` / 实例 `semiring`

English:
instance semiring
  signature: {R : Type*} [Semiring R] [TopologicalSpace R] [ChartedSpace H' R]
  body: { ContMDiffMap.addCommMonoid,
    ContMDiffMap.monoid with
    left_distrib := fun a b c => by ext; exact left_distrib _ _ _
    right_distrib := fun a b c => by ext; exact right_distrib _ _ _
    zero_mul := fun a => by ext; exact zero_mul _
    mul_zero := fun a => by ext; exact mul_zero _ }

中文:
实例 semiring
  签名: {R : 类型} [半环 R] [拓扑空间 R] [Charted空间 H' R]
  定义体: { ContMDiffMap.addCommMonoid,
    ContMDiffMap.monoid with
    left_distrib := fun a b c => by ext; exact left_distrib _ _ _
    right_distrib := fun a b c => by ext; exact right_distrib _ _ _
    zero_mul := fun a => by ext; exact zero_mul _
    mul_zero := fun a => by ext; exact mul_zero _ }

Depends on / 依赖: ContMDiffMap, ContMDiffMap.addCommMonoid, ContMDiffMap.monoid, addCommMonoid, left_distrib, monoid, mul_zero, right_distrib, zero_mul
-/
instance semiring {R : Type*} [Semiring R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] : Semiring C^n⟮I, N; I', R⟯ :=
  { ContMDiffMap.addCommMonoid,
    ContMDiffMap.monoid with
    left_distrib := fun a b c => by ext; exact left_distrib _ _ _
    right_distrib := fun a b c => by ext; exact right_distrib _ _ _
    zero_mul := fun a => by ext; exact zero_mul _
    mul_zero := fun a => by ext; exact mul_zero _ }

/--
Instance `ring` / 实例 `ring`

English:
instance ring
  signature: {R : Type*} [Ring R] [TopologicalSpace R] [ChartedSpace H' R] [ContMDiffRing I' n R]
  body: { ContMDiffMap.semiring, ContMDiffMap.addCommGroup with }

中文:
实例 ring
  签名: {R : 类型} [环 R] [拓扑空间 R] [Charted空间 H' R] [余ntMDiff环 I' n R]
  定义体: { ContMDiffMap.semiring, ContMDiffMap.addCommGroup with }

Depends on / 依赖: ContMDiffMap, ContMDiffMap.addCommGroup, ContMDiffMap.semiring, addCommGroup, semiring
-/
instance ring {R : Type*} [Ring R] [TopologicalSpace R] [ChartedSpace H' R] [ContMDiffRing I' n R] :
    Ring C^n⟮I, N; I', R⟯ :=
  { ContMDiffMap.semiring, ContMDiffMap.addCommGroup with }

/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
  body: { ContMDiffMap.semiring, ContMDiffMap.addCommGroup, ContMDiffMap.commMonoid with }

中文:
实例 commRing
  签名: {R : 类型} [交换环 R] [拓扑空间 R] [Charted空间 H' R]
  定义体: { ContMDiffMap.semiring, ContMDiffMap.addCommGroup, ContMDiffMap.commMonoid with }

Depends on / 依赖: ContMDiffMap, ContMDiffMap.addCommGroup, ContMDiffMap.commMonoid, ContMDiffMap.semiring, addCommGroup, commMonoid, semiring
-/
instance commRing {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] : CommRing C^n⟮I, N; I', R⟯ :=
  { ContMDiffMap.semiring, ContMDiffMap.addCommGroup, ContMDiffMap.commMonoid with }

variable (I N)

/--
Definition of `compLeftRingHom` / `compLeftRingHom` 的定义

English:
definition compLeftRingHom
  signature: {R' : Type*} [Ring R'] [TopologicalSpace R'] [ChartedSpace H' R']
  body: { ContMDiffMap.compLeftMonoidHom I N φ.toMonoidHom hφ,
    ContMDiffMap.compLeftAddMonoidHom I N φ.toAddMonoidHom hφ with
    toFun := fun f => ⟨φ ∘ f, hφ.comp f.contMDiff⟩ }

中文:
定义 compLeftRingHom
  签名: {R' : 类型} [环 R'] [拓扑空间 R'] [Charted空间 H' R']
  定义体: { ContMDiffMap.compLeftMonoidHom I N φ.toMonoidHom hφ,
    ContMDiffMap.compLeftAddMonoidHom I N φ.toAddMonoidHom hφ with
    toFun := fun f => ⟨φ ∘ f, hφ.comp f.contMDiff⟩ }

Depends on / 依赖: ContMDiffMap, ContMDiffMap.compLeftAddMonoidHom, ContMDiffMap.compLeftMonoidHom, compLeftAddMonoidHom, compLeftMonoidHom, contMDiff, f.contMDiff, toAddMonoidHom, toMonoidHom
-/
def compLeftRingHom {R' : Type*} [Ring R'] [TopologicalSpace R'] [ChartedSpace H' R']
    [ContMDiffRing I' n R'] {R'' : Type*} [Ring R''] [TopologicalSpace R''] [ChartedSpace H'' R'']
    [ContMDiffRing I'' n R''] (φ : R' ->+* R'') (hφ : CMDiff n φ) :
    C^n⟮I, N; I', R'⟯ ->+* C^n⟮I, N; I'', R''⟯ :=
  { ContMDiffMap.compLeftMonoidHom I N φ.toMonoidHom hφ,
    ContMDiffMap.compLeftAddMonoidHom I N φ.toAddMonoidHom hφ with
    toFun := fun f => ⟨φ ∘ f, hφ.comp f.contMDiff⟩ }

variable (I') {N}

/--
Definition of `restrictRingHom` / `restrictRingHom` 的定义

English:
definition restrictRingHom
  signature: (R : Type*) [Ring R] [TopologicalSpace R] [ChartedSpace H' R]
  body: { ContMDiffMap.restrictMonoidHom I I' R h, ContMDiffMap.restrictAddMonoidHom I I' R h with
    toFun := fun f => ⟨f ∘ Set.inclusion h, f.contMDiff.comp (contMDiff_inclusion h)⟩ }

中文:
定义 restrictRingHom
  签名: (R : 类型) [环 R] [拓扑空间 R] [Charted空间 H' R]
  定义体: { ContMDiffMap.restrictMonoidHom I I' R h, ContMDiffMap.restrictAddMonoidHom I I' R h with
    toFun := fun f => ⟨f ∘ Set.inclusion h, f.contMDiff.comp (contMDiff_inclusion h)⟩ }

Depends on / 依赖: ContMDiffMap, ContMDiffMap.restrictAddMonoidHom, ContMDiffMap.restrictMonoidHom, Set.inclusion, contMDiff, contMDiff_inclusion, f.contMDiff.comp, inclusion, restrictAddMonoidHom, restrictMonoidHom
-/
def restrictRingHom (R : Type*) [Ring R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] {U V : Opens N} (h : U <= V) :
    C^n⟮I, V; I', R⟯ ->+* C^n⟮I, U; I', R⟯ :=
  { ContMDiffMap.restrictMonoidHom I I' R h, ContMDiffMap.restrictAddMonoidHom I I' R h with
    toFun := fun f => ⟨f ∘ Set.inclusion h, f.contMDiff.comp (contMDiff_inclusion h)⟩ }

variable {I I'}

/-- Coercion to a function as a `RingHom`. -/
@[simps]
/--
Definition of `coeFnRingHom` / `coeFnRingHom` 的定义

English:
definition coeFnRingHom
  signature: {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
  body: { (coeFnMonoidHom : C^n⟮I, N; I', R⟯ ->* _), (coeFnAddMonoidHom : C^n⟮I, N; I', R⟯ ->+ _) with
    toFun := (↑) }

中文:
定义 coeFnRingHom
  签名: {R : 类型} [交换环 R] [拓扑空间 R] [Charted空间 H' R]
  定义体: { (coeFnMonoidHom : C^n⟮I, N; I', R⟯ ->* _), (coeFnAddMonoidHom : C^n⟮I, N; I', R⟯ ->+ _) with
    toFun := (↑) }

Depends on / 依赖: coeFnAddMonoidHom, coeFnMonoidHom
-/
def coeFnRingHom {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] : C^n⟮I, N; I', R⟯ ->+* N -> R :=
  { (coeFnMonoidHom : C^n⟮I, N; I', R⟯ ->* _), (coeFnAddMonoidHom : C^n⟮I, N; I', R⟯ ->+ _) with
    toFun := (↑) }

/--
Definition of `evalRingHom` / `evalRingHom` 的定义

English:
definition evalRingHom
  signature: {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
  body: (Pi.evalRingHom _ m : (N -> R) ->+* R).comp ContMDiffMap.coeFnRingHom

中文:
定义 evalRingHom
  签名: {R : 类型} [交换环 R] [拓扑空间 R] [Charted空间 H' R]
  定义体: (Pi.evalRingHom _ m : (N -> R) ->+* R).comp ContMDiffMap.coeFnRingHom

Depends on / 依赖: ContMDiffMap, ContMDiffMap.coeFnRingHom, Pi.evalRingHom, coeFnRingHom, evalRingHom
-/
def evalRingHom {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] (m : N) : C^n⟮I, N; I', R⟯ ->+* R :=
  (Pi.evalRingHom _ m : (N -> R) ->+* R).comp ContMDiffMap.coeFnRingHom

end RingStructure

section ModuleStructure



/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  body: ⟨fun r f => ⟨r • ⇑f, contMDiff_const.smul (I := 𝓘(𝕜)) f.contMDiff⟩⟩

@[simp]

中文:
实例 instSMul
  签名: {V : 类型} [赋范交换加群 V] [赋范空间 𝕜 V]
  定义体: ⟨fun r f => ⟨r • ⇑f, contMDiff_const.smul (I := 𝓘(𝕜)) f.contMDiff⟩⟩

@[simp]

Depends on / 依赖: contMDiff, contMDiff_const, contMDiff_const.smul, f.contMDiff
-/
instance instSMul {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    SMul 𝕜 C^n⟮I, N; 𝓘(𝕜, V), V⟯ :=
  ⟨fun r f => ⟨r • ⇑f, contMDiff_const.smul (I := 𝓘(𝕜)) f.contMDiff⟩⟩

@[simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  statement: {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (r : 𝕜)
  proof: rfl

@[simp]

中文:
定理 coe_smul
  结论: {V : 类型} [赋范交换加群 V] [赋范空间 𝕜 V] (r : 𝕜)
  证明: rfl

@[simp]
-/
theorem coe_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (r : 𝕜)
    (f : C^n⟮I, N; 𝓘(𝕜, V), V⟯) : ⇑(r • f) = r • ⇑f :=
  rfl

@[simp]
/--
theorem `smul_comp` / 定理 `smul_comp`

English:
theorem smul_comp
  statement: {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (r : 𝕜)
  proof: rfl

中文:
定理 smul_comp
  结论: {V : 类型} [赋范交换加群 V] [赋范空间 𝕜 V] (r : 𝕜)
  证明: rfl
-/
theorem smul_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (r : 𝕜)
    (g : C^n⟮I'', N'; 𝓘(𝕜, V), V⟯) (h : C^n⟮I, N; I'', N'⟯) : (r • g).comp h = r • g.comp h :=
  rfl

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  body: Function.Injective.module 𝕜 coeFnAddMonoidHom ContMDiffMap.coe_injective coe_smul

中文:
实例 module
  签名: {V : 类型} [赋范交换加群 V] [赋范空间 𝕜 V]
  定义体: Function.Injective.module 𝕜 coeFnAddMonoidHom ContMDiffMap.coe_injective coe_smul

Depends on / 依赖: ContMDiffMap, ContMDiffMap.coe_injective, Function, Function.Injective.module, Injective, coeFnAddMonoidHom, coe_injective, coe_smul, module
-/
instance module {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    Module 𝕜 C^n⟮I, N; 𝓘(𝕜, V), V⟯ :=
  Function.Injective.module 𝕜 coeFnAddMonoidHom ContMDiffMap.coe_injective coe_smul

/-- Coercion to a function as a `LinearMap`. -/
@[simps]
/--
Definition of `coeFnLinearMap` / `coeFnLinearMap` 的定义

English:
definition coeFnLinearMap
  signature: {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  body: { (coeFnAddMonoidHom : C^n⟮I, N; 𝓘(𝕜, V), V⟯ ->+ _) with
    toFun := (↑)
    map_smul' := coe_smul }

中文:
定义 coeFnLinearMap
  签名: {V : 类型} [赋范交换加群 V] [赋范空间 𝕜 V]
  定义体: { (coeFnAddMonoidHom : C^n⟮I, N; 𝓘(𝕜, V), V⟯ ->+ _) with
    toFun := (↑)
    map_smul' := coe_smul }

Depends on / 依赖: coeFnAddMonoidHom, coe_smul, map_smul
-/
def coeFnLinearMap {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    C^n⟮I, N; 𝓘(𝕜, V), V⟯ ->ₗ[𝕜] N -> V :=
  { (coeFnAddMonoidHom : C^n⟮I, N; 𝓘(𝕜, V), V⟯ ->+ _) with
    toFun := (↑)
    map_smul' := coe_smul }

end ModuleStructure

section AlgebraStructure

/-!
### Algebra structure

In this section we show that `C^n` functions valued in a normed algebra `A` over a normed field `𝕜`
inherit an algebra structure.
-/


variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [ContMDiffRing 𝓘(𝕜, A) n A]

/--
Definition of `C` / `C` 的定义

English:
definition C
  signature: : 𝕜 ->+* C^n⟮I, N; 𝓘(𝕜, A), A⟯ where
  body: fun c : 𝕜 => ⟨fun _ => (algebraMap 𝕜 A) c, contMDiff_const⟩
  map_one' := by ext; exact (algebraMap 𝕜 A).map_one
  map_mul' c₁ c₂ := by ext; exact (algebraMap 𝕜 A).map_mul _ _
  map_zero' := by ext; exact (algebraMap 𝕜 A).map_zero
  map_add' c₁ c₂ := by ext; exact (algebraMap 𝕜 A).map_add _ _

中文:
定义 C
  签名: : 𝕜 ->+* C^n⟮I, N; 𝓘(𝕜, A), A⟯ where
  定义体: fun c : 𝕜 => ⟨fun _ => (algebraMap 𝕜 A) c, contMDiff_const⟩
  map_one' := by ext; exact (algebraMap 𝕜 A).map_one
  map_mul' c₁ c₂ := by ext; exact (algebraMap 𝕜 A).map_mul _ _
  map_zero' := by ext; exact (algebraMap 𝕜 A).map_zero
  map_add' c₁ c₂ := by ext; exact (algebraMap 𝕜 A).map_add _ _

Depends on / 依赖: algebraMap, contMDiff_const
-/
def C : 𝕜 ->+* C^n⟮I, N; 𝓘(𝕜, A), A⟯ where
  toFun := fun c : 𝕜 => ⟨fun _ => (algebraMap 𝕜 A) c, contMDiff_const⟩
  map_one' := by ext; exact (algebraMap 𝕜 A).map_one
  map_mul' c₁ c₂ := by ext; exact (algebraMap 𝕜 A).map_mul _ _
  map_zero' := by ext; exact (algebraMap 𝕜 A).map_zero
  map_add' c₁ c₂ := by ext; exact (algebraMap 𝕜 A).map_add _ _

/--
Instance `algebra` / 实例 `algebra`

English:
instance algebra
  signature: : Algebra 𝕜 C^n⟮I, N; 𝓘(𝕜, A), A⟯ where
  body: fun r f => ⟨r • f, contMDiff_const.smul (I := 𝓘(𝕜)) f.contMDiff⟩
  algebraMap := ContMDiffMap.C
  commutes' := fun c f => by ext x; exact Algebra.commutes' _ _
  smul_def' := fun c f => by ext x; exact Algebra.smul_def' _ _

中文:
实例 algebra
  签名: : 代数 𝕜 C^n⟮I, N; 𝓘(𝕜, A), A⟯ where
  定义体: fun r f => ⟨r • f, contMDiff_const.smul (I := 𝓘(𝕜)) f.contMDiff⟩
  algebraMap := ContMDiffMap.C
  commutes' := fun c f => by ext x; exact Algebra.commutes' _ _
  smul_def' := fun c f => by ext x; exact Algebra.smul_def' _ _

Depends on / 依赖: contMDiff, contMDiff_const, contMDiff_const.smul, f.contMDiff
-/
instance algebra : Algebra 𝕜 C^n⟮I, N; 𝓘(𝕜, A), A⟯ where
  smul := fun r f => ⟨r • f, contMDiff_const.smul (I := 𝓘(𝕜)) f.contMDiff⟩
  algebraMap := ContMDiffMap.C
  commutes' := fun c f => by ext x; exact Algebra.commutes' _ _
  smul_def' := fun c f => by ext x; exact Algebra.smul_def' _ _

/-- Coercion to a function as an `AlgHom`. -/
@[simps]
/--
Definition of `coeFnAlgHom` / `coeFnAlgHom` 的定义

English:
definition coeFnAlgHom
  signature: : C^n⟮I, N; 𝓘(𝕜, A), A⟯ ->ₐ[𝕜] N -> A where
  body: (↑)
  commutes' _ := rfl
  -- `(ContMDiffMap.coeFnRingHom : C^n⟮I, N; 𝓘(𝕜, A), A⟯ →+* _) with` times out for some reason
  map_zero' := ContMDiffMap.coe_zero
  map_one' := ContMDiffMap.coe_one
  map_add' := ContMDiffMap.coe_add
  map_mul' := ContMDiffMap.coe_mul

中文:
定义 coeFnAlgHom
  签名: : C^n⟮I, N; 𝓘(𝕜, A), A⟯ ->ₐ[𝕜] N -> A where
  定义体: (↑)
  commutes' _ := rfl
  -- `(ContMDiffMap.coeFnRingHom : C^n⟮I, N; 𝓘(𝕜, A), A⟯ →+* _) with` times out for some reason
  map_zero' := ContMDiffMap.coe_zero
  map_one' := ContMDiffMap.coe_one
  map_add' := ContMDiffMap.coe_add
  map_mul' := ContMDiffMap.coe_mul
-/
def coeFnAlgHom : C^n⟮I, N; 𝓘(𝕜, A), A⟯ ->ₐ[𝕜] N -> A where
  toFun := (↑)
  commutes' _ := rfl
  -- `(ContMDiffMap.coeFnRingHom : C^n⟮I, N; 𝓘(𝕜, A), A⟯ →+* _) with` times out for some reason
  map_zero' := ContMDiffMap.coe_zero
  map_one' := ContMDiffMap.coe_one
  map_add' := ContMDiffMap.coe_add
  map_mul' := ContMDiffMap.coe_mul

end AlgebraStructure

section ModuleOverContinuousFunctions

/-!
### Structure as module over scalar functions

If `V` is a module over `𝕜`, then we show that the space of `C^n` functions from `N` to `V`
is naturally a vector space over the ring of `C^n` functions from `N` to `𝕜`. -/

/--
Instance `instSMul'` / 实例 `instSMul'`

English:
instance instSMul'
  signature: {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  body: ⟨fun f g => ⟨fun x => f x • g x, ContMDiff.smul f.2 g.2⟩⟩

中文:
实例 instSMul'
  签名: {V : 类型} [赋范交换加群 V] [赋范空间 𝕜 V]
  定义体: ⟨fun f g => ⟨fun x => f x • g x, ContMDiff.smul f.2 g.2⟩⟩

Depends on / 依赖: ContMDiff, ContMDiff.smul
-/
instance instSMul' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    SMul C^n⟮I, N; 𝕜⟯ C^n⟮I, N; 𝓘(𝕜, V), V⟯ :=
  ⟨fun f g => ⟨fun x => f x • g x, ContMDiff.smul f.2 g.2⟩⟩

/-- The left multiplication with a `C^n` scalar function commutes with composition. -/
@[simp]
/--
theorem `smul_comp'` / 定理 `smul_comp'`

English:
theorem smul_comp'
  statement: {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (f : C^n⟮I'', N'; 𝕜⟯)
  proof: rfl

中文:
定理 smul_comp'
  结论: {V : 类型} [赋范交换加群 V] [赋范空间 𝕜 V] (f : C^n⟮I'', N'; 𝕜⟯)
  证明: rfl
-/
theorem smul_comp' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (f : C^n⟮I'', N'; 𝕜⟯)
    (g : C^n⟮I'', N'; 𝓘(𝕜, V), V⟯) (h : C^n⟮I, N; I'', N'⟯) :
    (f • g).comp h = f.comp h • g.comp h :=
  rfl

/--
Instance `module'` / 实例 `module'`

English:
instance module'
  signature: {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  body: by ext x; exact smul_add (c x) (f x) (g x)
  add_smul c₁ c₂ f := by ext x; exact add_smul (c₁ x) (c₂ x) (f x)
  mul_smul c₁ c₂ f := by ext x; exact mul_smul (c₁ x) (c₂ x) (f x)
  one_smul f := by ext x; exact one_smul 𝕜 (f x)
  zero_smul f := by ext x; exact zero_smul _ _
  smul_zero r := by ext x; 

中文:
实例 module'
  签名: {V : 类型} [赋范交换加群 V] [赋范空间 𝕜 V]
  定义体: by ext x; exact smul_add (c x) (f x) (g x)
  add_smul c₁ c₂ f := by ext x; exact add_smul (c₁ x) (c₂ x) (f x)
  mul_smul c₁ c₂ f := by ext x; exact mul_smul (c₁ x) (c₂ x) (f x)
  one_smul f := by ext x; exact one_smul 𝕜 (f x)
  zero_smul f := by ext x; exact zero_smul _ _
  smul_zero r := by ext x; 

Depends on / 依赖: add_smul, mul_smul, one_smul, smul_add, smul_zero, zero_smul
-/
instance module' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    Module C^n⟮I, N; 𝓘(𝕜), 𝕜⟯ C^n⟮I, N; 𝓘(𝕜, V), V⟯ where
  smul_add c f g := by ext x; exact smul_add (c x) (f x) (g x)
  add_smul c₁ c₂ f := by ext x; exact add_smul (c₁ x) (c₂ x) (f x)
  mul_smul c₁ c₂ f := by ext x; exact mul_smul (c₁ x) (c₂ x) (f x)
  one_smul f := by ext x; exact one_smul 𝕜 (f x)
  zero_smul f := by ext x; exact zero_smul _ _
  smul_zero r := by ext x; exact smul_zero _

end ModuleOverContinuousFunctions

end ContMDiffMap
