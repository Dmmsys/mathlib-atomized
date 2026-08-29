/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Hom.Ring
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Topology.LocallyConstant.Basic

/-! # Germs of functions between topological spaces

In this file, we prove basic properties of germs of functions between topological spaces,
with respect to the neighbourhood filter `𝓝 x`.

## Main definitions and results

* `Filter.Germ.value φ f`: value associated to the germ `φ` at a point `x`, w.r.t. the
  neighbourhood filter at `x`. This is the common value of all representatives of `φ` at `x`.
* `Filter.Germ.valueOrderRingHom` and friends: the map `Germ (𝓝 x) E → E` is a
  monoid homomorphism, 𝕜-linear map, ring homomorphism, monotone ring homomorphism

* `RestrictGermPredicate`: given a predicate on germs `P : Π x : X, germ (𝓝 x) Y → Prop` and
  `A : set X`, build a new predicate on germs `restrictGermPredicate P A` such that
  `(∀ x, RestrictGermPredicate P A x f) ↔ ∀ᶠ x near A, P x f`;
  `forall_restrictGermPredicate_iff` is this equivalence.

* `Filter.Germ.sliceLeft, sliceRight`: map the germ of functions `X × Y → Z` at `p = (x,y) ∈ X × Y`
  to the corresponding germ of functions `X → Z` at `x ∈ X` resp. `Y → Z` at `y ∈ Y`.
* `eq_of_germ_isConstant`: if each germ of `f : X → Y` is constant and `X` is pre-connected,
  `f` is constant.
-/

@[expose] public section

open scoped Topology

open Filter Set

variable {X Y Z : Type*} [TopologicalSpace X] {f g : X -> Y} {A : Set X} {x : X}

namespace Filter.Germ

/--
Definition of `value` / `value` 的定义

English:
definition value
  signature: {X α : Type*} [TopologicalSpace X] {x : X} (φ : Germ (𝓝 x) α)
  body: Quotient.liftOn' φ (fun f => f x) fun f g h => by rw [Eventually.self_of_nhds h]

@[simp]

中文:
定义 value
  签名: {X α : 类型} [拓扑空间 X] {x : X} (φ : Germ (𝓝 x) α)
  定义体: Quotient.liftOn' φ (fun f => f x) fun f g h => by rw [Eventually.self_of_nhds h]

@[simp]

Depends on / 依赖: Eventually, Eventually.self_of_nhds, Quotient, Quotient.liftOn, liftOn, self_of_nhds
-/
def value {X α : Type*} [TopologicalSpace X] {x : X} (φ : Germ (𝓝 x) α) : α :=
  Quotient.liftOn' φ (fun f => f x) fun f g h => by rw [Eventually.self_of_nhds h]

@[simp]
/--
theorem `value_ofFun` / 定理 `value_ofFun`

English:
theorem value_ofFun
  given: (f : X -> Y) (x : X)
  statement: value (f : Germ (𝓝 x) Y) = f x
  proof: rfl

@[simp]

中文:
定理 value_ofFun
  条件: (f : X -> Y) (x : X)
  结论: value (f : Germ (𝓝 x) Y) = f x
  证明: rfl

@[simp]
-/
theorem value_ofFun (f : X -> Y) (x : X) : value (f : Germ (𝓝 x) Y) = f x := rfl

@[simp]
/--
theorem `value_const` / 定理 `value_const`

English:
theorem value_const
  given: (c : Y) (x : X)
  statement: value (c : Germ (𝓝 x) Y) = c
  proof: rfl

中文:
定理 value_const
  条件: (c : Y) (x : X)
  结论: value (c : Germ (𝓝 x) Y) = c
  证明: rfl
-/
theorem value_const (c : Y) (x : X) : value (c : Germ (𝓝 x) Y) = c := rfl

/--
theorem `value_smul` / 定理 `value_smul`

English:
theorem value_smul
  statement: {α β : Type*} [SMul α β] (φ : Germ (𝓝 x) α)
  proof: Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ => rfl

中文:
定理 value_smul
  结论: {α β : 类型} [标量乘法 α β] (φ : Germ (𝓝 x) α)
  证明: Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ => rfl

Depends on / 依赖: Germ.inductionOn, inductionOn
-/
theorem value_smul {α β : Type*} [SMul α β] (φ : Germ (𝓝 x) α)
    (ψ : Germ (𝓝 x) β) : (φ • ψ).value = φ.value • ψ.value :=
  Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ => rfl

/-- The map `Germ (𝓝 x) E → E` into a monoid `E` as a monoid homomorphism -/
@[to_additive /-- The map `Germ (𝓝 x) E → E` as an additive monoid homomorphism -/]
/--
Definition of `valueMulHom` / `valueMulHom` 的定义

English:
definition valueMulHom
  signature: {X E : Type*} [Monoid E] [TopologicalSpace X] {x : X}
  body: Filter.Germ.value
  map_one' := rfl
  map_mul' φ ψ := Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ => rfl

中文:
定义 valueMulHom
  签名: {X E : 类型} [幺半群 E] [拓扑空间 X] {x : X}
  定义体: Filter.Germ.value
  map_one' := rfl
  map_mul' φ ψ := Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ => rfl

Depends on / 依赖: Filter, Filter.Germ.value
-/
def valueMulHom {X E : Type*} [Monoid E] [TopologicalSpace X] {x : X} : Germ (𝓝 x) E ->* E where
  toFun := Filter.Germ.value
  map_one' := rfl
  map_mul' φ ψ := Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ => rfl

/--
Definition of `valueₗ` / `valueₗ` 的定义

English:
definition valueₗ
  signature: {X 𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace X]
  body: Filter.Germ.valueAddHom
  map_smul' := fun _ φ => Germ.inductionOn φ fun _ => rfl

中文:
定义 valueₗ
  签名: {X 𝕜 E : 类型} [半环 𝕜] [加法交换幺半群 E] [模 𝕜 E] [拓扑空间 X]
  定义体: Filter.Germ.valueAddHom
  map_smul' := fun _ φ => Germ.inductionOn φ fun _ => rfl

Depends on / 依赖: Filter, Filter.Germ.valueAddHom, valueAddHom
-/
def valueₗ {X 𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace X]
    {x : X} : Germ (𝓝 x) E ->ₗ[𝕜] E where
  __ := Filter.Germ.valueAddHom
  map_smul' := fun _ φ => Germ.inductionOn φ fun _ => rfl

/--
Definition of `valueRingHom` / `valueRingHom` 的定义

English:
definition valueRingHom
  signature: {X E : Type*} [Semiring E] [TopologicalSpace X] {x : X}
  body: { Filter.Germ.valueMulHom, Filter.Germ.valueAddHom with }

中文:
定义 valueRingHom
  签名: {X E : 类型} [半环 E] [拓扑空间 X] {x : X}
  定义体: { Filter.Germ.valueMulHom, Filter.Germ.valueAddHom with }

Depends on / 依赖: Filter, Filter.Germ.valueAddHom, Filter.Germ.valueMulHom, valueAddHom, valueMulHom
-/
def valueRingHom {X E : Type*} [Semiring E] [TopologicalSpace X] {x : X} : Germ (𝓝 x) E ->+* E :=
  { Filter.Germ.valueMulHom, Filter.Germ.valueAddHom with }

/--
Definition of `valueOrderRingHom` / `valueOrderRingHom` 的定义

English:
definition valueOrderRingHom
  signature: {X E : Type*} [Semiring E] [PartialOrder E] [TopologicalSpace X] {x : X}
  body: Filter.Germ.valueRingHom
  monotone' := fun φ ψ =>
  Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ h => h.self_of_nhds

中文:
定义 valueOrderRingHom
  签名: {X E : 类型} [半环 E] [偏序 E] [拓扑空间 X] {x : X}
  定义体: Filter.Germ.valueRingHom
  monotone' := fun φ ψ =>
  Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ h => h.self_of_nhds

Depends on / 依赖: Filter, Filter.Germ.valueRingHom, valueRingHom
-/
def valueOrderRingHom {X E : Type*} [Semiring E] [PartialOrder E] [TopologicalSpace X] {x : X} :
    Germ (𝓝 x) E ->+*o E where
  __ := Filter.Germ.valueRingHom
  monotone' := fun φ ψ =>
  Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ h => h.self_of_nhds

end Filter.Germ

section RestrictGermPredicate
/--
Definition of `RestrictGermPredicate` / `RestrictGermPredicate` 的定义

English:
definition RestrictGermPredicate
  signature: (P : forall x : X, Germ (𝓝 x) Y -> Prop)
  body: fun x φ =>
  Germ.liftOn φ (fun f => x in A -> forallᶠ y in 𝓝 x, P y f)
    haveI : forall f f' : X -> Y, f =ᶠ[𝓝 x] f' -> (forallᶠ y in 𝓝 x, P y f) -> forallᶠ y in 𝓝 x, P y f' := by
      intro f f' hff' hf
      apply (hf.and <| Eventually.eventually_nhds hff').mono
      rintro y ⟨hy, hy'⟩
      rwa [Germ.coe_eq.mpr (EventuallyEq.symm hy')]
fun f f' hff' => propext forall_congr' fun _ => ⟨this f f' hff', this f' f hff'.symm⟩

中文:
定义 RestrictGermPredicate
  签名: (P : 对任意 x : X, Germ (𝓝 x) Y -> 命题)
  定义体: fun x φ =>
  Germ.liftOn φ (fun f => x in A -> forallᶠ y in 𝓝 x, P y f)
    haveI : forall f f' : X -> Y, f =ᶠ[𝓝 x] f' -> (forallᶠ y in 𝓝 x, P y f) -> forallᶠ y in 𝓝 x, P y f' := by
      intro f f' hff' hf
      apply (hf.and <| Eventually.eventually_nhds hff').mono
      rintro y ⟨hy, hy'⟩
      rwa [Germ.coe_eq.mpr (EventuallyEq.symm hy')]
fun f f' hff' => propext forall_congr' fun _ => ⟨this f f' hff', this f' f hff'.symm⟩
-/
def RestrictGermPredicate (P : forall x : X, Germ (𝓝 x) Y -> Prop)
    (A : Set X) : forall x : X, Germ (𝓝 x) Y -> Prop := fun x φ =>
  Germ.liftOn φ (fun f => x in A -> forallᶠ y in 𝓝 x, P y f)
    haveI : forall f f' : X -> Y, f =ᶠ[𝓝 x] f' -> (forallᶠ y in 𝓝 x, P y f) -> forallᶠ y in 𝓝 x, P y f' := by
      intro f f' hff' hf
      apply (hf.and <| Eventually.eventually_nhds hff').mono
      rintro y ⟨hy, hy'⟩
      rwa [Germ.coe_eq.mpr (EventuallyEq.symm hy')]
fun f f' hff' => propext forall_congr' fun _ => ⟨this f f' hff', this f' f hff'.symm⟩

/--
theorem `Filter.Eventually.germ_congr_set` / 定理 `Filter.Eventually.germ_congr_set`

English:
theorem Filter.Eventually.germ_congr_set
  proof: by
  rw [eventually_nhdsSet_iff_forall] at *
  intro x hx
  apply ((hf x hx).and (h x hx).eventually_nhds).mono
  intro y hy
  convert! hy.1 using 1
  exact Germ.coe_eq.mpr hy.2

中文:
定理 滤子.Eventually.germ_congr_set
  证明: by
  rw [eventually_nhdsSet_iff_forall] at *
  intro x hx
  apply ((hf x hx).and (h x hx).eventually_nhds).mono
  intro y hy
  convert! hy.1 using 1
  exact Germ.coe_eq.mpr hy.2

Depends on / 依赖: Germ.coe_eq.mpr, coe_eq, convert, eventually_nhds, eventually_nhdsSet_iff_forall
-/
theorem Filter.Eventually.germ_congr_set
    {P : forall x : X, Germ (𝓝 x) Y -> Prop} (hf : forallᶠ x in 𝓝ˢ A, P x f)
    (h : forallᶠ z in 𝓝ˢ A, g z = f z) : forallᶠ x in 𝓝ˢ A, P x g := by
  rw [eventually_nhdsSet_iff_forall] at *
  intro x hx
  apply ((hf x hx).and (h x hx).eventually_nhds).mono
  intro y hy
  convert! hy.1 using 1
  exact Germ.coe_eq.mpr hy.2

/--
theorem `restrictGermPredicate_congr` / 定理 `restrictGermPredicate_congr`

English:
theorem restrictGermPredicate_congr
  statement: {P : forall x : X, Germ (𝓝 x) Y -> Prop}
  proof: by
  intro hx
  apply ((hf hx).and <| (eventually_nhdsSet_iff_forall.mp h x hx).eventually_nhds).mono
  rintro y ⟨hy, h'y⟩
  rwa [Germ.coe_eq.mpr h'y]

中文:
定理 restrictGermPredicate_congr
  结论: {P : 对任意 x : X, Germ (𝓝 x) Y -> 命题}
  证明: by
  intro hx
  apply ((hf hx).and <| (eventually_nhdsSet_iff_forall.mp h x hx).eventually_nhds).mono
  rintro y ⟨hy, h'y⟩
  rwa [Germ.coe_eq.mpr h'y]

Depends on / 依赖: Germ.coe_eq.mpr, coe_eq, eventually_nhds, eventually_nhdsSet_iff_forall, eventually_nhdsSet_iff_forall.mp
-/
theorem restrictGermPredicate_congr {P : forall x : X, Germ (𝓝 x) Y -> Prop}
    (hf : RestrictGermPredicate P A x f) (h : forallᶠ z in 𝓝ˢ A, g z = f z) :
    RestrictGermPredicate P A x g := by
  intro hx
  apply ((hf hx).and <| (eventually_nhdsSet_iff_forall.mp h x hx).eventually_nhds).mono
  rintro y ⟨hy, h'y⟩
  rwa [Germ.coe_eq.mpr h'y]

/--
theorem `forall_restrictGermPredicate_iff` / 定理 `forall_restrictGermPredicate_iff`

English:
theorem forall_restrictGermPredicate_iff
  given: {P : forall x : X, Germ (𝓝 x) Y -> Prop}
  proof: by
  rw [eventually_nhdsSet_iff_forall]
  rfl

中文:
定理 对任意_restrictGermPredicate_iff
  条件: {P : 对任意 x : X, Germ (𝓝 x) Y -> 命题}
  证明: by
  rw [eventually_nhdsSet_iff_forall]
  rfl

Depends on / 依赖: eventually_nhdsSet_iff_forall
-/
theorem forall_restrictGermPredicate_iff {P : forall x : X, Germ (𝓝 x) Y -> Prop} :
    (forall x, RestrictGermPredicate P A x f) ↔ forallᶠ x in 𝓝ˢ A, P x f := by
  rw [eventually_nhdsSet_iff_forall]
  rfl

/--
theorem `forall_restrictGermPredicate_of_forall` / 定理 `forall_restrictGermPredicate_of_forall`

English:
theorem forall_restrictGermPredicate_of_forall
  proof: forall_restrictGermPredicate_iff.mpr (Eventually.of_forall h)

中文:
定理 对任意_restrictGermPredicate_of_对任意
  证明: forall_restrictGermPredicate_iff.mpr (Eventually.of_forall h)

Depends on / 依赖: Eventually, Eventually.of_forall, forall_restrictGermPredicate_iff, forall_restrictGermPredicate_iff.mpr, of_forall
-/
theorem forall_restrictGermPredicate_of_forall
    {P : forall x : X, Germ (𝓝 x) Y -> Prop} (h : forall x, P x f) :
    forall x, RestrictGermPredicate P A x f :=
  forall_restrictGermPredicate_iff.mpr (Eventually.of_forall h)
end RestrictGermPredicate

namespace Filter.Germ
/--
Definition of `sliceLeft` / `sliceLeft` 的定义

English:
definition sliceLeft
  signature: [TopologicalSpace Y] {p : X × Y} (P : Germ (𝓝 p) Z)
  body: P.compTendsto (Prod.mk · p.2) (Continuous.prodMk_left p.2).continuousAt

@[simp]

中文:
定义 sliceLeft
  签名: [拓扑空间 Y] {p : X × Y} (P : Germ (𝓝 p) Z)
  定义体: P.compTendsto (Prod.mk · p.2) (Continuous.prodMk_left p.2).continuousAt

@[simp]

Depends on / 依赖: Continuous, Continuous.prodMk_left, P.compTendsto, Prod.mk, compTendsto, continuousAt, prodMk_left
-/
def sliceLeft [TopologicalSpace Y] {p : X × Y} (P : Germ (𝓝 p) Z) : Germ (𝓝 p.1) Z :=
  P.compTendsto (Prod.mk · p.2) (Continuous.prodMk_left p.2).continuousAt

@[simp]
/--
theorem `sliceLeft_coe` / 定理 `sliceLeft_coe`

English:
theorem sliceLeft_coe
  given: [TopologicalSpace Y] {y : Y} (f : X × Y -> Z)
  proof: rfl

中文:
定理 sliceLeft_coe
  条件: [拓扑空间 Y] {y : Y} (f : X × Y -> Z)
  证明: rfl
-/
theorem sliceLeft_coe [TopologicalSpace Y] {y : Y} (f : X × Y -> Z) :
    (↑f : Germ (𝓝 (x, y)) Z).sliceLeft = fun x' => f (x', y) :=
  rfl

/--
Definition of `sliceRight` / `sliceRight` 的定义

English:
definition sliceRight
  signature: [TopologicalSpace Y] {p : X × Y} (P : Germ (𝓝 p) Z)
  body: P.compTendsto (Prod.mk p.1) (Continuous.prodMk_right p.1).continuousAt

@[simp]

中文:
定义 sliceRight
  签名: [拓扑空间 Y] {p : X × Y} (P : Germ (𝓝 p) Z)
  定义体: P.compTendsto (Prod.mk p.1) (Continuous.prodMk_right p.1).continuousAt

@[simp]

Depends on / 依赖: Continuous, Continuous.prodMk_right, P.compTendsto, Prod.mk, compTendsto, continuousAt, prodMk_right
-/
def sliceRight [TopologicalSpace Y] {p : X × Y} (P : Germ (𝓝 p) Z) : Germ (𝓝 p.2) Z :=
  P.compTendsto (Prod.mk p.1) (Continuous.prodMk_right p.1).continuousAt

@[simp]
/--
theorem `sliceRight_coe` / 定理 `sliceRight_coe`

English:
theorem sliceRight_coe
  given: [TopologicalSpace Y] {y : Y} (f : X × Y -> Z)
  proof: rfl

中文:
定理 sliceRight_coe
  条件: [拓扑空间 Y] {y : Y} (f : X × Y -> Z)
  证明: rfl
-/
theorem sliceRight_coe [TopologicalSpace Y] {y : Y} (f : X × Y -> Z) :
    (↑f : Germ (𝓝 (x, y)) Z).sliceRight = fun y' => f (x, y') :=
  rfl

/--
lemma `isConstant_comp_subtype` / 引理 `isConstant_comp_subtype`

English:
lemma isConstant_comp_subtype
  statement: {s : Set X} {f : X -> Y} {x : s}
  proof: isConstant_comp_tendsto hf continuousAt_subtype_val

中文:
引理 isConstant_comp_subtype
  结论: {s : 集合 X} {f : X -> Y} {x : s}
  证明: isConstant_comp_tendsto hf continuousAt_subtype_val

Depends on / 依赖: continuousAt_subtype_val, isConstant_comp_tendsto
-/
lemma isConstant_comp_subtype {s : Set X} {f : X -> Y} {x : s}
    (hf : (f : Germ (𝓝 (x : X)) Y).IsConstant) :
    ((f ∘ Subtype.val : s -> Y) : Germ (𝓝 x) Y).IsConstant :=
  isConstant_comp_tendsto hf continuousAt_subtype_val

end Filter.Germ

/--
lemma `IsLocallyConstant.of_germ_isConstant` / 引理 `IsLocallyConstant.of_germ_isConstant`

English:
lemma IsLocallyConstant.of_germ_isConstant
  given: (h : forall x : X, (f : Germ (𝓝 x) Y).IsConstant)
  proof: by
  intro s
  rw [isOpen_iff_mem_nhds]
  intro a ha
  obtain ⟨b, hb⟩ := h a
  apply mem_of_superset hb
  intro x hx
  have : f x = f a := (mem_of_mem_nhds hb) ▸ hx
  rw [mem_preimage]; rw [this]
  exact ha

中文:
引理 IsLocallyConstant.of_germ_isConstant
  条件: (h : 对任意 x : X, (f : Germ (𝓝 x) Y).是常数)
  证明: by
  intro s
  rw [isOpen_iff_mem_nhds]
  intro a ha
  obtain ⟨b, hb⟩ := h a
  apply mem_of_superset hb
  intro x hx
  have : f x = f a := (mem_of_mem_nhds hb) ▸ hx
  rw [mem_preimage]; rw [this]
  exact ha

Depends on / 依赖: isOpen_iff_mem_nhds, mem_of_mem_nhds, mem_of_superset, mem_preimage
-/
lemma IsLocallyConstant.of_germ_isConstant (h : forall x : X, (f : Germ (𝓝 x) Y).IsConstant) :
    IsLocallyConstant f := by
  intro s
  rw [isOpen_iff_mem_nhds]
  intro a ha
  obtain ⟨b, hb⟩ := h a
  apply mem_of_superset hb
  intro x hx
  have : f x = f a := (mem_of_mem_nhds hb) ▸ hx
  rw [mem_preimage]; rw [this]
  exact ha

/--
theorem `eq_of_germ_isConstant` / 定理 `eq_of_germ_isConstant`

English:
theorem eq_of_germ_isConstant
  statement: [i : PreconnectedSpace X]
  proof: (IsLocallyConstant.of_germ_isConstant h).apply_eq_of_isPreconnected
    (preconnectedSpace_iff_univ.mp i) (by trivial) (by trivial)

中文:
定理 eq_of_germ_isConstant
  结论: [i : 预连通空间 X]
  证明: (IsLocallyConstant.of_germ_isConstant h).apply_eq_of_isPreconnected
    (preconnectedSpace_iff_univ.mp i) (by trivial) (by trivial)

Depends on / 依赖: IsLocallyConstant, IsLocallyConstant.of_germ_isConstant, apply_eq_of_isPreconnected, of_germ_isConstant, preconnectedSpace_iff_univ, preconnectedSpace_iff_univ.mp
-/
theorem eq_of_germ_isConstant [i : PreconnectedSpace X]
    (h : forall x : X, (f : Germ (𝓝 x) Y).IsConstant) (x x' : X) : f x = f x' :=
  (IsLocallyConstant.of_germ_isConstant h).apply_eq_of_isPreconnected
    (preconnectedSpace_iff_univ.mp i) (by trivial) (by trivial)

/--
lemma `eq_of_germ_isConstant_on` / 引理 `eq_of_germ_isConstant_on`

English:
lemma eq_of_germ_isConstant_on
  statement: {s : Set X} (h : forall x in s, (f : Germ (𝓝 x) Y).IsConstant)
  proof: by
  let i : s -> X := fun x => x
  change (f ∘ i) (⟨x, x_in⟩ : s) = (f ∘ i) (⟨x', x'_in⟩ : s)
  have : PreconnectedSpace s := Subtype.preconnectedSpace hs
  exact eq_of_germ_isConstant (fun y => Germ.isConstant_comp_subtype (h y y.2)) _ _

@[to_additive (attr := simp)]

中文:
引理 eq_of_germ_isConstant_on
  结论: {s : 集合 X} (h : 对任意 x in s, (f : Germ (𝓝 x) Y).是常数)
  证明: by
  let i : s -> X := fun x => x
  change (f ∘ i) (⟨x, x_in⟩ : s) = (f ∘ i) (⟨x', x'_in⟩ : s)
  have : PreconnectedSpace s := Subtype.preconnectedSpace hs
  exact eq_of_germ_isConstant (fun y => Germ.isConstant_comp_subtype (h y y.2)) _ _

@[to_additive (attr := simp)]

Depends on / 依赖: Germ.isConstant_comp_subtype, PreconnectedSpace, Subtype, Subtype.preconnectedSpace, eq_of_germ_isConstant, isConstant_comp_subtype, preconnectedSpace, x_in
-/
lemma eq_of_germ_isConstant_on {s : Set X} (h : forall x in s, (f : Germ (𝓝 x) Y).IsConstant)
    (hs : IsPreconnected s) {x' : X} (x_in : x in s) (x'_in : x' in s) : f x = f x' := by
  let i : s -> X := fun x => x
  change (f ∘ i) (⟨x, x_in⟩ : s) = (f ∘ i) (⟨x', x'_in⟩ : s)
  have : PreconnectedSpace s := Subtype.preconnectedSpace hs
  exact eq_of_germ_isConstant (fun y => Germ.isConstant_comp_subtype (h y y.2)) _ _

@[to_additive (attr := simp)]
/--
theorem `Germ.coe_prod` / 定理 `Germ.coe_prod`

English:
theorem Germ.coe_prod
  statement: {α : Type*} (l : Filter α) (R : Type*) [CommMonoid R] {ι} (f : ι -> α -> R)
  proof: map_prod (Germ.coeMulHom l : (α -> R) ->* Germ l R) f s

中文:
定理 Germ.coe_prod
  结论: {α : 类型} (l : 滤子 α) (R : 类型) [交换幺半群 R] {ι} (f : ι -> α -> R)
  证明: map_prod (Germ.coeMulHom l : (α -> R) ->* Germ l R) f s

Depends on / 依赖: Germ.coeMulHom, coeMulHom, map_prod
-/
theorem Germ.coe_prod {α : Type*} (l : Filter α) (R : Type*) [CommMonoid R] {ι} (f : ι -> α -> R)
    (s : Finset ι) : ((∏ i in s, f i : α -> R) : Germ l R) = ∏ i in s, (f i : Germ l R) :=
  map_prod (Germ.coeMulHom l : (α -> R) ->* Germ l R) f s
