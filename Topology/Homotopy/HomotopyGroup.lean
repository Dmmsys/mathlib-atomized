/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez
-/
module

public import Mathlib.Algebra.Group.Ext
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.GroupTheory.EckmannHilton

/-!
# `n`th homotopy group

We define the `n`th homotopy group at `x : X`, `π_n X x`, as the equivalence classes
of functions from the `n`-dimensional cube to the topological space `X`
that send the boundary to the base point `x`, up to homotopic equivalence.
Note that such functions are generalized loops `GenLoop (Fin n) x`; in particular
`GenLoop (Fin 1) x ≃ Path x x`.

We show that `π_0 X x` is equivalent to the path-connected components, and
that `π_1 X x` is equivalent to the fundamental group at `x`.
We provide a group instance using path composition and show commutativity when `n > 1`.

## definitions

* `GenLoop N x` is the type of continuous functions `I^N → X` that send the boundary to `x`,
* `HomotopyGroup.Pi n X x` denoted `π_ n X x` is the quotient of `GenLoop (Fin n) x` by
  homotopy relative to the boundary,
* group instance `Group (π_(n+1) X x)`,
* commutative group instance `CommGroup (π_(n+2) X x)`.

TODO:
* `Ω^M (Ω^N X) ≃ₜ Ω^(M⊕N) X`, and `Ω^M X ≃ₜ Ω^N X` when `M ≃ N`. Similarly for `π_`.
* Examples with `𝕊^n`: `π_n (𝕊^n) = ℤ`, `π_m (𝕊^n)` trivial for `m < n`.
* Actions of π_1 on π_n.
* Lie algebra: `⁅π_(n+1), π_(m+1)⁆` contained in `π_(n+m+1)`.

-/

@[expose] public section


open scoped unitInterval Topology

open Homeomorph

noncomputable section

/-- `I^N` is notation (in the Topology namespace) for `N → I`,
i.e. the unit cube indexed by a type `N`. -/
scoped[Topology] notation "I^" N => N -> I

namespace Cube

/--
Definition of `boundary` / `boundary` 的定义

English:
definition boundary
  signature: (N : Type*)
  body: {y | exists i, y i = 0 ∨ y i = 1}

中文:
定义 boundary
  签名: (N : 类型)
  定义体: {y | exists i, y i = 0 ∨ y i = 1}
-/
def boundary (N : Type*) : Set (I^N) :=
  {y | exists i, y i = 0 ∨ y i = 1}

variable {N : Type*} [DecidableEq N]

/--
Definition of `splitAt` / `splitAt` 的定义

English:
abbreviation splitAt
  signature: (i : N)
  body: funSplitAt I i

中文:
缩写 splitAt
  签名: (i : N)
  定义体: funSplitAt I i

Depends on / 依赖: funSplitAt
-/
abbrev splitAt (i : N) : (I^N) ≃ₜ I × I^{ j // j != i } :=
  funSplitAt I i

/--
Definition of `insertAt` / `insertAt` 的定义

English:
abbreviation insertAt
  signature: (i : N)
  body: (funSplitAt I i).symm

中文:
缩写 insertAt
  签名: (i : N)
  定义体: (funSplitAt I i).symm

Depends on / 依赖: funSplitAt
-/
abbrev insertAt (i : N) : (I × I^{ j // j != i }) ≃ₜ I^N :=
  (funSplitAt I i).symm

/--
theorem `insertAt_boundary` / 定理 `insertAt_boundary`

English:
theorem insertAt_boundary
  statement: (i : N) {t₀ : I} {t}
  proof: by
  obtain H | ⟨j, H⟩ := H
  · use i; rwa [funSplitAt_symm_apply, dif_pos rfl]
  · use j; rwa [funSplitAt_symm_apply, dif_neg j.prop, Subtype.coe_eta]

中文:
定理 insertAt_boundary
  结论: (i : N) {t₀ : I} {t}
  证明: by
  obtain H | ⟨j, H⟩ := H
  · use i; rwa [funSplitAt_symm_apply, dif_pos rfl]
  · use j; rwa [funSplitAt_symm_apply, dif_neg j.prop, Subtype.coe_eta]

Depends on / 依赖: Subtype, Subtype.coe_eta, coe_eta, dif_neg, dif_pos, funSplitAt_symm_apply, j.prop
-/
theorem insertAt_boundary (i : N) {t₀ : I} {t}
    (H : (t₀ = 0 ∨ t₀ = 1) ∨ t in boundary { j // j != i }) : insertAt i ⟨t₀, t⟩ in boundary N := by
  obtain H | ⟨j, H⟩ := H
  · use i; rwa [funSplitAt_symm_apply, dif_pos rfl]
  · use j; rwa [funSplitAt_symm_apply, dif_neg j.prop, Subtype.coe_eta]

end Cube

variable (N X : Type*) [TopologicalSpace X] (x : X)

/--
Definition of `LoopSpace` / `LoopSpace` 的定义

English:
abbreviation LoopSpace
  body: Path x x

@[inherit_doc] scoped[Topology.Homotopy] notation "Ω" => LoopSpace

中文:
缩写 LoopSpace
  定义体: Path x x

@[inherit_doc] scoped[Topology.Homotopy] notation "Ω" => LoopSpace
-/
abbrev LoopSpace :=
  Path x x

@[inherit_doc] scoped[Topology.Homotopy] notation "Ω" => LoopSpace

/--
Instance `LoopSpace.inhabited` / 实例 `LoopSpace.inhabited`

English:
instance LoopSpace.inhabited
  signature: : Inhabited (Path x x)
  body: ⟨Path.refl x⟩

中文:
实例 LoopSpace.inhabited
  签名: : Inhabited (Path x x)
  定义体: ⟨Path.refl x⟩

Depends on / 依赖: Path.refl
-/
instance LoopSpace.inhabited : Inhabited (Path x x) :=
  ⟨Path.refl x⟩

/--
Definition of `GenLoop` / `GenLoop` 的定义

English:
definition GenLoop
  signature: : Set C(I^N, X)
  body: {p | forall y in Cube.boundary N, p y = x}

@[inherit_doc] scoped[Topology.Homotopy] notation "Ω^" => GenLoop

中文:
定义 GenLoop
  签名: : Set C(I^N, X)
  定义体: {p | forall y in Cube.boundary N, p y = x}

@[inherit_doc] scoped[Topology.Homotopy] notation "Ω^" => GenLoop

Depends on / 依赖: Cube.boundary, boundary
-/
def GenLoop : Set C(I^N, X) :=
  {p | forall y in Cube.boundary N, p y = x}

@[inherit_doc] scoped[Topology.Homotopy] notation "Ω^" => GenLoop

open Topology.Homotopy

variable {N X x}

namespace GenLoop

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (Ω^ N X x) (I^N) X where
  body: f.1
  coe_injective := fun ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ _ => by congr

@[simp]

中文:
实例 instFunLike
  签名: : FunLike (Ω^ N X x) (I^N) X where
  定义体: f.1
  coe_injective := fun ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ _ => by congr

@[simp]
-/
instance instFunLike : FunLike (Ω^ N X x) (I^N) X where
  coe f := f.1
  coe_injective := fun ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ _ => by congr

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (f : Ω^ N X x)
  statement: ⇑(f : C(I^N, X)) = f
  proof: rfl

@[ext]

中文:
定理 coe_coe
  条件: (f : Ω^ N X x)
  结论: ⇑(f : C(I^N, X)) = f
  证明: rfl

@[ext]
-/
theorem coe_coe (f : Ω^ N X x) : ⇑(f : C(I^N, X)) = f := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (f g : Ω^ N X x) (H : forall y, f y = g y)
  statement: f = g
  proof: DFunLike.coe_injective (funext H)

@[simp]

中文:
定理 ext
  条件: (f g : Ω^ N X x) (H : 对任意 y, f y = g y)
  结论: f = g
  证明: DFunLike.coe_injective (funext H)

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem ext (f g : Ω^ N X x) (H : forall y, f y = g y) : f = g :=
  DFunLike.coe_injective (funext H)

@[simp]
/--
theorem `mk_apply` / 定理 `mk_apply`

English:
theorem mk_apply
  given: (f : C(I^N, X)) (H y)
  statement: (⟨f, H⟩ : Ω^ N X x) y = f y
  proof: rfl

中文:
定理 mk_apply
  条件: (f : C(I^N, X)) (H y)
  结论: (⟨f, H⟩ : Ω^ N X x) y = f y
  证明: rfl
-/
theorem mk_apply (f : C(I^N, X)) (H y) : (⟨f, H⟩ : Ω^ N X x) y = f y :=
  rfl

/--
Instance `instContinuousEval` / 实例 `instContinuousEval`

English:
instance instContinuousEval
  signature: : ContinuousEval (Ω^ N X x) (I^N) X
  body: .of_continuous_forget continuous_subtype_val

中文:
实例 instContinuousEval
  签名: : ContinuousEval (Ω^ N X x) (I^N) X
  定义体: .of_continuous_forget continuous_subtype_val

Depends on / 依赖: continuous_subtype_val, of_continuous_forget
-/
instance instContinuousEval : ContinuousEval (Ω^ N X x) (I^N) X :=
  .of_continuous_forget continuous_subtype_val

/--
Instance `instContinuousEvalConst` / 实例 `instContinuousEvalConst`

English:
instance instContinuousEvalConst
  signature: : ContinuousEvalConst (Ω^ N X x) (I^N) X
  body: inferInstance

中文:
实例 instContinuousEvalConst
  签名: : ContinuousEvalConst (Ω^ N X x) (I^N) X
  定义体: inferInstance
-/
instance instContinuousEvalConst : ContinuousEvalConst (Ω^ N X x) (I^N) X := inferInstance

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : Ω^ N X x) (g : (I^N) -> X) (h : g = f)
  body: ⟨⟨g, h.symm ▸ f.1.2⟩, by convert! f.2⟩

中文:
定义 copy
  签名: (f : Ω^ N X x) (g : (I^N) -> X) (h : g = f)
  定义体: ⟨⟨g, h.symm ▸ f.1.2⟩, by convert! f.2⟩

Depends on / 依赖: convert, h.symm
-/
def copy (f : Ω^ N X x) (g : (I^N) -> X) (h : g = f) : Ω^ N X x :=
  ⟨⟨g, h.symm ▸ f.1.2⟩, by convert! f.2⟩

/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : Ω^ N X x) {g : (I^N) -> X} (h : g = f)
  statement: ⇑(copy f g h) = g
  proof: rfl

中文:
定理 coe_copy
  条件: (f : Ω^ N X x) {g : (I^N) -> X} (h : g = f)
  结论: ⇑(copy f g h) = g
  证明: rfl
-/
theorem coe_copy (f : Ω^ N X x) {g : (I^N) -> X} (h : g = f) : ⇑(copy f g h) = g :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : Ω^ N X x) {g : (I^N) -> X} (h : g = f)
  statement: copy f g h = f
  proof: by
  ext x
  exact congr_fun h x

中文:
定理 copy_eq
  条件: (f : Ω^ N X x) {g : (I^N) -> X} (h : g = f)
  结论: copy f g h = f
  证明: by
  ext x
  exact congr_fun h x

Depends on / 依赖: congr_fun
-/
theorem copy_eq (f : Ω^ N X x) {g : (I^N) -> X} (h : g = f) : copy f g h = f := by
  ext x
  exact congr_fun h x

/--
theorem `boundary` / 定理 `boundary`

English:
theorem boundary
  given: (f : Ω^ N X x)
  statement: forall y in Cube.boundary N, f y = x
  proof: f.2

中文:
定理 boundary
  条件: (f : Ω^ N X x)
  结论: 对任意 y in Cube.boundary N, f y = x
  证明: f.2
-/
theorem boundary (f : Ω^ N X x) : forall y in Cube.boundary N, f y = x :=
  f.2

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: : Ω^ N X x
  body: ⟨ContinuousMap.const _ x, fun _ _ => rfl⟩

@[simp]

中文:
定义 const
  签名: : Ω^ N X x
  定义体: ⟨ContinuousMap.const _ x, fun _ _ => rfl⟩

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.const
-/
def const : Ω^ N X x :=
  ⟨ContinuousMap.const _ x, fun _ _ => rfl⟩

@[simp]
/--
theorem `const_apply` / 定理 `const_apply`

English:
theorem const_apply
  given: {t}
  statement: (@const N X _ x) t = x
  proof: rfl

中文:
定理 const_apply
  条件: {t}
  结论: (@const N X _ x) t = x
  证明: rfl
-/
theorem const_apply {t} : (@const N X _ x) t = x :=
  rfl

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (Ω^ N X x)
  body: ⟨const⟩

中文:
实例 inhabited
  签名: : Inhabited (Ω^ N X x)
  定义体: ⟨const⟩
-/
instance inhabited : Inhabited (Ω^ N X x) :=
  ⟨const⟩

section

variable {M} (x : X)

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (e : M ≃ N)
  body: ⟨p.1.comp ⟨fun t m => t (e m), by fun_prop⟩, fun y ⟨n, hn⟩ =>
    by simpa using p.2 _ ⟨e.symm n, by simpa using hn⟩⟩
  invFun p := ⟨p.1.comp ⟨fun t n => t (e.symm n), by fun_prop⟩, fun y ⟨m, hm⟩ => by
    simpa using p.2 _ ⟨e m, by simpa using hm⟩⟩
  left_inv p := by ext t; simp
  right_inv p := by

中文:
定义 congr
  签名: (e : M ≃ N)
  定义体: ⟨p.1.comp ⟨fun t m => t (e m), by fun_prop⟩, fun y ⟨n, hn⟩ =>
    by simpa using p.2 _ ⟨e.symm n, by simpa using hn⟩⟩
  invFun p := ⟨p.1.comp ⟨fun t n => t (e.symm n), by fun_prop⟩, fun y ⟨m, hm⟩ => by
    simpa using p.2 _ ⟨e m, by simpa using hm⟩⟩
  left_inv p := by ext t; simp
  right_inv p := by

Depends on / 依赖: fun_prop
-/
def congr (e : M ≃ N) : Ω^ M X x ≃ₜ Ω^ N X x where
  toFun p := ⟨p.1.comp ⟨fun t m => t (e m), by fun_prop⟩, fun y ⟨n, hn⟩ =>
    by simpa using p.2 _ ⟨e.symm n, by simpa using hn⟩⟩
  invFun p := ⟨p.1.comp ⟨fun t n => t (e.symm n), by fun_prop⟩, fun y ⟨m, hm⟩ => by
    simpa using p.2 _ ⟨e m, by simpa using hm⟩⟩
  left_inv p := by ext t; simp
  right_inv p := by ext t; simp

/--
theorem `_root_.Cube.boundary_sum_iff` / 定理 `_root_.Cube.boundary_sum_iff`

English:
theorem _root_.Cube.boundary_sum_iff
  given: {y : I^(M oplus N)}
  proof: by
  constructor
  · rintro ⟨i | i, hi⟩
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨i, hi⟩
  · rintro (⟨m, hm⟩ | ⟨n, hn⟩)
    · exact ⟨Sum.inl m, hm⟩
    · exact ⟨Sum.inr n, hn⟩

@[simp]

中文:
定理 _root_.Cube.boundary_sum_iff
  条件: {y : I^(M oplus N)}
  证明: by
  constructor
  · rintro ⟨i | i, hi⟩
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨i, hi⟩
  · rintro (⟨m, hm⟩ | ⟨n, hn⟩)
    · exact ⟨Sum.inl m, hm⟩
    · exact ⟨Sum.inr n, hn⟩

@[simp]

Depends on / 依赖: Or.inl, Or.inr, Sum.inl, Sum.inr
-/
theorem _root_.Cube.boundary_sum_iff {y : I^(M oplus N)} :
    y in Cube.boundary (M oplus N) ↔ y ∘ Sum.inl in Cube.boundary M ∨ y ∘ Sum.inr in Cube.boundary N := by
  constructor
  · rintro ⟨i | i, hi⟩
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨i, hi⟩
  · rintro (⟨m, hm⟩ | ⟨n, hn⟩)
    · exact ⟨Sum.inl m, hm⟩
    · exact ⟨Sum.inr n, hn⟩

@[simp]
/--
lemma `apply_inl_apply_inr_eq_of_mem_boundary_sum` / 引理 `apply_inl_apply_inr_eq_of_mem_boundary_sum`

English:
lemma apply_inl_apply_inr_eq_of_mem_boundary_sum
  proof: by
  rcases Cube.boundary_sum_iff.mp hy with hM | hN
  · have : p (y ∘ Sum.inl) = const := p.property (y ∘ Sum.inl) hM
    simp [this]
  · simpa using (p.val (y ∘ Sum.inl)).property (y ∘ Sum.inr) hN

中文:
引理 apply_inl_apply_inr_eq_of_mem_boundary_sum
  证明: by
  rcases Cube.boundary_sum_iff.mp hy with hM | hN
  · have : p (y ∘ Sum.inl) = const := p.property (y ∘ Sum.inl) hM
    simp [this]
  · simpa using (p.val (y ∘ Sum.inl)).property (y ∘ Sum.inr) hN

Depends on / 依赖: Cube.boundary_sum_iff.mp, Sum.inl, Sum.inr, boundary_sum_iff, p.property, p.val, property
-/
lemma apply_inl_apply_inr_eq_of_mem_boundary_sum
    (p : Ω^ M (Ω^ N X x) const) {y : I^(M oplus N)} (hy : y in Cube.boundary (M oplus N)) :
    p (y ∘ Sum.inl) (y ∘ Sum.inr) = x := by
  rcases Cube.boundary_sum_iff.mp hy with hM | hN
  · have : p (y ∘ Sum.inl) = const := p.property (y ∘ Sum.inl) hM
    simp [this]
  · simpa using (p.val (y ∘ Sum.inl)).property (y ∘ Sum.inr) hN

/-- Curries an `(M ⊕ N)`-cube into an `M`-cube of `N`-cubes. -/
@[simps]
/--
Definition of `currySum` / `currySum` 的定义

English:
definition currySum
  signature: (q : Ω^ (M oplus N) X x)
  body: ⟨(q.1.comp ⟨sumArrowHomeomorphProdArrow.invFun,
    sumArrowHomeomorphProdArrow.continuous_invFun⟩).curry.toFun a,
      fun _ hm => q.2 _ (Cube.boundary_sum_iff.mpr (Or.inr hm))⟩
  continuous_toFun := Continuous.subtype_mk (q.1.comp
    ⟨sumArrowHomeomorphProdArrow.invFun,
      sumArrowHomeomorphP

中文:
定义 currySum
  签名: (q : Ω^ (M oplus N) X x)
  定义体: ⟨(q.1.comp ⟨sumArrowHomeomorphProdArrow.invFun,
    sumArrowHomeomorphProdArrow.continuous_invFun⟩).curry.toFun a,
      fun _ hm => q.2 _ (Cube.boundary_sum_iff.mpr (Or.inr hm))⟩
  continuous_toFun := Continuous.subtype_mk (q.1.comp
    ⟨sumArrowHomeomorphProdArrow.invFun,
      sumArrowHomeomorphP

Depends on / 依赖: invFun, sumArrowHomeomorphProdArrow, sumArrowHomeomorphProdArrow.invFun
-/
def currySum (q : Ω^ (M oplus N) X x) : C(I^M, Ω^ N X x) where
  toFun a := ⟨(q.1.comp ⟨sumArrowHomeomorphProdArrow.invFun,
    sumArrowHomeomorphProdArrow.continuous_invFun⟩).curry.toFun a,
      fun _ hm => q.2 _ (Cube.boundary_sum_iff.mpr (Or.inr hm))⟩
  continuous_toFun := Continuous.subtype_mk (q.1.comp
    ⟨sumArrowHomeomorphProdArrow.invFun,
      sumArrowHomeomorphProdArrow.continuous_invFun⟩).curry.continuous_toFun _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `currySum_apply_inl_inr` / 引理 `currySum_apply_inl_inr`

English:
lemma currySum_apply_inl_inr
  given: (p : Ω^ (M oplus N) X x) (y : I^(M oplus N))
  proof: by
  simp [currySum, sumArrowHomeomorphProdArrow, Equiv.sumArrowEquivProdArrow]

@[fun_prop]

中文:
引理 currySum_apply_inl_inr
  条件: (p : Ω^ (M oplus N) X x) (y : I^(M oplus N))
  证明: by
  simp [currySum, sumArrowHomeomorphProdArrow, Equiv.sumArrowEquivProdArrow]

@[fun_prop]

Depends on / 依赖: Equiv.sumArrowEquivProdArrow, currySum, sumArrowEquivProdArrow, sumArrowHomeomorphProdArrow
-/
lemma currySum_apply_inl_inr (p : Ω^ (M oplus N) X x) (y : I^(M oplus N)) :
    currySum x p (y ∘ Sum.inl) (y ∘ Sum.inr) = p y := by
  simp [currySum, sumArrowHomeomorphProdArrow, Equiv.sumArrowEquivProdArrow]

@[fun_prop]
/--
lemma `continuous_currySum` / 引理 `continuous_currySum`

English:
lemma continuous_currySum
  statement: Continuous (currySum x (M := M) (N := N))
  proof: ContinuousMap.continuous_of_continuous_uncurry _ Continuous.subtype_mk
    (ContinuousMap.continuous_of_continuous_uncurry _ (by dsimp; fun_prop)) _

中文:
引理 continuous_currySum
  结论: Continuous (currySum x (M := M) (N := N))
  证明: ContinuousMap.continuous_of_continuous_uncurry _ Continuous.subtype_mk
    (ContinuousMap.continuous_of_continuous_uncurry _ (by dsimp; fun_prop)) _
-/
lemma continuous_currySum : Continuous (currySum x (M := M) (N := N)) :=
ContinuousMap.continuous_of_continuous_uncurry _ Continuous.subtype_mk
    (ContinuousMap.continuous_of_continuous_uncurry _ (by dsimp; fun_prop)) _

/--
Definition of `uncurry` / `uncurry` 的定义

English:
definition uncurry
  signature: (p : Ω^ M (Ω^ N X x) const)
  body: .uncurry ⟨fun a => ⟨(p.1 a).1, ContinuousMap.continuous _⟩, (map_continuous p).subtype_val⟩

@[simp]

中文:
定义 uncurry
  签名: (p : Ω^ M (Ω^ N X x) const)
  定义体: .uncurry ⟨fun a => ⟨(p.1 a).1, ContinuousMap.continuous _⟩, (map_continuous p).subtype_val⟩

@[simp]
-/
protected def uncurry (p : Ω^ M (Ω^ N X x) const) : C((I^M) × (I^N), X) :=
  .uncurry ⟨fun a => ⟨(p.1 a).1, ContinuousMap.continuous _⟩, (map_continuous p).subtype_val⟩

@[simp]
/--
lemma `uncurry_apply` / 引理 `uncurry_apply`

English:
lemma uncurry_apply
  given: (p : Ω^ M (Ω^ N X x) const) (y : (I^M) × (I^N))
  proof: rfl

中文:
引理 uncurry_apply
  条件: (p : Ω^ M (Ω^ N X x) const) (y : (I^M) × (I^N))
  证明: rfl
-/
lemma uncurry_apply (p : Ω^ M (Ω^ N X x) const) (y : (I^M) × (I^N)) :
    GenLoop.uncurry x p y = p y.1 y.2 := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `Ω^M (Ω^N X) ≃ₜ Ω^(M ⊕ N) X`. -/
@[simps]
/--
Definition of `genLoopGenLoopEquiv` / `genLoopGenLoopEquiv` 的定义

English:
definition genLoopGenLoopEquiv
  signature: : Ω^ M (Ω^ N X x) GenLoop.const ≃ₜ Ω^ (M oplus N) X x where
  body: ⟨(GenLoop.uncurry x p).comp ⟨sumArrowHomeomorphProdArrow.toFun,
    sumArrowHomeomorphProdArrow.continuous_toFun⟩, fun y hy => by simp [hy]⟩
  invFun q :=
    ⟨currySum x q, fun _ hm => by ext n; exact q.2 _ (Cube.boundary_sum_iff.mpr (Or.inl hm))⟩
  left_inv p := by ext; simp; rfl
  right_inv p := 

中文:
定义 genLoopGenLoopEquiv
  签名: : Ω^ M (Ω^ N X x) GenLoop.const ≃ₜ Ω^ (M oplus N) X x where
  定义体: ⟨(GenLoop.uncurry x p).comp ⟨sumArrowHomeomorphProdArrow.toFun,
    sumArrowHomeomorphProdArrow.continuous_toFun⟩, fun y hy => by simp [hy]⟩
  invFun q :=
    ⟨currySum x q, fun _ hm => by ext n; exact q.2 _ (Cube.boundary_sum_iff.mpr (Or.inl hm))⟩
  left_inv p := by ext; simp; rfl
  right_inv p := 

Depends on / 依赖: GenLoop, GenLoop.uncurry, sumArrowHomeomorphProdArrow, sumArrowHomeomorphProdArrow.toFun, uncurry
-/
def genLoopGenLoopEquiv : Ω^ M (Ω^ N X x) GenLoop.const ≃ₜ Ω^ (M oplus N) X x where
  toFun p := ⟨(GenLoop.uncurry x p).comp ⟨sumArrowHomeomorphProdArrow.toFun,
    sumArrowHomeomorphProdArrow.continuous_toFun⟩, fun y hy => by simp [hy]⟩
  invFun q :=
    ⟨currySum x q, fun _ hm => by ext n; exact q.2 _ (Cube.boundary_sum_iff.mpr (Or.inl hm))⟩
  left_inv p := by ext; simp; rfl
  right_inv p := by ext; simp
  continuous_toFun := ((ContinuousMap.continuous_uncurry.comp' ((ContinuousMap.continuous_postcomp
    ⟨_, continuous_subtype_val⟩).comp continuous_subtype_val)).compCM
      continuous_const).subtype_mk _

end

/--
Definition of `Homotopic` / `Homotopic` 的定义

English:
definition Homotopic
  signature: (f g : Ω^ N X x)
  body: f.1.HomotopicRel g.1 (Cube.boundary N)

中文:
定义 Homotopic
  签名: (f g : Ω^ N X x)
  定义体: f.1.HomotopicRel g.1 (Cube.boundary N)

Depends on / 依赖: Cube.boundary, HomotopicRel, boundary
-/
def Homotopic (f g : Ω^ N X x) : Prop :=
  f.1.HomotopicRel g.1 (Cube.boundary N)

namespace Homotopic

variable {f g h : Ω^ N X x}

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (f : Ω^ N X x)
  statement: Homotopic f f
  proof: ContinuousMap.HomotopicRel.refl _

@[symm]
nonrec theorem symm (H : Homotopic f g) : Homotopic g f :=
  H.symm

@[trans]
nonrec theorem trans (H0 : Homotopic f g) (H1 : Homotopic g h) : Homotopic f h :=
  H0.trans H1

中文:
定理 refl
  条件: (f : Ω^ N X x)
  结论: Homotopic f f
  证明: ContinuousMap.HomotopicRel.refl _

@[symm]
nonrec theorem symm (H : Homotopic f g) : Homotopic g f :=
  H.symm

@[trans]
nonrec theorem trans (H0 : Homotopic f g) (H1 : Homotopic g h) : Homotopic f h :=
  H0.trans H1

Depends on / 依赖: ContinuousMap, ContinuousMap.HomotopicRel.refl, HomotopicRel
-/
theorem refl (f : Ω^ N X x) : Homotopic f f :=
  ContinuousMap.HomotopicRel.refl _

@[symm]
nonrec theorem symm (H : Homotopic f g) : Homotopic g f :=
  H.symm

@[trans]
nonrec theorem trans (H0 : Homotopic f g) (H1 : Homotopic g h) : Homotopic f h :=
  H0.trans H1

/--
theorem `equiv` / 定理 `equiv`

English:
theorem equiv
  statement: Equivalence (@Homotopic N X _ x)
  proof: ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩

中文:
定理 equiv
  结论: Equivalence (@Homotopic N X _ x)
  证明: ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩

Depends on / 依赖: Homotopic, Homotopic.refl, Homotopic.symm, Homotopic.trans
-/
theorem equiv : Equivalence (@Homotopic N X _ x) :=
  ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩

/--
Instance `setoid` / 实例 `setoid`

English:
instance setoid
  signature: (N) (x : X)
  body: ⟨Homotopic, equiv⟩

中文:
实例 setoid
  签名: (N) (x : X)
  定义体: ⟨Homotopic, equiv⟩

Depends on / 依赖: Homotopic
-/
instance setoid (N) (x : X) : Setoid (Ω^ N X x) :=
  ⟨Homotopic, equiv⟩

end Homotopic

section LoopHomeo

variable [DecidableEq N]

/-- Loop from a generalized loop by currying $I^N → X$ into $I → (I^{N\setminus\{j\}} → X)$. -/
@[simps]
/--
Definition of `toLoop` / `toLoop` 的定义

English:
definition toLoop
  signature: (i : N) (p : Ω^ N X x)
  body: ⟨(p.val.comp (Cube.insertAt i)).curry t, fun y yH =>
      p.property (Cube.insertAt i (t, y)) (Cube.insertAt_boundary i <| Or.inr yH)⟩
  source' := by ext t; refine p.property (Cube.insertAt i (0, t)) ⟨i, Or.inl ?_⟩; simp
  target' := by ext t; refine p.property (Cube.insertAt i (1, t)) ⟨i, Or.inr 

中文:
定义 toLoop
  签名: (i : N) (p : Ω^ N X x)
  定义体: ⟨(p.val.comp (Cube.insertAt i)).curry t, fun y yH =>
      p.property (Cube.insertAt i (t, y)) (Cube.insertAt_boundary i <| Or.inr yH)⟩
  source' := by ext t; refine p.property (Cube.insertAt i (0, t)) ⟨i, Or.inl ?_⟩; simp
  target' := by ext t; refine p.property (Cube.insertAt i (1, t)) ⟨i, Or.inr 

Depends on / 依赖: Cube.insertAt, Cube.insertAt_boundary, Or.inl, Or.inr, insertAt, insertAt_boundary, p.property, p.val.comp, property, source, target
-/
def toLoop (i : N) (p : Ω^ N X x) : Ω (Ω^ { j // j != i } X x) const where
  toFun t :=
    ⟨(p.val.comp (Cube.insertAt i)).curry t, fun y yH =>
      p.property (Cube.insertAt i (t, y)) (Cube.insertAt_boundary i <| Or.inr yH)⟩
  source' := by ext t; refine p.property (Cube.insertAt i (0, t)) ⟨i, Or.inl ?_⟩; simp
  target' := by ext t; refine p.property (Cube.insertAt i (1, t)) ⟨i, Or.inr ?_⟩; simp


/--
theorem `continuous_toLoop` / 定理 `continuous_toLoop`

English:
theorem continuous_toLoop
  given: (i : N)
  statement: Continuous (@toLoop N X _ x _ i)
  proof: Path.continuous_uncurry_iff.1
    Continuous.subtype_mk
      (continuous_eval.comp <|
        Continuous.prodMap
          (ContinuousMap.continuous_curry.comp <|
            (ContinuousMap.continuous_precomp _).comp continuous_subtype_val)
          continuous_id)
      _

中文:
定理 continuous_toLoop
  条件: (i : N)
  结论: Continuous (@toLoop N X _ x _ i)
  证明: Path.continuous_uncurry_iff.1
    Continuous.subtype_mk
      (continuous_eval.comp <|
        Continuous.prodMap
          (ContinuousMap.continuous_curry.comp <|
            (ContinuousMap.continuous_precomp _).comp continuous_subtype_val)
          continuous_id)
      _

Depends on / 依赖: Continuous, Continuous.prodMap, Continuous.subtype_mk, ContinuousMap, ContinuousMap.continuous_curry.comp, ContinuousMap.continuous_precomp, Path.continuous_uncurry_iff, continuous_curry, continuous_eval, continuous_eval.comp, continuous_id, continuous_precomp, continuous_subtype_val, continuous_uncurry_iff, prodMap, subtype_mk
-/
theorem continuous_toLoop (i : N) : Continuous (@toLoop N X _ x _ i) :=
Path.continuous_uncurry_iff.1
    Continuous.subtype_mk
      (continuous_eval.comp <|
        Continuous.prodMap
          (ContinuousMap.continuous_curry.comp <|
            (ContinuousMap.continuous_precomp _).comp continuous_subtype_val)
          continuous_id)
      _

/-- Generalized loop from a loop by uncurrying $I → (I^{N\setminus\{j\}} → X)$ into $I^N → X$. -/
@[simps]
/--
Definition of `fromLoop` / `fromLoop` 的定义

English:
definition fromLoop
  signature: (i : N) (p : Ω (Ω^ { j // j != i } X x) const)
  body: ⟨(ContinuousMap.comp ⟨Subtype.val, by fun_prop⟩ p.toContinuousMap).uncurry.comp
    (Cube.splitAt i),
    by
    rintro y ⟨j, Hj⟩
    simp only [ContinuousMap.comp_apply,
      funSplitAt_apply, ContinuousMap.uncurry_apply, ContinuousMap.coe_mk,
      Function.uncurry_apply_pair]
    obtain rfl | Hn

中文:
定义 fromLoop
  签名: (i : N) (p : Ω (Ω^ { j // j != i } X x) const)
  定义体: ⟨(ContinuousMap.comp ⟨Subtype.val, by fun_prop⟩ p.toContinuousMap).uncurry.comp
    (Cube.splitAt i),
    by
    rintro y ⟨j, Hj⟩
    simp only [ContinuousMap.comp_apply,
      funSplitAt_apply, ContinuousMap.uncurry_apply, ContinuousMap.coe_mk,
      Function.uncurry_apply_pair]
    obtain rfl | Hn

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, ContinuousMap.comp, ContinuousMap.comp_apply, ContinuousMap.uncurry_apply, Cube.splitAt, Function, Function.uncurry_apply_pair, GenLoop, GenLoop.boundary, Subtype, Subtype.val, boundary, coe_mk, coe_toContinuousMap, comp_apply, eq_or_ne, funSplitAt_apply, fun_prop, p.coe_toContinuousMap
-/
def fromLoop (i : N) (p : Ω (Ω^ { j // j != i } X x) const) : Ω^ N X x :=
  ⟨(ContinuousMap.comp ⟨Subtype.val, by fun_prop⟩ p.toContinuousMap).uncurry.comp
    (Cube.splitAt i),
    by
    rintro y ⟨j, Hj⟩
    simp only [ContinuousMap.comp_apply,
      funSplitAt_apply, ContinuousMap.uncurry_apply, ContinuousMap.coe_mk,
      Function.uncurry_apply_pair]
    obtain rfl | Hne := eq_or_ne j i
    · rcases Hj with Hj | Hj <;> simp only [Hj, p.coe_toContinuousMap, p.source, p.target] <;> rfl
    · exact GenLoop.boundary _ _ ⟨⟨j, Hne⟩, Hj⟩⟩

/--
theorem `continuous_fromLoop` / 定理 `continuous_fromLoop`

English:
theorem continuous_fromLoop
  given: (i : N)
  statement: Continuous (@fromLoop N X _ x _ i)
  proof: ((ContinuousMap.continuous_precomp _).comp <|
ContinuousMap.continuous_uncurry.comp
          (ContinuousMap.continuous_postcomp _).comp continuous_induced_dom).subtype_mk
    _

中文:
定理 continuous_fromLoop
  条件: (i : N)
  结论: Continuous (@fromLoop N X _ x _ i)
  证明: ((ContinuousMap.continuous_precomp _).comp <|
ContinuousMap.continuous_uncurry.comp
          (ContinuousMap.continuous_postcomp _).comp continuous_induced_dom).subtype_mk
    _

Depends on / 依赖: ContinuousMap, ContinuousMap.continuous_postcomp, ContinuousMap.continuous_precomp, ContinuousMap.continuous_uncurry.comp, continuous_induced_dom, continuous_postcomp, continuous_precomp, continuous_uncurry, subtype_mk
-/
theorem continuous_fromLoop (i : N) : Continuous (@fromLoop N X _ x _ i) :=
  ((ContinuousMap.continuous_precomp _).comp <|
ContinuousMap.continuous_uncurry.comp
          (ContinuousMap.continuous_postcomp _).comp continuous_induced_dom).subtype_mk
    _

/--
theorem `to_from` / 定理 `to_from`

English:
theorem to_from
  given: (i : N) (p : Ω (Ω^ { j // j != i } X x) const)
  statement: toLoop i (fromLoop i p) = p
  proof: by
  simp_rw [toLoop, fromLoop, ContinuousMap.comp_assoc,
    toContinuousMap_comp_symm, ContinuousMap.comp_id]
  ext; rfl

中文:
定理 to_from
  条件: (i : N) (p : Ω (Ω^ { j // j != i } X x) const)
  结论: toLoop i (fromLoop i p) = p
  证明: by
  simp_rw [toLoop, fromLoop, ContinuousMap.comp_assoc,
    toContinuousMap_comp_symm, ContinuousMap.comp_id]
  ext; rfl

Depends on / 依赖: ContinuousMap, ContinuousMap.comp_assoc, ContinuousMap.comp_id, comp_assoc, comp_id, fromLoop, simp_rw, toContinuousMap_comp_symm, toLoop
-/
theorem to_from (i : N) (p : Ω (Ω^ { j // j != i } X x) const) : toLoop i (fromLoop i p) = p := by
  simp_rw [toLoop, fromLoop, ContinuousMap.comp_assoc,
    toContinuousMap_comp_symm, ContinuousMap.comp_id]
  ext; rfl

/-- The `n+1`-dimensional loops are in bijection with the loops in the space of
  `n`-dimensional loops with base point `const`.
  We allow an arbitrary indexing type `N` in place of `Fin n` here. -/
@[simps]
/--
Definition of `loopHomeo` / `loopHomeo` 的定义

English:
definition loopHomeo
  signature: (i : N)
  body: toLoop i
  invFun := fromLoop i
  left_inv p := by ext; exact congr_arg p (by dsimp; exact Equiv.apply_symm_apply _ _)
  right_inv := to_from i
  continuous_toFun := continuous_toLoop i
  continuous_invFun := continuous_fromLoop i

中文:
定义 loopHomeo
  签名: (i : N)
  定义体: toLoop i
  invFun := fromLoop i
  left_inv p := by ext; exact congr_arg p (by dsimp; exact Equiv.apply_symm_apply _ _)
  right_inv := to_from i
  continuous_toFun := continuous_toLoop i
  continuous_invFun := continuous_fromLoop i

Depends on / 依赖: toLoop
-/
def loopHomeo (i : N) : Ω^ N X x ≃ₜ Ω (Ω^ { j // j != i } X x) const where
  toFun := toLoop i
  invFun := fromLoop i
  left_inv p := by ext; exact congr_arg p (by dsimp; exact Equiv.apply_symm_apply _ _)
  right_inv := to_from i
  continuous_toFun := continuous_toLoop i
  continuous_invFun := continuous_fromLoop i

/--
theorem `toLoop_apply` / 定理 `toLoop_apply`

English:
theorem toLoop_apply
  given: (i : N) {p : Ω^ N X x} {t} {tn}
  proof: rfl

中文:
定理 toLoop_apply
  条件: (i : N) {p : Ω^ N X x} {t} {tn}
  证明: rfl
-/
theorem toLoop_apply (i : N) {p : Ω^ N X x} {t} {tn} :
    toLoop i p t tn = p (Cube.insertAt i ⟨t, tn⟩) :=
  rfl

/--
theorem `fromLoop_apply` / 定理 `fromLoop_apply`

English:
theorem fromLoop_apply
  given: (i : N) {p : Ω (Ω^ { j // j != i } X x) const} {t : I^N}
  proof: rfl

中文:
定理 fromLoop_apply
  条件: (i : N) {p : Ω (Ω^ { j // j != i } X x) const} {t : I^N}
  证明: rfl
-/
theorem fromLoop_apply (i : N) {p : Ω (Ω^ { j // j != i } X x) const} {t : I^N} :
    fromLoop i p t = p (t i) (Cube.splitAt i t).snd :=
  rfl

/--
Definition of `cCompInsert` / `cCompInsert` 的定义

English:
abbreviation cCompInsert
  signature: (i : N)
  body: ⟨fun f => f.comp (Cube.insertAt i),
    (toContinuousMap <| Cube.insertAt i).continuous_precomp⟩

中文:
缩写 cCompInsert
  签名: (i : N)
  定义体: ⟨fun f => f.comp (Cube.insertAt i),
    (toContinuousMap <| Cube.insertAt i).continuous_precomp⟩

Depends on / 依赖: Cube.insertAt, continuous_precomp, f.comp, insertAt, toContinuousMap
-/
abbrev cCompInsert (i : N) : C(C(I^N, X), C(I × I^{ j // j != i }, X)) :=
  ⟨fun f => f.comp (Cube.insertAt i),
    (toContinuousMap <| Cube.insertAt i).continuous_precomp⟩

/--
Definition of `homotopyTo` / `homotopyTo` 的定义

English:
definition homotopyTo
  signature: (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 (Cube.boundary N))
  body: ((⟨_, ContinuousMap.continuous_curry⟩ : C(_, _)).comp <|
      (cCompInsert i).comp H.toContinuousMap.curry).uncurry

中文:
定义 homotopyTo
  签名: (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 (Cube.boundary N))
  定义体: ((⟨_, ContinuousMap.continuous_curry⟩ : C(_, _)).comp <|
      (cCompInsert i).comp H.toContinuousMap.curry).uncurry

Depends on / 依赖: ContinuousMap, ContinuousMap.continuous_curry, H.toContinuousMap.curry, cCompInsert, continuous_curry, toContinuousMap, uncurry
-/
def homotopyTo (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 (Cube.boundary N)) :
    C(I × I, C(I^{ j // j != i }, X)) :=
  ((⟨_, ContinuousMap.continuous_curry⟩ : C(_, _)).comp <|
      (cCompInsert i).comp H.toContinuousMap.curry).uncurry

-- `@[simps]` generates this lemma but it's named `homotopyTo_apply_apply` instead
/--
theorem `homotopyTo_apply` / 定理 `homotopyTo_apply`

English:
theorem homotopyTo_apply
  statement: (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 <| Cube.boundary N)
  proof: rfl

中文:
定理 homotopyTo_apply
  结论: (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 <| Cube.boundary N)
  证明: rfl
-/
theorem homotopyTo_apply (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 <| Cube.boundary N)
    (t : I × I) (tₙ : I^{ j // j != i }) :
    homotopyTo i H t tₙ = H (t.fst, Cube.insertAt i (t.snd, tₙ)) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `homotopicTo` / 定理 `homotopicTo`

English:
theorem homotopicTo
  given: (i : N) {p q : Ω^ N X x}
  proof: by
  refine Nonempty.map fun H => ⟨⟨⟨fun t => ⟨homotopyTo i H t, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩
  · rintro y ⟨i, iH⟩
    rw [homotopyTo_apply]; rw [H.eq_fst]; rw [p.2]
    all_goals apply Cube.insertAt_boundary; right; exact ⟨i, iH⟩
  · fun_prop
  iterate 2
    intro
    ext
    dsimp
    rw [homotopyTo_app

中文:
定理 homotopicTo
  条件: (i : N) {p q : Ω^ N X x}
  证明: by
  refine Nonempty.map fun H => ⟨⟨⟨fun t => ⟨homotopyTo i H t, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩
  · rintro y ⟨i, iH⟩
    rw [homotopyTo_apply]; rw [H.eq_fst]; rw [p.2]
    all_goals apply Cube.insertAt_boundary; right; exact ⟨i, iH⟩
  · fun_prop
  iterate 2
    intro
    ext
    dsimp
    rw [homotopyTo_app

Depends on / 依赖: Cube.insertAt_boundary, H.apply_one, H.apply_zero, H.eq_fst, Nonempty, Nonempty.map, all_goals, apply_one, apply_zero, dif_pos, eq_fst, funSplitAt_symm_apply, fun_prop, homotopyTo, homotopyTo_apply, insertAt_boundary, iterate, toLoop_apply
-/
theorem homotopicTo (i : N) {p q : Ω^ N X x} :
    Homotopic p q -> (toLoop i p).Homotopic (toLoop i q) := by
  refine Nonempty.map fun H => ⟨⟨⟨fun t => ⟨homotopyTo i H t, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩
  · rintro y ⟨i, iH⟩
    rw [homotopyTo_apply]; rw [H.eq_fst]; rw [p.2]
    all_goals apply Cube.insertAt_boundary; right; exact ⟨i, iH⟩
  · fun_prop
  iterate 2
    intro
    ext
    dsimp
    rw [homotopyTo_apply]; rw [toLoop_apply]
    swap
  · apply H.apply_zero
  · apply H.apply_one
  intro t y yH
  ext
  dsimp
  rw [homotopyTo_apply]
  apply H.eq_fst; use i
  rw [funSplitAt_symm_apply]; rw [dif_pos rfl]; exact yH

/--
Definition of `homotopyFrom` / `homotopyFrom` 的定义

English:
definition homotopyFrom
  signature: (i : N) {p q : Ω^ N X x} (H : (toLoop i p).Homotopy (toLoop i q))
  body: (ContinuousMap.comp ⟨_, ContinuousMap.continuous_uncurry⟩
          (ContinuousMap.comp ⟨Subtype.val, by fun_prop⟩ H.toContinuousMap).curry).uncurry.comp <|
    (ContinuousMap.id I).prodMap (Cube.splitAt i)

中文:
定义 homotopyFrom
  签名: (i : N) {p q : Ω^ N X x} (H : (toLoop i p).Homotopy (toLoop i q))
  定义体: (ContinuousMap.comp ⟨_, ContinuousMap.continuous_uncurry⟩
          (ContinuousMap.comp ⟨Subtype.val, by fun_prop⟩ H.toContinuousMap).curry).uncurry.comp <|
    (ContinuousMap.id I).prodMap (Cube.splitAt i)
-/
@[simps!] def homotopyFrom (i : N) {p q : Ω^ N X x} (H : (toLoop i p).Homotopy (toLoop i q)) :
    C(I × I^N, X) :=
  (ContinuousMap.comp ⟨_, ContinuousMap.continuous_uncurry⟩
          (ContinuousMap.comp ⟨Subtype.val, by fun_prop⟩ H.toContinuousMap).curry).uncurry.comp <|
    (ContinuousMap.id I).prodMap (Cube.splitAt i)

/--
theorem `homotopicFrom` / 定理 `homotopicFrom`

English:
theorem homotopicFrom
  given: (i : N) {p q : Ω^ N X x}
  proof: by
  refine Nonempty.map fun H => ⟨⟨homotopyFrom i H, ?_, ?_⟩, ?_⟩
  pick_goal 3
  · rintro t y ⟨j, jH⟩
    erw [homotopyFrom_apply]
    obtain rfl | h := eq_or_ne j i
    · simp only [Prod.map_apply, id_eq, funSplitAt_apply, Function.uncurry_apply_pair]
      rw [H.eq_fst]
      exacts [congr_arg p

中文:
定理 homotopicFrom
  条件: (i : N) {p q : Ω^ N X x}
  证明: by
  refine Nonempty.map fun H => ⟨⟨homotopyFrom i H, ?_, ?_⟩, ?_⟩
  pick_goal 3
  · rintro t y ⟨j, jH⟩
    erw [homotopyFrom_apply]
    obtain rfl | h := eq_or_ne j i
    · simp only [Prod.map_apply, id_eq, funSplitAt_apply, Function.uncurry_apply_pair]
      rw [H.eq_fst]
      exacts [congr_arg p

Depends on / 依赖: Cube.splitAt, Function, Function.uncurry_apply_pair, H.eq_fst, Nonempty, Nonempty.map, Prod.map_apply, all_goals, boundary, congr_arg, eq_fst, eq_or_ne, exacts, funSplitAt_apply, homotopyFrom, homotopyFrom_apply, id_eq, left_inv, map_apply, pick_goal
-/
theorem homotopicFrom (i : N) {p q : Ω^ N X x} :
    (toLoop i p).Homotopic (toLoop i q) -> Homotopic p q := by
  refine Nonempty.map fun H => ⟨⟨homotopyFrom i H, ?_, ?_⟩, ?_⟩
  pick_goal 3
  · rintro t y ⟨j, jH⟩
    erw [homotopyFrom_apply]
    obtain rfl | h := eq_or_ne j i
    · simp only [Prod.map_apply, id_eq, funSplitAt_apply, Function.uncurry_apply_pair]
      rw [H.eq_fst]
      exacts [congr_arg p ((Cube.splitAt j).left_inv _), jH]
    · rw [p.2 _ ⟨j, jH⟩]; apply boundary; exact ⟨⟨j, h⟩, jH⟩
  all_goals
    intro
    apply (homotopyFrom_apply _ _ _).trans
    simp only [Prod.map_apply, id_eq, funSplitAt_apply,
      Function.uncurry_apply_pair, ContinuousMap.HomotopyWith.apply_zero,
      ContinuousMap.HomotopyWith.apply_one, ne_eq, Path.coe_toContinuousMap]
    first
    | apply congr_arg p
    | apply congr_arg q
    apply (Cube.splitAt i).left_inv

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `transAt` / `transAt` 的定义

English:
definition transAt
  signature: (i : N) (f g : Ω^ N X x)
  body: copy (fromLoop i <| (toLoop i f).trans <| toLoop i g)
    (fun t => if (t i : Real) <= 1 / 2
      then f (Function.update t i <| Set.projIcc 0 1 zero_le_one (2 * t i))
      else g (Function.update t i <| Set.projIcc 0 1 zero_le_one (2 * t i - 1)))
    (by
      ext1; symm
      dsimp only [Path.tr

中文:
定义 transAt
  签名: (i : N) (f g : Ω^ N X x)
  定义体: copy (fromLoop i <| (toLoop i f).trans <| toLoop i g)
    (fun t => if (t i : Real) <= 1 / 2
      then f (Function.update t i <| Set.projIcc 0 1 zero_le_one (2 * t i))
      else g (Function.update t i <| Set.projIcc 0 1 zero_le_one (2 * t i - 1)))
    (by
      ext1; symm
      dsimp only [Path.tr

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_coe, ContinuousMap.coe_mk, ContinuousMap.comp_apply, ContinuousMap.uncurry_apply, Function, Function.comp_apply, Function.uncurry_apply_pair, Function.update, Path.coe_mk_mk, Path.trans, Set.projIcc, coe_coe, coe_mk, coe_mk_mk, comp_apply, fromLoop, funSplitAt_apply, mk_apply, projIcc
-/
def transAt (i : N) (f g : Ω^ N X x) : Ω^ N X x :=
  copy (fromLoop i <| (toLoop i f).trans <| toLoop i g)
    (fun t => if (t i : Real) <= 1 / 2
      then f (Function.update t i <| Set.projIcc 0 1 zero_le_one (2 * t i))
      else g (Function.update t i <| Set.projIcc 0 1 zero_le_one (2 * t i - 1)))
    (by
      ext1; symm
      dsimp only [Path.trans, fromLoop, Path.coe_mk_mk, Function.comp_apply, mk_apply,
        ContinuousMap.comp_apply, ContinuousMap.coe_coe, funSplitAt_apply,
        ContinuousMap.uncurry_apply, ContinuousMap.coe_mk, Function.uncurry_apply_pair]
      split_ifs
      · change f _ = _; congr 1
      · change g _ = _; congr 1)

/--
Definition of `symmAt` / `symmAt` 的定义

English:
definition symmAt
  signature: (i : N) (f : Ω^ N X x)
  body: (copy (fromLoop i (toLoop i f).symm) fun t => f fun j => if j = i then σ (t i) else t j) by
    ext1; change _ = f _; congr; ext1; simp

中文:
定义 symmAt
  签名: (i : N) (f : Ω^ N X x)
  定义体: (copy (fromLoop i (toLoop i f).symm) fun t => f fun j => if j = i then σ (t i) else t j) by
    ext1; change _ = f _; congr; ext1; simp

Depends on / 依赖: fromLoop, toLoop
-/
def symmAt (i : N) (f : Ω^ N X x) : Ω^ N X x :=
(copy (fromLoop i (toLoop i f).symm) fun t => f fun j => if j = i then σ (t i) else t j) by
    ext1; change _ = f _; congr; ext1; simp

/--
theorem `transAt_distrib` / 定理 `transAt_distrib`

English:
theorem transAt_distrib
  given: {i j : N} (h : i != j) (a b c d : Ω^ N X x)
  proof: by
  ext; simp_rw [transAt, coe_copy, Function.update_apply, if_neg h, if_neg h.symm]
  split_ifs <;>
    · congr 1; ext1; simp only [Function.update, eq_rec_constant, dite_eq_ite]
      apply ite_ite_comm; rintro rfl; exact h.symm

中文:
定理 transAt_distrib
  条件: {i j : N} (h : i != j) (a b c d : Ω^ N X x)
  证明: by
  ext; simp_rw [transAt, coe_copy, Function.update_apply, if_neg h, if_neg h.symm]
  split_ifs <;>
    · congr 1; ext1; simp only [Function.update, eq_rec_constant, dite_eq_ite]
      apply ite_ite_comm; rintro rfl; exact h.symm

Depends on / 依赖: Function, Function.update, Function.update_apply, coe_copy, dite_eq_ite, eq_rec_constant, h.symm, if_neg, ite_ite_comm, simp_rw, split_ifs, transAt, update, update_apply
-/
theorem transAt_distrib {i j : N} (h : i != j) (a b c d : Ω^ N X x) :
    transAt i (transAt j a b) (transAt j c d) = transAt j (transAt i a c) (transAt i b d) := by
  ext; simp_rw [transAt, coe_copy, Function.update_apply, if_neg h, if_neg h.symm]
  split_ifs <;>
    · congr 1; ext1; simp only [Function.update, eq_rec_constant, dite_eq_ite]
      apply ite_ite_comm; rintro rfl; exact h.symm

/--
theorem `fromLoop_trans_toLoop` / 定理 `fromLoop_trans_toLoop`

English:
theorem fromLoop_trans_toLoop
  given: {i : N} {p q : Ω^ N X x}
  proof: (copy_eq _ _).symm

中文:
定理 fromLoop_trans_toLoop
  条件: {i : N} {p q : Ω^ N X x}
  证明: (copy_eq _ _).symm

Depends on / 依赖: copy_eq
-/
theorem fromLoop_trans_toLoop {i : N} {p q : Ω^ N X x} :
    fromLoop i ((toLoop i p).trans <| toLoop i q) = transAt i p q :=
  (copy_eq _ _).symm

/--
theorem `fromLoop_symm_toLoop` / 定理 `fromLoop_symm_toLoop`

English:
theorem fromLoop_symm_toLoop
  given: {i : N} {p : Ω^ N X x}
  statement: fromLoop i (toLoop i p).symm = symmAt i p
  proof: (copy_eq _ _).symm

中文:
定理 fromLoop_symm_toLoop
  条件: {i : N} {p : Ω^ N X x}
  结论: fromLoop i (toLoop i p).symm = symmAt i p
  证明: (copy_eq _ _).symm

Depends on / 依赖: copy_eq
-/
theorem fromLoop_symm_toLoop {i : N} {p : Ω^ N X x} : fromLoop i (toLoop i p).symm = symmAt i p :=
  (copy_eq _ _).symm

end LoopHomeo

end GenLoop

/--
Definition of `HomotopyGroup` / `HomotopyGroup` 的定义

English:
definition HomotopyGroup
  signature: (N X : Type*) [TopologicalSpace X] (x : X)
  body: Quotient (GenLoop.Homotopic.setoid N x)

中文:
定义 HomotopyGroup
  签名: (N X : 类型) [TopologicalSpace X] (x : X)
  定义体: Quotient (GenLoop.Homotopic.setoid N x)

Depends on / 依赖: GenLoop, GenLoop.Homotopic.setoid, Homotopic, Quotient, setoid
-/
def HomotopyGroup (N X : Type*) [TopologicalSpace X] (x : X) : Type _ :=
  Quotient (GenLoop.Homotopic.setoid N x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (HomotopyGroup N X x)
  body: inferInstanceAs Inhabited Quotient (GenLoop.Homotopic.setoid N x)

中文:
实例 :
  签名: Inhabited (HomotopyGroup N X x)
  定义体: inferInstanceAs Inhabited Quotient (GenLoop.Homotopic.setoid N x)

Depends on / 依赖: GenLoop, GenLoop.Homotopic.setoid, Homotopic, Inhabited, Quotient, setoid
-/
instance : Inhabited (HomotopyGroup N X x) :=
inferInstanceAs Inhabited Quotient (GenLoop.Homotopic.setoid N x)

variable [DecidableEq N]

open GenLoop

/--
Definition of `homotopyGroupEquivFundamentalGroup` / `homotopyGroupEquivFundamentalGroup` 的定义

English:
definition homotopyGroupEquivFundamentalGroup
  signature: (i : N)
  body: Quotient.congr (loopHomeo i).toEquiv fun _ _ => ⟨homotopicTo i, homotopicFrom i⟩

中文:
定义 homotopyGroupEquivFundamentalGroup
  签名: (i : N)
  定义体: Quotient.congr (loopHomeo i).toEquiv fun _ _ => ⟨homotopicTo i, homotopicFrom i⟩

Depends on / 依赖: Quotient, Quotient.congr, homotopicFrom, homotopicTo, loopHomeo, toEquiv
-/
def homotopyGroupEquivFundamentalGroup (i : N) :
    HomotopyGroup N X x ≃ FundamentalGroup (Ω^ { j // j != i } X x) const :=
  Quotient.congr (loopHomeo i).toEquiv fun _ _ => ⟨homotopicTo i, homotopicFrom i⟩

/--
Definition of `HomotopyGroup.Pi` / `HomotopyGroup.Pi` 的定义

English:
abbreviation HomotopyGroup.Pi
  signature: (n) (X : Type*) [TopologicalSpace X] (x : X)
  body: HomotopyGroup (Fin n) _ x

@[inherit_doc] scoped[Topology] notation "π_" => HomotopyGroup.Pi

中文:
缩写 HomotopyGroup.Pi
  签名: (n) (X : 类型) [TopologicalSpace X] (x : X)
  定义体: HomotopyGroup (Fin n) _ x

@[inherit_doc] scoped[Topology] notation "π_" => HomotopyGroup.Pi

Depends on / 依赖: HomotopyGroup
-/
abbrev HomotopyGroup.Pi (n) (X : Type*) [TopologicalSpace X] (x : X) :=
  HomotopyGroup (Fin n) _ x

@[inherit_doc] scoped[Topology] notation "π_" => HomotopyGroup.Pi

/--
Definition of `genLoopHomeoOfIsEmpty` / `genLoopHomeoOfIsEmpty` 的定义

English:
definition genLoopHomeoOfIsEmpty
  signature: (N x) [IsEmpty N]
  body: f 0
  invFun y := ⟨ContinuousMap.const _ y, fun _ ⟨i, _⟩ => isEmptyElim i⟩
  left_inv f := by ext; exact congr_arg f (Subsingleton.elim _ _)
  continuous_invFun := ContinuousMap.const'.2.subtype_mk _

中文:
定义 genLoopHomeoOfIsEmpty
  签名: (N x) [IsEmpty N]
  定义体: f 0
  invFun y := ⟨ContinuousMap.const _ y, fun _ ⟨i, _⟩ => isEmptyElim i⟩
  left_inv f := by ext; exact congr_arg f (Subsingleton.elim _ _)
  continuous_invFun := ContinuousMap.const'.2.subtype_mk _
-/
def genLoopHomeoOfIsEmpty (N x) [IsEmpty N] : Ω^ N X x ≃ₜ X where
  toFun f := f 0
  invFun y := ⟨ContinuousMap.const _ y, fun _ ⟨i, _⟩ => isEmptyElim i⟩
  left_inv f := by ext; exact congr_arg f (Subsingleton.elim _ _)
  continuous_invFun := ContinuousMap.const'.2.subtype_mk _

/--
Definition of `homotopyGroupEquivZerothHomotopyOfIsEmpty` / `homotopyGroupEquivZerothHomotopyOfIsEmpty` 的定义

English:
definition homotopyGroupEquivZerothHomotopyOfIsEmpty
  signature: (N x) [IsEmpty N]
  body: Quotient.congr (genLoopHomeoOfIsEmpty N x).toEquiv
    (by
      -- joined iff homotopic
      intro a₁ a₂
      constructor <;> rintro ⟨H⟩
      exacts
        [⟨{ toFun := fun t => H ⟨t, isEmptyElim⟩
            source' := (H.apply_zero _).trans (congr_arg a₁ <| Subsingleton.elim _ _)
            

中文:
定义 homotopyGroupEquivZerothHomotopyOfIsEmpty
  签名: (N x) [IsEmpty N]
  定义体: Quotient.congr (genLoopHomeoOfIsEmpty N x).toEquiv
    (by
      -- joined iff homotopic
      intro a₁ a₂
      constructor <;> rintro ⟨H⟩
      exacts
        [⟨{ toFun := fun t => H ⟨t, isEmptyElim⟩
            source' := (H.apply_zero _).trans (congr_arg a₁ <| Subsingleton.elim _ _)
            

Depends on / 依赖: Quotient, Quotient.congr, genLoopHomeoOfIsEmpty, toEquiv
-/
def homotopyGroupEquivZerothHomotopyOfIsEmpty (N x) [IsEmpty N] :
    HomotopyGroup N X x ≃ ZerothHomotopy X :=
  Quotient.congr (genLoopHomeoOfIsEmpty N x).toEquiv
    (by
      -- joined iff homotopic
      intro a₁ a₂
      constructor <;> rintro ⟨H⟩
      exacts
        [⟨{ toFun := fun t => H ⟨t, isEmptyElim⟩
            source' := (H.apply_zero _).trans (congr_arg a₁ <| Subsingleton.elim _ _)
            target' := (H.apply_one _).trans (congr_arg a₂ <| Subsingleton.elim _ _) }⟩,
        ⟨{ toFun := fun t0 => H t0.fst
            map_zero_left := fun _ => H.source.trans (congr_arg a₁ <| Subsingleton.elim _ _)
            map_one_left := fun _ => H.target.trans (congr_arg a₂ <| Subsingleton.elim _ _)
            prop' := fun _ _ ⟨i, _⟩ => isEmptyElim i }⟩])

/--
Definition of `HomotopyGroup.pi0EquivZerothHomotopy` / `HomotopyGroup.pi0EquivZerothHomotopy` 的定义

English:
definition HomotopyGroup.pi0EquivZerothHomotopy
  signature: : π_ 0 X x ≃ ZerothHomotopy X
  body: homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) x

中文:
定义 HomotopyGroup.pi0EquivZerothHomotopy
  签名: : π_ 0 X x ≃ ZerothHomotopy X
  定义体: homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) x

Depends on / 依赖: homotopyGroupEquivZerothHomotopyOfIsEmpty
-/
def HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x ≃ ZerothHomotopy X :=
  homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) x

/--
Definition of `genLoopEquivOfUnique` / `genLoopEquivOfUnique` 的定义

English:
definition genLoopEquivOfUnique
  signature: (N) [Unique N]
  body: Path.mk ⟨fun t => p fun _ => t, by fun_prop⟩
      (GenLoop.boundary _ (fun _ => 0) ⟨default, Or.inl rfl⟩)
      (GenLoop.boundary _ (fun _ => 1) ⟨default, Or.inr rfl⟩)
  invFun p :=
    ⟨⟨fun c => p (c default), by fun_prop⟩,
      by
      rintro y ⟨i, iH | iH⟩ <;> cases Unique.eq_default i <;> ap

中文:
定义 genLoopEquivOfUnique
  签名: (N) [Unique N]
  定义体: Path.mk ⟨fun t => p fun _ => t, by fun_prop⟩
      (GenLoop.boundary _ (fun _ => 0) ⟨default, Or.inl rfl⟩)
      (GenLoop.boundary _ (fun _ => 1) ⟨default, Or.inr rfl⟩)
  invFun p :=
    ⟨⟨fun c => p (c default), by fun_prop⟩,
      by
      rintro y ⟨i, iH | iH⟩ <;> cases Unique.eq_default i <;> ap

Depends on / 依赖: GenLoop, GenLoop.boundary, Or.inl, Or.inr, Path.mk, Unique, Unique.eq_default, boundary, congr_arg, eq_const_of_unique, eq_default, exacts, fun_prop, invFun, left_inv, p.source, p.target, source, target
-/
def genLoopEquivOfUnique (N) [Unique N] : Ω^ N X x ≃ Ω X x where
  toFun p :=
    Path.mk ⟨fun t => p fun _ => t, by fun_prop⟩
      (GenLoop.boundary _ (fun _ => 0) ⟨default, Or.inl rfl⟩)
      (GenLoop.boundary _ (fun _ => 1) ⟨default, Or.inr rfl⟩)
  invFun p :=
    ⟨⟨fun c => p (c default), by fun_prop⟩,
      by
      rintro y ⟨i, iH | iH⟩ <;> cases Unique.eq_default i <;> apply (congr_arg p iH).trans
      exacts [p.source, p.target]⟩
  left_inv p := by ext y; exact congr_arg p (eq_const_of_unique y).symm

/- TODO (?): deducing this from `homotopyGroupEquivFundamentalGroup` would require
  combination of `CategoryTheory.Functor.mapAut` and
  `FundamentalGroupoid.fundamentalGroupoidFunctor` applied to `genLoopHomeoOfIsEmpty`,
  with possibly worse defeq. -/
/--
Definition of `homotopyGroupEquivFundamentalGroupOfUnique` / `homotopyGroupEquivFundamentalGroupOfUnique` 的定义

English:
definition homotopyGroupEquivFundamentalGroupOfUnique
  signature: (N) [Unique N]
  body: Quotient.congr (genLoopEquivOfUnique N) fun a₁ a₂ => by
    constructor <;> rintro ⟨H⟩
    · exact
        ⟨{ toFun := fun tx => H (tx.fst, fun _ => tx.snd)
            map_zero_left := fun _ => H.apply_zero _
            map_one_left := fun _ => H.apply_one _
            prop' := fun t y iH => H.pr

中文:
定义 homotopyGroupEquivFundamentalGroupOfUnique
  签名: (N) [Unique N]
  定义体: Quotient.congr (genLoopEquivOfUnique N) fun a₁ a₂ => by
    constructor <;> rintro ⟨H⟩
    · exact
        ⟨{ toFun := fun tx => H (tx.fst, fun _ => tx.snd)
            map_zero_left := fun _ => H.apply_zero _
            map_one_left := fun _ => H.apply_one _
            prop' := fun t y iH => H.pr

Depends on / 依赖: H.apply_one, H.apply_zero, H.continuous.comp, H.prop, Quotient, Quotient.congr, apply_one, apply_zero, congr_a, congr_arg, continuous, eq_const_of_unique, fun_prop, genLoopEquivOfUnique, map_one_left, map_zero_left, tx.fst, tx.snd
-/
def homotopyGroupEquivFundamentalGroupOfUnique (N) [Unique N] :
    HomotopyGroup N X x ≃ FundamentalGroup X x :=
  Quotient.congr (genLoopEquivOfUnique N) fun a₁ a₂ => by
    constructor <;> rintro ⟨H⟩
    · exact
        ⟨{ toFun := fun tx => H (tx.fst, fun _ => tx.snd)
            map_zero_left := fun _ => H.apply_zero _
            map_one_left := fun _ => H.apply_one _
            prop' := fun t y iH => H.prop' _ _ ⟨default, iH⟩ }⟩
    refine
      ⟨⟨⟨⟨fun tx => H (tx.fst, tx.snd default), H.continuous.comp ?_⟩, fun y => ?_, fun y => ?_⟩, ?_⟩⟩
    · fun_prop
    · exact (H.apply_zero _).trans (congr_arg a₁ (eq_const_of_unique y).symm)
    · exact (H.apply_one _).trans (congr_arg a₂ (eq_const_of_unique y).symm)
    · rintro t y ⟨i, iH⟩
      cases Unique.eq_default i
      exact (H.eq_fst _ iH).trans (congr_arg a₁ (eq_const_of_unique y).symm)

/--
Definition of `HomotopyGroup.pi1EquivFundamentalGroup` / `HomotopyGroup.pi1EquivFundamentalGroup` 的定义

English:
definition HomotopyGroup.pi1EquivFundamentalGroup
  signature: : π_ 1 X x ≃ FundamentalGroup X x
  body: homotopyGroupEquivFundamentalGroupOfUnique (Fin 1)

中文:
定义 HomotopyGroup.pi1EquivFundamentalGroup
  签名: : π_ 1 X x ≃ FundamentalGroup X x
  定义体: homotopyGroupEquivFundamentalGroupOfUnique (Fin 1)

Depends on / 依赖: homotopyGroupEquivFundamentalGroupOfUnique
-/
def HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X x ≃ FundamentalGroup X x :=
  homotopyGroupEquivFundamentalGroupOfUnique (Fin 1)

/--
lemma `HomotopyGroup.genLoopEquivOfUnique_transAt` / 引理 `HomotopyGroup.genLoopEquivOfUnique_transAt`

English:
lemma HomotopyGroup.genLoopEquivOfUnique_transAt
  given: (N) [DecidableEq N] [Unique N] (p q : Ω^ N X x)
  proof: by
  ext t
  simp only [genLoopEquivOfUnique, GenLoop.transAt, GenLoop.copy,
    one_div, ContinuousMap.coe_mk, Path.coe_mk', Path.trans,
    Function.comp_apply]
  refine ite_congr rfl (fun _ => congrArg q ?_)
    fun _ => congrArg p ?_
  <;> (ext i; rw [Unique.eq_default i]; simp)

中文:
引理 HomotopyGroup.genLoopEquivOfUnique_transAt
  条件: (N) [DecidableEq N] [Unique N] (p q : Ω^ N X x)
  证明: by
  ext t
  simp only [genLoopEquivOfUnique, GenLoop.transAt, GenLoop.copy,
    one_div, ContinuousMap.coe_mk, Path.coe_mk', Path.trans,
    Function.comp_apply]
  refine ite_congr rfl (fun _ => congrArg q ?_)
    fun _ => congrArg p ?_
  <;> (ext i; rw [Unique.eq_default i]; simp)

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, Function, Function.comp_apply, GenLoop, GenLoop.copy, GenLoop.transAt, Path.coe_mk, Path.trans, Unique, Unique.eq_default, coe_mk, comp_apply, eq_default, genLoopEquivOfUnique, ite_congr, one_div, transAt
-/
lemma HomotopyGroup.genLoopEquivOfUnique_transAt (N) [DecidableEq N] [Unique N] (p q : Ω^ N X x) :
    genLoopEquivOfUnique _ (transAt default q p) =
      (genLoopEquivOfUnique _ q).trans (genLoopEquivOfUnique _ p) := by
  ext t
  simp only [genLoopEquivOfUnique, GenLoop.transAt, GenLoop.copy,
    one_div, ContinuousMap.coe_mk, Path.coe_mk', Path.trans,
    Function.comp_apply]
  refine ite_congr rfl (fun _ => congrArg q ?_)
    fun _ => congrArg p ?_
  <;> (ext i; rw [Unique.eq_default i]; simp)

namespace HomotopyGroup

/--
Instance `group` / 实例 `group`

English:
instance group
  signature: (N) [DecidableEq N] [Nonempty N]
  body: (homotopyGroupEquivFundamentalGroup <| Classical.arbitrary N).group

中文:
实例 group
  签名: (N) [DecidableEq N] [Nonempty N]
  定义体: (homotopyGroupEquivFundamentalGroup <| Classical.arbitrary N).group

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, homotopyGroupEquivFundamentalGroup
-/
instance group (N) [DecidableEq N] [Nonempty N] : Group (HomotopyGroup N X x) :=
  (homotopyGroupEquivFundamentalGroup <| Classical.arbitrary N).group

/--
Definition of `auxGroup` / `auxGroup` 的定义

English:
abbreviation auxGroup
  signature: (i : N)
  body: (homotopyGroupEquivFundamentalGroup i).group

中文:
缩写 auxGroup
  签名: (i : N)
  定义体: (homotopyGroupEquivFundamentalGroup i).group

Depends on / 依赖: homotopyGroupEquivFundamentalGroup
-/
abbrev auxGroup (i : N) : Group (HomotopyGroup N X x) :=
  (homotopyGroupEquivFundamentalGroup i).group

/--
theorem `isUnital_auxGroup` / 定理 `isUnital_auxGroup`

English:
theorem isUnital_auxGroup
  given: (i : N)
  proof: (auxGroup i).one_mul
  right_id := (auxGroup i).mul_one

中文:
定理 isUnital_auxGroup
  条件: (i : N)
  证明: (auxGroup i).one_mul
  right_id := (auxGroup i).mul_one

Depends on / 依赖: auxGroup, one_mul
-/
theorem isUnital_auxGroup (i : N) :
    EckmannHilton.IsUnital (auxGroup i).mul (⟦const⟧ : HomotopyGroup N X x) where
  left_id := (auxGroup i).one_mul
  right_id := (auxGroup i).mul_one

/--
theorem `auxGroup_indep` / 定理 `auxGroup_indep`

English:
theorem auxGroup_indep
  given: (i j : N)
  statement: (auxGroup i : Group (HomotopyGroup N X x)) = auxGroup j
  proof: by
  by_cases h : i = j; · rw [h]
  refine Group.ext (EckmannHilton.mul (isUnital_auxGroup i) (isUnital_auxGroup j) ?_)
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
  change Quotient.mk' _ = _
  apply congr_arg Quotient.mk'
  simp only [fromLoop_trans_toLoop, transAt_distrib h, coe_toEquiv, loopHomeo_apply,
    coe_sym

中文:
定理 auxGroup_indep
  条件: (i j : N)
  结论: (auxGroup i : Group (HomotopyGroup N X x)) = auxGroup j
  证明: by
  by_cases h : i = j; · rw [h]
  refine Group.ext (EckmannHilton.mul (isUnital_auxGroup i) (isUnital_auxGroup j) ?_)
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
  change Quotient.mk' _ = _
  apply congr_arg Quotient.mk'
  simp only [fromLoop_trans_toLoop, transAt_distrib h, coe_toEquiv, loopHomeo_apply,
    coe_sym

Depends on / 依赖: EckmannHilton, EckmannHilton.mul, Group.ext, Quotient, Quotient.mk, coe_symm_toEquiv, coe_toEquiv, congr_arg, fromLoop_trans_toLoop, isUnital_auxGroup, loopHomeo_apply, loopHomeo_symm_apply, transAt_distrib
-/
theorem auxGroup_indep (i j : N) : (auxGroup i : Group (HomotopyGroup N X x)) = auxGroup j := by
  by_cases h : i = j; · rw [h]
  refine Group.ext (EckmannHilton.mul (isUnital_auxGroup i) (isUnital_auxGroup j) ?_)
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
  change Quotient.mk' _ = _
  apply congr_arg Quotient.mk'
  simp only [fromLoop_trans_toLoop, transAt_distrib h, coe_toEquiv, loopHomeo_apply,
    coe_symm_toEquiv, loopHomeo_symm_apply]

/--
theorem `transAt_indep` / 定理 `transAt_indep`

English:
theorem transAt_indep
  given: {i} (j) (f g : Ω^ N X x)
  proof: by
  simp_rw [← fromLoop_trans_toLoop]
  let m := fun (G) (_ : Group G) => ((· * ·) : G -> G -> G)
  exact congr_fun₂ (congr_arg (m <| HomotopyGroup N X x) <| auxGroup_indep i j) ⟦g⟧ ⟦f⟧

中文:
定理 transAt_indep
  条件: {i} (j) (f g : Ω^ N X x)
  证明: by
  simp_rw [← fromLoop_trans_toLoop]
  let m := fun (G) (_ : Group G) => ((· * ·) : G -> G -> G)
  exact congr_fun₂ (congr_arg (m <| HomotopyGroup N X x) <| auxGroup_indep i j) ⟦g⟧ ⟦f⟧

Depends on / 依赖: HomotopyGroup, auxGroup_indep, congr_arg, fromLoop_trans_toLoop, simp_rw
-/
theorem transAt_indep {i} (j) (f g : Ω^ N X x) :
    (⟦transAt i f g⟧ : HomotopyGroup N X x) = ⟦transAt j f g⟧ := by
  simp_rw [← fromLoop_trans_toLoop]
  let m := fun (G) (_ : Group G) => ((· * ·) : G -> G -> G)
  exact congr_fun₂ (congr_arg (m <| HomotopyGroup N X x) <| auxGroup_indep i j) ⟦g⟧ ⟦f⟧

/--
theorem `symmAt_indep` / 定理 `symmAt_indep`

English:
theorem symmAt_indep
  given: {i} (j) (f : Ω^ N X x)
  proof: by
  simp_rw [← fromLoop_symm_toLoop]
  let inv := fun (G) (_ : Group G) => ((·⁻¹) : G -> G)
  exact congr_fun (congr_arg (inv <| HomotopyGroup N X x) <| auxGroup_indep i j) ⟦f⟧

中文:
定理 symmAt_indep
  条件: {i} (j) (f : Ω^ N X x)
  证明: by
  simp_rw [← fromLoop_symm_toLoop]
  let inv := fun (G) (_ : Group G) => ((·⁻¹) : G -> G)
  exact congr_fun (congr_arg (inv <| HomotopyGroup N X x) <| auxGroup_indep i j) ⟦f⟧

Depends on / 依赖: HomotopyGroup, auxGroup_indep, congr_arg, congr_fun, fromLoop_symm_toLoop, simp_rw
-/
theorem symmAt_indep {i} (j) (f : Ω^ N X x) :
    (⟦symmAt i f⟧ : HomotopyGroup N X x) = ⟦symmAt j f⟧ := by
  simp_rw [← fromLoop_symm_toLoop]
  let inv := fun (G) (_ : Group G) => ((·⁻¹) : G -> G)
  exact congr_fun (congr_arg (inv <| HomotopyGroup N X x) <| auxGroup_indep i j) ⟦f⟧

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  given: [Nonempty N]
  statement: (1 : HomotopyGroup N X x) = ⟦const⟧
  proof: rfl

中文:
定理 one_def
  条件: [Nonempty N]
  结论: (1 : HomotopyGroup N X x) = ⟦const⟧
  证明: rfl
-/
theorem one_def [Nonempty N] : (1 : HomotopyGroup N X x) = ⟦const⟧ :=
  rfl

/--
theorem `mul_spec` / 定理 `mul_spec`

English:
theorem mul_spec
  given: [Nonempty N] {i} {p q : Ω^ N X x}
  proof: by
  rw [transAt_indep (Classical.arbitrary N) q]; rw [← fromLoop_trans_toLoop]
  apply Quotient.sound
  rfl

中文:
定理 mul_spec
  条件: [Nonempty N] {i} {p q : Ω^ N X x}
  证明: by
  rw [transAt_indep (Classical.arbitrary N) q]; rw [← fromLoop_trans_toLoop]
  apply Quotient.sound
  rfl

Depends on / 依赖: Classical, Classical.arbitrary, Quotient, Quotient.sound, arbitrary, fromLoop_trans_toLoop, transAt_indep
-/
theorem mul_spec [Nonempty N] {i} {p q : Ω^ N X x} :
    -- TODO: introduce `HomotopyGroup.mk` and remove defeq abuse.
    ((· * ·) : _ -> _ -> HomotopyGroup N X x) ⟦p⟧ ⟦q⟧ = ⟦transAt i q p⟧ := by
  rw [transAt_indep (Classical.arbitrary N) q]; rw [← fromLoop_trans_toLoop]
  apply Quotient.sound
  rfl

/--
theorem `inv_spec` / 定理 `inv_spec`

English:
theorem inv_spec
  given: [Nonempty N] {i} {p : Ω^ N X x}
  proof: by
  rw [symmAt_indep (Classical.arbitrary N) p]; rw [← fromLoop_symm_toLoop]
  apply Quotient.sound
  rfl

中文:
定理 inv_spec
  条件: [Nonempty N] {i} {p : Ω^ N X x}
  证明: by
  rw [symmAt_indep (Classical.arbitrary N) p]; rw [← fromLoop_symm_toLoop]
  apply Quotient.sound
  rfl

Depends on / 依赖: Classical, Classical.arbitrary, Quotient, Quotient.sound, arbitrary, fromLoop_symm_toLoop, symmAt_indep
-/
theorem inv_spec [Nonempty N] {i} {p : Ω^ N X x} :
    ((⟦p⟧)⁻¹ : HomotopyGroup N X x) = ⟦symmAt i p⟧ := by
  rw [symmAt_indep (Classical.arbitrary N) p]; rw [← fromLoop_symm_toLoop]
  apply Quotient.sound
  rfl

/--
Instance `commGroup` / 实例 `commGroup`

English:
instance commGroup
  signature: [Nontrivial N]
  body: let h := exists_ne (Classical.arbitrary N)
  fast_instance% @EckmannHilton.commGroup (HomotopyGroup N X x) _ 1
    (isUnital_auxGroup <| Classical.choose h) _
    (by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
      apply congr_arg Quotient.mk'
      simp only [fromLoop_trans_toLoop, transAt_distrib <| Classical.

中文:
实例 commGroup
  签名: [Nontrivial N]
  定义体: let h := exists_ne (Classical.arbitrary N)
  fast_instance% @EckmannHilton.commGroup (HomotopyGroup N X x) _ 1
    (isUnital_auxGroup <| Classical.choose h) _
    (by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
      apply congr_arg Quotient.mk'
      simp only [fromLoop_trans_toLoop, transAt_distrib <| Classical.

Depends on / 依赖: Classical, Classical.arbitrary, Classical.choose, Classical.choose_spec, EckmannHilton, EckmannHilton.commGroup, HomotopyGroup, Quotient, Quotient.mk, arbitrary, choose_spec, coe_symm_toEquiv, coe_toEquiv, commGroup, congr_arg, exists_ne, fast_instance, fromLoop_trans_toLoop, isUnital_auxGroup, loopHomeo_apply
-/
instance commGroup [Nontrivial N] : CommGroup (HomotopyGroup N X x) :=
  let h := exists_ne (Classical.arbitrary N)
  fast_instance% @EckmannHilton.commGroup (HomotopyGroup N X x) _ 1
    (isUnital_auxGroup <| Classical.choose h) _
    (by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
      apply congr_arg Quotient.mk'
      simp only [fromLoop_trans_toLoop, transAt_distrib <| Classical.choose_spec h, coe_toEquiv,
        loopHomeo_apply, coe_symm_toEquiv, loopHomeo_symm_apply])

/--
Definition of `homotopyGroupOfUniqueMulEquivFundamentalGroup` / `homotopyGroupOfUniqueMulEquivFundamentalGroup` 的定义

English:
definition homotopyGroupOfUniqueMulEquivFundamentalGroup
  signature: (N) [Unique N]
  body: homotopyGroupEquivFundamentalGroupOfUnique N
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    simp only [HomotopyGroup.mul_spec (i := default)]
    apply Quotient.sound
    simp [genLoopEquivOfUnique_transAt]

中文:
定义 homotopyGroupOfUniqueMulEquivFundamentalGroup
  签名: (N) [Unique N]
  定义体: homotopyGroupEquivFundamentalGroupOfUnique N
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    simp only [HomotopyGroup.mul_spec (i := default)]
    apply Quotient.sound
    simp [genLoopEquivOfUnique_transAt]

Depends on / 依赖: homotopyGroupEquivFundamentalGroupOfUnique
-/
def homotopyGroupOfUniqueMulEquivFundamentalGroup (N) [Unique N] :
    HomotopyGroup N X x ≃* FundamentalGroup X x where
  toEquiv := homotopyGroupEquivFundamentalGroupOfUnique N
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    simp only [HomotopyGroup.mul_spec (i := default)]
    apply Quotient.sound
    simp [genLoopEquivOfUnique_transAt]

/--
Definition of `pi1MulEquivFundamentalGroup` / `pi1MulEquivFundamentalGroup` 的定义

English:
definition pi1MulEquivFundamentalGroup
  signature: :
  body: HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    simp only [HomotopyGroup.mul_spec (i := (0 : Fin 1))]
    apply Quotient.sound
    rw [Unique.eq_default 0]; rw [genLoopEquivOfUnique_transAt]

中文:
定义 pi1MulEquivFundamentalGroup
  签名: :
  定义体: HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    simp only [HomotopyGroup.mul_spec (i := (0 : Fin 1))]
    apply Quotient.sound
    rw [Unique.eq_default 0]; rw [genLoopEquivOfUnique_transAt]

Depends on / 依赖: HomotopyGroup, HomotopyGroup.pi1EquivFundamentalGroup, pi1EquivFundamentalGroup
-/
def pi1MulEquivFundamentalGroup :
    π_ 1 X x ≃* FundamentalGroup X x where
  toEquiv := HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    simp only [HomotopyGroup.mul_spec (i := (0 : Fin 1))]
    apply Quotient.sound
    rw [Unique.eq_default 0]; rw [genLoopEquivOfUnique_transAt]

end HomotopyGroup
