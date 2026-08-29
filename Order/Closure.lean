/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
module

public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.Hom.Basic

/-!
# Closure operators between preorders

We define (bundled) closure operators on a preorder as monotone (increasing), extensive
(inflationary) and idempotent functions.
We define closed elements for the operator as elements which are fixed by it.

Lower adjoints to a function between preorders `u : β → α` allow to generalise closure operators to
situations where the closure operator we are dealing with naturally decomposes as `u ∘ l` where `l`
is a worthy function to have on its own. Typical examples include
`l : Set G → Subgroup G := Subgroup.closure`, `u : Subgroup G → Set G := (↑)`, where `G` is a group.
This shows there is a close connection between closure operators, lower adjoints and Galois
connections/insertions: every Galois connection induces a lower adjoint which itself induces a
closure operator by composition (see `GaloisConnection.lowerAdjoint` and
`LowerAdjoint.closureOperator`), and every closure operator on a partial order induces a Galois
insertion from the set of closed elements to the underlying type (see `ClosureOperator.gi`).

## Main definitions

* `ClosureOperator`: A closure operator is a monotone function `f : α → α` such that
  `∀ x, x ≤ f x` and `∀ x, f (f x) = f x`.
* `LowerAdjoint`: A lower adjoint to `u : β → α` is a function `l : α → β` such that `l` and `u`
  form a Galois connection.

## Implementation details

Although `LowerAdjoint` is technically a generalisation of `ClosureOperator` (by defining
`toFun := id`), it is desirable to have both as otherwise `id`s would be carried all over the
place when using concrete closure operators such as `ConvexHull`.

`LowerAdjoint` really is a semibundled `structure` version of `GaloisConnection`.

## References

* https://en.wikipedia.org/wiki/Closure_operator#Closure_operators_on_partially_ordered_sets
-/

@[expose] public section

open Set

/-! ### Closure operator -/


variable (α : Type*) {ι : Sort*} {κ : ι -> Sort*}

/--
Definition of `ClosureOperator` / `ClosureOperator` 的定义

English:
structure ClosureOperator
  parameters: [Preorder α]
  extends: α ->o α
  axioms and operations (4):
    - le_closure' : forall x, x <= toFun x
    - idempotent' : forall x, toFun (toFun x) = toFun x
    - IsClosed((x : α)) : Prop  [default: toFun x = x]
    - isClosed_iff({x : α}) : IsClosed x ↔ toFun x = x  [default: by aesop]

中文:
结构 ClosureOperator
  参数: [Preorder α]
  继承: α ->o α
  公理与运算 (4 个):
    - le_closure' : 对任意 x, x <= toFun x
    - idempotent' : 对任意 x, toFun (toFun x) = toFun x
    - IsClosed((x : α)) : 命题  [默认: toFun x = x]
    - isClosed_iff({x : α}) : IsClosed x ↔ toFun x = x  [默认: by aesop]

Depends on / 依赖: isClosed_iff
-/
structure ClosureOperator [Preorder α] extends α ->o α where
  /-- An element is less than or equal its closure -/
  le_closure' : forall x, x <= toFun x
  /-- Closures are idempotent -/
  idempotent' : forall x, toFun (toFun x) = toFun x
  /-- Predicate for an element to be closed.

  By default, this is defined as `c.IsClosed x := (c x = x)` (see `isClosed_iff`).
  We allow an override to fix definitional equalities. -/
  IsClosed (x : α) : Prop := toFun x = x
  isClosed_iff {x : α} : IsClosed x ↔ toFun x = x := by aesop

namespace ClosureOperator

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : FunLike (ClosureOperator α) α α where
  body: c.1
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; obtain rfl := DFunLike.ext' h; congr with x; simp_all

中文:
实例 [Preorder
  签名: α] : FunLike (ClosureOperator α) α α where
  定义体: c.1
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; obtain rfl := DFunLike.ext' h; congr with x; simp_all
-/
instance [Preorder α] : FunLike (ClosureOperator α) α α where
  coe c := c.1
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; obtain rfl := DFunLike.ext' h; congr with x; simp_all

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : OrderHomClass (ClosureOperator α) α α where
  body: f.mono h

initialize_simps_projections ClosureOperator (toFun -> apply, IsClosed -> isClosed)

中文:
实例 [Preorder
  签名: α] : OrderHomClass (ClosureOperator α) α α where
  定义体: f.mono h

initialize_simps_projections ClosureOperator (toFun -> apply, IsClosed -> isClosed)

Depends on / 依赖: f.mono
-/
instance [Preorder α] : OrderHomClass (ClosureOperator α) α α where
  map_rel f _ _ h := f.mono h

initialize_simps_projections ClosureOperator (toFun -> apply, IsClosed -> isClosed)


/-- If `c` is a closure operator on `α` and `e` an order-isomorphism
between `α` and `β` then `e ∘ c ∘ e⁻¹` is a closure operator on `β`. -/
@[simps apply]
/--
Definition of `conjBy` / `conjBy` 的定义

English:
definition conjBy
  signature: {α β} [Preorder α] [Preorder β] (c : ClosureOperator α)
  body: e.conj c
  IsClosed b := c.IsClosed (e.symm b)
  monotone' _ _ h :=
(map_le_map_iff e).mpr c.monotone (map_le_map_iff e.symm).mpr h
  le_closure' _ := e.symm_apply_le.mp (c.le_closure' _)
  idempotent' _ :=
congrArg e Eq.trans (congrArg c (e.symm_apply_apply _)) (c.idempotent' _)
  isClosed_iff := I

中文:
定义 conjBy
  签名: {α β} [Preorder α] [Preorder β] (c : ClosureOperator α)
  定义体: e.conj c
  IsClosed b := c.IsClosed (e.symm b)
  monotone' _ _ h :=
(map_le_map_iff e).mpr c.monotone (map_le_map_iff e.symm).mpr h
  le_closure' _ := e.symm_apply_le.mp (c.le_closure' _)
  idempotent' _ :=
congrArg e Eq.trans (congrArg c (e.symm_apply_apply _)) (c.idempotent' _)
  isClosed_iff := I

Depends on / 依赖: e.conj
-/
def conjBy {α β} [Preorder α] [Preorder β] (c : ClosureOperator α)
    (e : α ≃o β) : ClosureOperator β where
  toFun := e.conj c
  IsClosed b := c.IsClosed (e.symm b)
  monotone' _ _ h :=
(map_le_map_iff e).mpr c.monotone (map_le_map_iff e.symm).mpr h
  le_closure' _ := e.symm_apply_le.mp (c.le_closure' _)
  idempotent' _ :=
congrArg e Eq.trans (congrArg c (e.symm_apply_apply _)) (c.idempotent' _)
  isClosed_iff := Iff.trans c.isClosed_iff e.eq_symm_apply

/--
lemma `conjBy_refl` / 引理 `conjBy_refl`

English:
lemma conjBy_refl
  given: {α} [Preorder α] (c : ClosureOperator α)
  proof: rfl

中文:
引理 conjBy_refl
  条件: {α} [Preorder α] (c : ClosureOperator α)
  证明: rfl
-/
lemma conjBy_refl {α} [Preorder α] (c : ClosureOperator α) :
    c.conjBy (OrderIso.refl α) = c := rfl

/--
lemma `conjBy_trans` / 引理 `conjBy_trans`

English:
lemma conjBy_trans
  statement: {α β γ} [Preorder α] [Preorder β] [Preorder γ]
  proof: rfl

中文:
引理 conjBy_trans
  结论: {α β γ} [Preorder α] [Preorder β] [Preorder γ]
  证明: rfl
-/
lemma conjBy_trans {α β γ} [Preorder α] [Preorder β] [Preorder γ]
    (e₁ : α ≃o β) (e₂ : β ≃o γ) (c : ClosureOperator α) :
    c.conjBy (e₁.trans e₂) = (c.conjBy e₁).conjBy e₂ := rfl

section Preorder

variable [Preorder α]

/-- The identity function as a closure operator. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : ClosureOperator α where
  body: OrderHom.id
  le_closure' _ := le_rfl
  idempotent' _ := rfl
  IsClosed _ := True

中文:
定义 id
  签名: : ClosureOperator α where
  定义体: OrderHom.id
  le_closure' _ := le_rfl
  idempotent' _ := rfl
  IsClosed _ := True

Depends on / 依赖: OrderHom, OrderHom.id
-/
def id : ClosureOperator α where
  toOrderHom := OrderHom.id
  le_closure' _ := le_rfl
  idempotent' _ := rfl
  IsClosed _ := True

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (ClosureOperator α)
  body: ⟨id α⟩

中文:
实例 :
  签名: Inhabited (ClosureOperator α)
  定义体: ⟨id α⟩
-/
instance : Inhabited (ClosureOperator α) :=
  ⟨id α⟩

variable {α} (c : ClosureOperator α)

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: forall c₁ c₂ : ClosureOperator α, (forall x, c₁ x = c₂ x) -> c₁ = c₂
  proof: DFunLike.ext

@[gcongr, mono]

中文:
定理 ext
  结论: 对任意 c₁ c₂ : ClosureOperator α, (对任意 x, c₁ x = c₂ x) -> c₁ = c₂
  证明: DFunLike.ext

@[gcongr, mono]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext : forall c₁ c₂ : ClosureOperator α, (forall x, c₁ x = c₂ x) -> c₁ = c₂ :=
  DFunLike.ext

@[gcongr, mono]
/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  statement: Monotone c
  proof: c.monotone'

中文:
定理 monotone
  结论: Monotone c
  证明: c.monotone'

Depends on / 依赖: c.monotone, monotone
-/
theorem monotone : Monotone c :=
  c.monotone'

/--
theorem `le_closure` / 定理 `le_closure`

English:
theorem le_closure
  given: (x : α)
  statement: x <= c x
  proof: c.le_closure' x

@[simp]

中文:
定理 le_closure
  条件: (x : α)
  结论: x <= c x
  证明: c.le_closure' x

@[simp]

Depends on / 依赖: c.le_closure, le_closure
-/
theorem le_closure (x : α) : x <= c x :=
  c.le_closure' x

@[simp]
/--
theorem `idempotent` / 定理 `idempotent`

English:
theorem idempotent
  given: (x : α)
  statement: c (c x) = c x
  proof: c.idempotent' x

中文:
定理 idempotent
  条件: (x : α)
  结论: c (c x) = c x
  证明: c.idempotent' x

Depends on / 依赖: c.idempotent, idempotent
-/
theorem idempotent (x : α) : c (c x) = c x :=
  c.idempotent' x

/--
lemma `isClosed_closure` / 引理 `isClosed_closure`

English:
lemma isClosed_closure
  given: (x : α)
  statement: c.IsClosed (c x)
  proof: c.isClosed_iff.2 c.idempotent x

中文:
引理 isClosed_closure
  条件: (x : α)
  结论: c.IsClosed (c x)
  证明: c.isClosed_iff.2 c.idempotent x
-/
@[simp] lemma isClosed_closure (x : α) : c.IsClosed (c x) := c.isClosed_iff.2 c.idempotent x

/--
Definition of `Closeds` / `Closeds` 的定义

English:
abbreviation Closeds
  body: {x // c.IsClosed x}

中文:
缩写 Closeds
  定义体: {x // c.IsClosed x}

Depends on / 依赖: IsClosed, c.IsClosed
-/
abbrev Closeds := {x // c.IsClosed x}

/--
Definition of `toCloseds` / `toCloseds` 的定义

English:
definition toCloseds
  signature: (x : α)
  body: ⟨c x, c.isClosed_closure x⟩

中文:
定义 toCloseds
  签名: (x : α)
  定义体: ⟨c x, c.isClosed_closure x⟩

Depends on / 依赖: c.isClosed_closure, isClosed_closure
-/
def toCloseds (x : α) : c.Closeds := ⟨c x, c.isClosed_closure x⟩

variable {c} {x y : α}

/--
theorem `IsClosed.closure_eq` / 定理 `IsClosed.closure_eq`

English:
theorem IsClosed.closure_eq
  statement: c.IsClosed x -> c x = x
  proof: c.isClosed_iff.1

中文:
定理 IsClosed.closure_eq
  结论: c.IsClosed x -> c x = x
  证明: c.isClosed_iff.1

Depends on / 依赖: c.isClosed_iff, isClosed_iff
-/
theorem IsClosed.closure_eq : c.IsClosed x -> c x = x := c.isClosed_iff.1

/--
theorem `setOfPred_isClosed_eq_range_closure` / 定理 `setOfPred_isClosed_eq_range_closure`

English:
theorem setOfPred_isClosed_eq_range_closure
  statement: {x | c.IsClosed x} = Set.range c
  proof: by
  ext x; exact ⟨fun hx => ⟨x, hx.closure_eq⟩, by rintro ⟨y, rfl⟩; exact c.isClosed_closure _⟩

@[deprecated (since := "2026-07-09")]
alias setOf_isClosed_eq_range_closure := setOfPred_isClosed_eq_range_closure

中文:
定理 setOfPred_isClosed_eq_range_closure
  结论: {x | c.IsClosed x} = Set.range c
  证明: by
  ext x; exact ⟨fun hx => ⟨x, hx.closure_eq⟩, by rintro ⟨y, rfl⟩; exact c.isClosed_closure _⟩

@[deprecated (since := "2026-07-09")]
alias setOf_isClosed_eq_range_closure := setOfPred_isClosed_eq_range_closure

Depends on / 依赖: c.isClosed_closure, closure_eq, hx.closure_eq, isClosed_closure
-/
theorem setOfPred_isClosed_eq_range_closure : {x | c.IsClosed x} = Set.range c := by
  ext x; exact ⟨fun hx => ⟨x, hx.closure_eq⟩, by rintro ⟨y, rfl⟩; exact c.isClosed_closure _⟩

@[deprecated (since := "2026-07-09")]
alias setOf_isClosed_eq_range_closure := setOfPred_isClosed_eq_range_closure

/--
theorem `le_closure_iff` / 定理 `le_closure_iff`

English:
theorem le_closure_iff
  statement: x <= c y ↔ c x <= c y
  proof: ⟨fun h => c.idempotent y ▸ c.monotone h, (c.le_closure x).trans⟩

@[simp]

中文:
定理 le_closure_iff
  结论: x <= c y ↔ c x <= c y
  证明: ⟨fun h => c.idempotent y ▸ c.monotone h, (c.le_closure x).trans⟩

@[simp]

Depends on / 依赖: c.idempotent, c.le_closure, c.monotone, idempotent, le_closure, monotone
-/
theorem le_closure_iff : x <= c y ↔ c x <= c y :=
  ⟨fun h => c.idempotent y ▸ c.monotone h, (c.le_closure x).trans⟩

@[simp]
/--
theorem `IsClosed.closure_le_iff` / 定理 `IsClosed.closure_le_iff`

English:
theorem IsClosed.closure_le_iff
  given: (hy : c.IsClosed y)
  statement: c x <= y ↔ x <= y
  proof: by
  rw [← hy.closure_eq]; rw [← le_closure_iff]

中文:
定理 IsClosed.closure_le_iff
  条件: (hy : c.IsClosed y)
  结论: c x <= y ↔ x <= y
  证明: by
  rw [← hy.closure_eq]; rw [← le_closure_iff]

Depends on / 依赖: closure_eq, hy.closure_eq, le_closure_iff
-/
theorem IsClosed.closure_le_iff (hy : c.IsClosed y) : c x <= y ↔ x <= y := by
  rw [← hy.closure_eq]; rw [← le_closure_iff]

/--
lemma `closure_min` / 引理 `closure_min`

English:
lemma closure_min
  given: (hxy : x <= y) (hy : c.IsClosed y)
  statement: c x <= y
  proof: hy.closure_le_iff.2 hxy

中文:
引理 closure_min
  条件: (hxy : x <= y) (hy : c.IsClosed y)
  结论: c x <= y
  证明: hy.closure_le_iff.2 hxy

Depends on / 依赖: closure_le_iff, hy.closure_le_iff
-/
lemma closure_min (hxy : x <= y) (hy : c.IsClosed y) : c x <= y := hy.closure_le_iff.2 hxy

/--
lemma `closure_isGLB` / 引理 `closure_isGLB`

English:
lemma closure_isGLB
  given: (x : α)
  statement: IsGLB { y | x <= y ∧ c.IsClosed y } (c x) where
  proof: and_imp.mpr closure_min
  right _ h := h ⟨c.le_closure x, c.isClosed_closure x⟩

中文:
引理 closure_isGLB
  条件: (x : α)
  结论: IsGLB { y | x <= y ∧ c.IsClosed y } (c x) where
  证明: and_imp.mpr closure_min
  right _ h := h ⟨c.le_closure x, c.isClosed_closure x⟩

Depends on / 依赖: and_imp, and_imp.mpr, closure_min
-/
lemma closure_isGLB (x : α) : IsGLB { y | x <= y ∧ c.IsClosed y } (c x) where
  left _ := and_imp.mpr closure_min
  right _ h := h ⟨c.le_closure x, c.isClosed_closure x⟩

end Preorder

section PartialOrder

variable {α} [PartialOrder α] {c : ClosureOperator α} {x y : α}

/-- Constructor for a closure operator using the weaker idempotency axiom: `f (f x) ≤ f x`. -/
@[simps]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (f : α -> α) (hf₁ : Monotone f) (hf₂ : forall x, x <= f x) (hf₃ : forall x, f (f x) <= f x)
  body: f
  monotone' := hf₁
  le_closure' := hf₂
  idempotent' x := (hf₃ x).antisymm (hf₁ (hf₂ x))

中文:
定义 mk'
  签名: (f : α -> α) (hf₁ : Monotone f) (hf₂ : 对任意 x, x <= f x) (hf₃ : 对任意 x, f (f x) <= f x)
  定义体: f
  monotone' := hf₁
  le_closure' := hf₂
  idempotent' x := (hf₃ x).antisymm (hf₁ (hf₂ x))
-/
def mk' (f : α -> α) (hf₁ : Monotone f) (hf₂ : forall x, x <= f x) (hf₃ : forall x, f (f x) <= f x) :
    ClosureOperator α where
  toFun := f
  monotone' := hf₁
  le_closure' := hf₂
  idempotent' x := (hf₃ x).antisymm (hf₁ (hf₂ x))

/-- Convenience constructor for a closure operator using the weaker minimality axiom:
`x ≤ f y → f x ≤ f y`, which is sometimes easier to prove in practice. -/
@[simps]
/--
Definition of `mk₂` / `mk₂` 的定义

English:
definition mk₂
  signature: (f : α -> α) (hf : forall x, x <= f x) (hmin : forall ⦃x y⦄, x <= f y -> f x <= f y)
  body: f
  monotone' _ y hxy := hmin (hxy.trans (hf y))
  le_closure' := hf
  idempotent' _ := (hmin le_rfl).antisymm (hf _)

中文:
定义 mk₂
  签名: (f : α -> α) (hf : 对任意 x, x <= f x) (hmin : 对任意 ⦃x y⦄, x <= f y -> f x <= f y)
  定义体: f
  monotone' _ y hxy := hmin (hxy.trans (hf y))
  le_closure' := hf
  idempotent' _ := (hmin le_rfl).antisymm (hf _)
-/
def mk₂ (f : α -> α) (hf : forall x, x <= f x) (hmin : forall ⦃x y⦄, x <= f y -> f x <= f y) :
    ClosureOperator α where
  toFun := f
  monotone' _ y hxy := hmin (hxy.trans (hf y))
  le_closure' := hf
  idempotent' _ := (hmin le_rfl).antisymm (hf _)

/-- Construct a closure operator from an inflationary function `f` and a "closedness" predicate `p`
witnessing minimality of `f x` among closed elements greater than `x`. -/
@[simps!]
/--
Definition of `ofPred` / `ofPred` 的定义

English:
definition ofPred
  signature: (f : α -> α) (p : α -> Prop) (hf : forall x, x <= f x) (hfp : forall x, p (f x))
  body: mk₂ f hf fun _ y hxy => hmin hxy (hfp y)
  IsClosed := p
isClosed_iff := ⟨fun hx => (hmin le_rfl hx).antisymm hf _, fun hx => hx ▸ hfp _⟩

中文:
定义 ofPred
  签名: (f : α -> α) (p : α -> 命题) (hf : 对任意 x, x <= f x) (hfp : 对任意 x, p (f x))
  定义体: mk₂ f hf fun _ y hxy => hmin hxy (hfp y)
  IsClosed := p
isClosed_iff := ⟨fun hx => (hmin le_rfl hx).antisymm hf _, fun hx => hx ▸ hfp _⟩
-/
def ofPred (f : α -> α) (p : α -> Prop) (hf : forall x, x <= f x) (hfp : forall x, p (f x))
    (hmin : forall ⦃x y⦄, x <= y -> p y -> f x <= y) : ClosureOperator α where
  __ := mk₂ f hf fun _ y hxy => hmin hxy (hfp y)
  IsClosed := p
isClosed_iff := ⟨fun hx => (hmin le_rfl hx).antisymm hf _, fun hx => hx ▸ hfp _⟩

/--
theorem `isClosed_iff_closure_le` / 定理 `isClosed_iff_closure_le`

English:
theorem isClosed_iff_closure_le
  statement: c.IsClosed x ↔ c x <= x
  proof: ⟨fun h => h.closure_eq.le, fun h => c.isClosed_iff.2 h.antisymm c.le_closure x⟩

中文:
定理 isClosed_iff_closure_le
  结论: c.IsClosed x ↔ c x <= x
  证明: ⟨fun h => h.closure_eq.le, fun h => c.isClosed_iff.2 h.antisymm c.le_closure x⟩

Depends on / 依赖: antisymm, c.isClosed_iff, c.le_closure, closure_eq, h.antisymm, h.closure_eq.le, isClosed_iff, le_closure
-/
theorem isClosed_iff_closure_le : c.IsClosed x ↔ c x <= x :=
⟨fun h => h.closure_eq.le, fun h => c.isClosed_iff.2 h.antisymm c.le_closure x⟩

/--
theorem `ext_isClosed` / 定理 `ext_isClosed`

English:
theorem ext_isClosed
  statement: (c₁ c₂ : ClosureOperator α)
  proof: ext c₁ c₂ fun x => IsGLB.unique (c₁.closure_isGLB x) by simpa [h] using c₂.closure_isGLB x

中文:
定理 ext_isClosed
  结论: (c₁ c₂ : ClosureOperator α)
  证明: ext c₁ c₂ fun x => IsGLB.unique (c₁.closure_isGLB x) by simpa [h] using c₂.closure_isGLB x

Depends on / 依赖: IsGLB.unique, closure_isGLB, unique
-/
theorem ext_isClosed (c₁ c₂ : ClosureOperator α)
    (h : forall x, c₁.IsClosed x ↔ c₂.IsClosed x) : c₁ = c₂ :=
ext c₁ c₂ fun x => IsGLB.unique (c₁.closure_isGLB x) by simpa [h] using c₂.closure_isGLB x

/--
theorem `eq_ofPred_closed` / 定理 `eq_ofPred_closed`

English:
theorem eq_ofPred_closed
  given: (c : ClosureOperator α)
  proof: by
  ext
  simp

中文:
定理 eq_ofPred_closed
  条件: (c : ClosureOperator α)
  证明: by
  ext
  simp
-/
theorem eq_ofPred_closed (c : ClosureOperator α) :
    c = ofPred c c.IsClosed c.le_closure c.isClosed_closure fun _ _ => closure_min := by
  ext
  simp

end PartialOrder

variable {α}

section OrderTop

variable [PartialOrder α] [OrderTop α] (c : ClosureOperator α)

@[simp]
/--
theorem `closure_top` / 定理 `closure_top`

English:
theorem closure_top
  statement: c ⊤ = ⊤
  proof: le_top.antisymm (c.le_closure _)

中文:
定理 closure_top
  结论: c ⊤ = ⊤
  证明: le_top.antisymm (c.le_closure _)

Depends on / 依赖: antisymm, c.le_closure, le_closure, le_top, le_top.antisymm
-/
theorem closure_top : c ⊤ = ⊤ :=
  le_top.antisymm (c.le_closure _)

/--
lemma `isClosed_top` / 引理 `isClosed_top`

English:
lemma isClosed_top
  statement: c.IsClosed ⊤
  proof: c.isClosed_iff.2 c.closure_top

中文:
引理 isClosed_top
  结论: c.IsClosed ⊤
  证明: c.isClosed_iff.2 c.closure_top
-/
@[simp] lemma isClosed_top : c.IsClosed ⊤ := c.isClosed_iff.2 c.closure_top

end OrderTop

/--
theorem `closure_inf_le` / 定理 `closure_inf_le`

English:
theorem closure_inf_le
  given: [SemilatticeInf α] (c : ClosureOperator α) (x y : α)
  proof: c.monotone.map_inf_le _ _

中文:
定理 closure_inf_le
  条件: [SemilatticeInf α] (c : ClosureOperator α) (x y : α)
  证明: c.monotone.map_inf_le _ _

Depends on / 依赖: c.monotone.map_inf_le, map_inf_le, monotone
-/
theorem closure_inf_le [SemilatticeInf α] (c : ClosureOperator α) (x y : α) :
    c (x ⊓ y) <= c x ⊓ c y :=
  c.monotone.map_inf_le _ _

section SemilatticeSup

variable [SemilatticeSup α] (c : ClosureOperator α)

/--
theorem `closure_sup_closure_le` / 定理 `closure_sup_closure_le`

English:
theorem closure_sup_closure_le
  given: (x y : α)
  statement: c x ⊔ c y <= c (x ⊔ y)
  proof: c.monotone.le_map_sup _ _

中文:
定理 closure_sup_closure_le
  条件: (x y : α)
  结论: c x ⊔ c y <= c (x ⊔ y)
  证明: c.monotone.le_map_sup _ _

Depends on / 依赖: c.monotone.le_map_sup, le_map_sup, monotone
-/
theorem closure_sup_closure_le (x y : α) : c x ⊔ c y <= c (x ⊔ y) :=
  c.monotone.le_map_sup _ _

/--
theorem `closure_sup_closure_left` / 定理 `closure_sup_closure_left`

English:
theorem closure_sup_closure_left
  given: (x y : α)
  statement: c (c x ⊔ y) = c (x ⊔ y)
  proof: le_antisymm
    (le_closure_iff.1 (sup_le (c.monotone le_sup_left) (le_sup_right.trans (c.le_closure _))))
    (by grw [← c.le_closure x])

中文:
定理 closure_sup_closure_left
  条件: (x y : α)
  结论: c (c x ⊔ y) = c (x ⊔ y)
  证明: le_antisymm
    (le_closure_iff.1 (sup_le (c.monotone le_sup_left) (le_sup_right.trans (c.le_closure _))))
    (by grw [← c.le_closure x])

Depends on / 依赖: c.le_closure, c.monotone, le_antisymm, le_closure, le_closure_iff, le_sup_left, le_sup_right, le_sup_right.trans, monotone, sup_le
-/
theorem closure_sup_closure_left (x y : α) : c (c x ⊔ y) = c (x ⊔ y) :=
  le_antisymm
    (le_closure_iff.1 (sup_le (c.monotone le_sup_left) (le_sup_right.trans (c.le_closure _))))
    (by grw [← c.le_closure x])

/--
theorem `closure_sup_closure_right` / 定理 `closure_sup_closure_right`

English:
theorem closure_sup_closure_right
  given: (x y : α)
  statement: c (x ⊔ c y) = c (x ⊔ y)
  proof: by
  rw [sup_comm]; rw [closure_sup_closure_left]; rw [sup_comm (a := x)]

中文:
定理 closure_sup_closure_right
  条件: (x y : α)
  结论: c (x ⊔ c y) = c (x ⊔ y)
  证明: by
  rw [sup_comm]; rw [closure_sup_closure_left]; rw [sup_comm (a := x)]

Depends on / 依赖: closure_sup_closure_left, sup_comm
-/
theorem closure_sup_closure_right (x y : α) : c (x ⊔ c y) = c (x ⊔ y) := by
  rw [sup_comm]; rw [closure_sup_closure_left]; rw [sup_comm (a := x)]

/--
theorem `closure_sup_closure` / 定理 `closure_sup_closure`

English:
theorem closure_sup_closure
  given: (x y : α)
  statement: c (c x ⊔ c y) = c (x ⊔ y)
  proof: by
  rw [closure_sup_closure_left]; rw [closure_sup_closure_right]

中文:
定理 closure_sup_closure
  条件: (x y : α)
  结论: c (c x ⊔ c y) = c (x ⊔ y)
  证明: by
  rw [closure_sup_closure_left]; rw [closure_sup_closure_right]

Depends on / 依赖: closure_sup_closure_left, closure_sup_closure_right
-/
theorem closure_sup_closure (x y : α) : c (c x ⊔ c y) = c (x ⊔ y) := by
  rw [closure_sup_closure_left]; rw [closure_sup_closure_right]

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] (c : ClosureOperator α)

/-- Define a closure operator from a predicate that's preserved under infima. -/
@[simps!]
/--
Definition of `ofCompletePred` / `ofCompletePred` 的定义

English:
definition ofCompletePred
  signature: (p : α -> Prop) (hsinf : forall s, (forall a in s, p a) -> p (sInf s))
  body: ofPred (fun a => ⨅ b : {b // a <= b ∧ p b}, b) p
    (fun a => by simp +contextual)
    (fun _ => hsinf _ <| forall_mem_range.2 fun b => b.2.2)
    (fun _ b hab hb => iInf_le_of_le ⟨b, hab, hb⟩ le_rfl)

中文:
定义 ofCompletePred
  签名: (p : α -> 命题) (hsinf : 对任意 s, (对任意 a in s, p a) -> p (sInf s))
  定义体: ofPred (fun a => ⨅ b : {b // a <= b ∧ p b}, b) p
    (fun a => by simp +contextual)
    (fun _ => hsinf _ <| forall_mem_range.2 fun b => b.2.2)
    (fun _ b hab hb => iInf_le_of_le ⟨b, hab, hb⟩ le_rfl)

Depends on / 依赖: contextual, forall_mem_range, iInf_le_of_le, le_rfl, ofPred
-/
def ofCompletePred (p : α -> Prop) (hsinf : forall s, (forall a in s, p a) -> p (sInf s)) : ClosureOperator α :=
  ofPred (fun a => ⨅ b : {b // a <= b ∧ p b}, b) p
    (fun a => by simp +contextual)
    (fun _ => hsinf _ <| forall_mem_range.2 fun b => b.2.2)
    (fun _ b hab hb => iInf_le_of_le ⟨b, hab, hb⟩ le_rfl)

/--
theorem `sInf_isClosed` / 定理 `sInf_isClosed`

English:
theorem sInf_isClosed
  statement: {c : ClosureOperator α} {S : Set α}
  proof: isClosed_iff_closure_le.mpr le_of_le_of_eq c.monotone.map_sInf_le
    Eq.trans (biInf_congr (c.isClosed_iff.mp <| H · ·)) sInf_eq_iInf.symm

@[simp]

中文:
定理 sInf_isClosed
  结论: {c : ClosureOperator α} {S : Set α}
  证明: isClosed_iff_closure_le.mpr le_of_le_of_eq c.monotone.map_sInf_le
    Eq.trans (biInf_congr (c.isClosed_iff.mp <| H · ·)) sInf_eq_iInf.symm

@[simp]

Depends on / 依赖: Eq.trans, biInf_congr, c.isClosed_iff.mp, c.monotone.map_sInf_le, isClosed_iff, isClosed_iff_closure_le, isClosed_iff_closure_le.mpr, le_of_le_of_eq, map_sInf_le, monotone, sInf_eq_iInf, sInf_eq_iInf.symm
-/
theorem sInf_isClosed {c : ClosureOperator α} {S : Set α}
    (H : forall x in S, c.IsClosed x) : c.IsClosed (sInf S) :=
isClosed_iff_closure_le.mpr le_of_le_of_eq c.monotone.map_sInf_le
    Eq.trans (biInf_congr (c.isClosed_iff.mp <| H · ·)) sInf_eq_iInf.symm

@[simp]
/--
theorem `closure_iSup_closure` / 定理 `closure_iSup_closure`

English:
theorem closure_iSup_closure
  given: (f : ι -> α)
  statement: c (⨆ i, c (f i)) = c (⨆ i, f i)
  proof: le_antisymm (le_closure_iff.1 <| iSup_le fun i => c.monotone <| le_iSup f i)
c.monotone iSup_mono fun _ => c.le_closure _

@[simp]

中文:
定理 closure_iSup_closure
  条件: (f : ι -> α)
  结论: c (⨆ i, c (f i)) = c (⨆ i, f i)
  证明: le_antisymm (le_closure_iff.1 <| iSup_le fun i => c.monotone <| le_iSup f i)
c.monotone iSup_mono fun _ => c.le_closure _

@[simp]

Depends on / 依赖: c.le_closure, c.monotone, iSup_le, iSup_mono, le_antisymm, le_closure, le_closure_iff, le_iSup, monotone
-/
theorem closure_iSup_closure (f : ι -> α) : c (⨆ i, c (f i)) = c (⨆ i, f i) :=
le_antisymm (le_closure_iff.1 <| iSup_le fun i => c.monotone <| le_iSup f i)
c.monotone iSup_mono fun _ => c.le_closure _

@[simp]
/--
theorem `closure_iSup₂_closure` / 定理 `closure_iSup₂_closure`

English:
theorem closure_iSup₂_closure
  given: (f : forall i, κ i -> α)
  proof: le_antisymm (le_closure_iff.1 <| iSup₂_le fun i j => c.monotone <| le_iSup₂ i j)
c.monotone iSup₂_mono fun _ _ => c.le_closure _

中文:
定理 closure_iSup₂_closure
  条件: (f : 对任意 i, κ i -> α)
  证明: le_antisymm (le_closure_iff.1 <| iSup₂_le fun i j => c.monotone <| le_iSup₂ i j)
c.monotone iSup₂_mono fun _ _ => c.le_closure _

Depends on / 依赖: c.le_closure, c.monotone, le_antisymm, le_closure, le_closure_iff, monotone
-/
theorem closure_iSup₂_closure (f : forall i, κ i -> α) :
    c (⨆ (i) (j), c (f i j)) = c (⨆ (i) (j), f i j) :=
le_antisymm (le_closure_iff.1 <| iSup₂_le fun i j => c.monotone <| le_iSup₂ i j)
c.monotone iSup₂_mono fun _ _ => c.le_closure _

end CompleteLattice

end ClosureOperator

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Conjugating `ClosureOperators` on `α` and on `β` by a fixed isomorphism
`e : α ≃o β` gives an equivalence `ClosureOperator α ≃ ClosureOperator β`. -/
@[simps apply symm_apply]
/--
Definition of `OrderIso.equivClosureOperator` / `OrderIso.equivClosureOperator` 的定义

English:
definition OrderIso.equivClosureOperator
  signature: {α β} [Preorder α] [Preorder β] (e : α ≃o β)
  body: c.conjBy e
  invFun c := c.conjBy e.symm
  left_inv c := Eq.trans (c.conjBy_trans _ _).symm
 Eq.trans (congrArg _ e.self_trans_symm) c.conjBy_refl
  right_inv c := Eq.trans (c.conjBy_trans _ _).symm
 Eq.trans (congrArg _ e.symm_trans_self) c.conjBy_refl

中文:
定义 OrderIso.equivClosureOperator
  签名: {α β} [Preorder α] [Preorder β] (e : α ≃o β)
  定义体: c.conjBy e
  invFun c := c.conjBy e.symm
  left_inv c := Eq.trans (c.conjBy_trans _ _).symm
 Eq.trans (congrArg _ e.self_trans_symm) c.conjBy_refl
  right_inv c := Eq.trans (c.conjBy_trans _ _).symm
 Eq.trans (congrArg _ e.symm_trans_self) c.conjBy_refl

Depends on / 依赖: c.conjBy, conjBy
-/
def OrderIso.equivClosureOperator {α β} [Preorder α] [Preorder β] (e : α ≃o β) :
    ClosureOperator α ≃ ClosureOperator β where
  toFun c := c.conjBy e
  invFun c := c.conjBy e.symm
  left_inv c := Eq.trans (c.conjBy_trans _ _).symm
 Eq.trans (congrArg _ e.self_trans_symm) c.conjBy_refl
  right_inv c := Eq.trans (c.conjBy_trans _ _).symm
 Eq.trans (congrArg _ e.symm_trans_self) c.conjBy_refl

/-! ### Lower adjoint -/


variable {α} {β : Type*}

/--
Definition of `LowerAdjoint` / `LowerAdjoint` 的定义

English:
structure LowerAdjoint
  parameters: [Preorder α] [Preorder β] (u : β -> α)
  axioms and operations (2):
    - toFun : α -> β
    - gc' : GaloisConnection toFun u

中文:
结构 LowerAdjoint
  参数: [Preorder α] [Preorder β] (u : β -> α)
  公理与运算 (2 个):
    - toFun : α -> β
    - gc' : GaloisConnection toFun u
-/
structure LowerAdjoint [Preorder α] [Preorder β] (u : β -> α) where
  /-- The underlying function -/
  toFun : α -> β
  /-- The underlying function is a lower adjoint. -/
  gc' : GaloisConnection toFun u

namespace LowerAdjoint

variable (α)

/-- The identity function as a lower adjoint to itself. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: [Preorder α]
  body: x
  gc' := GaloisConnection.id

中文:
定义 id
  签名: [Preorder α]
  定义体: x
  gc' := GaloisConnection.id
-/
protected def id [Preorder α] : LowerAdjoint (id : α -> α) where
  toFun x := x
  gc' := GaloisConnection.id

variable {α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : Inhabited (LowerAdjoint (id : α -> α))
  body: ⟨LowerAdjoint.id α⟩

中文:
实例 [Preorder
  签名: α] : Inhabited (LowerAdjoint (id : α -> α))
  定义体: ⟨LowerAdjoint.id α⟩

Depends on / 依赖: LowerAdjoint, LowerAdjoint.id
-/
instance [Preorder α] : Inhabited (LowerAdjoint (id : α -> α)) :=
  ⟨LowerAdjoint.id α⟩

section Preorder

variable [Preorder α] [Preorder β] {u : β -> α} (l : LowerAdjoint u)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (LowerAdjoint u) fun _ => α -> β
  body: toFun

中文:
实例 :
  签名: CoeFun (LowerAdjoint u) fun _ => α -> β
  定义体: toFun
-/
instance : CoeFun (LowerAdjoint u) fun _ => α -> β where coe := toFun

/--
theorem `gc` / 定理 `gc`

English:
theorem gc
  statement: GaloisConnection l u
  proof: l.gc'

@[ext]

中文:
定理 gc
  结论: GaloisConnection l u
  证明: l.gc'

@[ext]

Depends on / 依赖: l.gc
-/
theorem gc : GaloisConnection l u :=
  l.gc'

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: forall l₁ l₂ : LowerAdjoint u, (l₁ : α -> β) = (l₂ : α -> β) -> l₁ = l₂

中文:
定理 ext
  结论: 对任意 l₁ l₂ : LowerAdjoint u, (l₁ : α -> β) = (l₂ : α -> β) -> l₁ = l₂
-/
theorem ext : forall l₁ l₂ : LowerAdjoint u, (l₁ : α -> β) = (l₂ : α -> β) -> l₁ = l₂
  | ⟨l₁, _⟩, ⟨l₂, _⟩, h => by
    congr

@[gcongr, mono]
/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  statement: Monotone (u ∘ l)
  proof: l.gc.monotone_u.comp l.gc.monotone_l

中文:
定理 monotone
  结论: Monotone (u ∘ l)
  证明: l.gc.monotone_u.comp l.gc.monotone_l

Depends on / 依赖: l.gc.monotone_l, l.gc.monotone_u.comp, monotone_l, monotone_u
-/
theorem monotone : Monotone (u ∘ l) :=
  l.gc.monotone_u.comp l.gc.monotone_l

/--
theorem `le_closure` / 定理 `le_closure`

English:
theorem le_closure
  given: (x : α)
  statement: x <= u (l x)
  proof: l.gc.le_u_l _

中文:
定理 le_closure
  条件: (x : α)
  结论: x <= u (l x)
  证明: l.gc.le_u_l _

Depends on / 依赖: l.gc.le_u_l, le_u_l
-/
theorem le_closure (x : α) : x <= u (l x) :=
  l.gc.le_u_l _

end Preorder

section PartialOrder

variable [PartialOrder α] [Preorder β] {u : β -> α} (l : LowerAdjoint u)

/-- Every lower adjoint induces a closure operator given by the composition. This is the partial
order version of the statement that every adjunction induces a monad. -/
@[simps]
/--
Definition of `closureOperator` / `closureOperator` 的定义

English:
definition closureOperator
  signature: : ClosureOperator α where
  body: u (l x)
  monotone' := l.monotone
  le_closure' := l.le_closure
  idempotent' x := l.gc.u_l_u_eq_u (l x)

中文:
定义 closureOperator
  签名: : ClosureOperator α where
  定义体: u (l x)
  monotone' := l.monotone
  le_closure' := l.le_closure
  idempotent' x := l.gc.u_l_u_eq_u (l x)
-/
def closureOperator : ClosureOperator α where
  toFun x := u (l x)
  monotone' := l.monotone
  le_closure' := l.le_closure
  idempotent' x := l.gc.u_l_u_eq_u (l x)

/--
theorem `idempotent` / 定理 `idempotent`

English:
theorem idempotent
  given: (x : α)
  statement: u (l (u (l x))) = u (l x)
  proof: l.closureOperator.idempotent _

中文:
定理 idempotent
  条件: (x : α)
  结论: u (l (u (l x))) = u (l x)
  证明: l.closureOperator.idempotent _

Depends on / 依赖: closureOperator, idempotent, l.closureOperator.idempotent
-/
theorem idempotent (x : α) : u (l (u (l x))) = u (l x) :=
  l.closureOperator.idempotent _

/--
theorem `le_closure_iff` / 定理 `le_closure_iff`

English:
theorem le_closure_iff
  given: (x y : α)
  statement: x <= u (l y) ↔ u (l x) <= u (l y)
  proof: l.closureOperator.le_closure_iff

中文:
定理 le_closure_iff
  条件: (x y : α)
  结论: x <= u (l y) ↔ u (l x) <= u (l y)
  证明: l.closureOperator.le_closure_iff

Depends on / 依赖: closureOperator, l.closureOperator.le_closure_iff, le_closure_iff
-/
theorem le_closure_iff (x y : α) : x <= u (l y) ↔ u (l x) <= u (l y) :=
  l.closureOperator.le_closure_iff

end PartialOrder

section Preorder

variable [Preorder α] [Preorder β] {u : β -> α} (l : LowerAdjoint u)

/--
Definition of `closed` / `closed` 的定义

English:
definition closed
  signature: : Set α
  body: {x | u (l x) = x}

中文:
定义 closed
  签名: : Set α
  定义体: {x | u (l x) = x}
-/
def closed : Set α := {x | u (l x) = x}

/--
theorem `mem_closed_iff` / 定理 `mem_closed_iff`

English:
theorem mem_closed_iff
  given: (x : α)
  statement: x in l.closed ↔ u (l x) = x
  proof: Iff.rfl

中文:
定理 mem_closed_iff
  条件: (x : α)
  结论: x in l.closed ↔ u (l x) = x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_closed_iff (x : α) : x in l.closed ↔ u (l x) = x :=
  Iff.rfl

/--
theorem `closure_eq_self_of_mem_closed` / 定理 `closure_eq_self_of_mem_closed`

English:
theorem closure_eq_self_of_mem_closed
  given: {x : α} (h : x in l.closed)
  statement: u (l x) = x
  proof: h

中文:
定理 closure_eq_self_of_mem_closed
  条件: {x : α} (h : x in l.closed)
  结论: u (l x) = x
  证明: h
-/
theorem closure_eq_self_of_mem_closed {x : α} (h : x in l.closed) : u (l x) = x :=
  h

end Preorder

section PartialOrder

variable [PartialOrder α] [Preorder β] {u : β -> α} (l : LowerAdjoint u)

/--
theorem `mem_closed_iff_closure_le` / 定理 `mem_closed_iff_closure_le`

English:
theorem mem_closed_iff_closure_le
  given: (x : α)
  statement: x in l.closed ↔ u (l x) <= x
  proof: l.closureOperator.isClosed_iff_closure_le

@[simp]

中文:
定理 mem_closed_iff_closure_le
  条件: (x : α)
  结论: x in l.closed ↔ u (l x) <= x
  证明: l.closureOperator.isClosed_iff_closure_le

@[simp]

Depends on / 依赖: closureOperator, isClosed_iff_closure_le, l.closureOperator.isClosed_iff_closure_le
-/
theorem mem_closed_iff_closure_le (x : α) : x in l.closed ↔ u (l x) <= x :=
  l.closureOperator.isClosed_iff_closure_le

@[simp]
/--
theorem `closure_is_closed` / 定理 `closure_is_closed`

English:
theorem closure_is_closed
  given: (x : α)
  statement: u (l x) in l.closed
  proof: l.idempotent x

中文:
定理 closure_is_closed
  条件: (x : α)
  结论: u (l x) in l.closed
  证明: l.idempotent x

Depends on / 依赖: idempotent, l.idempotent
-/
theorem closure_is_closed (x : α) : u (l x) in l.closed :=
  l.idempotent x

/--
theorem `closed_eq_range_close` / 定理 `closed_eq_range_close`

English:
theorem closed_eq_range_close
  statement: l.closed = Set.range (u ∘ l)
  proof: l.closureOperator.setOfPred_isClosed_eq_range_closure

中文:
定理 closed_eq_range_close
  结论: l.closed = Set.range (u ∘ l)
  证明: l.closureOperator.setOfPred_isClosed_eq_range_closure

Depends on / 依赖: closureOperator, l.closureOperator.setOfPred_isClosed_eq_range_closure, setOfPred_isClosed_eq_range_closure
-/
theorem closed_eq_range_close : l.closed = Set.range (u ∘ l) :=
  l.closureOperator.setOfPred_isClosed_eq_range_closure

/--
Definition of `toClosed` / `toClosed` 的定义

English:
definition toClosed
  signature: (x : α)
  body: ⟨u (l x), l.closure_is_closed x⟩

@[simp]

中文:
定义 toClosed
  签名: (x : α)
  定义体: ⟨u (l x), l.closure_is_closed x⟩

@[simp]

Depends on / 依赖: closure_is_closed, l.closure_is_closed
-/
def toClosed (x : α) : l.closed :=
  ⟨u (l x), l.closure_is_closed x⟩

@[simp]
/--
theorem `closure_le_closed_iff_le` / 定理 `closure_le_closed_iff_le`

English:
theorem closure_le_closed_iff_le
  given: (x : α) {y : α} (hy : y in l.closed)
  statement: u (l x) <= y ↔ x <= y
  proof: (show l.closureOperator.IsClosed y from hy).closure_le_iff

中文:
定理 closure_le_closed_iff_le
  条件: (x : α) {y : α} (hy : y in l.closed)
  结论: u (l x) <= y ↔ x <= y
  证明: (show l.closureOperator.IsClosed y from hy).closure_le_iff

Depends on / 依赖: IsClosed, closureOperator, closure_le_iff, l.closureOperator.IsClosed
-/
theorem closure_le_closed_iff_le (x : α) {y : α} (hy : y in l.closed) : u (l x) <= y ↔ x <= y :=
  (show l.closureOperator.IsClosed y from hy).closure_le_iff

end PartialOrder

/--
theorem `closure_top` / 定理 `closure_top`

English:
theorem closure_top
  given: [PartialOrder α] [OrderTop α] [Preorder β] {u : β -> α} (l : LowerAdjoint u)
  proof: l.closureOperator.closure_top

中文:
定理 closure_top
  条件: [PartialOrder α] [OrderTop α] [Preorder β] {u : β -> α} (l : LowerAdjoint u)
  证明: l.closureOperator.closure_top

Depends on / 依赖: closureOperator, closure_top, l.closureOperator.closure_top
-/
theorem closure_top [PartialOrder α] [OrderTop α] [Preorder β] {u : β -> α} (l : LowerAdjoint u) :
    u (l ⊤) = ⊤ :=
  l.closureOperator.closure_top

/--
theorem `closure_inf_le` / 定理 `closure_inf_le`

English:
theorem closure_inf_le
  given: [SemilatticeInf α] [Preorder β] {u : β -> α} (l : LowerAdjoint u) (x y : α)
  proof: l.closureOperator.closure_inf_le x y

中文:
定理 closure_inf_le
  条件: [SemilatticeInf α] [Preorder β] {u : β -> α} (l : LowerAdjoint u) (x y : α)
  证明: l.closureOperator.closure_inf_le x y

Depends on / 依赖: closureOperator, closure_inf_le, l.closureOperator.closure_inf_le
-/
theorem closure_inf_le [SemilatticeInf α] [Preorder β] {u : β -> α} (l : LowerAdjoint u) (x y : α) :
    u (l (x ⊓ y)) <= u (l x) ⊓ u (l y) :=
  l.closureOperator.closure_inf_le x y

section SemilatticeSup

variable [SemilatticeSup α] [Preorder β] {u : β -> α} (l : LowerAdjoint u)

/--
theorem `closure_sup_closure_le` / 定理 `closure_sup_closure_le`

English:
theorem closure_sup_closure_le
  given: (x y : α)
  statement: u (l x) ⊔ u (l y) <= u (l (x ⊔ y))
  proof: l.closureOperator.closure_sup_closure_le x y

中文:
定理 closure_sup_closure_le
  条件: (x y : α)
  结论: u (l x) ⊔ u (l y) <= u (l (x ⊔ y))
  证明: l.closureOperator.closure_sup_closure_le x y

Depends on / 依赖: closureOperator, closure_sup_closure_le, l.closureOperator.closure_sup_closure_le
-/
theorem closure_sup_closure_le (x y : α) : u (l x) ⊔ u (l y) <= u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure_le x y

/--
theorem `closure_sup_closure_left` / 定理 `closure_sup_closure_left`

English:
theorem closure_sup_closure_left
  given: (x y : α)
  statement: u (l (u (l x) ⊔ y)) = u (l (x ⊔ y))
  proof: l.closureOperator.closure_sup_closure_left x y

中文:
定理 closure_sup_closure_left
  条件: (x y : α)
  结论: u (l (u (l x) ⊔ y)) = u (l (x ⊔ y))
  证明: l.closureOperator.closure_sup_closure_left x y

Depends on / 依赖: closureOperator, closure_sup_closure_left, l.closureOperator.closure_sup_closure_left
-/
theorem closure_sup_closure_left (x y : α) : u (l (u (l x) ⊔ y)) = u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure_left x y

/--
theorem `closure_sup_closure_right` / 定理 `closure_sup_closure_right`

English:
theorem closure_sup_closure_right
  given: (x y : α)
  statement: u (l (x ⊔ u (l y))) = u (l (x ⊔ y))
  proof: l.closureOperator.closure_sup_closure_right x y

中文:
定理 closure_sup_closure_right
  条件: (x y : α)
  结论: u (l (x ⊔ u (l y))) = u (l (x ⊔ y))
  证明: l.closureOperator.closure_sup_closure_right x y

Depends on / 依赖: closureOperator, closure_sup_closure_right, l.closureOperator.closure_sup_closure_right
-/
theorem closure_sup_closure_right (x y : α) : u (l (x ⊔ u (l y))) = u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure_right x y

/--
theorem `closure_sup_closure` / 定理 `closure_sup_closure`

English:
theorem closure_sup_closure
  given: (x y : α)
  statement: u (l (u (l x) ⊔ u (l y))) = u (l (x ⊔ y))
  proof: l.closureOperator.closure_sup_closure x y

中文:
定理 closure_sup_closure
  条件: (x y : α)
  结论: u (l (u (l x) ⊔ u (l y))) = u (l (x ⊔ y))
  证明: l.closureOperator.closure_sup_closure x y

Depends on / 依赖: closureOperator, closure_sup_closure, l.closureOperator.closure_sup_closure
-/
theorem closure_sup_closure (x y : α) : u (l (u (l x) ⊔ u (l y))) = u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure x y

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] [Preorder β] {u : β -> α} (l : LowerAdjoint u)

/--
theorem `closure_iSup_closure` / 定理 `closure_iSup_closure`

English:
theorem closure_iSup_closure
  given: (f : ι -> α)
  statement: u (l (⨆ i, u (l (f i)))) = u (l (⨆ i, f i))
  proof: l.closureOperator.closure_iSup_closure _

中文:
定理 closure_iSup_closure
  条件: (f : ι -> α)
  结论: u (l (⨆ i, u (l (f i)))) = u (l (⨆ i, f i))
  证明: l.closureOperator.closure_iSup_closure _

Depends on / 依赖: closureOperator, closure_iSup_closure, l.closureOperator.closure_iSup_closure
-/
theorem closure_iSup_closure (f : ι -> α) : u (l (⨆ i, u (l (f i)))) = u (l (⨆ i, f i)) :=
  l.closureOperator.closure_iSup_closure _

/--
theorem `closure_iSup₂_closure` / 定理 `closure_iSup₂_closure`

English:
theorem closure_iSup₂_closure
  given: (f : forall i, κ i -> α)
  proof: l.closureOperator.closure_iSup₂_closure _

中文:
定理 closure_iSup₂_closure
  条件: (f : 对任意 i, κ i -> α)
  证明: l.closureOperator.closure_iSup₂_closure _

Depends on / 依赖: closureOperator, l.closureOperator.closure_iSup
-/
theorem closure_iSup₂_closure (f : forall i, κ i -> α) :
    u (l <| ⨆ (i) (j), u (l <| f i j)) = u (l <| ⨆ (i) (j), f i j) :=
  l.closureOperator.closure_iSup₂_closure _

end CompleteLattice

-- Lemmas for `LowerAdjoint ((↑) : α → Set β)`, where `SetLike α β`
section CoeToSet

variable [SetLike α β]

section Preorder

variable [Preorder α] (l : LowerAdjoint ((↑) : α -> Set β))

/--
theorem `subset_closure` / 定理 `subset_closure`

English:
theorem subset_closure
  given: (s : Set β)
  statement: s subseteq l s
  proof: l.le_closure s

中文:
定理 subset_closure
  条件: (s : Set β)
  结论: s subseteq l s
  证明: l.le_closure s

Depends on / 依赖: l.le_closure, le_closure
-/
theorem subset_closure (s : Set β) : s subseteq l s :=
  l.le_closure s

/--
theorem `notMem_of_notMem_closure` / 定理 `notMem_of_notMem_closure`

English:
theorem notMem_of_notMem_closure
  given: {s : Set β} {P : β} (hP : P ∉ l s)
  statement: P ∉ s
  proof: fun h =>
  hP (subset_closure _ s h)

中文:
定理 notMem_of_notMem_closure
  条件: {s : Set β} {P : β} (hP : P ∉ l s)
  结论: P ∉ s
  证明: fun h =>
  hP (subset_closure _ s h)
-/
theorem notMem_of_notMem_closure {s : Set β} {P : β} (hP : P ∉ l s) : P ∉ s := fun h =>
  hP (subset_closure _ s h)

/--
theorem `le_iff_subset` / 定理 `le_iff_subset`

English:
theorem le_iff_subset
  given: (s : Set β) (S : α)
  statement: l s <= S ↔ s subseteq S
  proof: l.gc s S

中文:
定理 le_iff_subset
  条件: (s : Set β) (S : α)
  结论: l s <= S ↔ s subseteq S
  证明: l.gc s S

Depends on / 依赖: l.gc
-/
theorem le_iff_subset (s : Set β) (S : α) : l s <= S ↔ s subseteq S :=
  l.gc s S

/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: (s : Set β) (x : β)
  statement: x in l s ↔ forall S : α, s subseteq S -> x in S
  proof: by
  simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← l.le_iff_subset]
  exact ⟨fun h S => h.trans, fun h => h _ le_rfl⟩

中文:
定理 mem_iff
  条件: (s : Set β) (x : β)
  结论: x in l s ↔ 对任意 S : α, s subseteq S -> x in S
  证明: by
  simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← l.le_iff_subset]
  exact ⟨fun h S => h.trans, fun h => h _ le_rfl⟩

Depends on / 依赖: Set.singleton_subset_iff, SetLike, SetLike.mem_coe, h.trans, l.le_iff_subset, le_iff_subset, le_rfl, mem_coe, simp_rw, singleton_subset_iff
-/
theorem mem_iff (s : Set β) (x : β) : x in l s ↔ forall S : α, s subseteq S -> x in S := by
  simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← l.le_iff_subset]
  exact ⟨fun h S => h.trans, fun h => h _ le_rfl⟩

/--
theorem `closure_union_closure_subset` / 定理 `closure_union_closure_subset`

English:
theorem closure_union_closure_subset
  given: (x y : α)
  statement: (l x : Set β) union l y subseteq l (x union y)
  proof: l.closure_sup_closure_le x y

@[simp]

中文:
定理 closure_union_closure_subset
  条件: (x y : α)
  结论: (l x : Set β) union l y subseteq l (x union y)
  证明: l.closure_sup_closure_le x y

@[simp]

Depends on / 依赖: closure_sup_closure_le, l.closure_sup_closure_le
-/
theorem closure_union_closure_subset (x y : α) : (l x : Set β) union l y subseteq l (x union y) :=
  l.closure_sup_closure_le x y

@[simp]
/--
theorem `closure_union_closure_left` / 定理 `closure_union_closure_left`

English:
theorem closure_union_closure_left
  given: (x y : α)
  statement: l (l x union y) = l (x union y)
  proof: SetLike.coe_injective (l.closure_sup_closure_left x y)

@[simp]

中文:
定理 closure_union_closure_left
  条件: (x y : α)
  结论: l (l x union y) = l (x union y)
  证明: SetLike.coe_injective (l.closure_sup_closure_left x y)

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, closure_sup_closure_left, coe_injective, l.closure_sup_closure_left
-/
theorem closure_union_closure_left (x y : α) : l (l x union y) = l (x union y) :=
  SetLike.coe_injective (l.closure_sup_closure_left x y)

@[simp]
/--
theorem `closure_union_closure_right` / 定理 `closure_union_closure_right`

English:
theorem closure_union_closure_right
  given: (x y : α)
  statement: l (x union l y) = l (x union y)
  proof: SetLike.coe_injective (l.closure_sup_closure_right x y)

中文:
定理 closure_union_closure_right
  条件: (x y : α)
  结论: l (x union l y) = l (x union y)
  证明: SetLike.coe_injective (l.closure_sup_closure_right x y)

Depends on / 依赖: SetLike, SetLike.coe_injective, closure_sup_closure_right, coe_injective, l.closure_sup_closure_right
-/
theorem closure_union_closure_right (x y : α) : l (x union l y) = l (x union y) :=
  SetLike.coe_injective (l.closure_sup_closure_right x y)

/--
theorem `closure_union_closure` / 定理 `closure_union_closure`

English:
theorem closure_union_closure
  given: (x y : α)
  statement: l (l x union l y) = l (x union y)
  proof: by
  rw [closure_union_closure_right]; rw [closure_union_closure_left]

@[simp]

中文:
定理 closure_union_closure
  条件: (x y : α)
  结论: l (l x union l y) = l (x union y)
  证明: by
  rw [closure_union_closure_right]; rw [closure_union_closure_left]

@[simp]

Depends on / 依赖: closure_union_closure_left, closure_union_closure_right
-/
theorem closure_union_closure (x y : α) : l (l x union l y) = l (x union y) := by
  rw [closure_union_closure_right]; rw [closure_union_closure_left]

@[simp]
/--
theorem `closure_iUnion_closure` / 定理 `closure_iUnion_closure`

English:
theorem closure_iUnion_closure
  given: (f : ι -> α)
  statement: l (⋃ i, l (f i)) = l (⋃ i, f i)
  proof: SetLike.coe_injective l.closure_iSup_closure _

@[simp]

中文:
定理 closure_iUnion_closure
  条件: (f : ι -> α)
  结论: l (⋃ i, l (f i)) = l (⋃ i, f i)
  证明: SetLike.coe_injective l.closure_iSup_closure _

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, closure_iSup_closure, coe_injective, l.closure_iSup_closure
-/
theorem closure_iUnion_closure (f : ι -> α) : l (⋃ i, l (f i)) = l (⋃ i, f i) :=
SetLike.coe_injective l.closure_iSup_closure _

@[simp]
/--
theorem `closure_iUnion₂_closure` / 定理 `closure_iUnion₂_closure`

English:
theorem closure_iUnion₂_closure
  given: (f : forall i, κ i -> α)
  proof: SetLike.coe_injective l.closure_iSup₂_closure _

中文:
定理 closure_iUnion₂_closure
  条件: (f : 对任意 i, κ i -> α)
  证明: SetLike.coe_injective l.closure_iSup₂_closure _

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, l.closure_iSup
-/
theorem closure_iUnion₂_closure (f : forall i, κ i -> α) :
    l (⋃ (i) (j), l (f i j)) = l (⋃ (i) (j), f i j) :=
SetLike.coe_injective l.closure_iSup₂_closure _

end Preorder

section PartialOrder

variable [PartialOrder α] (l : LowerAdjoint ((↑) : α -> Set β))

/--
theorem `eq_of_le` / 定理 `eq_of_le`

English:
theorem eq_of_le
  given: {s : Set β} {S : α} (h₁ : s subseteq S) (h₂ : S <= l s)
  statement: l s = S
  proof: ((l.le_iff_subset _ _).2 h₁).antisymm h₂

中文:
定理 eq_of_le
  条件: {s : Set β} {S : α} (h₁ : s subseteq S) (h₂ : S <= l s)
  结论: l s = S
  证明: ((l.le_iff_subset _ _).2 h₁).antisymm h₂

Depends on / 依赖: antisymm, l.le_iff_subset, le_iff_subset
-/
theorem eq_of_le {s : Set β} {S : α} (h₁ : s subseteq S) (h₂ : S <= l s) : l s = S :=
  ((l.le_iff_subset _ _).2 h₁).antisymm h₂

end PartialOrder

end CoeToSet

end LowerAdjoint

/-! ### Translations between `GaloisConnection`, `LowerAdjoint`, `ClosureOperator` -/

/-- Every Galois connection induces a lower adjoint. -/
@[simps]
/--
Definition of `GaloisConnection.lowerAdjoint` / `GaloisConnection.lowerAdjoint` 的定义

English:
definition GaloisConnection.lowerAdjoint
  signature: [Preorder α] [Preorder β] {l : α -> β} {u : β -> α}
  body: l
  gc' := gc

中文:
定义 GaloisConnection.lowerAdjoint
  签名: [Preorder α] [Preorder β] {l : α -> β} {u : β -> α}
  定义体: l
  gc' := gc
-/
def GaloisConnection.lowerAdjoint [Preorder α] [Preorder β] {l : α -> β} {u : β -> α}
    (gc : GaloisConnection l u) : LowerAdjoint u where
  toFun := l
  gc' := gc

/-- Every Galois connection induces a closure operator given by the composition. This is the partial
order version of the statement that every adjunction induces a monad. -/
@[simps!]
/--
Definition of `GaloisConnection.closureOperator` / `GaloisConnection.closureOperator` 的定义

English:
definition GaloisConnection.closureOperator
  signature: [PartialOrder α] [Preorder β] {l : α -> β} {u : β -> α}
  body: gc.lowerAdjoint.closureOperator

中文:
定义 GaloisConnection.closureOperator
  签名: [PartialOrder α] [Preorder β] {l : α -> β} {u : β -> α}
  定义体: gc.lowerAdjoint.closureOperator

Depends on / 依赖: closureOperator, gc.lowerAdjoint.closureOperator, lowerAdjoint
-/
def GaloisConnection.closureOperator [PartialOrder α] [Preorder β] {l : α -> β} {u : β -> α}
    (gc : GaloisConnection l u) : ClosureOperator α :=
  gc.lowerAdjoint.closureOperator

/--
Definition of `ClosureOperator.gi` / `ClosureOperator.gi` 的定义

English:
definition ClosureOperator.gi
  signature: [PartialOrder α] (c : ClosureOperator α)
  body: ⟨x, isClosed_iff_closure_le.2 hx⟩
  gc _ y := y.2.closure_le_iff
  le_l_u _ := c.le_closure _
  choice_eq x hx := le_antisymm (c.le_closure x) hx

中文:
定义 ClosureOperator.gi
  签名: [PartialOrder α] (c : ClosureOperator α)
  定义体: ⟨x, isClosed_iff_closure_le.2 hx⟩
  gc _ y := y.2.closure_le_iff
  le_l_u _ := c.le_closure _
  choice_eq x hx := le_antisymm (c.le_closure x) hx

Depends on / 依赖: isClosed_iff_closure_le
-/
def ClosureOperator.gi [PartialOrder α] (c : ClosureOperator α) :
    GaloisInsertion c.toCloseds (↑) where
  choice x hx := ⟨x, isClosed_iff_closure_le.2 hx⟩
  gc _ y := y.2.closure_le_iff
  le_l_u _ := c.le_closure _
  choice_eq x hx := le_antisymm (c.le_closure x) hx

/-- The Galois insertion associated to a closure operator can be used to reconstruct the closure
operator.
Note that the inverse in the opposite direction does not hold in general. -/
@[simp]
/--
theorem `closureOperator_gi_self` / 定理 `closureOperator_gi_self`

English:
theorem closureOperator_gi_self
  given: [PartialOrder α] (c : ClosureOperator α)
  proof: by
  ext x
  rfl

中文:
定理 closureOperator_gi_self
  条件: [PartialOrder α] (c : ClosureOperator α)
  证明: by
  ext x
  rfl
-/
theorem closureOperator_gi_self [PartialOrder α] (c : ClosureOperator α) :
    c.gi.gc.closureOperator = c := by
  ext x
  rfl
