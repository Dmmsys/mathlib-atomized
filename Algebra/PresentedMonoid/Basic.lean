/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.GroupTheory.Congruence.Hom

/-!
# Defining a monoid given by generators and relations

Given relations `rels` on the free monoid on a type `α`, this file constructs the monoid
given by generators `x : α` and relations `rels`.

## Main definitions

* `PresentedMonoid rels`: the quotient of the free monoid on a type `α` by the closure of one-step
  reductions (arising from a binary relation on free monoid elements `rels`).
* `PresentedMonoid.of`: The canonical map from `α` to a presented monoid with generators `α`.
* `PresentedMonoid.lift f`: the canonical monoid homomorphism `PresentedMonoid rels → M`, given
  a function `f : α → G` from a type `α` to a monoid `M` which satisfies the relations `rels`.

## Tags

generators, relations, monoid presentations
-/

@[expose] public section

variable {α : Type*}

/-- Given a set of relations, `rels`, over a type `α`, `PresentedMonoid` constructs the monoid with
generators `x : α` and relations `rels` as a quotient of a congruence structure over rels. -/
@[to_additive /-- Given a set of relations, `rels`, over a type `α`, `PresentedAddMonoid` constructs
the monoid with generators `x : α` and relations `rels` as a quotient of an AddCon structure over
rels -/]
/--
Definition of `PresentedMonoid` / `PresentedMonoid` 的定义

English:
definition PresentedMonoid
  signature: (rels : FreeMonoid α -> FreeMonoid α -> Prop)
  body: (conGen rels).Quotient

中文:
定义 PresentedMonoid
  签名: (rels : FreeMonoid α -> FreeMonoid α -> 命题)
  定义体: (conGen rels).Quotient

Depends on / 依赖: Quotient, conGen
-/
def PresentedMonoid (rels : FreeMonoid α -> FreeMonoid α -> Prop) := (conGen rels).Quotient

namespace PresentedMonoid

open Set Submonoid

@[to_additive]
instance {rels : FreeMonoid α -> FreeMonoid α -> Prop} : Monoid (PresentedMonoid rels) :=
inferInstanceAs Monoid (conGen rels).Quotient

/-- The quotient map from the free monoid on `α` to the presented monoid with the same generators
and the given relations `rels`. -/
@[to_additive /-- The quotient map from the free additive monoid on `α` to the presented additive
monoid with the same generators and the given relations `rels` -/]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (rels : FreeMonoid α -> FreeMonoid α -> Prop)
  body: Quotient.mk (conGen rels).toSetoid
  map_one' := rfl
  map_mul' := fun _ _ => rfl

中文:
定义 mk
  签名: (rels : FreeMonoid α -> FreeMonoid α -> 命题)
  定义体: Quotient.mk (conGen rels).toSetoid
  map_one' := rfl
  map_mul' := fun _ _ => rfl

Depends on / 依赖: Quotient, Quotient.mk, conGen, toSetoid
-/
def mk (rels : FreeMonoid α -> FreeMonoid α -> Prop) : FreeMonoid α ->* PresentedMonoid rels where
  toFun := Quotient.mk (conGen rels).toSetoid
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- `of` is the canonical map from `α` to a presented monoid with generators `x : α`. The term `x`
is mapped to the equivalence class of the image of `x` in `FreeMonoid α`. -/
@[to_additive
/-- `of` is the canonical map from `α` to a presented additive monoid with generators `x : α`. The
term `x` is mapped to the equivalence class of the image of `x` in `FreeAddMonoid α`. -/]
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (rels : FreeMonoid α -> FreeMonoid α -> Prop) (x : α)
  body: mk rels (.of x)

中文:
定义 of
  签名: (rels : FreeMonoid α -> FreeMonoid α -> 命题) (x : α)
  定义体: mk rels (.of x)
-/
def of (rels : FreeMonoid α -> FreeMonoid α -> Prop) (x : α) : PresentedMonoid rels :=
  mk rels (.of x)

section inductionOn

variable {α₁ α₂ α₃ : Type*} {rels₁ : FreeMonoid α₁ -> FreeMonoid α₁ -> Prop}
  {rels₂ : FreeMonoid α₂ -> FreeMonoid α₂ -> Prop} {rels₃ : FreeMonoid α₃ -> FreeMonoid α₃ -> Prop}

local notation "P₁" => PresentedMonoid rels₁
local notation "P₂" => PresentedMonoid rels₂
local notation "P₃" => PresentedMonoid rels₃

@[to_additive (attr := elab_as_elim), induction_eliminator]
/--
theorem `inductionOn` / 定理 `inductionOn`

English:
theorem inductionOn
  given: {δ : P₁ -> Prop} (q : P₁) (h : forall a, δ (mk rels₁ a))
  statement: δ q
  proof: Quotient.ind h q

@[to_additive (attr := elab_as_elim)]

中文:
定理 inductionOn
  条件: {δ : P₁ -> 命题} (q : P₁) (h : 对任意 a, δ (mk rels₁ a))
  结论: δ q
  证明: Quotient.ind h q

@[to_additive (attr := elab_as_elim)]
-/
protected theorem inductionOn {δ : P₁ -> Prop} (q : P₁) (h : forall a, δ (mk rels₁ a)) : δ q :=
  Quotient.ind h q

@[to_additive (attr := elab_as_elim)]
/--
theorem `inductionOn₂` / 定理 `inductionOn₂`

English:
theorem inductionOn₂
  statement: {δ : P₁ -> P₂ -> Prop} (q₁ : P₁) (q₂ : P₂)
  proof: Quotient.inductionOn₂ q₁ q₂ h

@[to_additive (attr := elab_as_elim)]

中文:
定理 inductionOn₂
  结论: {δ : P₁ -> P₂ -> 命题} (q₁ : P₁) (q₂ : P₂)
  证明: Quotient.inductionOn₂ q₁ q₂ h

@[to_additive (attr := elab_as_elim)]
-/
protected theorem inductionOn₂ {δ : P₁ -> P₂ -> Prop} (q₁ : P₁) (q₂ : P₂)
    (h : forall a b, δ (mk rels₁ a) (mk rels₂ b)) : δ q₁ q₂ :=
  Quotient.inductionOn₂ q₁ q₂ h

@[to_additive (attr := elab_as_elim)]
/--
theorem `inductionOn₃` / 定理 `inductionOn₃`

English:
theorem inductionOn₃
  statement: {δ : P₁ -> P₂ -> P₃ -> Prop} (q₁ : P₁)
  proof: Quotient.inductionOn₃ q₁ q₂ q₃ h

中文:
定理 inductionOn₃
  结论: {δ : P₁ -> P₂ -> P₃ -> 命题} (q₁ : P₁)
  证明: Quotient.inductionOn₃ q₁ q₂ q₃ h
-/
protected theorem inductionOn₃ {δ : P₁ -> P₂ -> P₃ -> Prop} (q₁ : P₁)
    (q₂ : P₂) (q₃ : P₃) (h : forall a b c, δ (mk rels₁ a) (mk rels₂ b) (mk rels₃ c)) :
    δ q₁ q₂ q₃ :=
  Quotient.inductionOn₃ q₁ q₂ q₃ h

end inductionOn

variable {α : Type*} {rels : FreeMonoid α -> FreeMonoid α -> Prop} {x y : FreeMonoid α}

/--
lemma `mk_eq_mk_iff` / 引理 `mk_eq_mk_iff`

English:
lemma mk_eq_mk_iff
  statement: mk rels x = mk rels y ↔ conGen rels x y
  proof: Quotient.eq

中文:
引理 mk_eq_mk_iff
  结论: mk rels x = mk rels y ↔ conGen rels x y
  证明: Quotient.eq

Depends on / 依赖: Quotient, Quotient.eq
-/
lemma mk_eq_mk_iff : mk rels x = mk rels y ↔ conGen rels x y := Quotient.eq

/--
lemma `mk_eq_mk_of_rel` / 引理 `mk_eq_mk_of_rel`

English:
lemma mk_eq_mk_of_rel
  given: (h : rels x y)
  statement: mk rels x = mk rels y
  proof: mk_eq_mk_iff.2 (.of _ _ h)

中文:
引理 mk_eq_mk_of_rel
  条件: (h : rels x y)
  结论: mk rels x = mk rels y
  证明: mk_eq_mk_iff.2 (.of _ _ h)

Depends on / 依赖: mk_eq_mk_iff
-/
lemma mk_eq_mk_of_rel (h : rels x y) : mk rels x = mk rels y := mk_eq_mk_iff.2 (.of _ _ h)

/-- The generators of a presented monoid generate the presented monoid. That is, the submonoid
closure of the set of generators equals `⊤`. -/
@[to_additive (attr := simp) /-- The generators of a presented additive monoid generate the
presented additive monoid. That is, the additive submonoid closure of the set of generators equals
`⊤`. -/]
/--
theorem `closure_range_of` / 定理 `closure_range_of`

English:
theorem closure_range_of
  given: (rels : FreeMonoid α -> FreeMonoid α -> Prop)
  proof: by
  rw [Submonoid.eq_top_iff']
  intro x
  induction x with | _ a
  induction a with
  | one => exact Submonoid.one_mem _
| of x => exact subset_closure by simp [range, of]
  | mul x y hx hy => exact Submonoid.mul_mem _ hx hy

@[to_additive]

中文:
定理 closure_range_of
  条件: (rels : FreeMonoid α -> FreeMonoid α -> 命题)
  证明: by
  rw [Submonoid.eq_top_iff']
  intro x
  induction x with | _ a
  induction a with
  | one => exact Submonoid.one_mem _
| of x => exact subset_closure by simp [range, of]
  | mul x y hx hy => exact Submonoid.mul_mem _ hx hy

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.eq_top_iff, Submonoid.mul_mem, Submonoid.one_mem, eq_top_iff, mul_mem, one_mem, subset_closure
-/
theorem closure_range_of (rels : FreeMonoid α -> FreeMonoid α -> Prop) :
    Submonoid.closure (Set.range (of rels)) = ⊤ := by
  rw [Submonoid.eq_top_iff']
  intro x
  induction x with | _ a
  induction a with
  | one => exact Submonoid.one_mem _
| of x => exact subset_closure by simp [range, of]
  | mul x y hx hy => exact Submonoid.mul_mem _ hx hy

@[to_additive]
/--
theorem `surjective_mk` / 定理 `surjective_mk`

English:
theorem surjective_mk
  given: {rels : FreeMonoid α -> FreeMonoid α -> Prop}
  proof: fun x => PresentedMonoid.inductionOn x fun a => .intro a rfl

中文:
定理 surjective_mk
  条件: {rels : FreeMonoid α -> FreeMonoid α -> 命题}
  证明: fun x => PresentedMonoid.inductionOn x fun a => .intro a rfl

Depends on / 依赖: PresentedMonoid, PresentedMonoid.inductionOn, inductionOn
-/
theorem surjective_mk {rels : FreeMonoid α -> FreeMonoid α -> Prop} :
    Function.Surjective (mk rels) := fun x => PresentedMonoid.inductionOn x fun a => .intro a rfl

section ToMonoid
variable {α M : Type*} [Monoid M] (f : α -> M)
variable {rels : FreeMonoid α -> FreeMonoid α -> Prop}
variable (h : forall a b : FreeMonoid α, rels a b -> FreeMonoid.lift f a = FreeMonoid.lift f b)

/-- The extension of a map `f : α → M` that satisfies the given relations to a monoid homomorphism
from `PresentedMonoid rels → M`. -/
@[to_additive /-- The extension of a map `f : α → M` that satisfies the given relations to an
additive-monoid homomorphism from `PresentedAddMonoid rels → M` -/]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : PresentedMonoid rels ->* M
  body: Con.lift _ (FreeMonoid.lift f) (Con.conGen_le.2 h)

@[to_additive]

中文:
定义 lift
  签名: : PresentedMonoid rels ->* M
  定义体: Con.lift _ (FreeMonoid.lift f) (Con.conGen_le.2 h)

@[to_additive]

Depends on / 依赖: Con.conGen_le, Con.lift, FreeMonoid, FreeMonoid.lift, conGen_le
-/
def lift : PresentedMonoid rels ->* M :=
  Con.lift _ (FreeMonoid.lift f) (Con.conGen_le.2 h)

@[to_additive]
/--
theorem `toMonoid.unique` / 定理 `toMonoid.unique`

English:
theorem toMonoid.unique
  statement: (g : MonoidHom (conGen rels).Quotient M)
  proof: Con.lift_unique (Con.conGen_le.2 h) g (FreeMonoid.hom_eq hg)

@[to_additive (attr := simp)]

中文:
定理 toMonoid.unique
  结论: (g : MonoidHom (conGen rels).Quotient M)
  证明: Con.lift_unique (Con.conGen_le.2 h) g (FreeMonoid.hom_eq hg)

@[to_additive (attr := simp)]

Depends on / 依赖: Con.conGen_le, Con.lift_unique, FreeMonoid, FreeMonoid.hom_eq, conGen_le, hom_eq, lift_unique
-/
theorem toMonoid.unique (g : MonoidHom (conGen rels).Quotient M)
    (hg : forall a : α, g (of rels a) = f a) : g = lift f h :=
  Con.lift_unique (Con.conGen_le.2 h) g (FreeMonoid.hom_eq hg)

@[to_additive (attr := simp)]
/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: {x : α}
  statement: lift f h (of rels x) = f x
  proof: rfl

中文:
定理 lift_of
  条件: {x : α}
  结论: lift f h (of rels x) = f x
  证明: rfl
-/
theorem lift_of {x : α} : lift f h (of rels x) = f x := rfl

end ToMonoid

@[to_additive (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {M : Type*} [Monoid M] (rels : FreeMonoid α -> FreeMonoid α -> Prop)
  proof: by
  apply MonoidHom.eq_of_eqOn_denseM (closure_range_of _)
  grind [Set.eqOn_range]

中文:
定理 ext
  结论: {M : 类型} [Monoid M] (rels : FreeMonoid α -> FreeMonoid α -> 命题)
  证明: by
  apply MonoidHom.eq_of_eqOn_denseM (closure_range_of _)
  grind [Set.eqOn_range]

Depends on / 依赖: MonoidHom, MonoidHom.eq_of_eqOn_denseM, Set.eqOn_range, closure_range_of, eqOn_range, eq_of_eqOn_denseM
-/
theorem ext {M : Type*} [Monoid M] (rels : FreeMonoid α -> FreeMonoid α -> Prop)
    {φ ψ : PresentedMonoid rels ->* M} (hx : forall (x : α), φ (.of rels x) = ψ (.of rels x)) :
    φ = ψ := by
  apply MonoidHom.eq_of_eqOn_denseM (closure_range_of _)
  grind [Set.eqOn_range]

end PresentedMonoid
