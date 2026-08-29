/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Data.Sym.Basic
public import Mathlib.Data.Sym.Sym2.Init

/-!
# The symmetric square

This file defines the symmetric square, which is `α × α` modulo
swapping. This is also known as the type of unordered pairs.

More generally, the symmetric square is the second symmetric power
(see `Data.Sym.Basic`). The equivalence is `Sym2.equivSym`.

From the point of view that an unordered pair is equivalent to a
multiset of cardinality two (see `Sym2.equivMultiset`), there is a
`Mem` instance `Sym2.Mem`, which is a `Prop`-valued membership
test. Given `h : a ∈ z` for `z : Sym2 α`, then `Mem.other h` is the other
element of the pair, defined using `Classical.choice`. If `α` has
decidable equality, then `h.other'` computably gives the other element.

The universal property of `Sym2` is provided as `Sym2.lift`, which
states that functions from `Sym2 α` are equivalent to symmetric
two-argument functions from `α`.

Recall that an undirected graph (allowing self loops, but no multiple
edges) is equivalent to a symmetric relation on the vertex type `α`.
Given a symmetric relation on `α`, the corresponding edge set is
constructed by `Sym2.fromRel` which is a special case of `Sym2.lift`.

## Notation

The element `Sym2.mk (a, b)` can be written as `s(a, b)` for short.

## Tags

symmetric square, unordered pairs, symmetric powers
-/

@[expose] public section

assert_not_exists MonoidWithZero

open List (Vector)
open Finset Function Sym

universe u

variable {α β γ : Type*}

namespace Sym2

/-- This is the relation capturing the notion of pairs equivalent up to permutations. -/
@[aesop (rule_sets := [Sym2]) [safe [constructors, cases], norm]]
/--
Inductive type `Rel` / 归纳类型 `Rel`

English:
inductive Rel
  parameters: (α : Type u)
  constructors (2):
    - refl: (x y : α) : Rel _ (x, y) (x, y)
    - swap: (x y : α) : Rel _ (x, y) (y, x)

中文:
归纳类型 Rel
  参数: (α : 类型u)
  构造子 (2 个):
    - refl: (x y : α) : Rel _ (x, y) (x, y)
    - swap: (x y : α) : Rel _ (x, y) (y, x)
-/
inductive Rel (α : Type u) : α × α -> α × α -> Prop
  | refl (x y : α) : Rel _ (x, y) (x, y)
  | swap (x y : α) : Rel _ (x, y) (y, x)

attribute [refl] Rel.refl

@[symm]
/--
theorem `Rel.symm` / 定理 `Rel.symm`

English:
theorem Rel.symm
  given: {x y : α × α}
  statement: Rel α x y -> Rel α y x
  proof: by aesop (rule_sets := [Sym2])

@[trans]

中文:
定理 Rel.symm
  条件: {x y : α × α}
  结论: Rel α x y -> Rel α y x
  证明: by aesop (rule_sets := [Sym2])

@[trans]

Depends on / 依赖: rule_sets
-/
theorem Rel.symm {x y : α × α} : Rel α x y -> Rel α y x := by aesop (rule_sets := [Sym2])

@[trans]
/--
theorem `Rel.trans` / 定理 `Rel.trans`

English:
theorem Rel.trans
  given: {x y z : α × α} (a : Rel α x y) (b : Rel α y z)
  statement: Rel α x z
  proof: by
  aesop (rule_sets := [Sym2])

中文:
定理 Rel.trans
  条件: {x y z : α × α} (a : Rel α x y) (b : Rel α y z)
  结论: Rel α x z
  证明: by
  aesop (rule_sets := [Sym2])
-/
theorem Rel.trans {x y z : α × α} (a : Rel α x y) (b : Rel α y z) : Rel α x z := by
  aesop (rule_sets := [Sym2])

/--
theorem `Rel.is_equivalence` / 定理 `Rel.is_equivalence`

English:
theorem Rel.is_equivalence
  statement: Equivalence (Rel α)
  proof: { refl := fun (x, y) => Rel.refl x y, symm := Rel.symm, trans := Rel.trans }

中文:
定理 Rel.is_equivalence
  结论: Equivalence (Rel α)
  证明: { refl := fun (x, y) => Rel.refl x y, symm := Rel.symm, trans := Rel.trans }

Depends on / 依赖: Rel.refl, Rel.symm, Rel.trans
-/
theorem Rel.is_equivalence : Equivalence (Rel α) :=
  { refl := fun (x, y) => Rel.refl x y, symm := Rel.symm, trans := Rel.trans }

/-- One can use `attribute [local instance] Sym2.Rel.setoid` to temporarily
make `Quotient` functionality work for `α × α`. -/
@[instance_reducible]
/--
Definition of `Rel.setoid` / `Rel.setoid` 的定义

English:
definition Rel.setoid
  signature: (α : Type u)
  body: ⟨Rel α, Rel.is_equivalence⟩

@[simp, grind =]

中文:
定义 Rel.setoid
  签名: (α : 类型u)
  定义体: ⟨Rel α, Rel.is_equivalence⟩

@[simp, grind =]

Depends on / 依赖: Rel.is_equivalence, is_equivalence
-/
def Rel.setoid (α : Type u) : Setoid (α × α) :=
  ⟨Rel α, Rel.is_equivalence⟩

@[simp, grind =]
/--
theorem `rel_iff'` / 定理 `rel_iff'`

English:
theorem rel_iff'
  given: {p q : α × α}
  statement: Rel α p q ↔ p = q ∨ p = q.swap
  proof: by
  aesop (rule_sets := [Sym2])

中文:
定理 rel_iff'
  条件: {p q : α × α}
  结论: Rel α p q ↔ p = q ∨ p = q.swap
  证明: by
  aesop (rule_sets := [Sym2])

Depends on / 依赖: rule_sets
-/
theorem rel_iff' {p q : α × α} : Rel α p q ↔ p = q ∨ p = q.swap := by
  aesop (rule_sets := [Sym2])

/--
theorem `rel_iff` / 定理 `rel_iff`

English:
theorem rel_iff
  given: {x y z w : α}
  statement: Rel α (x, y) (z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z
  proof: by
  simp

中文:
定理 rel_iff
  条件: {x y z w : α}
  结论: Rel α (x, y) (z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z
  证明: by
  simp
-/
theorem rel_iff {x y z w : α} : Rel α (x, y) (z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp

end Sym2

/--
Definition of `Sym2` / `Sym2` 的定义

English:
abbreviation Sym2
  signature: (α : Type u)
  body: Quot (Sym2.Rel α)

中文:
缩写 Sym2
  签名: (α : 类型u)
  定义体: Quot (Sym2.Rel α)

Depends on / 依赖: Sym2.Rel
-/
abbrev Sym2 (α : Type u) := Quot (Sym2.Rel α)

/--
Definition of `Sym2.mk` / `Sym2.mk` 的定义

English:
abbreviation Sym2.mk
  signature: {α : Type*} (a b : α)
  body: Quot.mk (Sym2.Rel α) (a, b)

中文:
缩写 Sym2.mk
  签名: {α : 类型} (a b : α)
  定义体: Quot.mk (Sym2.Rel α) (a, b)
-/
protected abbrev Sym2.mk {α : Type*} (a b : α) : Sym2 α := Quot.mk (Sym2.Rel α) (a, b)

/-- `s(x, y)` is an unordered pair,
which is to say a pair modulo the action of the symmetric group.

It is equal to `Sym2.mk (x, y)`. -/
notation3 "s(" x ", " y ")" => Sym2.mk x y

namespace Sym2

/--
theorem `sound` / 定理 `sound`

English:
theorem sound
  given: {a b c d : α} (h : Rel α (a, b) (c, d))
  statement: s(a, b) = s(c, d)
  proof: Quot.sound h

中文:
定理 sound
  条件: {a b c d : α} (h : Rel α (a, b) (c, d))
  结论: s(a, b) = s(c, d)
  证明: Quot.sound h
-/
protected theorem sound {a b c d : α} (h : Rel α (a, b) (c, d)) : s(a, b) = s(c, d) :=
  Quot.sound h

/--
theorem `exact` / 定理 `exact`

English:
theorem exact
  given: {a b c d : α} (h : s(a, b) = s(c, d))
  statement: Rel α (a, b) (c, d)
  proof: Quotient.exact (s := Sym2.Rel.setoid α) h

@[simp, grind =]

中文:
定理 exact
  条件: {a b c d : α} (h : s(a, b) = s(c, d))
  结论: Rel α (a, b) (c, d)
  证明: Quotient.exact (s := Sym2.Rel.setoid α) h

@[simp, grind =]
-/
protected theorem exact {a b c d : α} (h : s(a, b) = s(c, d)) : Rel α (a, b) (c, d) :=
  Quotient.exact (s := Sym2.Rel.setoid α) h

@[simp, grind =]
/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {a b c d : α}
  statement: s(a, b) = s(c, d) ↔ Rel α (a, b) (c, d)
  proof: Quotient.eq' (s₁ := Sym2.Rel.setoid α)

@[elab_as_elim, cases_eliminator, induction_eliminator]

中文:
定理 eq
  条件: {a b c d : α}
  结论: s(a, b) = s(c, d) ↔ Rel α (a, b) (c, d)
  证明: Quotient.eq' (s₁ := Sym2.Rel.setoid α)

@[elab_as_elim, cases_eliminator, induction_eliminator]
-/
protected theorem eq {a b c d : α} : s(a, b) = s(c, d) ↔ Rel α (a, b) (c, d) :=
  Quotient.eq' (s₁ := Sym2.Rel.setoid α)

@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  given: {f : Sym2 α -> Prop} (h : forall x y, f s(x, y))
  statement: forall i, f i
  proof: Quot.ind Prod.rec h

@[elab_as_elim]

中文:
定理 ind
  条件: {f : Sym2 α -> 命题} (h : 对任意 x y, f s(x, y))
  结论: 对任意 i, f i
  证明: Quot.ind Prod.rec h

@[elab_as_elim]
-/
protected theorem ind {f : Sym2 α -> Prop} (h : forall x y, f s(x, y)) : forall i, f i :=
Quot.ind Prod.rec h

@[elab_as_elim]
/--
theorem `inductionOn` / 定理 `inductionOn`

English:
theorem inductionOn
  given: {f : Sym2 α -> Prop} (i : Sym2 α) (hf : forall x y, f s(x, y))
  statement: f i
  proof: i.ind hf

@[elab_as_elim]

中文:
定理 inductionOn
  条件: {f : Sym2 α -> 命题} (i : Sym2 α) (hf : 对任意 x y, f s(x, y))
  结论: f i
  证明: i.ind hf

@[elab_as_elim]
-/
protected theorem inductionOn {f : Sym2 α -> Prop} (i : Sym2 α) (hf : forall x y, f s(x, y)) : f i :=
  i.ind hf

@[elab_as_elim]
/--
theorem `inductionOn₂` / 定理 `inductionOn₂`

English:
theorem inductionOn₂
  statement: {f : Sym2 α -> Sym2 β -> Prop} (i : Sym2 α) (j : Sym2 β)
  proof: Quot.induction_on₂ i j by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    exact hf _ _ _ _

中文:
定理 inductionOn₂
  结论: {f : Sym2 α -> Sym2 β -> 命题} (i : Sym2 α) (j : Sym2 β)
  证明: Quot.induction_on₂ i j by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    exact hf _ _ _ _
-/
protected theorem inductionOn₂ {f : Sym2 α -> Sym2 β -> Prop} (i : Sym2 α) (j : Sym2 β)
    (hf : forall a₁ a₂ b₁ b₂, f s(a₁, a₂) s(b₁, b₂)) : f i j :=
Quot.induction_on₂ i j by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    exact hf _ _ _ _

/-- Dependent recursion principle for `Sym2`. See `Quot.rec`. -/
@[elab_as_elim]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {motive : Sym2 α -> Sort*}
  body: Quot.rec (fun (a, b) => f a b) (fun (a, b) (c, d) => h a b c d) z

中文:
定义 rec
  签名: {motive : Sym2 α -> Sort*}
  定义体: Quot.rec (fun (a, b) => f a b) (fun (a, b) (c, d) => h a b c d) z
-/
protected def rec {motive : Sym2 α -> Sort*}
    (f : (a b : α) -> motive s(a, b))
    (h : (a b c d : α) -> (h : Rel α (a, b) (c, d)) -> Eq.ndrec (f a b) (Sym2.sound h) = f c d)
    (z : Sym2 α) : motive z :=
  Quot.rec (fun (a, b) => f a b) (fun (a, b) (c, d) => h a b c d) z

/-- Dependent recursion principle for `Sym2`. See `Quot.recOn`. -/
@[elab_as_elim]
/--
Definition of `recOn` / `recOn` 的定义

English:
definition recOn
  signature: {motive : Sym2 α -> Sort*} (z : Sym2 α)
  body: Quot.recOn z (fun (a, b) => f a b) (fun (a, b) (c, d) => h a b c d)

中文:
定义 recOn
  签名: {motive : Sym2 α -> Sort*} (z : Sym2 α)
  定义体: Quot.recOn z (fun (a, b) => f a b) (fun (a, b) (c, d) => h a b c d)
-/
protected def recOn {motive : Sym2 α -> Sort*} (z : Sym2 α)
    (f : (a b : α) -> motive s(a, b))
    (h : (a b c d : α) -> (h : Rel α (a, b) (c, d)) -> Eq.ndrec (f a b) (Sym2.sound h) = f c d) :
    motive z :=
  Quot.recOn z (fun (a, b) => f a b) (fun (a, b) (c, d) => h a b c d)

/-- A dependent recursion principle for `Sym2` that uses heterogeneous equality. -/
@[elab_as_elim]
/--
Definition of `hrec` / `hrec` 的定义

English:
definition hrec
  signature: {motive : Sym2 α -> Sort*}
  body: Quot.hrecOn _ (fun (a, b) => f a b) by
    simp only [rel_iff']
    rintro _ _ (rfl | rfl)
    exacts [HEq.rfl, h _ _]

中文:
定义 hrec
  签名: {motive : Sym2 α -> Sort*}
  定义体: Quot.hrecOn _ (fun (a, b) => f a b) by
    simp only [rel_iff']
    rintro _ _ (rfl | rfl)
    exacts [HEq.rfl, h _ _]
-/
protected def hrec {motive : Sym2 α -> Sort*}
    (f : (a b : α) -> motive s(a, b))
    (h : (a b : α) -> f a b ≍ f b a)
    (z : Sym2 α) : motive z :=
Quot.hrecOn _ (fun (a, b) => f a b) by
    simp only [rel_iff']
    rintro _ _ (rfl | rfl)
    exacts [HEq.rfl, h _ _]

/-- Dependent recursion principal for `Sym2` when the target is a `Subsingleton` type.
See `Quot.recOnSubsingleton`. -/
@[elab_as_elim]
/--
Definition of `recOnSubsingleton` / `recOnSubsingleton` 的定义

English:
abbreviation recOnSubsingleton
  signature: {motive : Sym2 α -> Sort*}
  body: Quot.recOnSubsingleton z fun (a, b) => f a b

中文:
缩写 recOnSubsingleton
  签名: {motive : Sym2 α -> Sort*}
  定义体: Quot.recOnSubsingleton z fun (a, b) => f a b
-/
protected abbrev recOnSubsingleton {motive : Sym2 α -> Sort*}
    [(a b : α) -> Subsingleton (motive s(a, b))]
    (z : Sym2 α) (f : (a b : α) -> motive s(a, b)) : motive z :=
  Quot.recOnSubsingleton z fun (a, b) => f a b

/--
theorem `mk_surjective` / 定理 `mk_surjective`

English:
theorem mk_surjective
  statement: (Sym2.mk (α := α)).uncurry.Surjective
  proof: Quot.mk_surjective

中文:
定理 mk_surjective
  结论: (Sym2.mk (α := α)).uncurry.Surjective
  证明: Quot.mk_surjective

Depends on / 依赖: Quot.mk_surjective, Surjective, mk_surjective, uncurry, uncurry.Surjective
-/
theorem mk_surjective : (Sym2.mk (α := α)).uncurry.Surjective := Quot.mk_surjective

/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {α : Sort _} {f : Sym2 α -> Prop}
  proof: mk_surjective.exists.trans Prod.exists

中文:
定理 «exists»
  条件: {α : Sort _} {f : Sym2 α -> 命题}
  证明: mk_surjective.exists.trans Prod.exists
-/
protected theorem «exists» {α : Sort _} {f : Sym2 α -> Prop} :
    (exists x : Sym2 α, f x) ↔ exists x y, f s(x, y) :=
  mk_surjective.exists.trans Prod.exists

/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {α : Sort _} {f : Sym2 α -> Prop}
  proof: mk_surjective.forall.trans Prod.forall

中文:
定理 «forall»
  条件: {α : Sort _} {f : Sym2 α -> 命题}
  证明: mk_surjective.forall.trans Prod.forall
-/
protected theorem «forall» {α : Sort _} {f : Sym2 α -> Prop} :
    (forall x : Sym2 α, f x) ↔ forall x y, f s(x, y) :=
  mk_surjective.forall.trans Prod.forall

/--
theorem `eq_swap` / 定理 `eq_swap`

English:
theorem eq_swap
  given: {a b : α}
  statement: s(a, b) = s(b, a)
  proof: Quot.sound (Rel.swap _ _)

@[deprecated (since := "2026-02-05")] alias mk_prod_swap_eq := eq_swap

中文:
定理 eq_swap
  条件: {a b : α}
  结论: s(a, b) = s(b, a)
  证明: Quot.sound (Rel.swap _ _)

@[deprecated (since := "2026-02-05")] alias mk_prod_swap_eq := eq_swap

Depends on / 依赖: Quot.sound, Rel.swap
-/
theorem eq_swap {a b : α} : s(a, b) = s(b, a) := Quot.sound (Rel.swap _ _)

@[deprecated (since := "2026-02-05")] alias mk_prod_swap_eq := eq_swap

/--
theorem `congr_right` / 定理 `congr_right`

English:
theorem congr_right
  given: {a b c : α}
  statement: s(a, b) = s(a, c) ↔ b = c
  proof: by
  simp +contextual

中文:
定理 congr_right
  条件: {a b c : α}
  结论: s(a, b) = s(a, c) ↔ b = c
  证明: by
  simp +contextual

Depends on / 依赖: contextual
-/
theorem congr_right {a b c : α} : s(a, b) = s(a, c) ↔ b = c := by
  simp +contextual

/--
theorem `congr_left` / 定理 `congr_left`

English:
theorem congr_left
  given: {a b c : α}
  statement: s(b, a) = s(c, a) ↔ b = c
  proof: by
  simp +contextual

中文:
定理 congr_left
  条件: {a b c : α}
  结论: s(b, a) = s(c, a) ↔ b = c
  证明: by
  simp +contextual

Depends on / 依赖: contextual
-/
theorem congr_left {a b c : α} : s(b, a) = s(c, a) ↔ b = c := by
  simp +contextual

/--
theorem `eq_iff` / 定理 `eq_iff`

English:
theorem eq_iff
  given: {x y z w : α}
  statement: s(x, y) = s(z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z
  proof: by
  simp

中文:
定理 eq_iff
  条件: {x y z w : α}
  结论: s(x, y) = s(z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z
  证明: by
  simp
-/
theorem eq_iff {x y z w : α} : s(x, y) = s(z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp

/--
theorem `mk_eq_mk_iff` / 定理 `mk_eq_mk_iff`

English:
theorem mk_eq_mk_iff
  given: {p q : α × α}
  statement: s(p.1, p.2) = s(q.1, q.2) ↔ p = q ∨ p = q.swap
  proof: by
  simp

中文:
定理 mk_eq_mk_iff
  条件: {p q : α × α}
  结论: s(p.1, p.2) = s(q.1, q.2) ↔ p = q ∨ p = q.swap
  证明: by
  simp
-/
theorem mk_eq_mk_iff {p q : α × α} : s(p.1, p.2) = s(q.1, q.2) ↔ p = q ∨ p = q.swap := by
  simp

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : { f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁ } ≃ (Sym2 α -> β) where
  body: Quot.lift (uncurry ↑f) by
      rintro _ _ ⟨⟩
      exacts [rfl, f.prop _ _]
  invFun F := ⟨fun a b => F s(a, b), fun _ _ => congr_arg F eq_swap⟩
right_inv _ := funext Sym2.ind fun _ _ => rfl

@[simp]

中文:
定义 lift
  签名: : { f : α -> α -> β // 对任意 a₁ a₂, f a₁ a₂ = f a₂ a₁ } ≃ (Sym2 α -> β) where
  定义体: Quot.lift (uncurry ↑f) by
      rintro _ _ ⟨⟩
      exacts [rfl, f.prop _ _]
  invFun F := ⟨fun a b => F s(a, b), fun _ _ => congr_arg F eq_swap⟩
right_inv _ := funext Sym2.ind fun _ _ => rfl

@[simp]

Depends on / 依赖: Quot.lift, Sym2.ind, congr_arg, eq_swap, exacts, f.prop, invFun, right_inv, uncurry
-/
def lift : { f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁ } ≃ (Sym2 α -> β) where
  toFun f :=
Quot.lift (uncurry ↑f) by
      rintro _ _ ⟨⟩
      exacts [rfl, f.prop _ _]
  invFun F := ⟨fun a b => F s(a, b), fun _ _ => congr_arg F eq_swap⟩
right_inv _ := funext Sym2.ind fun _ _ => rfl

@[simp]
/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  given: (f : { f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁ }) (a b : α)
  proof: rfl

@[simp]

中文:
定理 lift_mk
  条件: (f : { f : α -> α -> β // 对任意 a₁ a₂, f a₁ a₂ = f a₂ a₁ }) (a b : α)
  证明: rfl

@[simp]
-/
theorem lift_mk (f : { f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁ }) (a b : α) :
    lift f s(a, b) = (f : α -> α -> β) a b :=
  rfl

@[simp]
/--
theorem `coe_lift_symm_apply` / 定理 `coe_lift_symm_apply`

English:
theorem coe_lift_symm_apply
  given: (F : Sym2 α -> β) (a₁ a₂ : α)
  proof: rfl

中文:
定理 coe_lift_symm_apply
  条件: (F : Sym2 α -> β) (a₁ a₂ : α)
  证明: rfl
-/
theorem coe_lift_symm_apply (F : Sym2 α -> β) (a₁ a₂ : α) :
    (lift.symm F : α -> α -> β) a₁ a₂ = F s(a₁, a₂) :=
  rfl

/--
Definition of `lift₂` / `lift₂` 的定义

English:
definition lift₂
  signature: :
  body: Quotient.lift₂ (s₁ := Sym2.Rel.setoid α) (s₂ := Sym2.Rel.setoid β)
      (fun (a : α × α) (b : β × β) => f.1 a.1 a.2 b.1 b.2)
      (by
        rintro _ _ _ _ ⟨⟩ ⟨⟩
        exacts [rfl, (f.2 _ _ _ _).2, (f.2 _ _ _ _).1, (f.2 _ _ _ _).1.trans (f.2 _ _ _ _).2])
  invFun F :=
    ⟨fun a₁ a₂ b₁ b₂ => F 

中文:
定义 lift₂
  签名: :
  定义体: Quotient.lift₂ (s₁ := Sym2.Rel.setoid α) (s₂ := Sym2.Rel.setoid β)
      (fun (a : α × α) (b : β × β) => f.1 a.1 a.2 b.1 b.2)
      (by
        rintro _ _ _ _ ⟨⟩ ⟨⟩
        exacts [rfl, (f.2 _ _ _ _).2, (f.2 _ _ _ _).1, (f.2 _ _ _ _).1.trans (f.2 _ _ _ _).2])
  invFun F :=
    ⟨fun a₁ a₂ b₁ b₂ => F 

Depends on / 依赖: Quotient, Quotient.lift, Sym2.Rel.setoid, Sym2.inductionOn, eq_swap, exacts, invFun, right_inv, setoid
-/
def lift₂ :
    { f : α -> α -> β -> β -> γ //
        forall a₁ a₂ b₁ b₂, f a₁ a₂ b₁ b₂ = f a₂ a₁ b₁ b₂ ∧ f a₁ a₂ b₁ b₂ = f a₁ a₂ b₂ b₁ } ≃
      (Sym2 α -> Sym2 β -> γ) where
  toFun f :=
    Quotient.lift₂ (s₁ := Sym2.Rel.setoid α) (s₂ := Sym2.Rel.setoid β)
      (fun (a : α × α) (b : β × β) => f.1 a.1 a.2 b.1 b.2)
      (by
        rintro _ _ _ _ ⟨⟩ ⟨⟩
        exacts [rfl, (f.2 _ _ _ _).2, (f.2 _ _ _ _).1, (f.2 _ _ _ _).1.trans (f.2 _ _ _ _).2])
  invFun F :=
    ⟨fun a₁ a₂ b₁ b₂ => F s(a₁, a₂) s(b₁, b₂), fun a₁ a₂ b₁ b₂ => by
      constructor
      exacts [congr_arg₂ F eq_swap rfl, congr_arg₂ F rfl eq_swap]⟩
  right_inv _ := funext₂ fun a b => Sym2.inductionOn₂ a b fun _ _ _ _ => rfl

@[simp]
/--
theorem `lift₂_mk` / 定理 `lift₂_mk`

English:
theorem lift₂_mk
  proof: rfl

@[simp]

中文:
定理 lift₂_mk
  证明: rfl

@[simp]
-/
theorem lift₂_mk
    (f :
    { f : α -> α -> β -> β -> γ //
      forall a₁ a₂ b₁ b₂, f a₁ a₂ b₁ b₂ = f a₂ a₁ b₁ b₂ ∧ f a₁ a₂ b₁ b₂ = f a₁ a₂ b₂ b₁ })
    (a₁ a₂ : α) (b₁ b₂ : β) : lift₂ f s(a₁, a₂) s(b₁, b₂) = (f : α -> α -> β -> β -> γ) a₁ a₂ b₁ b₂ :=
  rfl

@[simp]
/--
theorem `coe_lift₂_symm_apply` / 定理 `coe_lift₂_symm_apply`

English:
theorem coe_lift₂_symm_apply
  given: (F : Sym2 α -> Sym2 β -> γ) (a₁ a₂ : α) (b₁ b₂ : β)
  proof: rfl

中文:
定理 coe_lift₂_symm_apply
  条件: (F : Sym2 α -> Sym2 β -> γ) (a₁ a₂ : α) (b₁ b₂ : β)
  证明: rfl
-/
theorem coe_lift₂_symm_apply (F : Sym2 α -> Sym2 β -> γ) (a₁ a₂ : α) (b₁ b₂ : β) :
    (lift₂.symm F : α -> α -> β -> β -> γ) a₁ a₂ b₁ b₂ = F s(a₁, a₂) s(b₁, b₂) :=
  rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)
  body: Quot.map (Prod.map f f)
    (by intro _ _ h; cases h <;> constructor)

@[simp]

中文:
定义 map
  签名: (f : α -> β)
  定义体: Quot.map (Prod.map f f)
    (by intro _ _ h; cases h <;> constructor)

@[simp]

Depends on / 依赖: Prod.map, Quot.map
-/
def map (f : α -> β) : Sym2 α -> Sym2 β :=
  Quot.map (Prod.map f f)
    (by intro _ _ h; cases h <;> constructor)

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (@id α) = id
  proof: by
  ext ⟨⟨x, y⟩⟩
  rfl

中文:
定理 map_id
  结论: map (@id α) = id
  证明: by
  ext ⟨⟨x, y⟩⟩
  rfl
-/
theorem map_id : map (@id α) = id := by
  ext ⟨⟨x, y⟩⟩
  rfl

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: {g : β -> γ} {f : α -> β}
  statement: Sym2.map (g ∘ f) = Sym2.map g ∘ Sym2.map f
  proof: by
  ext ⟨⟨x, y⟩⟩
  rfl

中文:
定理 map_comp
  条件: {g : β -> γ} {f : α -> β}
  结论: Sym2.map (g ∘ f) = Sym2.map g ∘ Sym2.map f
  证明: by
  ext ⟨⟨x, y⟩⟩
  rfl
-/
theorem map_comp {g : β -> γ} {f : α -> β} : Sym2.map (g ∘ f) = Sym2.map g ∘ Sym2.map f := by
  ext ⟨⟨x, y⟩⟩
  rfl

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: {g : β -> γ} {f : α -> β} (x : Sym2 α)
  statement: map g (map f x) = map (g ∘ f) x
  proof: by
  induction x; aesop

@[simp]

中文:
定理 map_map
  条件: {g : β -> γ} {f : α -> β} (x : Sym2 α)
  结论: map g (map f x) = map (g ∘ f) x
  证明: by
  induction x; aesop

@[simp]
-/
theorem map_map {g : β -> γ} {f : α -> β} (x : Sym2 α) : map g (map f x) = map (g ∘ f) x := by
  induction x; aesop

@[simp]
/--
theorem `map_mk` / 定理 `map_mk`

English:
theorem map_mk
  given: (f : α -> β) (a b : α)
  statement: map f s(a, b) = s(f a, f b)
  proof: rfl

@[deprecated (since := "2026-02-05")] alias map_pair_eq := map_mk

中文:
定理 map_mk
  条件: (f : α -> β) (a b : α)
  结论: map f s(a, b) = s(f a, f b)
  证明: rfl

@[deprecated (since := "2026-02-05")] alias map_pair_eq := map_mk
-/
theorem map_mk (f : α -> β) (a b : α) : map f s(a, b) = s(f a, f b) := rfl

@[deprecated (since := "2026-02-05")] alias map_pair_eq := map_mk

/--
theorem `map.injective` / 定理 `map.injective`

English:
theorem map.injective
  given: {f : α -> β} (hinj : Injective f)
  statement: Injective (map f)
  proof: by
  intro z z'
  refine Sym2.inductionOn₂ z z' (fun x y x' y' => ?_)
  simp [hinj.eq_iff]

中文:
定理 map.injective
  条件: {f : α -> β} (hinj : Injective f)
  结论: Injective (map f)
  证明: by
  intro z z'
  refine Sym2.inductionOn₂ z z' (fun x y x' y' => ?_)
  simp [hinj.eq_iff]

Depends on / 依赖: Sym2.inductionOn, eq_iff, hinj.eq_iff
-/
theorem map.injective {f : α -> β} (hinj : Injective f) : Injective (map f) := by
  intro z z'
  refine Sym2.inductionOn₂ z z' (fun x y x' y' => ?_)
  simp [hinj.eq_iff]

/-- `mk a` as an embedding. This is the symmetric version of `Function.Embedding.sectL`. -/
@[simps]
/--
Definition of `mkEmbedding` / `mkEmbedding` 的定义

English:
definition mkEmbedding
  signature: (a : α)
  body: s(a, b)
  inj' b₁ b₁ h := by
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk] at h
    obtain rfl | ⟨rfl, rfl⟩ := h <;> rfl

中文:
定义 mkEmbedding
  签名: (a : α)
  定义体: s(a, b)
  inj' b₁ b₁ h := by
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk] at h
    obtain rfl | ⟨rfl, rfl⟩ := h <;> rfl
-/
def mkEmbedding (a : α) : α ↪ Sym2 α where
  toFun b := s(a, b)
  inj' b₁ b₁ h := by
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk] at h
    obtain rfl | ⟨rfl, rfl⟩ := h <;> rfl

/-- `Sym2.map` as an embedding. -/
@[simps]
/--
Definition of `_root_.Function.Embedding.sym2Map` / `_root_.Function.Embedding.sym2Map` 的定义

English:
definition _root_.Function.Embedding.sym2Map
  signature: (f : α ↪ β)
  body: map f
  inj' := map.injective f.injective

中文:
定义 _root_.Function.Embedding.sym2Map
  签名: (f : α ↪ β)
  定义体: map f
  inj' := map.injective f.injective
-/
def _root_.Function.Embedding.sym2Map (f : α ↪ β) : Sym2 α ↪ Sym2 β where
  toFun := map f
  inj' := map.injective f.injective

/--
lemma `lift_comp_map` / 引理 `lift_comp_map`

English:
lemma lift_comp_map
  given: {g : γ -> α} (f : {f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁})
  proof: lift.symm_apply_eq.mp rfl

中文:
引理 lift_comp_map
  条件: {g : γ -> α} (f : {f : α -> α -> β // 对任意 a₁ a₂, f a₁ a₂ = f a₂ a₁})
  证明: lift.symm_apply_eq.mp rfl

Depends on / 依赖: lift.symm_apply_eq.mp, symm_apply_eq
-/
lemma lift_comp_map {g : γ -> α} (f : {f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁}) :
    lift f ∘ map g = lift ⟨fun (c₁ c₂ : γ) => f.val (g c₁) (g c₂), fun _ _ => f.prop _ _⟩ :=
  lift.symm_apply_eq.mp rfl

/--
lemma `lift_map_apply` / 引理 `lift_map_apply`

English:
lemma lift_map_apply
  given: {g : γ -> α} (f : {f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁}) (p : Sym2 γ)
  proof: by
  conv_rhs => rw [← lift_comp_map, comp_apply]

中文:
引理 lift_map_apply
  条件: {g : γ -> α} (f : {f : α -> α -> β // 对任意 a₁ a₂, f a₁ a₂ = f a₂ a₁}) (p : Sym2 γ)
  证明: by
  conv_rhs => rw [← lift_comp_map, comp_apply]

Depends on / 依赖: comp_apply, conv_rhs, lift_comp_map
-/
lemma lift_map_apply {g : γ -> α} (f : {f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁}) (p : Sym2 γ) :
    lift f (map g p) = lift ⟨fun (c₁ c₂ : γ) => f.val (g c₁) (g c₂), fun _ _ => f.prop _ _⟩ p := by
  conv_rhs => rw [← lift_comp_map, comp_apply]

section Membership

/-! ### Membership and set coercion -/


/--
Definition of `Mem` / `Mem` 的定义

English:
definition Mem
  signature: (x : α) (z : Sym2 α)
  body: exists y : α, z = s(x, y)

@[aesop norm (rule_sets := [Sym2])]

中文:
定义 Mem
  签名: (x : α) (z : Sym2 α)
  定义体: exists y : α, z = s(x, y)

@[aesop norm (rule_sets := [Sym2])]
-/
protected def Mem (x : α) (z : Sym2 α) : Prop :=
  exists y : α, z = s(x, y)

@[aesop norm (rule_sets := [Sym2])]
/--
theorem `mem_iff'` / 定理 `mem_iff'`

English:
theorem mem_iff'
  given: {a b c : α}
  statement: Sym2.Mem a s(b, c) ↔ a = b ∨ a = c
  proof: { mp := by
      rintro ⟨_, h⟩
      rw [eq_iff] at h
      aesop
    mpr := by
      rintro (rfl | rfl)
      · exact ⟨_, rfl⟩
      rw [eq_swap]
      exact ⟨_, rfl⟩ }

中文:
定理 mem_iff'
  条件: {a b c : α}
  结论: Sym2.Mem a s(b, c) ↔ a = b ∨ a = c
  证明: { mp := by
      rintro ⟨_, h⟩
      rw [eq_iff] at h
      aesop
    mpr := by
      rintro (rfl | rfl)
      · exact ⟨_, rfl⟩
      rw [eq_swap]
      exact ⟨_, rfl⟩ }

Depends on / 依赖: eq_iff, eq_swap
-/
theorem mem_iff' {a b c : α} : Sym2.Mem a s(b, c) ↔ a = b ∨ a = c :=
  { mp := by
      rintro ⟨_, h⟩
      rw [eq_iff] at h
      aesop
    mpr := by
      rintro (rfl | rfl)
      · exact ⟨_, rfl⟩
      rw [eq_swap]
      exact ⟨_, rfl⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Sym2 α) α
  body: { x | z.Mem x }
  coe_injective z z' h := by
    simp only [Set.ext_iff, Set.mem_ofPred_eq] at h
    obtain ⟨x, y⟩ := z
    obtain ⟨x', y'⟩ := z'
    have hx := h x; have hy := h y; have hx' := h x'; have hy' := h y'
    simp only [mem_iff'] at hx hy hx' hy'
    aesop

中文:
实例 :
  签名: SetLike (Sym2 α) α
  定义体: { x | z.Mem x }
  coe_injective z z' h := by
    simp only [Set.ext_iff, Set.mem_ofPred_eq] at h
    obtain ⟨x, y⟩ := z
    obtain ⟨x', y'⟩ := z'
    have hx := h x; have hy := h y; have hx' := h x'; have hy' := h y'
    simp only [mem_iff'] at hx hy hx' hy'
    aesop

Depends on / 依赖: z.Mem
-/
instance : SetLike (Sym2 α) α where
  coe z := { x | z.Mem x }
  coe_injective z z' h := by
    simp only [Set.ext_iff, Set.mem_ofPred_eq] at h
    obtain ⟨x, y⟩ := z
    obtain ⟨x', y'⟩ := z'
    have hx := h x; have hy := h y; have hx' := h x'; have hy' := h y'
    simp only [mem_iff'] at hx hy hx' hy'
    aesop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Sym2 α)
  body: .ofSetLike (Sym2 α) α

@[simp]

中文:
实例 :
  签名: PartialOrder (Sym2 α)
  定义体: .ofSetLike (Sym2 α) α

@[simp]

Depends on / 依赖: ofSetLike
-/
instance : PartialOrder (Sym2 α) := .ofSetLike (Sym2 α) α

@[simp]
/--
theorem `mem_iff_mem` / 定理 `mem_iff_mem`

English:
theorem mem_iff_mem
  given: {x : α} {z : Sym2 α}
  statement: Sym2.Mem x z ↔ x in z
  proof: Iff.rfl

中文:
定理 mem_iff_mem
  条件: {x : α} {z : Sym2 α}
  结论: Sym2.Mem x z ↔ x in z
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_iff_mem {x : α} {z : Sym2 α} : Sym2.Mem x z ↔ x in z :=
  Iff.rfl

/--
theorem `mem_iff_exists` / 定理 `mem_iff_exists`

English:
theorem mem_iff_exists
  given: {x : α} {z : Sym2 α}
  statement: x in z ↔ exists y : α, z = s(x, y)
  proof: Iff.rfl

@[ext]

中文:
定理 mem_iff_exists
  条件: {x : α} {z : Sym2 α}
  结论: x in z ↔ 存在 y : α, z = s(x, y)
  证明: Iff.rfl

@[ext]

Depends on / 依赖: Iff.rfl
-/
theorem mem_iff_exists {x : α} {z : Sym2 α} : x in z ↔ exists y : α, z = s(x, y) :=
  Iff.rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {p q : Sym2 α} (h : forall x, x in p ↔ x in q)
  statement: p = q
  proof: SetLike.ext h

中文:
定理 ext
  条件: {p q : Sym2 α} (h : 对任意 x, x in p ↔ x in q)
  结论: p = q
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {p q : Sym2 α} (h : forall x, x in p ↔ x in q) : p = q :=
  SetLike.ext h

/--
theorem `mem_mk_left` / 定理 `mem_mk_left`

English:
theorem mem_mk_left
  given: (x y : α)
  statement: x in s(x, y)
  proof: ⟨y, rfl⟩

中文:
定理 mem_mk_left
  条件: (x y : α)
  结论: x in s(x, y)
  证明: ⟨y, rfl⟩
-/
theorem mem_mk_left (x y : α) : x in s(x, y) :=
  ⟨y, rfl⟩

/--
theorem `mem_mk_right` / 定理 `mem_mk_right`

English:
theorem mem_mk_right
  given: (x y : α)
  statement: y in s(x, y)
  proof: eq_swap ▸ mem_mk_left y x

@[simp, aesop norm (rule_sets := [Sym2]), grind =]

中文:
定理 mem_mk_right
  条件: (x y : α)
  结论: y in s(x, y)
  证明: eq_swap ▸ mem_mk_left y x

@[simp, aesop norm (rule_sets := [Sym2]), grind =]

Depends on / 依赖: eq_swap, mem_mk_left
-/
theorem mem_mk_right (x y : α) : y in s(x, y) :=
  eq_swap ▸ mem_mk_left y x

@[simp, aesop norm (rule_sets := [Sym2]), grind =]
/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: {a b c : α}
  statement: a in s(b, c) ↔ a = b ∨ a = c
  proof: mem_iff'

中文:
定理 mem_iff
  条件: {a b c : α}
  结论: a in s(b, c) ↔ a = b ∨ a = c
  证明: mem_iff'

Depends on / 依赖: mem_iff
-/
theorem mem_iff {a b c : α} : a in s(b, c) ↔ a = b ∨ a = c :=
  mem_iff'

/--
theorem `out_fst_mem` / 定理 `out_fst_mem`

English:
theorem out_fst_mem
  given: (e : Sym2 α)
  statement: e.out.1 in e
  proof: ⟨e.out.2, by rw [Sym2.mk, e.out_eq]⟩

中文:
定理 out_fst_mem
  条件: (e : Sym2 α)
  结论: e.out.1 in e
  证明: ⟨e.out.2, by rw [Sym2.mk, e.out_eq]⟩

Depends on / 依赖: Sym2.mk, e.out, e.out_eq, out_eq
-/
theorem out_fst_mem (e : Sym2 α) : e.out.1 in e :=
  ⟨e.out.2, by rw [Sym2.mk, e.out_eq]⟩

/--
theorem `out_snd_mem` / 定理 `out_snd_mem`

English:
theorem out_snd_mem
  given: (e : Sym2 α)
  statement: e.out.2 in e
  proof: ⟨e.out.1, by rw [eq_swap, Sym2.mk, e.out_eq]⟩

中文:
定理 out_snd_mem
  条件: (e : Sym2 α)
  结论: e.out.2 in e
  证明: ⟨e.out.1, by rw [eq_swap, Sym2.mk, e.out_eq]⟩

Depends on / 依赖: Sym2.mk, e.out, e.out_eq, eq_swap, out_eq
-/
theorem out_snd_mem (e : Sym2 α) : e.out.2 in e :=
  ⟨e.out.1, by rw [eq_swap, Sym2.mk, e.out_eq]⟩

/--
theorem `ball` / 定理 `ball`

English:
theorem ball
  given: {p : α -> Prop} {a b : α}
  statement: (forall c in s(a, b), p c) ↔ p a ∧ p b
  proof: by
  simp

中文:
定理 ball
  条件: {p : α -> 命题} {a b : α}
  结论: (对任意 c in s(a, b), p c) ↔ p a ∧ p b
  证明: by
  simp
-/
theorem ball {p : α -> Prop} {a b : α} : (forall c in s(a, b), p c) ↔ p a ∧ p b := by
  simp

/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: {x y : α}
  statement: (s(x, y) : Set α) = {x, y}
  proof: by ext z; simp

中文:
引理 coe_mk
  条件: {x y : α}
  结论: (s(x, y) : Set α) = {x, y}
  证明: by ext z; simp
-/
@[simp] lemma coe_mk {x y : α} : (s(x, y) : Set α) = {x, y} := by ext z; simp

/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (f : α -> β) (z : Sym2 α)
  statement: z.map f = f '' z
  proof: by
  cases z
  simp [Set.image_pair]

中文:
定理 coe_map
  条件: (f : α -> β) (z : Sym2 α)
  结论: z.map f = f '' z
  证明: by
  cases z
  simp [Set.image_pair]

Depends on / 依赖: Set.image_pair, image_pair
-/
theorem coe_map (f : α -> β) (z : Sym2 α) : z.map f = f '' z := by
  cases z
  simp [Set.image_pair]

/--
Definition of `Mem.other` / `Mem.other` 的定义

English:
definition Mem.other
  signature: {a : α} {z : Sym2 α} (h : a in z)
  body: Classical.choose h

@[simp]

中文:
定义 Mem.other
  签名: {a : α} {z : Sym2 α} (h : a in z)
  定义体: Classical.choose h

@[simp]

Depends on / 依赖: Classical, Classical.choose
-/
noncomputable def Mem.other {a : α} {z : Sym2 α} (h : a in z) : α :=
  Classical.choose h

@[simp]
/--
theorem `other_spec` / 定理 `other_spec`

English:
theorem other_spec
  given: {a : α} {z : Sym2 α} (h : a in z)
  statement: s(a, Mem.other h) = z
  proof: (Classical.choose_spec h).symm

中文:
定理 other_spec
  条件: {a : α} {z : Sym2 α} (h : a in z)
  结论: s(a, Mem.other h) = z
  证明: (Classical.choose_spec h).symm

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
theorem other_spec {a : α} {z : Sym2 α} (h : a in z) : s(a, Mem.other h) = z :=
  (Classical.choose_spec h).symm

/--
theorem `other_mem` / 定理 `other_mem`

English:
theorem other_mem
  given: {a : α} {z : Sym2 α} (h : a in z)
  statement: Mem.other h in z
  proof: by
convert! mem_mk_right a Mem.other h
  rw [other_spec h]

中文:
定理 other_mem
  条件: {a : α} {z : Sym2 α} (h : a in z)
  结论: Mem.other h in z
  证明: by
convert! mem_mk_right a Mem.other h
  rw [other_spec h]

Depends on / 依赖: Mem.other, convert, mem_mk_right, other_spec
-/
theorem other_mem {a : α} {z : Sym2 α} (h : a in z) : Mem.other h in z := by
convert! mem_mk_right a Mem.other h
  rw [other_spec h]

/--
theorem `mem_and_mem_iff` / 定理 `mem_and_mem_iff`

English:
theorem mem_and_mem_iff
  given: {x y : α} {z : Sym2 α} (hne : x != y)
  statement: x in z ∧ y in z ↔ z = s(x, y)
  proof: by
  constructor
  · cases z
    rw [mem_iff]; rw [mem_iff]
    aesop
  · rintro rfl
    simp

中文:
定理 mem_and_mem_iff
  条件: {x y : α} {z : Sym2 α} (hne : x != y)
  结论: x in z ∧ y in z ↔ z = s(x, y)
  证明: by
  constructor
  · cases z
    rw [mem_iff]; rw [mem_iff]
    aesop
  · rintro rfl
    simp

Depends on / 依赖: mem_iff
-/
theorem mem_and_mem_iff {x y : α} {z : Sym2 α} (hne : x != y) : x in z ∧ y in z ↔ z = s(x, y) := by
  constructor
  · cases z
    rw [mem_iff]; rw [mem_iff]
    aesop
  · rintro rfl
    simp

/--
theorem `eq_of_ne_mem` / 定理 `eq_of_ne_mem`

English:
theorem eq_of_ne_mem
  statement: {x y : α} {z z' : Sym2 α} (h : x != y) (h1 : x in z) (h2 : y in z) (h3 : x in z')
  proof: ((mem_and_mem_iff h).mp ⟨h1, h2⟩).trans ((mem_and_mem_iff h).mp ⟨h3, h4⟩).symm

中文:
定理 eq_of_ne_mem
  结论: {x y : α} {z z' : Sym2 α} (h : x != y) (h1 : x in z) (h2 : y in z) (h3 : x in z')
  证明: ((mem_and_mem_iff h).mp ⟨h1, h2⟩).trans ((mem_and_mem_iff h).mp ⟨h3, h4⟩).symm

Depends on / 依赖: mem_and_mem_iff
-/
theorem eq_of_ne_mem {x y : α} {z z' : Sym2 α} (h : x != y) (h1 : x in z) (h2 : y in z) (h3 : x in z')
    (h4 : y in z') : z = z' :=
  ((mem_and_mem_iff h).mp ⟨h1, h2⟩).trans ((mem_and_mem_iff h).mp ⟨h3, h4⟩).symm

/--
Instance `Mem.decidable` / 实例 `Mem.decidable`

English:
instance Mem.decidable
  signature: [DecidableEq α] (x : α) (z : Sym2 α)
  body: z.recOnSubsingleton fun _ _ => decidable_of_iff' _ mem_iff

中文:
实例 Mem.decidable
  签名: [DecidableEq α] (x : α) (z : Sym2 α)
  定义体: z.recOnSubsingleton fun _ _ => decidable_of_iff' _ mem_iff

Depends on / 依赖: decidable_of_iff, mem_iff, recOnSubsingleton, z.recOnSubsingleton
-/
instance Mem.decidable [DecidableEq α] (x : α) (z : Sym2 α) : Decidable (x in z) :=
  z.recOnSubsingleton fun _ _ => decidable_of_iff' _ mem_iff

end Membership

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : α -> β} {b : β} {z : Sym2 α}
  statement: b in Sym2.map f z ↔ exists a, a in z ∧ f a = b
  proof: by
  cases z
  aesop

@[congr]

中文:
定理 mem_map
  条件: {f : α -> β} {b : β} {z : Sym2 α}
  结论: b in Sym2.map f z ↔ 存在 a, a in z ∧ f a = b
  证明: by
  cases z
  aesop

@[congr]
-/
theorem mem_map {f : α -> β} {b : β} {z : Sym2 α} : b in Sym2.map f z ↔ exists a, a in z ∧ f a = b := by
  cases z
  aesop

@[congr]
/--
theorem `map_congr` / 定理 `map_congr`

English:
theorem map_congr
  given: {f g : α -> β} {s : Sym2 α} (h : forall x in s, f x = g x)
  statement: map f s = map g s
  proof: by
  ext y
  simp only [mem_map]
  constructor <;>
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [hw, h]⟩

中文:
定理 map_congr
  条件: {f g : α -> β} {s : Sym2 α} (h : 对任意 x in s, f x = g x)
  结论: map f s = map g s
  证明: by
  ext y
  simp only [mem_map]
  constructor <;>
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [hw, h]⟩

Depends on / 依赖: mem_map
-/
theorem map_congr {f g : α -> β} {s : Sym2 α} (h : forall x in s, f x = g x) : map f s = map g s := by
  ext y
  simp only [mem_map]
  constructor <;>
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [hw, h]⟩

/-- Note: `Sym2.map_id` will not simplify `Sym2.map id z` due to `Sym2.map_congr`. -/
@[simp]
/--
theorem `map_id'` / 定理 `map_id'`

English:
theorem map_id'
  statement: (map fun x : α => x) = id
  proof: map_id

中文:
定理 map_id'
  结论: (map fun x : α => x) = id
  证明: map_id

Depends on / 依赖: map_id
-/
theorem map_id' : (map fun x : α => x) = id :=
  map_id

/--
Definition of `pmap` / `pmap` 的定义

English:
definition pmap
  signature: {P : α -> Prop} (f : forall a, P a -> β) (s : Sym2 α)
  body: let g (p : α × α) (H : forall a in Sym2.mk p.1 p.2, P a) : Sym2 β :=
    s(f p.1 (H p.1 <| mem_mk_left _ _), f p.2 (H p.2 <| mem_mk_right _ _))
  Quot.recOn s g fun p q hpq => funext fun Hq => by
    rw [rel_iff'] at hpq
    have Hp : forall a in s(p.1, p.2), P a := fun a hmem =>
      Hq a (Sym2.mk

中文:
定义 pmap
  签名: {P : α -> 命题} (f : 对任意 a, P a -> β) (s : Sym2 α)
  定义体: let g (p : α × α) (H : forall a in Sym2.mk p.1 p.2, P a) : Sym2 β :=
    s(f p.1 (H p.1 <| mem_mk_left _ _), f p.2 (H p.2 <| mem_mk_right _ _))
  Quot.recOn s g fun p q hpq => funext fun Hq => by
    rw [rel_iff'] at hpq
    have Hp : forall a in s(p.1, p.2), P a := fun a hmem =>
      Hq a (Sym2.mk

Depends on / 依赖: Eq.ndrec, Quot.recOn, Quot.sound, Sym2.mk, Sym2.mk_eq_mk_iff, h.trans, mem_mk_left, mem_mk_right, mk_eq_mk_iff, motive, rel_iff
-/
def pmap {P : α -> Prop} (f : forall a, P a -> β) (s : Sym2 α) : (forall a in s, P a) -> Sym2 β :=
  let g (p : α × α) (H : forall a in Sym2.mk p.1 p.2, P a) : Sym2 β :=
    s(f p.1 (H p.1 <| mem_mk_left _ _), f p.2 (H p.2 <| mem_mk_right _ _))
  Quot.recOn s g fun p q hpq => funext fun Hq => by
    rw [rel_iff'] at hpq
    have Hp : forall a in s(p.1, p.2), P a := fun a hmem =>
      Hq a (Sym2.mk_eq_mk_iff.2 hpq ▸ hmem : a in s(q.1, q.2))
    have h : forall {s₂ e H}, Eq.ndrec (motive := fun s => (forall a in s, P a) -> Sym2 β) (g p) (b := s₂) e H =
      g p Hp := by
      rintro s₂ rfl _
      rfl
    refine h.trans (Quot.sound ?_)
    rw [rel_iff']; rw [Prod.mk.injEq]; rw [Prod.swap_prod_mk]
    apply hpq.imp <;> rintro rfl <;> simp

/--
theorem `forall_mem_pair` / 定理 `forall_mem_pair`

English:
theorem forall_mem_pair
  given: {P : α -> Prop} {a b : α}
  statement: (forall x in s(a, b), P x) ↔ P a ∧ P b
  proof: by
  simp only [mem_iff, forall_eq_or_imp, forall_eq]

中文:
定理 forall_mem_pair
  条件: {P : α -> 命题} {a b : α}
  结论: (对任意 x in s(a, b), P x) ↔ P a ∧ P b
  证明: by
  simp only [mem_iff, forall_eq_or_imp, forall_eq]

Depends on / 依赖: forall_eq, forall_eq_or_imp, mem_iff
-/
theorem forall_mem_pair {P : α -> Prop} {a b : α} : (forall x in s(a, b), P x) ↔ P a ∧ P b := by
  simp only [mem_iff, forall_eq_or_imp, forall_eq]

/--
lemma `pair_eq_pmap` / 引理 `pair_eq_pmap`

English:
lemma pair_eq_pmap
  given: {P : α -> Prop} (f : forall a, P a -> β) (a b : α) (h : P a) (h' : P b)
  proof: rfl

中文:
引理 pair_eq_pmap
  条件: {P : α -> 命题} (f : 对任意 a, P a -> β) (a b : α) (h : P a) (h' : P b)
  证明: rfl
-/
lemma pair_eq_pmap {P : α -> Prop} (f : forall a, P a -> β) (a b : α) (h : P a) (h' : P b) :
    s(f a h, f b h') = pmap f s(a, b) (forall_mem_pair.mpr ⟨h, h'⟩) := rfl

/--
lemma `pmap_pair` / 引理 `pmap_pair`

English:
lemma pmap_pair
  given: {P : α -> Prop} (f : forall a, P a -> β) (a b : α) (h : forall x in s(a, b), P x)
  proof: rfl

@[simp]

中文:
引理 pmap_pair
  条件: {P : α -> 命题} (f : 对任意 a, P a -> β) (a b : α) (h : 对任意 x in s(a, b), P x)
  证明: rfl

@[simp]
-/
lemma pmap_pair {P : α -> Prop} (f : forall a, P a -> β) (a b : α) (h : forall x in s(a, b), P x) :
    pmap f s(a, b) h = s(f a (h a (mem_mk_left a b)), f b (h b (mem_mk_right a b))) := rfl

@[simp]
/--
lemma `mem_pmap_iff` / 引理 `mem_pmap_iff`

English:
lemma mem_pmap_iff
  given: {P : α -> Prop} (f : forall a, P a -> β) (z : Sym2 α) (h : forall a in z, P a) (b : β)
  proof: by
  obtain ⟨x, y⟩ := z
  rw [pmap_pair f x y h]
  aesop

中文:
引理 mem_pmap_iff
  条件: {P : α -> 命题} (f : 对任意 a, P a -> β) (z : Sym2 α) (h : 对任意 a in z, P a) (b : β)
  证明: by
  obtain ⟨x, y⟩ := z
  rw [pmap_pair f x y h]
  aesop

Depends on / 依赖: pmap_pair
-/
lemma mem_pmap_iff {P : α -> Prop} (f : forall a, P a -> β) (z : Sym2 α) (h : forall a in z, P a) (b : β) :
    b in z.pmap f h ↔ exists (a : α) (ha : a in z), b = f a (h a ha) := by
  obtain ⟨x, y⟩ := z
  rw [pmap_pair f x y h]
  aesop

/--
lemma `pmap_eq_map` / 引理 `pmap_eq_map`

English:
lemma pmap_eq_map
  given: {P : α -> Prop} (f : α -> β) (z : Sym2 α) (h : forall a in z, P a)
  proof: by
  cases z; rfl

中文:
引理 pmap_eq_map
  条件: {P : α -> 命题} (f : α -> β) (z : Sym2 α) (h : 对任意 a in z, P a)
  证明: by
  cases z; rfl
-/
lemma pmap_eq_map {P : α -> Prop} (f : α -> β) (z : Sym2 α) (h : forall a in z, P a) :
    z.pmap (fun a _ => f a) h = z.map f := by
  cases z; rfl

/--
lemma `map_pmap` / 引理 `map_pmap`

English:
lemma map_pmap
  given: {Q : β -> Prop} (f : α -> β) (g : forall b, Q b -> γ) (z : Sym2 α) (h : forall b in z.map f, Q b)
  proof: by
  cases z; rfl

中文:
引理 map_pmap
  条件: {Q : β -> 命题} (f : α -> β) (g : 对任意 b, Q b -> γ) (z : Sym2 α) (h : 对任意 b in z.map f, Q b)
  证明: by
  cases z; rfl
-/
lemma map_pmap {Q : β -> Prop} (f : α -> β) (g : forall b, Q b -> γ) (z : Sym2 α) (h : forall b in z.map f, Q b) :
    (z.map f).pmap g h =
    z.pmap (fun a ha => g (f a) (h (f a) (mem_map.mpr ⟨a, ha, rfl⟩))) (fun _ ha => ha) := by
  cases z; rfl

/--
lemma `pmap_map` / 引理 `pmap_map`

English:
lemma pmap_map
  statement: {P : α -> Prop} {Q : β -> Prop} (f : forall a, P a -> β) (g : β -> γ)
  proof: by
  cases z; rfl

中文:
引理 pmap_map
  结论: {P : α -> 命题} {Q : β -> 命题} (f : 对任意 a, P a -> β) (g : β -> γ)
  证明: by
  cases z; rfl
-/
lemma pmap_map {P : α -> Prop} {Q : β -> Prop} (f : forall a, P a -> β) (g : β -> γ)
    (z : Sym2 α) (h : forall a in z, P a) (h' : forall b in z.pmap f h, Q b) :
    (z.pmap f h).map g = z.pmap (fun a ha => g (f a (h a ha))) (fun _ ha => ha) := by
  cases z; rfl

/--
lemma `pmap_pmap` / 引理 `pmap_pmap`

English:
lemma pmap_pmap
  statement: {P : α -> Prop} {Q : β -> Prop} (f : forall a, P a -> β) (g : forall b, Q b -> γ)
  proof: by
  cases z; rfl

@[simp]

中文:
引理 pmap_pmap
  结论: {P : α -> 命题} {Q : β -> 命题} (f : 对任意 a, P a -> β) (g : 对任意 b, Q b -> γ)
  证明: by
  cases z; rfl

@[simp]
-/
lemma pmap_pmap {P : α -> Prop} {Q : β -> Prop} (f : forall a, P a -> β) (g : forall b, Q b -> γ)
    (z : Sym2 α) (h : forall a in z, P a) (h' : forall b in z.pmap f h, Q b) :
    (z.pmap f h).pmap g h' = z.pmap (fun a ha => g (f a (h a ha))
    (h' _ ((mem_pmap_iff f z h _).mpr ⟨a, ha, rfl⟩))) (fun _ ha => ha) := by
  cases z; rfl

@[simp]
/--
lemma `pmap_subtype_map_subtypeVal` / 引理 `pmap_subtype_map_subtypeVal`

English:
lemma pmap_subtype_map_subtypeVal
  given: {P : α -> Prop} (s : Sym2 α) (h : forall a in s, P a)
  proof: by
  cases s; rfl

中文:
引理 pmap_subtype_map_subtypeVal
  条件: {P : α -> 命题} (s : Sym2 α) (h : 对任意 a in s, P a)
  证明: by
  cases s; rfl
-/
lemma pmap_subtype_map_subtypeVal {P : α -> Prop} (s : Sym2 α) (h : forall a in s, P a) :
    (s.pmap Subtype.mk h).map Subtype.val = s := by
  cases s; rfl

/--
Definition of `attachWith` / `attachWith` 的定义

English:
definition attachWith
  signature: {P : α -> Prop} (s : Sym2 α) (h : forall a in s, P a)
  body: pmap Subtype.mk s h

@[simp]

中文:
定义 attachWith
  签名: {P : α -> 命题} (s : Sym2 α) (h : 对任意 a in s, P a)
  定义体: pmap Subtype.mk s h

@[simp]

Depends on / 依赖: Subtype, Subtype.mk
-/
def attachWith {P : α -> Prop} (s : Sym2 α) (h : forall a in s, P a) : Sym2 {a // P a} :=
  pmap Subtype.mk s h

@[simp]
/--
lemma `attachWith_map_subtypeVal` / 引理 `attachWith_map_subtypeVal`

English:
lemma attachWith_map_subtypeVal
  given: {s : Sym2 α} {P : α -> Prop} (h : forall a in s, P a)
  proof: by
  cases s; rfl

中文:
引理 attachWith_map_subtypeVal
  条件: {s : Sym2 α} {P : α -> 命题} (h : 对任意 a in s, P a)
  证明: by
  cases s; rfl
-/
lemma attachWith_map_subtypeVal {s : Sym2 α} {P : α -> Prop} (h : forall a in s, P a) :
    (s.attachWith h).map Subtype.val = s := by
  cases s; rfl

/-! ### Diagonal -/

variable {z : Sym2 α} {f : α -> β}

/--
Definition of `diag` / `diag` 的定义

English:
definition diag
  signature: (x : α)
  body: s(x, x)

中文:
定义 diag
  签名: (x : α)
  定义体: s(x, x)
-/
def diag (x : α) : Sym2 α := s(x, x)

/--
theorem `diag_injective` / 定理 `diag_injective`

English:
theorem diag_injective
  statement: Function.Injective (Sym2.diag : α -> Sym2 α)
  proof: fun x y h => by
  cases Sym2.exact h <;> rfl

中文:
定理 diag_injective
  结论: Function.Injective (Sym2.diag : α -> Sym2 α)
  证明: fun x y h => by
  cases Sym2.exact h <;> rfl

Depends on / 依赖: Sym2.exact
-/
theorem diag_injective : Function.Injective (Sym2.diag : α -> Sym2 α) := fun x y h => by
  cases Sym2.exact h <;> rfl

/--
Definition of `IsDiag` / `IsDiag` 的定义

English:
definition IsDiag
  signature: : Sym2 α -> Prop
  body: lift ⟨Eq, fun _ _ => propext eq_comm⟩

@[simp]

中文:
定义 IsDiag
  签名: : Sym2 α -> 命题
  定义体: lift ⟨Eq, fun _ _ => propext eq_comm⟩

@[simp]

Depends on / 依赖: eq_comm, propext
-/
def IsDiag : Sym2 α -> Prop :=
  lift ⟨Eq, fun _ _ => propext eq_comm⟩

@[simp]
/--
theorem `mk_isDiag_iff` / 定理 `mk_isDiag_iff`

English:
theorem mk_isDiag_iff
  given: {x y : α}
  statement: IsDiag s(x, y) ↔ x = y
  proof: Iff.rfl

@[deprecated (since := "2026-02-05")] alias isDiag_iff_proj_eq := mk_isDiag_iff

中文:
定理 mk_isDiag_iff
  条件: {x y : α}
  结论: IsDiag s(x, y) ↔ x = y
  证明: Iff.rfl

@[deprecated (since := "2026-02-05")] alias isDiag_iff_proj_eq := mk_isDiag_iff

Depends on / 依赖: Iff.rfl
-/
theorem mk_isDiag_iff {x y : α} : IsDiag s(x, y) ↔ x = y :=
  Iff.rfl

@[deprecated (since := "2026-02-05")] alias isDiag_iff_proj_eq := mk_isDiag_iff

/--
lemma `IsDiag.map` / 引理 `IsDiag.map`

English:
lemma IsDiag.map
  statement: z.IsDiag -> (z.map f).IsDiag
  proof: Sym2.ind (fun _ _ => congr_arg f) z

中文:
引理 IsDiag.map
  结论: z.IsDiag -> (z.map f).IsDiag
  证明: Sym2.ind (fun _ _ => congr_arg f) z
-/
protected lemma IsDiag.map : z.IsDiag -> (z.map f).IsDiag := Sym2.ind (fun _ _ => congr_arg f) z

/--
lemma `isDiag_map` / 引理 `isDiag_map`

English:
lemma isDiag_map
  given: (hf : Injective f)
  statement: (z.map f).IsDiag ↔ z.IsDiag
  proof: Sym2.ind (fun _ _ => hf.eq_iff) z

@[simp]

中文:
引理 isDiag_map
  条件: (hf : Injective f)
  结论: (z.map f).IsDiag ↔ z.IsDiag
  证明: Sym2.ind (fun _ _ => hf.eq_iff) z

@[simp]

Depends on / 依赖: Sym2.ind, eq_iff, hf.eq_iff
-/
lemma isDiag_map (hf : Injective f) : (z.map f).IsDiag ↔ z.IsDiag :=
  Sym2.ind (fun _ _ => hf.eq_iff) z

@[simp]
/--
theorem `diag_isDiag` / 定理 `diag_isDiag`

English:
theorem diag_isDiag
  given: (a : α)
  statement: IsDiag (diag a)
  proof: Eq.refl a

@[simp, nontriviality]

中文:
定理 diag_isDiag
  条件: (a : α)
  结论: IsDiag (diag a)
  证明: Eq.refl a

@[simp, nontriviality]

Depends on / 依赖: Eq.refl
-/
theorem diag_isDiag (a : α) : IsDiag (diag a) :=
  Eq.refl a

@[simp, nontriviality]
/--
lemma `isDiag_of_subsingleton` / 引理 `isDiag_of_subsingleton`

English:
lemma isDiag_of_subsingleton
  given: [Subsingleton α] (z : Sym2 α)
  statement: z.IsDiag
  proof: z.ind Subsingleton.elim

中文:
引理 isDiag_of_subsingleton
  条件: [Subsingleton α] (z : Sym2 α)
  结论: z.IsDiag
  证明: z.ind Subsingleton.elim

Depends on / 依赖: Subsingleton, Subsingleton.elim, z.ind
-/
lemma isDiag_of_subsingleton [Subsingleton α] (z : Sym2 α) : z.IsDiag := z.ind Subsingleton.elim

variable (z) in
/--
Definition of `diagElem` / `diagElem` 的定义

English:
definition diagElem
  signature: : z.IsDiag -> α
  body: z.rec (fun a b _ => a) fun a b a' b' h => funext fun hx : a' = b' => by
    cases hx
    cases h <;> rfl

@[simp]

中文:
定义 diagElem
  签名: : z.IsDiag -> α
  定义体: z.rec (fun a b _ => a) fun a b a' b' h => funext fun hx : a' = b' => by
    cases hx
    cases h <;> rfl

@[simp]

Depends on / 依赖: z.rec
-/
def diagElem : z.IsDiag -> α :=
  z.rec (fun a b _ => a) fun a b a' b' h => funext fun hx : a' = b' => by
    cases hx
    cases h <;> rfl

@[simp]
/--
theorem `diagElem_mk` / 定理 `diagElem_mk`

English:
theorem diagElem_mk
  given: {a b : α} (h : IsDiag s(a, b))
  statement: s(a, b).diagElem h = a
  proof: rfl

@[simp]

中文:
定理 diagElem_mk
  条件: {a b : α} (h : IsDiag s(a, b))
  结论: s(a, b).diagElem h = a
  证明: rfl

@[simp]
-/
theorem diagElem_mk {a b : α} (h : IsDiag s(a, b)) : s(a, b).diagElem h = a := rfl

@[simp]
/--
theorem `diag_diagElem` / 定理 `diag_diagElem`

English:
theorem diag_diagElem
  given: (h : z.IsDiag)
  statement: diag (z.diagElem h) = z
  proof: by
  cases z; cases h; rfl

中文:
定理 diag_diagElem
  条件: (h : z.IsDiag)
  结论: diag (z.diagElem h) = z
  证明: by
  cases z; cases h; rfl
-/
theorem diag_diagElem (h : z.IsDiag) : diag (z.diagElem h) = z := by
  cases z; cases h; rfl

/-- `Sym2.diagElem` and `Sym2.diag` as an equivalence. -/
@[simps]
/--
Definition of `diagElemEquiv` / `diagElemEquiv` 的定义

English:
definition diagElemEquiv
  signature: : { a : Sym2 α // a.IsDiag } ≃ α where
  body: x.1.diagElem x.2
  invFun a := ⟨diag a, rfl⟩
  left_inv x := by ext; simp
  right_inv a := by simp [diag]

中文:
定义 diagElemEquiv
  签名: : { a : Sym2 α // a.IsDiag } ≃ α where
  定义体: x.1.diagElem x.2
  invFun a := ⟨diag a, rfl⟩
  left_inv x := by ext; simp
  right_inv a := by simp [diag]

Depends on / 依赖: diagElem
-/
def diagElemEquiv : { a : Sym2 α // a.IsDiag } ≃ α where
  toFun x := x.1.diagElem x.2
  invFun a := ⟨diag a, rfl⟩
  left_inv x := by ext; simp
  right_inv a := by simp [diag]

/--
Definition of `diagSet` / `diagSet` 的定义

English:
definition diagSet
  signature: : Set (Sym2 α)
  body: {z | z.IsDiag}

中文:
定义 diagSet
  签名: : Set (Sym2 α)
  定义体: {z | z.IsDiag}

Depends on / 依赖: IsDiag, z.IsDiag
-/
def diagSet : Set (Sym2 α) := {z | z.IsDiag}

/--
lemma `mem_diagSet` / 引理 `mem_diagSet`

English:
lemma mem_diagSet
  statement: z in diagSet ↔ z.IsDiag
  proof: .rfl

中文:
引理 mem_diagSet
  结论: z in diagSet ↔ z.IsDiag
  证明: .rfl
-/
@[simp] lemma mem_diagSet : z in diagSet ↔ z.IsDiag := .rfl

/--
lemma `range_diag` / 引理 `range_diag`

English:
lemma range_diag
  statement: .range (diag : α -> Sym2 α) = diagSet
  proof: by
  ext ⟨a, b⟩; simp [diag, eq_comm]

中文:
引理 range_diag
  结论: .range (diag : α -> Sym2 α) = diagSet
  证明: by
  ext ⟨a, b⟩; simp [diag, eq_comm]
-/
@[simp] lemma range_diag : .range (diag : α -> Sym2 α) = diagSet := by
  ext ⟨a, b⟩; simp [diag, eq_comm]

/--
theorem `diagSet_eq_setOfPred_isDiag` / 定理 `diagSet_eq_setOfPred_isDiag`

English:
theorem diagSet_eq_setOfPred_isDiag
  statement: diagSet = {z : Sym2 α | z.IsDiag}
  proof: rfl

@[deprecated (since := "2026-07-09")]
alias diagSet_eq_setOf_isDiag := diagSet_eq_setOfPred_isDiag

中文:
定理 diagSet_eq_setOfPred_isDiag
  结论: diagSet = {z : Sym2 α | z.IsDiag}
  证明: rfl

@[deprecated (since := "2026-07-09")]
alias diagSet_eq_setOf_isDiag := diagSet_eq_setOfPred_isDiag
-/
theorem diagSet_eq_setOfPred_isDiag : diagSet = {z : Sym2 α | z.IsDiag} := rfl

@[deprecated (since := "2026-07-09")]
alias diagSet_eq_setOf_isDiag := diagSet_eq_setOfPred_isDiag

/--
theorem `diagSet_eq_univ_of_subsingleton` / 定理 `diagSet_eq_univ_of_subsingleton`

English:
theorem diagSet_eq_univ_of_subsingleton
  given: [Subsingleton α]
  statement: @diagSet α = Set.univ
  proof: by ext; simp

中文:
定理 diagSet_eq_univ_of_subsingleton
  条件: [Subsingleton α]
  结论: @diagSet α = Set.univ
  证明: by ext; simp
-/
theorem diagSet_eq_univ_of_subsingleton [Subsingleton α] : @diagSet α = Set.univ := by ext; simp

/--
Instance `IsDiag.decidablePred` / 实例 `IsDiag.decidablePred`

English:
instance IsDiag.decidablePred
  signature: (α : Type u) [DecidableEq α]
  body: fun z => z.recOnSubsingleton fun _ _ => decidable_of_iff' _ mk_isDiag_iff

中文:
实例 IsDiag.decidablePred
  签名: (α : 类型u) [DecidableEq α]
  定义体: fun z => z.recOnSubsingleton fun _ _ => decidable_of_iff' _ mk_isDiag_iff

Depends on / 依赖: decidable_of_iff, mk_isDiag_iff, recOnSubsingleton, z.recOnSubsingleton
-/
instance IsDiag.decidablePred (α : Type u) [DecidableEq α] : DecidablePred (@IsDiag α) :=
  fun z => z.recOnSubsingleton fun _ _ => decidable_of_iff' _ mk_isDiag_iff

/--
Instance `decidablePred_mem_diagSet` / 实例 `decidablePred_mem_diagSet`

English:
instance decidablePred_mem_diagSet
  signature: (α : Type u) [DecidableEq α]
  body: IsDiag.decidablePred _

中文:
实例 decidablePred_mem_diagSet
  签名: (α : 类型u) [DecidableEq α]
  定义体: IsDiag.decidablePred _

Depends on / 依赖: IsDiag, IsDiag.decidablePred, decidablePred
-/
instance decidablePred_mem_diagSet (α : Type u) [DecidableEq α] : DecidablePred (· in @diagSet α) :=
  IsDiag.decidablePred _

/--
theorem `other_ne` / 定理 `other_ne`

English:
theorem other_ne
  given: {a : α} {z : Sym2 α} (hd : ¬IsDiag z) (h : a in z)
  statement: Mem.other h != a
  proof: by
  contrapose hd
  have h' := Sym2.other_spec h
  rw [hd] at h'
  rw [← h']
  simp

中文:
定理 other_ne
  条件: {a : α} {z : Sym2 α} (hd : ¬IsDiag z) (h : a in z)
  结论: Mem.other h != a
  证明: by
  contrapose hd
  have h' := Sym2.other_spec h
  rw [hd] at h'
  rw [← h']
  simp

Depends on / 依赖: Sym2.other_spec, contrapose, other_spec
-/
theorem other_ne {a : α} {z : Sym2 α} (hd : ¬IsDiag z) (h : a in z) : Mem.other h != a := by
  contrapose hd
  have h' := Sym2.other_spec h
  rw [hd] at h'
  rw [← h']
  simp

section Relations

/-! ### Declarations about symmetric relations -/


variable {r r₁ r₂ : α -> α -> Prop}

/--
Definition of `fromRel` / `fromRel` 的定义

English:
definition fromRel
  signature: (sym : Std.Symm r)
  body: Set.ofPred lift ⟨r, fun _ _ => propext ⟨symm, symm⟩⟩

@[simp]

中文:
定义 fromRel
  签名: (sym : Std.Symm r)
  定义体: Set.ofPred lift ⟨r, fun _ _ => propext ⟨symm, symm⟩⟩

@[simp]

Depends on / 依赖: Set.ofPred, ofPred, propext
-/
def fromRel (sym : Std.Symm r) : Set (Sym2 α) :=
Set.ofPred lift ⟨r, fun _ _ => propext ⟨symm, symm⟩⟩

@[simp]
/--
theorem `fromRel_prop` / 定理 `fromRel_prop`

English:
theorem fromRel_prop
  given: {sym : Std.Symm r} {a b : α}
  statement: s(a, b) in fromRel sym ↔ r a b
  proof: Iff.rfl

@[deprecated (since := "2026-02-05")] alias fromRel_proj_prop := fromRel_prop

中文:
定理 fromRel_prop
  条件: {sym : Std.Symm r} {a b : α}
  结论: s(a, b) in fromRel sym ↔ r a b
  证明: Iff.rfl

@[deprecated (since := "2026-02-05")] alias fromRel_proj_prop := fromRel_prop

Depends on / 依赖: Iff.rfl
-/
theorem fromRel_prop {sym : Std.Symm r} {a b : α} : s(a, b) in fromRel sym ↔ r a b :=
  Iff.rfl

@[deprecated (since := "2026-02-05")] alias fromRel_proj_prop := fromRel_prop

/--
theorem `fromRel_mono_iff` / 定理 `fromRel_mono_iff`

English:
theorem fromRel_mono_iff
  given: (sym₁ : Std.Symm r₁) (sym₂ : Std.Symm r₂)
  proof: ⟨fun hle a b => @hle s(a, b), fun hle => Sym2.ind hle⟩

@[gcongr]
alias ⟨_, fromRel_mono⟩ := fromRel_mono_iff

中文:
定理 fromRel_mono_iff
  条件: (sym₁ : Std.Symm r₁) (sym₂ : Std.Symm r₂)
  证明: ⟨fun hle a b => @hle s(a, b), fun hle => Sym2.ind hle⟩

@[gcongr]
alias ⟨_, fromRel_mono⟩ := fromRel_mono_iff

Depends on / 依赖: Sym2.ind
-/
theorem fromRel_mono_iff (sym₁ : Std.Symm r₁) (sym₂ : Std.Symm r₂) :
    fromRel sym₁ subseteq fromRel sym₂ ↔ r₁ <= r₂ :=
  ⟨fun hle a b => @hle s(a, b), fun hle => Sym2.ind hle⟩

@[gcongr]
alias ⟨_, fromRel_mono⟩ := fromRel_mono_iff

/--
theorem `mem_fromRel_comap` / 定理 `mem_fromRel_comap`

English:
theorem mem_fromRel_comap
  given: {r : β -> β -> Prop} (sym : Std.Symm r) (f : α -> β) (z : Sym2 α)
  proof: by
  cases z
  simp

中文:
定理 mem_fromRel_comap
  条件: {r : β -> β -> 命题} (sym : Std.Symm r) (f : α -> β) (z : Sym2 α)
  证明: by
  cases z
  simp
-/
theorem mem_fromRel_comap {r : β -> β -> Prop} (sym : Std.Symm r) (f : α -> β) (z : Sym2 α) :
    z in fromRel (sym.comap f) ↔ z.map f in fromRel sym := by
  cases z
  simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fromRel_bot` / 定理 `fromRel_bot`

English:
theorem fromRel_bot
  statement: fromRel (α := α) (r := ⊥) inferInstance = ∅
  proof: Set.eq_empty_of_forall_notMem Sym2.ind by simp

@[simp]

中文:
定理 fromRel_bot
  结论: fromRel (α := α) (r := ⊥) inferInstance = ∅
  证明: Set.eq_empty_of_forall_notMem Sym2.ind by simp

@[simp]
-/
theorem fromRel_bot : fromRel (α := α) (r := ⊥) inferInstance = ∅ :=
Set.eq_empty_of_forall_notMem Sym2.ind by simp

@[simp]
/--
theorem `fromRel_bot_iff` / 定理 `fromRel_bot_iff`

English:
theorem fromRel_bot_iff
  given: {sym : Std.Symm r}
  statement: fromRel sym = ∅ ↔ r = ⊥
  proof: by
  refine ⟨fun h => ?_, (· ▸ fromRel_bot)⟩
  ext x y
  simpa [h] using fromRel_prop (sym := sym)

中文:
定理 fromRel_bot_iff
  条件: {sym : Std.Symm r}
  结论: fromRel sym = ∅ ↔ r = ⊥
  证明: by
  refine ⟨fun h => ?_, (· ▸ fromRel_bot)⟩
  ext x y
  simpa [h] using fromRel_prop (sym := sym)

Depends on / 依赖: fromRel_bot, fromRel_prop
-/
theorem fromRel_bot_iff {sym : Std.Symm r} : fromRel sym = ∅ ↔ r = ⊥ := by
  refine ⟨fun h => ?_, (· ▸ fromRel_bot)⟩
  ext x y
  simpa [h] using fromRel_prop (sym := sym)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fromRel_top` / 定理 `fromRel_top`

English:
theorem fromRel_top
  statement: fromRel (α := α) (r := ⊤) inferInstance = .univ
  proof: Set.eq_univ_of_forall Sym2.ind by simp

@[simp]

中文:
定理 fromRel_top
  结论: fromRel (α := α) (r := ⊤) inferInstance = .univ
  证明: Set.eq_univ_of_forall Sym2.ind by simp

@[simp]
-/
theorem fromRel_top : fromRel (α := α) (r := ⊤) inferInstance = .univ :=
Set.eq_univ_of_forall Sym2.ind by simp

@[simp]
/--
theorem `fromRel_top_iff` / 定理 `fromRel_top_iff`

English:
theorem fromRel_top_iff
  given: {sym : Std.Symm r}
  statement: fromRel sym = .univ ↔ r = ⊤
  proof: by
  refine ⟨fun h => ?_, (· ▸ fromRel_top)⟩
  ext x y
  simpa [h] using fromRel_prop (sym := sym)

中文:
定理 fromRel_top_iff
  条件: {sym : Std.Symm r}
  结论: fromRel sym = .univ ↔ r = ⊤
  证明: by
  refine ⟨fun h => ?_, (· ▸ fromRel_top)⟩
  ext x y
  simpa [h] using fromRel_prop (sym := sym)

Depends on / 依赖: fromRel_prop, fromRel_top
-/
theorem fromRel_top_iff {sym : Std.Symm r} : fromRel sym = .univ ↔ r = ⊤ := by
  refine ⟨fun h => ?_, (· ▸ fromRel_top)⟩
  ext x y
  simpa [h] using fromRel_prop (sym := sym)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fromRel_ne` / 定理 `fromRel_ne`

English:
theorem fromRel_ne
  statement: fromRel (α := α) (r := Ne) inferInstance = {z | ¬IsDiag z}
  proof: by
  ext z; exact z.ind (by simp)

中文:
定理 fromRel_ne
  结论: fromRel (α := α) (r := Ne) inferInstance = {z | ¬IsDiag z}
  证明: by
  ext z; exact z.ind (by simp)

Depends on / 依赖: IsDiag, z.ind
-/
theorem fromRel_ne : fromRel (α := α) (r := Ne) inferInstance = {z | ¬IsDiag z} := by
  ext z; exact z.ind (by simp)

/--
lemma `diagSet_eq_fromRel_eq` / 引理 `diagSet_eq_fromRel_eq`

English:
lemma diagSet_eq_fromRel_eq
  statement: diagSet = fromRel (α := α) eq_equivalence.stdSymm
  proof: by
  ext ⟨a, b⟩; simp

中文:
引理 diagSet_eq_fromRel_eq
  结论: diagSet = fromRel (α := α) eq_equivalence.stdSymm
  证明: by
  ext ⟨a, b⟩; simp

Depends on / 依赖: eq_equivalence, eq_equivalence.stdSymm, stdSymm
-/
lemma diagSet_eq_fromRel_eq : diagSet = fromRel (α := α) eq_equivalence.stdSymm := by
  ext ⟨a, b⟩; simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `diagSet_compl_eq_fromRel_ne` / 引理 `diagSet_compl_eq_fromRel_ne`

English:
lemma diagSet_compl_eq_fromRel_ne
  statement: diagSetᶜ = fromRel (α := α) (r := Ne) inferInstance
  proof: by
  ext ⟨a, b⟩; simp

中文:
引理 diagSet_compl_eq_fromRel_ne
  结论: diagSetᶜ = fromRel (α := α) (r := Ne) inferInstance
  证明: by
  ext ⟨a, b⟩; simp
-/
lemma diagSet_compl_eq_fromRel_ne : diagSetᶜ = fromRel (α := α) (r := Ne) inferInstance := by
  ext ⟨a, b⟩; simp

/--
lemma `diagSet_subset_fromRel` / 引理 `diagSet_subset_fromRel`

English:
lemma diagSet_subset_fromRel
  given: (hr : Std.Symm r)
  statement: diagSet subseteq fromRel hr ↔ Std.Refl r
  proof: by
  simp [Set.subset_def, Sym2.forall, refl_def]

中文:
引理 diagSet_subset_fromRel
  条件: (hr : Std.Symm r)
  结论: diagSet subseteq fromRel hr ↔ Std.Refl r
  证明: by
  simp [Set.subset_def, Sym2.forall, refl_def]
-/
@[simp] lemma diagSet_subset_fromRel (hr : Std.Symm r) : diagSet subseteq fromRel hr ↔ Std.Refl r := by
  simp [Set.subset_def, Sym2.forall, refl_def]

/--
lemma `disjoint_diagSet_fromRel` / 引理 `disjoint_diagSet_fromRel`

English:
lemma disjoint_diagSet_fromRel
  given: (hr : Std.Symm r)
  proof: by
  simp [Set.disjoint_left, Sym2.forall, irrefl_def]

中文:
引理 disjoint_diagSet_fromRel
  条件: (hr : Std.Symm r)
  证明: by
  simp [Set.disjoint_left, Sym2.forall, irrefl_def]
-/
@[simp] lemma disjoint_diagSet_fromRel (hr : Std.Symm r) :
    Disjoint diagSet (fromRel hr) ↔ Std.Irrefl r := by
  simp [Set.disjoint_left, Sym2.forall, irrefl_def]

/--
lemma `fromRel_subset_compl_diagSet` / 引理 `fromRel_subset_compl_diagSet`

English:
lemma fromRel_subset_compl_diagSet
  given: (hr : Std.Symm r)
  proof: by simp [Set.subset_compl_iff_disjoint_left]

中文:
引理 fromRel_subset_compl_diagSet
  条件: (hr : Std.Symm r)
  证明: by simp [Set.subset_compl_iff_disjoint_left]
-/
@[simp] lemma fromRel_subset_compl_diagSet (hr : Std.Symm r) :
    fromRel hr subseteq diagSetᶜ ↔ Std.Irrefl r := by simp [Set.subset_compl_iff_disjoint_left]

/--
theorem `fromRel_irrefl` / 定理 `fromRel_irrefl`

English:
theorem fromRel_irrefl
  given: {sym : Std.Symm r}
  statement: Std.Irrefl r ↔ forall {z}, z in fromRel sym -> ¬IsDiag z where
  proof: by intro ⟨h⟩; apply Sym2.ind; aesop
  mpr h := ⟨fun _ hr => h (fromRel_prop.mpr hr) rfl⟩

@[deprecated (since := "2026-02-12")] alias fromRel_irreflexive := fromRel_irrefl

中文:
定理 fromRel_irrefl
  条件: {sym : Std.Symm r}
  结论: Std.Irrefl r ↔ 对任意 {z}, z in fromRel sym -> ¬IsDiag z where
  证明: by intro ⟨h⟩; apply Sym2.ind; aesop
  mpr h := ⟨fun _ hr => h (fromRel_prop.mpr hr) rfl⟩

@[deprecated (since := "2026-02-12")] alias fromRel_irreflexive := fromRel_irrefl

Depends on / 依赖: Sym2.ind, fromRel_prop, fromRel_prop.mpr
-/
theorem fromRel_irrefl {sym : Std.Symm r} : Std.Irrefl r ↔ forall {z}, z in fromRel sym -> ¬IsDiag z where
  mp := by intro ⟨h⟩; apply Sym2.ind; aesop
  mpr h := ⟨fun _ hr => h (fromRel_prop.mpr hr) rfl⟩

@[deprecated (since := "2026-02-12")] alias fromRel_irreflexive := fromRel_irrefl

/--
theorem `mem_fromRel_irrefl_other_ne` / 定理 `mem_fromRel_irrefl_other_ne`

English:
theorem mem_fromRel_irrefl_other_ne
  statement: {sym : Std.Symm r} (irrefl : Std.Irrefl r) {a : α}
  proof: other_ne (fromRel_irrefl.mp irrefl hz) h

中文:
定理 mem_fromRel_irrefl_other_ne
  结论: {sym : Std.Symm r} (irrefl : Std.Irrefl r) {a : α}
  证明: other_ne (fromRel_irrefl.mp irrefl hz) h

Depends on / 依赖: fromRel_irrefl, fromRel_irrefl.mp, irrefl, other_ne
-/
theorem mem_fromRel_irrefl_other_ne {sym : Std.Symm r} (irrefl : Std.Irrefl r) {a : α}
    {z : Sym2 α} (hz : z in fromRel sym) (h : a in z) : Mem.other h != a :=
  other_ne (fromRel_irrefl.mp irrefl hz) h

/--
Instance `fromRel.decidablePred` / 实例 `fromRel.decidablePred`

English:
instance fromRel.decidablePred
  signature: (sym : Std.Symm r) [h : DecidableRel r]
  body: fun z => z.recOnSubsingleton h

中文:
实例 fromRel.decidablePred
  签名: (sym : Std.Symm r) [h : DecidableRel r]
  定义体: fun z => z.recOnSubsingleton h

Depends on / 依赖: Quotient, Quotient.instUniqueQuotient, instUniqueQuotient, recOnSubsingleton, z.recOnSubsingleton
-/
instance fromRel.decidablePred (sym : Std.Symm r) [h : DecidableRel r] :
    DecidablePred (· in Sym2.fromRel sym) := fun z => z.recOnSubsingleton h

/--
lemma `fromRel_relationMap` / 引理 `fromRel_relationMap`

English:
lemma fromRel_relationMap
  given: {r : α -> α -> Prop} (hr : Std.Symm r) (f : α -> β)
  proof: by
  ext ⟨a, b⟩
  simp only [fromRel_prop, Relation.Map, Set.mem_image, Sym2.exists, map_mk, Sym2.eq,
    rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, and_or_left, exists_or, iff_self_or,
    forall_exists_index, and_imp]
  exact fun c d hcd hc hd => ⟨d, c, symm hcd, hd, hc⟩

中文:
引理 fromRel_relationMap
  条件: {r : α -> α -> 命题} (hr : Std.Symm r) (f : α -> β)
  证明: by
  ext ⟨a, b⟩
  simp only [fromRel_prop, Relation.Map, Set.mem_image, Sym2.exists, map_mk, Sym2.eq,
    rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, and_or_left, exists_or, iff_self_or,
    forall_exists_index, and_imp]
  exact fun c d hcd hc hd => ⟨d, c, symm hcd, hd, hc⟩

Depends on / 依赖: Prod.mk.injEq, Prod.swap_prod_mk, QuotientGroup, QuotientGroup.fintype, Relation, Relation.Map, Set.mem_image, Sym2.eq, Sym2.exists, and_imp, and_or_left, commutator, exists_or, fintype, forall_exists_index, fromRel_prop, iff_self_or, map_mk, mem_image, rel_iff
-/
lemma fromRel_relationMap {r : α -> α -> Prop} (hr : Std.Symm r) (f : α -> β) :
    fromRel (hr.map f) = Sym2.map f '' Sym2.fromRel hr := by
  ext ⟨a, b⟩
  simp only [fromRel_prop, Relation.Map, Set.mem_image, Sym2.exists, map_mk, Sym2.eq,
    rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, and_or_left, exists_or, iff_self_or,
    forall_exists_index, and_imp]
  exact fun c d hcd hc hd => ⟨d, c, symm hcd, hd, hc⟩

/--
Definition of `fromRelNdrec` / `fromRelNdrec` 的定义

English:
definition fromRelNdrec
  signature: {motive : Sort*} {sym : Std.Symm r} (z : Sym2 α) (hz : z in fromRel sym)
  body: z.hrec f (fun _ _ => Function.hfunext (sym.iff .. |>.eq) fun _ _ _ => heq_of_eq <| h ..) hz

@[simp]

中文:
定义 fromRelNdrec
  签名: {motive : Sort*} {sym : Std.Symm r} (z : Sym2 α) (hz : z in fromRel sym)
  定义体: z.hrec f (fun _ _ => Function.hfunext (sym.iff .. |>.eq) fun _ _ _ => heq_of_eq <| h ..) hz

@[simp]

Depends on / 依赖: Function, Function.hfunext, heq_of_eq, hfunext, sym.iff, z.hrec
-/
def fromRelNdrec {motive : Sort*} {sym : Std.Symm r} (z : Sym2 α) (hz : z in fromRel sym)
    (f : (a b : α) -> r a b -> motive) (h : forall (a b : α) (h : r a b), f a b h = f b a (symm h)) :
    motive :=
  z.hrec f (fun _ _ => Function.hfunext (sym.iff .. |>.eq) fun _ _ _ => heq_of_eq <| h ..) hz

@[simp]
/--
theorem `fromRelNdrec_mk` / 定理 `fromRelNdrec_mk`

English:
theorem fromRelNdrec_mk
  statement: {motive : Sort*} {sym : Std.Symm r} {a b : α} (hz : r a b)
  proof: rfl

中文:
定理 fromRelNdrec_mk
  结论: {motive : Sort*} {sym : Std.Symm r} {a b : α} (hz : r a b)
  证明: rfl
-/
theorem fromRelNdrec_mk {motive : Sort*} {sym : Std.Symm r} {a b : α} (hz : r a b)
    (f : (a b : α) -> r a b -> motive) (h : forall (a b : α) (h : r a b), f a b h = f b a (symm h)) :
    fromRelNdrec (sym := sym) s(a, b) hz f h = f a b hz :=
  rfl

/-- The `fromRel` set of a symmetric relation `r` is equivalent to summing that set restricted to
fibers of a function `f`, given that `f` agrees on elements related by `r`. -/
@[simps]
/--
Definition of `_root_.Equiv.sigmaFiberFromRel` / `_root_.Equiv.sigmaFiberFromRel` 的定义

English:
definition _root_.Equiv.sigmaFiberFromRel
  signature: (sym : Std.Symm r) {f : α -> β} (hf : r <= Setoid.ker f)
  body: z.val.fromRelNdrec z.prop
    (fun a₁ a₂ h => ⟨f a₁, s(⟨a₁, rfl⟩, ⟨a₂, hf a₁ a₂ h |>.symm⟩), h⟩)
    fun a₁ a₂ h => by
      rw! [hf a₁ a₂ h, eq_swap]
      rfl
.mp z.snd.prop⟩ invFun z := ⟨z.snd.val.map (↑), mem_fromRel_comap sym ..
  left_inv z := by
    rcases z with ⟨⟨a₁, a₂⟩, h⟩
    rfl
  right

中文:
定义 _root_.Equiv.sigmaFiberFromRel
  签名: (sym : Std.Symm r) {f : α -> β} (hf : r <= Setoid.ker f)
  定义体: z.val.fromRelNdrec z.prop
    (fun a₁ a₂ h => ⟨f a₁, s(⟨a₁, rfl⟩, ⟨a₂, hf a₁ a₂ h |>.symm⟩), h⟩)
    fun a₁ a₂ h => by
      rw! [hf a₁ a₂ h, eq_swap]
      rfl
.mp z.snd.prop⟩ invFun z := ⟨z.snd.val.map (↑), mem_fromRel_comap sym ..
  left_inv z := by
    rcases z with ⟨⟨a₁, a₂⟩, h⟩
    rfl
  right

Depends on / 依赖: sym.comap
-/
def _root_.Equiv.sigmaFiberFromRel (sym : Std.Symm r) {f : α -> β} (hf : r <= Setoid.ker f) :
fromRel sym ≃ Σ b : β, fromRel (α := { a // f a = b }) sym.comap (↑) where
  toFun z := z.val.fromRelNdrec z.prop
    (fun a₁ a₂ h => ⟨f a₁, s(⟨a₁, rfl⟩, ⟨a₂, hf a₁ a₂ h |>.symm⟩), h⟩)
    fun a₁ a₂ h => by
      rw! [hf a₁ a₂ h, eq_swap]
      rfl
.mp z.snd.prop⟩ invFun z := ⟨z.snd.val.map (↑), mem_fromRel_comap sym ..
  left_inv z := by
    rcases z with ⟨⟨a₁, a₂⟩, h⟩
    rfl
  right_inv z := by
    rcases z with ⟨b, ⟨⟨a₁, rfl⟩, ⟨a₂, ha₂⟩⟩, h⟩
    rfl

/-- For a relation homomorphism `r →r r'` where `r` is symmetric, the `fromRel` set of `r` is
equivalent to summing that set restricted to equivalence classes of `r'` using a `Subtype`,
`Quot` version -/
@[simps!]
/--
Definition of `_root_.Equiv.sigmaQuotFromRel` / `_root_.Equiv.sigmaQuotFromRel` 的定义

English:
definition _root_.Equiv.sigmaQuotFromRel
  signature: (sym : Std.Symm r) {r' : β -> β -> Prop} (f : r ->r r')
  body: .sigmaFiberFromRel sym fun _ _ h => Quot.sound f.map_rel h

中文:
定义 _root_.Equiv.sigmaQuotFromRel
  签名: (sym : Std.Symm r) {r' : β -> β -> 命题} (f : r ->r r')
  定义体: .sigmaFiberFromRel sym fun _ _ h => Quot.sound f.map_rel h

Depends on / 依赖: sym.comap
-/
def _root_.Equiv.sigmaQuotFromRel (sym : Std.Symm r) {r' : β -> β -> Prop} (f : r ->r r') :
fromRel sym ≃ Σ q : Quot r', fromRel (α := { x // .mk r' (f x) = q }) sym.comap (↑) :=
.sigmaFiberFromRel sym fun _ _ h => Quot.sound f.map_rel h

/-- For a relation homomorphism `r →r r'` where `r` is symmetric, the `fromRel` set of `r` is
equivalent to summing that set restricted to equivalence classes of `r'` using a `Subtype`,
`Quotient` version -/
@[simps!]
/--
Definition of `_root_.Equiv.sigmaQuotientFromRel` / `_root_.Equiv.sigmaQuotientFromRel` 的定义

English:
definition _root_.Equiv.sigmaQuotientFromRel
  signature: (sym : Std.Symm r) {r' : Setoid β} (f : r ->r r')
  body: .sigmaFiberFromRel sym fun _ _ h => Quotient.sound f.map_rel h

中文:
定义 _root_.Equiv.sigmaQuotientFromRel
  签名: (sym : Std.Symm r) {r' : Setoid β} (f : r ->r r')
  定义体: .sigmaFiberFromRel sym fun _ _ h => Quotient.sound f.map_rel h

Depends on / 依赖: sym.comap
-/
def _root_.Equiv.sigmaQuotientFromRel (sym : Std.Symm r) {r' : Setoid β} (f : r ->r r') :
fromRel sym ≃ Σ q : Quotient r', fromRel (α := { x // ⟦f x⟧ = q }) sym.comap (↑) :=
.sigmaFiberFromRel sym fun _ _ h => Quotient.sound f.map_rel h

/--
Definition of `ToRel` / `ToRel` 的定义

English:
definition ToRel
  signature: (s : Set (Sym2 α)) (x y : α)
  body: s(x, y) in s

@[simp]

中文:
定义 ToRel
  签名: (s : Set (Sym2 α)) (x y : α)
  定义体: s(x, y) in s

@[simp]
-/
def ToRel (s : Set (Sym2 α)) (x y : α) : Prop :=
  s(x, y) in s

@[simp]
/--
theorem `toRel_prop` / 定理 `toRel_prop`

English:
theorem toRel_prop
  given: (s : Set (Sym2 α)) (x y : α)
  statement: ToRel s x y ↔ s(x, y) in s
  proof: Iff.rfl

中文:
定理 toRel_prop
  条件: (s : Set (Sym2 α)) (x y : α)
  结论: ToRel s x y ↔ s(x, y) in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toRel_prop (s : Set (Sym2 α)) (x y : α) : ToRel s x y ↔ s(x, y) in s :=
  Iff.rfl

/--
Instance `toRel_symm` / 实例 `toRel_symm`

English:
instance toRel_symm
  signature: (s : Set (Sym2 α))
  body: by simp [eq_swap]

@[deprecated (since := "2026-06-10")] alias toRel_symmetric := toRel_symm

中文:
实例 toRel_symm
  签名: (s : Set (Sym2 α))
  定义体: by simp [eq_swap]

@[deprecated (since := "2026-06-10")] alias toRel_symmetric := toRel_symm

Depends on / 依赖: eq_swap
-/
instance toRel_symm (s : Set (Sym2 α)) : Std.Symm (ToRel s) where
  symm x y := by simp [eq_swap]

@[deprecated (since := "2026-06-10")] alias toRel_symmetric := toRel_symm

/--
theorem `toRel_fromRel` / 定理 `toRel_fromRel`

English:
theorem toRel_fromRel
  given: (sym : Std.Symm r)
  statement: ToRel (fromRel sym) = r
  proof: rfl

中文:
定理 toRel_fromRel
  条件: (sym : Std.Symm r)
  结论: ToRel (fromRel sym) = r
  证明: rfl
-/
theorem toRel_fromRel (sym : Std.Symm r) : ToRel (fromRel sym) = r :=
  rfl

/--
theorem `fromRel_toRel` / 定理 `fromRel_toRel`

English:
theorem fromRel_toRel
  given: (s : Set (Sym2 α))
  statement: fromRel (toRel_symm s) = s
  proof: Set.ext fun z => Sym2.ind (fun _ _ => Iff.rfl) z

中文:
定理 fromRel_toRel
  条件: (s : Set (Sym2 α))
  结论: fromRel (toRel_symm s) = s
  证明: Set.ext fun z => Sym2.ind (fun _ _ => Iff.rfl) z

Depends on / 依赖: Iff.rfl, Set.ext, Sym2.ind
-/
theorem fromRel_toRel (s : Set (Sym2 α)) : fromRel (toRel_symm s) = s :=
  Set.ext fun z => Sym2.ind (fun _ _ => Iff.rfl) z

/--
theorem `toRel_mono_iff` / 定理 `toRel_mono_iff`

English:
theorem toRel_mono_iff
  given: (s₁ s₂ : Set (Sym2 α))
  statement: ToRel s₁ <= ToRel s₂ ↔ s₁ subseteq s₂
  proof: ⟨(Sym2.ind ·), (@· s(·, ·))⟩

@[gcongr]
alias ⟨_, toRel_mono⟩ := toRel_mono_iff

中文:
定理 toRel_mono_iff
  条件: (s₁ s₂ : Set (Sym2 α))
  结论: ToRel s₁ <= ToRel s₂ ↔ s₁ subseteq s₂
  证明: ⟨(Sym2.ind ·), (@· s(·, ·))⟩

@[gcongr]
alias ⟨_, toRel_mono⟩ := toRel_mono_iff

Depends on / 依赖: Sym2.ind
-/
theorem toRel_mono_iff (s₁ s₂ : Set (Sym2 α)) : ToRel s₁ <= ToRel s₂ ↔ s₁ subseteq s₂ :=
  ⟨(Sym2.ind ·), (@· s(·, ·))⟩

@[gcongr]
alias ⟨_, toRel_mono⟩ := toRel_mono_iff

variable (α) in
/--
Definition of `toRelOrderEmbedding` / `toRelOrderEmbedding` 的定义

English:
definition toRelOrderEmbedding
  signature: : Set (Sym2 α) ↪o (α -> α -> Prop)
  body: .ofMapLEIff ToRel toRel_mono_iff

中文:
定义 toRelOrderEmbedding
  签名: : Set (Sym2 α) ↪o (α -> α -> 命题)
  定义体: .ofMapLEIff ToRel toRel_mono_iff

Depends on / 依赖: ofMapLEIff, toRel_mono_iff
-/
def toRelOrderEmbedding : Set (Sym2 α) ↪o (α -> α -> Prop) :=
  .ofMapLEIff ToRel toRel_mono_iff

set_option backward.isDefEq.respectTransparency false in
variable (α) in
/-- `fromRel`/`ToRel` induce an order isomorphism between symmetric relations and `Sym2` sets -/
@[simps]
/--
Definition of `fromRelOrderIso` / `fromRelOrderIso` 的定义

English:
definition fromRelOrderIso
  signature: : { r : α -> α -> Prop // Std.Symm r } ≃o Set (Sym2 α) where
  body: fromRel r.prop
  invFun s := ⟨ToRel s, toRel_symm s⟩
  left_inv r := by simp [toRel_fromRel]
  right_inv s := by simp [fromRel_toRel]
  map_rel_iff' {r₁ r₂} := by simpa using! fromRel_mono_iff ..

中文:
定义 fromRelOrderIso
  签名: : { r : α -> α -> 命题 // Std.Symm r } ≃o Set (Sym2 α) where
  定义体: fromRel r.prop
  invFun s := ⟨ToRel s, toRel_symm s⟩
  left_inv r := by simp [toRel_fromRel]
  right_inv s := by simp [fromRel_toRel]
  map_rel_iff' {r₁ r₂} := by simpa using! fromRel_mono_iff ..

Depends on / 依赖: fromRel, r.prop
-/
def fromRelOrderIso : { r : α -> α -> Prop // Std.Symm r } ≃o Set (Sym2 α) where
  toFun r := fromRel r.prop
  invFun s := ⟨ToRel s, toRel_symm s⟩
  left_inv r := by simp [toRel_fromRel]
  right_inv s := by simp [fromRel_toRel]
  map_rel_iff' {r₁ r₂} := by simpa using! fromRel_mono_iff ..

/-- `fromRel` induces an order embedding from symmetric relations to `Sym2` sets. -/
@[deprecated fromRelOrderIso (since := "2026-03-11")]
/--
Definition of `fromRelOrderEmbedding` / `fromRelOrderEmbedding` 的定义

English:
definition fromRelOrderEmbedding
  signature: : { r : α -> α -> Prop // Std.Symm r } ↪o Set (Sym2 α)
  body: .toOrderEmbedding fromRelOrderIso α

@[simp]

中文:
定义 fromRelOrderEmbedding
  签名: : { r : α -> α -> 命题 // Std.Symm r } ↪o Set (Sym2 α)
  定义体: .toOrderEmbedding fromRelOrderIso α

@[simp]

Depends on / 依赖: fromRelOrderIso, toOrderEmbedding
-/
def fromRelOrderEmbedding : { r : α -> α -> Prop // Std.Symm r } ↪o Set (Sym2 α) :=
.toOrderEmbedding fromRelOrderIso α

@[simp]
/--
theorem `fromRel_eq_fromRel_iff_eq` / 定理 `fromRel_eq_fromRel_iff_eq`

English:
theorem fromRel_eq_fromRel_iff_eq
  given: {r₁ r₂ : α -> α -> Prop} (sym₁ : Std.Symm r₁) (sym₂ : Std.Symm r₂)
  proof: by
  rw [← Subtype.mk.injEq r₁ sym₁ r₂ sym₂]; rw [← fromRelOrderIso α |>.eq_iff_eq]
  rfl

@[deprecated (since := "2026-03-11")] alias fromRel_eq_fromRell_iff_eq := fromRel_eq_fromRel_iff_eq

中文:
定理 fromRel_eq_fromRel_iff_eq
  条件: {r₁ r₂ : α -> α -> 命题} (sym₁ : Std.Symm r₁) (sym₂ : Std.Symm r₂)
  证明: by
  rw [← Subtype.mk.injEq r₁ sym₁ r₂ sym₂]; rw [← fromRelOrderIso α |>.eq_iff_eq]
  rfl

@[deprecated (since := "2026-03-11")] alias fromRel_eq_fromRell_iff_eq := fromRel_eq_fromRel_iff_eq

Depends on / 依赖: Subtype, Subtype.mk.injEq, eq_iff_eq, fromRelOrderIso
-/
theorem fromRel_eq_fromRel_iff_eq {r₁ r₂ : α -> α -> Prop} (sym₁ : Std.Symm r₁) (sym₂ : Std.Symm r₂) :
    fromRel sym₁ = fromRel sym₂ ↔ r₁ = r₂ := by
  rw [← Subtype.mk.injEq r₁ sym₁ r₂ sym₂]; rw [← fromRelOrderIso α |>.eq_iff_eq]
  rfl

@[deprecated (since := "2026-03-11")] alias fromRel_eq_fromRell_iff_eq := fromRel_eq_fromRel_iff_eq

end Relations

section ToMultiset

/--
Definition of `toMultiset` / `toMultiset` 的定义

English:
definition toMultiset
  signature: {α : Type*} (z : Sym2 α)
  body: by
  refine Sym2.lift ?_ z
  use (Multiset.ofList [·, ·])
  simp [List.Perm.swap]

中文:
定义 toMultiset
  签名: {α : 类型} (z : Sym2 α)
  定义体: by
  refine Sym2.lift ?_ z
  use (Multiset.ofList [·, ·])
  simp [List.Perm.swap]

Depends on / 依赖: List.Perm.swap, Multiset, Multiset.ofList, Sym2.lift, ofList
-/
def toMultiset {α : Type*} (z : Sym2 α) : Multiset α := by
  refine Sym2.lift ?_ z
  use (Multiset.ofList [·, ·])
  simp [List.Perm.swap]

/--
lemma `card_toMultiset` / 引理 `card_toMultiset`

English:
lemma card_toMultiset
  given: {α : Type*} (z : Sym2 α)
  statement: z.toMultiset.card = 2
  proof: by
  induction z
  simp [Sym2.toMultiset]

中文:
引理 card_toMultiset
  条件: {α : 类型} (z : Sym2 α)
  结论: z.toMultiset.card = 2
  证明: by
  induction z
  simp [Sym2.toMultiset]

Depends on / 依赖: Sym2.toMultiset, toMultiset
-/
lemma card_toMultiset {α : Type*} (z : Sym2 α) : z.toMultiset.card = 2 := by
  induction z
  simp [Sym2.toMultiset]

/-- The members of an unordered pair are members of the corresponding unordered list. -/
@[simp]
/--
theorem `mem_toMultiset` / 定理 `mem_toMultiset`

English:
theorem mem_toMultiset
  given: {α : Type*} {x : α} {z : Sym2 α}
  proof: by
  induction z
  simp [Sym2.toMultiset]

中文:
定理 mem_toMultiset
  条件: {α : 类型} {x : α} {z : Sym2 α}
  证明: by
  induction z
  simp [Sym2.toMultiset]

Depends on / 依赖: Sym2.toMultiset, toMultiset
-/
theorem mem_toMultiset {α : Type*} {x : α} {z : Sym2 α} :
    x in (z.toMultiset : Multiset α) ↔ x in z := by
  induction z
  simp [Sym2.toMultiset]

end ToMultiset

section ToFinset

variable [DecidableEq α]

/--
Definition of `toFinset` / `toFinset` 的定义

English:
definition toFinset
  signature: (z : Sym2 α)
  body: (z.toMultiset : Multiset α).toFinset

中文:
定义 toFinset
  签名: (z : Sym2 α)
  定义体: (z.toMultiset : Multiset α).toFinset

Depends on / 依赖: Multiset, toFinset, toMultiset, z.toMultiset
-/
def toFinset (z : Sym2 α) : Finset α := (z.toMultiset : Multiset α).toFinset

/-- The members of an unordered pair are members of the corresponding finite set. -/
@[simp]
/--
theorem `mem_toFinset` / 定理 `mem_toFinset`

English:
theorem mem_toFinset
  given: {x : α} {z : Sym2 α}
  statement: x in z.toFinset ↔ x in z
  proof: by
  rw [← Sym2.mem_toMultiset]; rw [Sym2.toFinset]; rw [Multiset.mem_toFinset]

@[simp]

中文:
定理 mem_toFinset
  条件: {x : α} {z : Sym2 α}
  结论: x in z.toFinset ↔ x in z
  证明: by
  rw [← Sym2.mem_toMultiset]; rw [Sym2.toFinset]; rw [Multiset.mem_toFinset]

@[simp]

Depends on / 依赖: Multiset, Multiset.mem_toFinset, Sym2.mem_toMultiset, Sym2.toFinset, mem_toFinset, mem_toMultiset, toFinset
-/
theorem mem_toFinset {x : α} {z : Sym2 α} : x in z.toFinset ↔ x in z := by
  rw [← Sym2.mem_toMultiset]; rw [Sym2.toFinset]; rw [Multiset.mem_toFinset]

@[simp]
/--
theorem `toFinset_ne_empty` / 定理 `toFinset_ne_empty`

English:
theorem toFinset_ne_empty
  given: (z : Sym2 α)
  statement: z.toFinset != ∅
  proof: by
  exact Finset.ne_empty_of_mem (Sym2.mem_toFinset.mpr (Sym2.out_fst_mem _))

中文:
定理 toFinset_ne_empty
  条件: (z : Sym2 α)
  结论: z.toFinset != ∅
  证明: by
  exact Finset.ne_empty_of_mem (Sym2.mem_toFinset.mpr (Sym2.out_fst_mem _))

Depends on / 依赖: Finset, Finset.ne_empty_of_mem, Sym2.mem_toFinset.mpr, Sym2.out_fst_mem, mem_toFinset, ne_empty_of_mem, out_fst_mem
-/
theorem toFinset_ne_empty (z : Sym2 α) : z.toFinset != ∅ := by
  exact Finset.ne_empty_of_mem (Sym2.mem_toFinset.mpr (Sym2.out_fst_mem _))

/--
lemma `toFinset_mk_eq` / 引理 `toFinset_mk_eq`

English:
lemma toFinset_mk_eq
  given: {x y : α}
  statement: s(x, y).toFinset = {x, y}
  proof: by
  ext; simp [← Sym2.mem_toFinset, ← Sym2.mem_iff]

中文:
引理 toFinset_mk_eq
  条件: {x y : α}
  结论: s(x, y).toFinset = {x, y}
  证明: by
  ext; simp [← Sym2.mem_toFinset, ← Sym2.mem_iff]

Depends on / 依赖: Sym2.mem_iff, Sym2.mem_toFinset, mem_iff, mem_toFinset
-/
lemma toFinset_mk_eq {x y : α} : s(x, y).toFinset = {x, y} := by
  ext; simp [← Sym2.mem_toFinset, ← Sym2.mem_iff]

/--
theorem `card_toFinset_of_isDiag` / 定理 `card_toFinset_of_isDiag`

English:
theorem card_toFinset_of_isDiag
  given: (z : Sym2 α) (h : z.IsDiag)
  statement: #(z : Sym2 α).toFinset = 1
  proof: by
  induction z
  rw [Sym2.mk_isDiag_iff] at h
  simp [Sym2.toFinset_mk_eq, h]

中文:
定理 card_toFinset_of_isDiag
  条件: (z : Sym2 α) (h : z.IsDiag)
  结论: #(z : Sym2 α).toFinset = 1
  证明: by
  induction z
  rw [Sym2.mk_isDiag_iff] at h
  simp [Sym2.toFinset_mk_eq, h]

Depends on / 依赖: Sym2.mk_isDiag_iff, Sym2.toFinset_mk_eq, mk_isDiag_iff, toFinset_mk_eq
-/
theorem card_toFinset_of_isDiag (z : Sym2 α) (h : z.IsDiag) : #(z : Sym2 α).toFinset = 1 := by
  induction z
  rw [Sym2.mk_isDiag_iff] at h
  simp [Sym2.toFinset_mk_eq, h]

/--
theorem `card_toFinset_of_not_isDiag` / 定理 `card_toFinset_of_not_isDiag`

English:
theorem card_toFinset_of_not_isDiag
  given: (z : Sym2 α) (h : ¬z.IsDiag)
  statement: #(z : Sym2 α).toFinset = 2
  proof: by
  induction z
  rw [Sym2.mk_isDiag_iff] at h
  simp [Sym2.toFinset_mk_eq, h]

中文:
定理 card_toFinset_of_not_isDiag
  条件: (z : Sym2 α) (h : ¬z.IsDiag)
  结论: #(z : Sym2 α).toFinset = 2
  证明: by
  induction z
  rw [Sym2.mk_isDiag_iff] at h
  simp [Sym2.toFinset_mk_eq, h]

Depends on / 依赖: Sym2.mk_isDiag_iff, Sym2.toFinset_mk_eq, mk_isDiag_iff, toFinset_mk_eq
-/
theorem card_toFinset_of_not_isDiag (z : Sym2 α) (h : ¬z.IsDiag) : #(z : Sym2 α).toFinset = 2 := by
  induction z
  rw [Sym2.mk_isDiag_iff] at h
  simp [Sym2.toFinset_mk_eq, h]

/--
theorem `card_toFinset` / 定理 `card_toFinset`

English:
theorem card_toFinset
  given: (z : Sym2 α)
  statement: #(z : Sym2 α).toFinset = if z.IsDiag then 1 else 2
  proof: by
  by_cases h : z.IsDiag
  · simp [card_toFinset_of_isDiag z h, h]
  · simp [card_toFinset_of_not_isDiag z h, h]

中文:
定理 card_toFinset
  条件: (z : Sym2 α)
  结论: #(z : Sym2 α).toFinset = if z.IsDiag then 1 else 2
  证明: by
  by_cases h : z.IsDiag
  · simp [card_toFinset_of_isDiag z h, h]
  · simp [card_toFinset_of_not_isDiag z h, h]

Depends on / 依赖: IsDiag, card_toFinset_of_isDiag, card_toFinset_of_not_isDiag, z.IsDiag
-/
theorem card_toFinset (z : Sym2 α) : #(z : Sym2 α).toFinset = if z.IsDiag then 1 else 2 := by
  by_cases h : z.IsDiag
  · simp [card_toFinset_of_isDiag z h, h]
  · simp [card_toFinset_of_not_isDiag z h, h]

end ToFinset

section SymEquiv

/-! ### Equivalence to the second symmetric power -/


attribute [local instance] List.Vector.Perm.isSetoid

set_option backward.privateInPublic true in
/--
Definition of `fromVector` / `fromVector` 的定义

English:
definition fromVector
  signature: : List.Vector α 2 -> α × α

中文:
定义 fromVector
  签名: : List.Vector α 2 -> α × α
-/
private def fromVector : List.Vector α 2 -> α × α
  | ⟨[a, b], _⟩ => (a, b)

/--
theorem `perm_card_two_iff` / 定理 `perm_card_two_iff`

English:
theorem perm_card_two_iff
  given: {a₁ b₁ a₂ b₂ : α}
  proof: { mp := by
      simp only [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.coe_nil, Multiset.cons_zero,
        Multiset.cons_eq_cons, Multiset.singleton_inj, ne_eq, Multiset.singleton_eq_cons_iff,
        exists_eq_right_right, and_true]
      tauto
    mpr := fun
        | .inl ⟨h₁, h₂⟩ | .i

中文:
定理 perm_card_two_iff
  条件: {a₁ b₁ a₂ b₂ : α}
  证明: { mp := by
      simp only [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.coe_nil, Multiset.cons_zero,
        Multiset.cons_eq_cons, Multiset.singleton_inj, ne_eq, Multiset.singleton_eq_cons_iff,
        exists_eq_right_right, and_true]
      tauto
    mpr := fun
        | .inl ⟨h₁, h₂⟩ | .i
-/
private theorem perm_card_two_iff {a₁ b₁ a₂ b₂ : α} :
    [a₁, b₁].Perm [a₂, b₂] ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ a₁ = b₂ ∧ b₁ = a₂ :=
  { mp := by
      simp only [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.coe_nil, Multiset.cons_zero,
        Multiset.cons_eq_cons, Multiset.singleton_inj, ne_eq, Multiset.singleton_eq_cons_iff,
        exists_eq_right_right, and_true]
      tauto
    mpr := fun
        | .inl ⟨h₁, h₂⟩ | .inr ⟨h₁, h₂⟩ => by
          rw [h₁]; rw [h₂]
          first | done | constructor }

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `sym2EquivSym'` / `sym2EquivSym'` 的定义

English:
definition sym2EquivSym'
  signature: : Equiv (Sym2 α) (Sym' α 2) where
  body: Quot.map (fun x : α × α => ⟨[x.1, x.2], rfl⟩)
      (by
        rintro _ _ ⟨_⟩
        · constructor; apply List.Perm.refl
        apply List.Perm.swap'
        rfl)
  invFun :=
    Quot.map fromVector
      (by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        rcases x with - | ⟨_, x⟩; · simp at hx
        

中文:
定义 sym2EquivSym'
  签名: : Equiv (Sym2 α) (Sym' α 2) where
  定义体: Quot.map (fun x : α × α => ⟨[x.1, x.2], rfl⟩)
      (by
        rintro _ _ ⟨_⟩
        · constructor; apply List.Perm.refl
        apply List.Perm.swap'
        rfl)
  invFun :=
    Quot.map fromVector
      (by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        rcases x with - | ⟨_, x⟩; · simp at hx
        

Depends on / 依赖: List.Perm.refl, List.Perm.swap, Quot.map, fromVector, invFun, perm_card_two_iff, perm_card_two_iff.mp
-/
def sym2EquivSym' : Equiv (Sym2 α) (Sym' α 2) where
  toFun :=
    Quot.map (fun x : α × α => ⟨[x.1, x.2], rfl⟩)
      (by
        rintro _ _ ⟨_⟩
        · constructor; apply List.Perm.refl
        apply List.Perm.swap'
        rfl)
  invFun :=
    Quot.map fromVector
      (by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        rcases x with - | ⟨_, x⟩; · simp at hx
        rcases x with - | ⟨_, x⟩; · simp at hx
        rcases x with - | ⟨_, x⟩; swap
        · exfalso
          simp at hx
        rcases y with - | ⟨_, y⟩; · simp at hy
        rcases y with - | ⟨_, y⟩; · simp at hy
        rcases y with - | ⟨_, y⟩; swap
        · exfalso
          simp at hy
        rcases perm_card_two_iff.mp h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · constructor
        apply Sym2.Rel.swap)
  left_inv := by apply Sym2.ind; aesop (add norm unfold [Sym2.fromVector])
  right_inv x := by
    refine x.recOnSubsingleton fun x => ?_
    obtain ⟨x, hx⟩ := x
    obtain - | ⟨-, x⟩ := x
    · simp at hx
    rcases x with - | ⟨_, x⟩
    · simp at hx
    rcases x with - | ⟨_, x⟩
    swap
    · exfalso
      simp at hx
    rfl

/--
Definition of `equivSym` / `equivSym` 的定义

English:
definition equivSym
  signature: (α : Type*)
  body: Equiv.trans sym2EquivSym' symEquivSym'.symm

中文:
定义 equivSym
  签名: (α : 类型)
  定义体: Equiv.trans sym2EquivSym' symEquivSym'.symm

Depends on / 依赖: Equiv.trans, sym2EquivSym, symEquivSym
-/
def equivSym (α : Type*) : Sym2 α ≃ Sym α 2 :=
  Equiv.trans sym2EquivSym' symEquivSym'.symm

/--
Definition of `equivMultiset` / `equivMultiset` 的定义

English:
definition equivMultiset
  signature: (α : Type*)
  body: equivSym α

中文:
定义 equivMultiset
  签名: (α : 类型)
  定义体: equivSym α

Depends on / 依赖: equivSym
-/
def equivMultiset (α : Type*) : Sym2 α ≃ { s : Multiset α // Multiset.card s = 2 } :=
  equivSym α

end SymEquiv

section Decidable

/--
Instance `instDecidableRel` / 实例 `instDecidableRel`

English:
instance instDecidableRel
  signature: [DecidableEq α]
  body: fun _ _ => decidable_of_iff' _ rel_iff

中文:
实例 instDecidableRel
  签名: [DecidableEq α]
  定义体: fun _ _ => decidable_of_iff' _ rel_iff

Depends on / 依赖: decidable_of_iff, rel_iff
-/
instance instDecidableRel [DecidableEq α] : DecidableRel (Rel α) :=
  fun _ _ => decidable_of_iff' _ rel_iff

section
attribute [local instance] Sym2.Rel.setoid

/--
Instance `instDecidableRel'` / 实例 `instDecidableRel'`

English:
instance instDecidableRel'
  signature: [DecidableEq α]
  body: instDecidableRel

中文:
实例 instDecidableRel'
  签名: [DecidableEq α]
  定义体: instDecidableRel
-/
instance instDecidableRel' [DecidableEq α] : DecidableRel (HasEquiv.Equiv (α := α × α)) :=
  instDecidableRel

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] : DecidableEq (Sym2 α)
  body: inferInstanceAs DecidableEq (Quotient (Sym2.Rel.setoid α))

中文:
实例 [DecidableEq
  签名: α] : DecidableEq (Sym2 α)
  定义体: inferInstanceAs DecidableEq (Quotient (Sym2.Rel.setoid α))

Depends on / 依赖: DecidableEq, Quotient, Sym2.Rel.setoid, setoid
-/
instance [DecidableEq α] : DecidableEq (Sym2 α) :=
inferInstanceAs DecidableEq (Quotient (Sym2.Rel.setoid α))

/-! ### The other element of an element of the symmetric square -/

/-- Get the other element of the unordered pair using the decidable equality.
This is the computable version of `Mem.other`. -/
@[aesop norm unfold (rule_sets := [Sym2])]
/--
Definition of `Mem.other'` / `Mem.other'` 的定义

English:
definition Mem.other'
  signature: [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z)
  body: Sym2.rec (fun b c _ => if a = b then c else b) (by
    clear h z
    intro b c d e h
    ext hy
    have {f g h} : @Eq.ndrec (Sym2 α) s(b, c)
      (fun x => a in x -> α) (fun _ => if a = b then c else b) f g h =
        if a = b then c else b := by subst g; rfl
    aesop)
    z h

@[simp]

中文:
定义 Mem.other'
  签名: [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z)
  定义体: Sym2.rec (fun b c _ => if a = b then c else b) (by
    clear h z
    intro b c d e h
    ext hy
    have {f g h} : @Eq.ndrec (Sym2 α) s(b, c)
      (fun x => a in x -> α) (fun _ => if a = b then c else b) f g h =
        if a = b then c else b := by subst g; rfl
    aesop)
    z h

@[simp]

Depends on / 依赖: Eq.ndrec, Sym2.rec
-/
def Mem.other' [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z) : α :=
  Sym2.rec (fun b c _ => if a = b then c else b) (by
    clear h z
    intro b c d e h
    ext hy
    have {f g h} : @Eq.ndrec (Sym2 α) s(b, c)
      (fun x => a in x -> α) (fun _ => if a = b then c else b) f g h =
        if a = b then c else b := by subst g; rfl
    aesop)
    z h

@[simp]
/--
theorem `other_spec'` / 定理 `other_spec'`

English:
theorem other_spec'
  given: [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z)
  statement: s(a, Mem.other' h) = z
  proof: by
  induction z
  aesop (add norm unfold [Sym2.rec, Quot.rec]) (rule_sets := [Sym2])

@[simp]

中文:
定理 other_spec'
  条件: [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z)
  结论: s(a, Mem.other' h) = z
  证明: by
  induction z
  aesop (add norm unfold [Sym2.rec, Quot.rec]) (rule_sets := [Sym2])

@[simp]

Depends on / 依赖: Quot.rec, Sym2.rec, rule_sets
-/
theorem other_spec' [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z) : s(a, Mem.other' h) = z := by
  induction z
  aesop (add norm unfold [Sym2.rec, Quot.rec]) (rule_sets := [Sym2])

@[simp]
/--
theorem `other_eq_other'` / 定理 `other_eq_other'`

English:
theorem other_eq_other'
  given: [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z)
  proof: by rw [← congr_right, other_spec' h, other_spec]

中文:
定理 other_eq_other'
  条件: [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z)
  证明: by rw [← congr_right, other_spec' h, other_spec]

Depends on / 依赖: congr_right, other_spec
-/
theorem other_eq_other' [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z) :
    Mem.other h = Mem.other' h := by rw [← congr_right, other_spec' h, other_spec]

/--
theorem `other_mem'` / 定理 `other_mem'`

English:
theorem other_mem'
  given: [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z)
  statement: Mem.other' h in z
  proof: by
  rw [← other_eq_other']
  exact other_mem h

中文:
定理 other_mem'
  条件: [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z)
  结论: Mem.other' h in z
  证明: by
  rw [← other_eq_other']
  exact other_mem h

Depends on / 依赖: other_eq_other, other_mem
-/
theorem other_mem' [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z) : Mem.other' h in z := by
  rw [← other_eq_other']
  exact other_mem h

/--
theorem `other_invol'` / 定理 `other_invol'`

English:
theorem other_invol'
  given: [DecidableEq α] {a : α} {z : Sym2 α} (ha : a in z) (hb : Mem.other' ha in z)
  proof: by
  induction z
  aesop (rule_sets := [Sym2]) (add norm unfold [Sym2.rec, Quot.rec])

中文:
定理 other_invol'
  条件: [DecidableEq α] {a : α} {z : Sym2 α} (ha : a in z) (hb : Mem.other' ha in z)
  证明: by
  induction z
  aesop (rule_sets := [Sym2]) (add norm unfold [Sym2.rec, Quot.rec])

Depends on / 依赖: Quot.rec, Sym2.rec, rule_sets
-/
theorem other_invol' [DecidableEq α] {a : α} {z : Sym2 α} (ha : a in z) (hb : Mem.other' ha in z) :
    Mem.other' hb = a := by
  induction z
  aesop (rule_sets := [Sym2]) (add norm unfold [Sym2.rec, Quot.rec])

/--
theorem `other_invol` / 定理 `other_invol`

English:
theorem other_invol
  given: {a : α} {z : Sym2 α} (ha : a in z) (hb : Mem.other ha in z)
  proof: by
  classical
    rw [other_eq_other'] at hb ⊢
    convert! other_invol' ha hb using 2
    apply other_eq_other'

中文:
定理 other_invol
  条件: {a : α} {z : Sym2 α} (ha : a in z) (hb : Mem.other ha in z)
  证明: by
  classical
    rw [other_eq_other'] at hb ⊢
    convert! other_invol' ha hb using 2
    apply other_eq_other'

Depends on / 依赖: classical, convert, other_eq_other, other_invol
-/
theorem other_invol {a : α} {z : Sym2 α} (ha : a in z) (hb : Mem.other ha in z) :
    Mem.other hb = a := by
  classical
    rw [other_eq_other'] at hb ⊢
    convert! other_invol' ha hb using 2
    apply other_eq_other'

/--
theorem `filter_image_mk_isDiag` / 定理 `filter_image_mk_isDiag`

English:
theorem filter_image_mk_isDiag
  given: [DecidableEq α] (s : Finset α)
  proof: by aesop

中文:
定理 filter_image_mk_isDiag
  条件: [DecidableEq α] (s : Finset α)
  证明: by aesop
-/
theorem filter_image_mk_isDiag [DecidableEq α] (s : Finset α) :
    {x in (s ×ˢ s).image Sym2.mk.uncurry | x.IsDiag} = s.diag.image Sym2.mk.uncurry := by aesop

/--
theorem `filter_image_mk_not_isDiag` / 定理 `filter_image_mk_not_isDiag`

English:
theorem filter_image_mk_not_isDiag
  given: [DecidableEq α] (s : Finset α)
  proof: by aesop

中文:
定理 filter_image_mk_not_isDiag
  条件: [DecidableEq α] (s : Finset α)
  证明: by aesop
-/
theorem filter_image_mk_not_isDiag [DecidableEq α] (s : Finset α) :
    {x in (s ×ˢ s).image Sym2.mk.uncurry | ¬x.IsDiag} = s.offDiag.image Sym2.mk.uncurry := by aesop

end Decidable

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] : Subsingleton (Sym2 α)
  body: (equivSym α).injective.subsingleton

中文:
实例 [Subsingleton
  签名: α] : Subsingleton (Sym2 α)
  定义体: (equivSym α).injective.subsingleton

Depends on / 依赖: equivSym, injective, injective.subsingleton, subsingleton
-/
instance [Subsingleton α] : Subsingleton (Sym2 α) :=
  (equivSym α).injective.subsingleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: α] : Unique (Sym2 α)
  body: Unique.mk' _

中文:
实例 [Unique
  签名: α] : Unique (Sym2 α)
  定义体: Unique.mk' _

Depends on / 依赖: Unique, Unique.mk
-/
instance [Unique α] : Unique (Sym2 α) :=
  Unique.mk' _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : IsEmpty (Sym2 α)
  body: (equivSym α).isEmpty

中文:
实例 [IsEmpty
  签名: α] : IsEmpty (Sym2 α)
  定义体: (equivSym α).isEmpty

Depends on / 依赖: equivSym, isEmpty
-/
instance [IsEmpty α] : IsEmpty (Sym2 α) :=
  (equivSym α).isEmpty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: α] : Nontrivial (Sym2 α)
  body: diag_injective.nontrivial

中文:
实例 [Nontrivial
  签名: α] : Nontrivial (Sym2 α)
  定义体: diag_injective.nontrivial

Depends on / 依赖: diag_injective, diag_injective.nontrivial, nontrivial
-/
instance [Nontrivial α] : Nontrivial (Sym2 α) :=
  diag_injective.nontrivial

-- TODO: use a sort order if available, https://github.com/leanprover-community/mathlib/issues/18166
unsafe instance [Repr α] : Repr (Sym2 α) where
  reprPrec s _ := f!"s({repr s.unquot.1}, {repr s.unquot.2})"

/--
lemma `lift_smul_lift` / 引理 `lift_smul_lift`

English:
lemma lift_smul_lift
  statement: {α R N} [SMul R N] (f : { f : α -> α -> R // forall a₁ a₂, f a₁ a₂ = f a₂ a₁ })
  proof: by
  ext ⟨i, j⟩
  simp_all only [Pi.smul_apply', lift_mk]

中文:
引理 lift_smul_lift
  结论: {α R N} [SMul R N] (f : { f : α -> α -> R // 对任意 a₁ a₂, f a₁ a₂ = f a₂ a₁ })
  证明: by
  ext ⟨i, j⟩
  simp_all only [Pi.smul_apply', lift_mk]

Depends on / 依赖: Pi.smul_apply, lift_mk, smul_apply
-/
lemma lift_smul_lift {α R N} [SMul R N] (f : { f : α -> α -> R // forall a₁ a₂, f a₁ a₂ = f a₂ a₁ })
    (g : { g : α -> α -> N // forall a₁ a₂, g a₁ a₂ = g a₂ a₁ }) :
    lift f • lift g = lift ⟨f.val • g.val, fun _ _ => by
      rw [Pi.smul_apply']; rw [Pi.smul_apply']; rw [Pi.smul_apply']; rw [Pi.smul_apply']; rw [f.prop]; rw [g.prop]⟩ := by
  ext ⟨i, j⟩
  simp_all only [Pi.smul_apply', lift_mk]

/--
Multiplication as a function from `Sym2`.
-/
@[to_additive /-- Addition as a function from `Sym2`. -/]
/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: {M} [CommMagma M]
  body: lift ⟨(· * ·), mul_comm⟩

@[to_additive (attr := simp)]

中文:
定义 mul
  签名: {M} [CommMagma M]
  定义体: lift ⟨(· * ·), mul_comm⟩

@[to_additive (attr := simp)]

Depends on / 依赖: mul_comm
-/
def mul {M} [CommMagma M] : Sym2 M -> M := lift ⟨(· * ·), mul_comm⟩

@[to_additive (attr := simp)]
/--
lemma `mul_mk` / 引理 `mul_mk`

English:
lemma mul_mk
  given: {M} [CommMagma M] (a b : M)
  statement: mul s(a, b) = a * b
  proof: rfl

中文:
引理 mul_mk
  条件: {M} [CommMagma M] (a b : M)
  结论: mul s(a, b) = a * b
  证明: rfl
-/
lemma mul_mk {M} [CommMagma M] (a b : M) : mul s(a, b) = a * b := rfl

end Sym2

namespace Set

open Sym2

variable {s : Set α}

/--
Definition of `sym2` / `sym2` 的定义

English:
definition sym2
  signature: (s : Set α)
  body: fromRel (r := fun x y => x in s ∧ y in s) ⟨fun _ _ => .symm⟩

中文:
定义 sym2
  签名: (s : Set α)
  定义体: fromRel (r := fun x y => x in s ∧ y in s) ⟨fun _ _ => .symm⟩

Depends on / 依赖: fromRel
-/
def sym2 (s : Set α) : Set (Sym2 α) := fromRel (r := fun x y => x in s ∧ y in s) ⟨fun _ _ => .symm⟩

/--
lemma `mk_mem_sym2_iff` / 引理 `mk_mem_sym2_iff`

English:
lemma mk_mem_sym2_iff
  given: {x y : α}
  statement: s(x, y) in s.sym2 ↔ x in s ∧ y in s
  proof: Iff.rfl

@[deprecated (since := "2026-02-05")] alias mk'_mem_sym2_iff := mk_mem_sym2_iff

中文:
引理 mk_mem_sym2_iff
  条件: {x y : α}
  结论: s(x, y) in s.sym2 ↔ x in s ∧ y in s
  证明: Iff.rfl

@[deprecated (since := "2026-02-05")] alias mk'_mem_sym2_iff := mk_mem_sym2_iff
-/
@[simp] lemma mk_mem_sym2_iff {x y : α} : s(x, y) in s.sym2 ↔ x in s ∧ y in s := Iff.rfl

@[deprecated (since := "2026-02-05")] alias mk'_mem_sym2_iff := mk_mem_sym2_iff

/--
lemma `mem_sym2_iff_subset` / 引理 `mem_sym2_iff_subset`

English:
lemma mem_sym2_iff_subset
  given: {z : Sym2 α}
  statement: z in s.sym2 ↔ (z : Set α) subseteq s
  proof: by
  induction z using Sym2.inductionOn
  simp [pair_subset_iff]

中文:
引理 mem_sym2_iff_subset
  条件: {z : Sym2 α}
  结论: z in s.sym2 ↔ (z : Set α) subseteq s
  证明: by
  induction z using Sym2.inductionOn
  simp [pair_subset_iff]

Depends on / 依赖: Sym2.inductionOn, inductionOn, pair_subset_iff
-/
lemma mem_sym2_iff_subset {z : Sym2 α} : z in s.sym2 ↔ (z : Set α) subseteq s := by
  induction z using Sym2.inductionOn
  simp [pair_subset_iff]

/--
lemma `sym2_eq_mk_image` / 引理 `sym2_eq_mk_image`

English:
lemma sym2_eq_mk_image
  statement: s.sym2 = (Sym2.mk.uncurry) '' s ×ˢ s
  proof: by ext ⟨x, y⟩; aesop

中文:
引理 sym2_eq_mk_image
  结论: s.sym2 = (Sym2.mk.uncurry) '' s ×ˢ s
  证明: by ext ⟨x, y⟩; aesop
-/
lemma sym2_eq_mk_image : s.sym2 = (Sym2.mk.uncurry) '' s ×ˢ s := by ext ⟨x, y⟩; aesop

/--
lemma `mk_preimage_sym2` / 引理 `mk_preimage_sym2`

English:
lemma mk_preimage_sym2
  statement: (Sym2.mk.uncurry) ⁻¹' s.sym2 = s ×ˢ s
  proof: rfl

中文:
引理 mk_preimage_sym2
  结论: (Sym2.mk.uncurry) ⁻¹' s.sym2 = s ×ˢ s
  证明: rfl
-/
@[simp] lemma mk_preimage_sym2 : (Sym2.mk.uncurry) ⁻¹' s.sym2 = s ×ˢ s := rfl

/--
lemma `sym2_empty` / 引理 `sym2_empty`

English:
lemma sym2_empty
  statement: (∅ : Set α).sym2 = ∅
  proof: by ext ⟨x, y⟩; simp

中文:
引理 sym2_empty
  结论: (∅ : Set α).sym2 = ∅
  证明: by ext ⟨x, y⟩; simp
-/
@[simp] lemma sym2_empty : (∅ : Set α).sym2 = ∅ := by ext ⟨x, y⟩; simp
/--
lemma `sym2_univ` / 引理 `sym2_univ`

English:
lemma sym2_univ
  statement: (Set.univ : Set α).sym2 = Set.univ
  proof: by ext ⟨x, y⟩; simp

中文:
引理 sym2_univ
  结论: (Set.univ : Set α).sym2 = Set.univ
  证明: by ext ⟨x, y⟩; simp
-/
@[simp] lemma sym2_univ : (Set.univ : Set α).sym2 = Set.univ := by ext ⟨x, y⟩; simp

/--
lemma `sym2_singleton` / 引理 `sym2_singleton`

English:
lemma sym2_singleton
  given: (a : α)
  statement: ({a} : Set α).sym2 = {s(a, a)}
  proof: by ext ⟨x, y⟩; simp

中文:
引理 sym2_singleton
  条件: (a : α)
  结论: ({a} : Set α).sym2 = {s(a, a)}
  证明: by ext ⟨x, y⟩; simp
-/
@[simp] lemma sym2_singleton (a : α) : ({a} : Set α).sym2 = {s(a, a)} := by ext ⟨x, y⟩; simp
/--
lemma `sym2_insert` / 引理 `sym2_insert`

English:
lemma sym2_insert
  given: (a : α) (s : Set α)
  proof: by
  ext ⟨x, y⟩; aesop

中文:
引理 sym2_insert
  条件: (a : α) (s : Set α)
  证明: by
  ext ⟨x, y⟩; aesop
-/
lemma sym2_insert (a : α) (s : Set α) :
    (insert a s).sym2 = (fun b => s(a, b)) '' insert a s union s.sym2 := by
  ext ⟨x, y⟩; aesop

/--
lemma `sym2_preimage` / 引理 `sym2_preimage`

English:
lemma sym2_preimage
  given: {f : α -> β} {s : Set β}
  statement: (f ⁻¹' s).sym2 = Sym2.map f ⁻¹' s.sym2
  proof: by
  ext ⟨x, y⟩
  simp

中文:
引理 sym2_preimage
  条件: {f : α -> β} {s : Set β}
  结论: (f ⁻¹' s).sym2 = Sym2.map f ⁻¹' s.sym2
  证明: by
  ext ⟨x, y⟩
  simp
-/
lemma sym2_preimage {f : α -> β} {s : Set β} : (f ⁻¹' s).sym2 = Sym2.map f ⁻¹' s.sym2 := by
  ext ⟨x, y⟩
  simp

/--
lemma `sym2_image` / 引理 `sym2_image`

English:
lemma sym2_image
  given: {f : α -> β} {s : Set α}
  statement: (f '' s).sym2 = Sym2.map f '' s.sym2
  proof: by
  simp_rw [sym2_eq_mk_image, prod_image_image_eq, image_image, uncurry, Sym2.map_mk]

中文:
引理 sym2_image
  条件: {f : α -> β} {s : Set α}
  结论: (f '' s).sym2 = Sym2.map f '' s.sym2
  证明: by
  simp_rw [sym2_eq_mk_image, prod_image_image_eq, image_image, uncurry, Sym2.map_mk]

Depends on / 依赖: Sym2.map_mk, image_image, map_mk, prod_image_image_eq, simp_rw, sym2_eq_mk_image, uncurry
-/
lemma sym2_image {f : α -> β} {s : Set α} : (f '' s).sym2 = Sym2.map f '' s.sym2 := by
  simp_rw [sym2_eq_mk_image, prod_image_image_eq, image_image, uncurry, Sym2.map_mk]

/--
lemma `sym2_inter` / 引理 `sym2_inter`

English:
lemma sym2_inter
  given: (s t : Set α)
  statement: (s inter t).sym2 = s.sym2 inter t.sym2
  proof: preimage_injective.mpr Sym2.mk_surjective Set.prod_inter_prod.symm

中文:
引理 sym2_inter
  条件: (s t : Set α)
  结论: (s inter t).sym2 = s.sym2 inter t.sym2
  证明: preimage_injective.mpr Sym2.mk_surjective Set.prod_inter_prod.symm

Depends on / 依赖: Set.prod_inter_prod.symm, Sym2.mk_surjective, mk_surjective, one_mem_commutatorSet, preimage_injective, preimage_injective.mpr, prod_inter_prod
-/
lemma sym2_inter (s t : Set α) : (s inter t).sym2 = s.sym2 inter t.sym2 :=
preimage_injective.mpr Sym2.mk_surjective Set.prod_inter_prod.symm

/--
lemma `sym2_iInter` / 引理 `sym2_iInter`

English:
lemma sym2_iInter
  given: {ι : Type*} (f : ι -> Set α)
  statement: (⋂ i, f i).sym2 = ⋂ i, (f i).sym2
  proof: by
  ext ⟨x, y⟩; simp [forall_and]

中文:
引理 sym2_iInter
  条件: {ι : 类型} (f : ι -> Set α)
  结论: (⋂ i, f i).sym2 = ⋂ i, (f i).sym2
  证明: by
  ext ⟨x, y⟩; simp [forall_and]

Depends on / 依赖: forall_and
-/
lemma sym2_iInter {ι : Type*} (f : ι -> Set α) : (⋂ i, f i).sym2 = ⋂ i, (f i).sym2 := by
  ext ⟨x, y⟩; simp [forall_and]

end Set
