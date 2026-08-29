/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Equivalence relations

This file defines the complete lattice of equivalence relations on a type, results about the
inductively defined equivalence closure of a binary relation, and the analogues of some isomorphism
theorems for quotients of arbitrary types.

## Implementation notes

The complete lattice instance for equivalence relations could have been defined by lifting
the Galois insertion of equivalence relations on α into binary relations on α, and then using
`CompleteLattice.copy` to define a complete lattice instance with more appropriate
definitional equalities (a similar example is `Filter.CompleteLattice` in
`Mathlib/Order/Filter/Basic.lean`). This does not save space, however, and is less clear.

Partitions are not defined as a separate structure here; users are encouraged to
reason about them using the existing `Setoid` and its infrastructure.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation
-/

@[expose] public section

attribute [refl, simp] Setoid.refl
attribute [symm] Setoid.symm
attribute [trans] Setoid.trans

variable {α β γ : Type*}

namespace Setoid

attribute [ext] ext

/--
theorem `eq_iff_rel_eq` / 定理 `eq_iff_rel_eq`

English:
theorem eq_iff_rel_eq
  given: {r₁ r₂ : Setoid α}
  statement: r₁ = r₂ ↔ ⇑r₁ = ⇑r₂
  proof: ⟨fun h => h ▸ rfl, fun h => Setoid.ext fun _ _ => h ▸ Iff.rfl⟩

中文:
定理 eq_iff_rel_eq
  条件: {r₁ r₂ : 集合等价关系 α}
  结论: r₁ = r₂ ↔ ⇑r₁ = ⇑r₂
  证明: ⟨fun h => h ▸ rfl, fun h => Setoid.ext fun _ _ => h ▸ Iff.rfl⟩

Depends on / 依赖: Iff.rfl, Setoid, Setoid.ext
-/
theorem eq_iff_rel_eq {r₁ r₂ : Setoid α} : r₁ = r₂ ↔ ⇑r₁ = ⇑r₂ :=
  ⟨fun h => h ▸ rfl, fun h => Setoid.ext fun _ _ => h ▸ Iff.rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (Setoid α)
  body: ⟨fun r s => forall ⦃x y⦄, r x y -> s x y⟩

中文:
实例 :
  签名: LE (集合等价关系 α)
  定义体: ⟨fun r s => forall ⦃x y⦄, r x y -> s x y⟩
-/
instance : LE (Setoid α) :=
  ⟨fun r s => forall ⦃x y⦄, r x y -> s x y⟩

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {r s : Setoid α}
  statement: r <= s ↔ forall {x y}, r x y -> s x y
  proof: Iff.rfl

中文:
定理 le_def
  条件: {r s : 集合等价关系 α}
  结论: r <= s ↔ 对任意 {x y}, r x y -> s x y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def {r s : Setoid α} : r <= s ↔ forall {x y}, r x y -> s x y :=
  Iff.rfl

/--
theorem `le_iff_rel_le` / 定理 `le_iff_rel_le`

English:
theorem le_iff_rel_le
  given: {r₁ r₂ : Setoid α}
  statement: r₁ <= r₂ ↔ ⇑r₁ <= ⇑r₂
  proof: Iff.rfl

@[refl]

中文:
定理 le_iff_rel_le
  条件: {r₁ r₂ : 集合等价关系 α}
  结论: r₁ <= r₂ ↔ ⇑r₁ <= ⇑r₂
  证明: Iff.rfl

@[refl]

Depends on / 依赖: Iff.rfl
-/
theorem le_iff_rel_le {r₁ r₂ : Setoid α} : r₁ <= r₂ ↔ ⇑r₁ <= ⇑r₂ := Iff.rfl

@[refl]
/--
theorem `refl'` / 定理 `refl'`

English:
theorem refl'
  given: (r : Setoid α) (x)
  statement: r x x
  proof: r.iseqv.refl x

@[symm]

中文:
定理 refl'
  条件: (r : 集合等价关系 α) (x)
  结论: r x x
  证明: r.iseqv.refl x

@[symm]

Depends on / 依赖: r.iseqv.refl
-/
theorem refl' (r : Setoid α) (x) : r x x := r.iseqv.refl x

@[symm]
/--
theorem `symm'` / 定理 `symm'`

English:
theorem symm'
  given: (r : Setoid α)
  statement: forall {x y}, r x y -> r y x
  proof: r.iseqv.symm

@[trans]

中文:
定理 symm'
  条件: (r : 集合等价关系 α)
  结论: 对任意 {x y}, r x y -> r y x
  证明: r.iseqv.symm

@[trans]

Depends on / 依赖: r.iseqv.symm
-/
theorem symm' (r : Setoid α) : forall {x y}, r x y -> r y x := r.iseqv.symm

@[trans]
/--
theorem `trans'` / 定理 `trans'`

English:
theorem trans'
  given: (r : Setoid α)
  statement: forall {x y z}, r x y -> r y z -> r x z
  proof: r.iseqv.trans

中文:
定理 trans'
  条件: (r : 集合等价关系 α)
  结论: 对任意 {x y z}, r x y -> r y z -> r x z
  证明: r.iseqv.trans

Depends on / 依赖: r.iseqv.trans
-/
theorem trans' (r : Setoid α) : forall {x y z}, r x y -> r y z -> r x z := r.iseqv.trans

/--
theorem `comm'` / 定理 `comm'`

English:
theorem comm'
  given: (s : Setoid α) {x y}
  statement: s x y ↔ s y x
  proof: ⟨s.symm', s.symm'⟩

中文:
定理 comm'
  条件: (s : 集合等价关系 α) {x y}
  结论: s x y ↔ s y x
  证明: ⟨s.symm', s.symm'⟩

Depends on / 依赖: s.symm
-/
theorem comm' (s : Setoid α) {x y} : s x y ↔ s y x :=
  ⟨s.symm', s.symm'⟩

/--
theorem `comm` / 定理 `comm`

English:
theorem comm
  given: [Setoid α] {x y : α}
  statement: x ≈ y ↔ y ≈ x
  proof: ⟨Setoid.symm, Setoid.symm⟩

中文:
定理 comm
  条件: [集合等价关系 α] {x y : α}
  结论: x ≈ y ↔ y ≈ x
  证明: ⟨Setoid.symm, Setoid.symm⟩

Depends on / 依赖: Setoid, Setoid.symm
-/
theorem comm [Setoid α] {x y : α} : x ≈ y ↔ y ≈ x :=
  ⟨Setoid.symm, Setoid.symm⟩

open scoped Function -- required for scoped `on` notation

/-- The kernel of a function is an equivalence relation. -/
@[instance_reducible]
/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: (f : α -> β)
  body: ⟨(· = ·) on f, eq_equivalence.comap f⟩

中文:
定义 ker
  签名: (f : α -> β)
  定义体: ⟨(· = ·) on f, eq_equivalence.comap f⟩

Depends on / 依赖: eq_equivalence, eq_equivalence.comap
-/
def ker (f : α -> β) : Setoid α :=
  ⟨(· = ·) on f, eq_equivalence.comap f⟩

/-- The kernel of the quotient map induced by an equivalence relation r equals r. -/
@[simp]
/--
theorem `ker_mk_eq` / 定理 `ker_mk_eq`

English:
theorem ker_mk_eq
  given: (r : Setoid α)
  statement: ker (@Quotient.mk'' _ r) = r
  proof: ext fun _ _ => Quotient.eq

中文:
定理 ker_mk_eq
  条件: (r : 集合等价关系 α)
  结论: ker (@商.mk'' _ r) = r
  证明: ext fun _ _ => Quotient.eq

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem ker_mk_eq (r : Setoid α) : ker (@Quotient.mk'' _ r) = r :=
  ext fun _ _ => Quotient.eq

/--
theorem `ker_apply_mk_out` / 定理 `ker_apply_mk_out`

English:
theorem ker_apply_mk_out
  given: {f : α -> β} (a : α)
  statement: f (⟦a⟧ : Quotient (Setoid.ker f)).out = f a
  proof: @Quotient.mk_out _ (Setoid.ker f) a

@[simp]

中文:
定理 ker_apply_mk_out
  条件: {f : α -> β} (a : α)
  结论: f (⟦a⟧ : 商 (集合等价关系.ker f)).out = f a
  证明: @Quotient.mk_out _ (Setoid.ker f) a

@[simp]

Depends on / 依赖: Quotient, Quotient.mk_out, Setoid, Setoid.ker, mk_out
-/
theorem ker_apply_mk_out {f : α -> β} (a : α) : f (⟦a⟧ : Quotient (Setoid.ker f)).out = f a :=
  @Quotient.mk_out _ (Setoid.ker f) a

@[simp]
/--
theorem `ker_def` / 定理 `ker_def`

English:
theorem ker_def
  given: {f : α -> β} {x y : α}
  statement: ker f x y ↔ f x = f y
  proof: Iff.rfl

中文:
定理 ker_def
  条件: {f : α -> β} {x y : α}
  结论: ker f x y ↔ f x = f y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem ker_def {f : α -> β} {x y : α} : ker f x y ↔ f x = f y :=
  Iff.rfl

/-- Given types `α`, `β`, the product of two equivalence relations `r` on `α` and `s` on `β`:
`(x₁, x₂), (y₁, y₂) ∈ α × β` are related by `r.prod s` iff `x₁` is related to `y₁`
by `r` and `x₂` is related to `y₂` by `s`. -/
@[instance_reducible]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (r : Setoid α) (s : Setoid β)
  body: r x.1 y.1 ∧ s x.2 y.2
  iseqv :=
    ⟨fun x => ⟨r.refl' x.1, s.refl' x.2⟩, fun h => ⟨r.symm' h.1, s.symm' h.2⟩,
      fun h₁ h₂ => ⟨r.trans' h₁.1 h₂.1, s.trans' h₁.2 h₂.2⟩⟩

中文:
定义 乘积
  签名: (r : 集合等价关系 α) (s : 集合等价关系 β)
  定义体: r x.1 y.1 ∧ s x.2 y.2
  iseqv :=
    ⟨fun x => ⟨r.refl' x.1, s.refl' x.2⟩, fun h => ⟨r.symm' h.1, s.symm' h.2⟩,
      fun h₁ h₂ => ⟨r.trans' h₁.1 h₂.1, s.trans' h₁.2 h₂.2⟩⟩
-/
protected def prod (r : Setoid α) (s : Setoid β) :
    Setoid (α × β) where
  r x y := r x.1 y.1 ∧ s x.2 y.2
  iseqv :=
    ⟨fun x => ⟨r.refl' x.1, s.refl' x.2⟩, fun h => ⟨r.symm' h.1, s.symm' h.2⟩,
      fun h₁ h₂ => ⟨r.trans' h₁.1 h₂.1, s.trans' h₁.2 h₂.2⟩⟩

/--
lemma `prod_apply` / 引理 `prod_apply`

English:
lemma prod_apply
  given: {r : Setoid α} {s : Setoid β} {x₁ x₂ : α} {y₁ y₂ : β}
  proof: Iff.rfl

中文:
引理 prod_apply
  条件: {r : 集合等价关系 α} {s : 集合等价关系 β} {x₁ x₂ : α} {y₁ y₂ : β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma prod_apply {r : Setoid α} {s : Setoid β} {x₁ x₂ : α} {y₁ y₂ : β} :
    @Setoid.r _ (r.prod s) (x₁, y₁) (x₂, y₂) ↔ (@Setoid.r _ r x₁ x₂ ∧ @Setoid.r _ s y₁ y₂) :=
  Iff.rfl

/--
lemma `piSetoid_apply` / 引理 `piSetoid_apply`

English:
lemma piSetoid_apply
  given: {ι : Sort*} {α : ι -> Sort*} {r : forall i, Setoid (α i)} {x y : forall i, α i}
  proof: Iff.rfl

中文:
引理 piSetoid_apply
  条件: {ι : 类型层*} {α : ι -> 类型层*} {r : 对任意 i, 集合等价关系 (α i)} {x y : 对任意 i, α i}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma piSetoid_apply {ι : Sort*} {α : ι -> Sort*} {r : forall i, Setoid (α i)} {x y : forall i, α i} :
    @Setoid.r _ (@piSetoid _ _ r) x y ↔ forall i, @Setoid.r _ (r i) (x i) (y i) :=
  Iff.rfl

/-- A bijection between the product of two quotients and the quotient by the product of the
equivalence relations. -/
@[simps]
/--
Definition of `prodQuotientEquiv` / `prodQuotientEquiv` 的定义

English:
definition prodQuotientEquiv
  signature: (r : Setoid α) (s : Setoid β)
  body: Quotient.liftOn' q (fun xy => (Quotient.mk'' xy.1, Quotient.mk'' xy.2))
    fun x y hxy => Prod.ext (by simpa [Quotient.eq] using hxy.1) (by simpa [Quotient.eq] using hxy.2)
  left_inv q := by
    rcases q with ⟨qa, qb⟩
    induction qa, qb using Quotient.inductionOn₂'
    rfl
  right_inv q := by in

中文:
定义 prodQuotientEquiv
  签名: (r : 集合等价关系 α) (s : 集合等价关系 β)
  定义体: Quotient.liftOn' q (fun xy => (Quotient.mk'' xy.1, Quotient.mk'' xy.2))
    fun x y hxy => Prod.ext (by simpa [Quotient.eq] using hxy.1) (by simpa [Quotient.eq] using hxy.2)
  left_inv q := by
    rcases q with ⟨qa, qb⟩
    induction qa, qb using Quotient.inductionOn₂'
    rfl
  right_inv q := by in

Depends on / 依赖: Quotient, Quotient.liftOn, Quotient.mk, liftOn
-/
def prodQuotientEquiv (r : Setoid α) (s : Setoid β) :
    Quotient r × Quotient s ≃ Quotient (r.prod s) where
  toFun | (x, y) => Quotient.map₂ Prod.mk (fun _ _ hx _ _ hy => ⟨hx, hy⟩) x y
  invFun q := Quotient.liftOn' q (fun xy => (Quotient.mk'' xy.1, Quotient.mk'' xy.2))
    fun x y hxy => Prod.ext (by simpa [Quotient.eq] using hxy.1) (by simpa [Quotient.eq] using hxy.2)
  left_inv q := by
    rcases q with ⟨qa, qb⟩
    induction qa, qb using Quotient.inductionOn₂'
    rfl
  right_inv q := by induction q using Quotient.inductionOn'; rfl

/-- A bijection between an indexed product of quotients and the quotient by the product of the
equivalence relations. -/
@[simps]
/--
Definition of `piQuotientEquiv` / `piQuotientEquiv` 的定义

English:
definition piQuotientEquiv
  signature: {ι : Sort*} {α : ι -> Sort*} (r : forall i, Setoid (α i))
  body: Quotient.mk'' fun i => (x i).out
  invFun q := Quotient.liftOn' q (fun x i => Quotient.mk'' (x i)) fun x y hxy => by
    ext i
    simpa [Quotient.eq] using hxy i
  left_inv q := by
    ext i
    simp
  right_inv q := by
    induction q using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'

中文:
定义 piQuotientEquiv
  签名: {ι : 类型层*} {α : ι -> 类型层*} (r : 对任意 i, 集合等价关系 (α i))
  定义体: Quotient.mk'' fun i => (x i).out
  invFun q := Quotient.liftOn' q (fun x i => Quotient.mk'' (x i)) fun x y hxy => by
    ext i
    simpa [Quotient.eq] using hxy i
  left_inv q := by
    ext i
    simp
  right_inv q := by
    induction q using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'

Depends on / 依赖: Quotient, Quotient.mk
-/
noncomputable def piQuotientEquiv {ι : Sort*} {α : ι -> Sort*} (r : forall i, Setoid (α i)) :
    (forall i, Quotient (r i)) ≃ Quotient (@piSetoid _ _ r) where
  toFun x := Quotient.mk'' fun i => (x i).out
  invFun q := Quotient.liftOn' q (fun x i => Quotient.mk'' (x i)) fun x y hxy => by
    ext i
    simpa [Quotient.eq] using hxy i
  left_inv q := by
    ext i
    simp
  right_inv q := by
    induction q using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'', Quotient.eq'']
    intro i
    change Setoid.r _ _
    rw [← Quotient.eq'']
    simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Setoid α)
  body: ⟨fun r s =>
    ⟨fun x y => r x y ∧ s x y,
      ⟨fun x => ⟨r.refl' x, s.refl' x⟩, fun h => ⟨r.symm' h.1, s.symm' h.2⟩, fun h1 h2 =>
        ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩⟩

中文:
实例 :
  签名: 最小值 (集合等价关系 α)
  定义体: ⟨fun r s =>
    ⟨fun x y => r x y ∧ s x y,
      ⟨fun x => ⟨r.refl' x, s.refl' x⟩, fun h => ⟨r.symm' h.1, s.symm' h.2⟩, fun h1 h2 =>
        ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩⟩

Depends on / 依赖: r.refl, r.symm, r.trans, s.refl, s.symm, s.trans
-/
instance : Min (Setoid α) :=
  ⟨fun r s =>
    ⟨fun x y => r x y ∧ s x y,
      ⟨fun x => ⟨r.refl' x, s.refl' x⟩, fun h => ⟨r.symm' h.1, s.symm' h.2⟩, fun h1 h2 =>
        ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩⟩

/--
theorem `inf_def` / 定理 `inf_def`

English:
theorem inf_def
  given: {r s : Setoid α}
  statement: ⇑(r ⊓ s) = ⇑r ⊓ ⇑s
  proof: rfl

中文:
定理 inf_def
  条件: {r s : 集合等价关系 α}
  结论: ⇑(r ⊓ s) = ⇑r ⊓ ⇑s
  证明: rfl
-/
theorem inf_def {r s : Setoid α} : ⇑(r ⊓ s) = ⇑r ⊓ ⇑s :=
  rfl

/--
theorem `inf_iff_and` / 定理 `inf_iff_and`

English:
theorem inf_iff_and
  given: {r s : Setoid α} {x y}
  statement: (r ⊓ s) x y ↔ r x y ∧ s x y
  proof: Iff.rfl

中文:
定理 inf_iff_and
  条件: {r s : 集合等价关系 α} {x y}
  结论: (r ⊓ s) x y ↔ r x y ∧ s x y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem inf_iff_and {r s : Setoid α} {x y} : (r ⊓ s) x y ↔ r x y ∧ s x y :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Setoid α)
  body: ⟨fun S =>
    { r := fun x y => forall r in S, r x y
iseqv := ⟨fun x r _ => r.refl' x, fun h r hr => r.symm' h r hr, fun h1 h2 r hr =>
r.trans' (h1 r hr) h2 r hr⟩ }⟩

中文:
实例 :
  签名: 下确界集 (集合等价关系 α)
  定义体: ⟨fun S =>
    { r := fun x y => forall r in S, r x y
iseqv := ⟨fun x r _ => r.refl' x, fun h r hr => r.symm' h r hr, fun h1 h2 r hr =>
r.trans' (h1 r hr) h2 r hr⟩ }⟩

Depends on / 依赖: r.refl, r.symm, r.trans
-/
instance : InfSet (Setoid α) :=
  ⟨fun S =>
    { r := fun x y => forall r in S, r x y
iseqv := ⟨fun x r _ => r.refl' x, fun h r hr => r.symm' h r hr, fun h1 h2 r hr =>
r.trans' (h1 r hr) h2 r hr⟩ }⟩

/--
theorem `sInf_def` / 定理 `sInf_def`

English:
theorem sInf_def
  given: {s : Set (Setoid α)}
  statement: ⇑(sInf s) = sInf ((⇑) '' s)
  proof: by
  ext
  simp only [sInf_image, iInf_apply, iInf_Prop_eq]
  rfl

中文:
定理 sInf_def
  条件: {s : 集合 (集合等价关系 α)}
  结论: ⇑(sInf s) = sInf ((⇑) '' s)
  证明: by
  ext
  simp only [sInf_image, iInf_apply, iInf_Prop_eq]
  rfl

Depends on / 依赖: iInf_Prop_eq, iInf_apply, sInf_image
-/
theorem sInf_def {s : Set (Setoid α)} : ⇑(sInf s) = sInf ((⇑) '' s) := by
  ext
  simp only [sInf_image, iInf_apply, iInf_Prop_eq]
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Setoid α)
  body: r <= s ∧ ¬s <= r
  le_refl _ _ _ := id
le_trans _ _ _ hr hs _ _ h := hs hr h
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm _ _ h1 h2 := Setoid.ext fun _ _ => ⟨fun h => h1 h, fun h => h2 h⟩

中文:
实例 :
  签名: 偏序 (集合等价关系 α)
  定义体: r <= s ∧ ¬s <= r
  le_refl _ _ _ := id
le_trans _ _ _ hr hs _ _ h := hs hr h
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm _ _ h1 h2 := Setoid.ext fun _ _ => ⟨fun h => h1 h, fun h => h2 h⟩
-/
instance : PartialOrder (Setoid α) where
  lt r s := r <= s ∧ ¬s <= r
  le_refl _ _ _ := id
le_trans _ _ _ hr hs _ _ h := hs hr h
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm _ _ h1 h2 := Setoid.ext fun _ _ => ⟨fun h => h1 h, fun h => h2 h⟩

/--
Instance `completeLattice` / 实例 `completeLattice`

English:
instance completeLattice
  signature: : CompleteLattice (Setoid α)
  body: { (completeLatticeOfInf (Setoid α)) fun _ =>
      ⟨fun _ hr _ _ h => h _ hr, fun _ hr _ _ h _ hr' => hr hr' h⟩ with
    inf := Min.min
    inf_le_left := fun _ _ _ _ h => h.1
    inf_le_right := fun _ _ _ _ h => h.2
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 h, h2 h⟩
    top := ⟨fun _ _ => True, ⟨f

中文:
实例 completeLattice
  签名: : 完备格 (集合等价关系 α)
  定义体: { (completeLatticeOfInf (Setoid α)) fun _ =>
      ⟨fun _ hr _ _ h => h _ hr, fun _ hr _ _ h _ hr' => hr hr' h⟩ with
    inf := Min.min
    inf_le_left := fun _ _ _ _ h => h.1
    inf_le_right := fun _ _ _ _ h => h.2
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 h, h2 h⟩
    top := ⟨fun _ _ => True, ⟨f

Depends on / 依赖: Min.min, Setoid, bot_le, completeLatticeOfInf, h.symm, h1.trans, inf_le_left, inf_le_right, le_inf, le_top
-/
instance completeLattice : CompleteLattice (Setoid α) :=
  { (completeLatticeOfInf (Setoid α)) fun _ =>
      ⟨fun _ hr _ _ h => h _ hr, fun _ hr _ _ h _ hr' => hr hr' h⟩ with
    inf := Min.min
    inf_le_left := fun _ _ _ _ h => h.1
    inf_le_right := fun _ _ _ _ h => h.2
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 h, h2 h⟩
    top := ⟨fun _ _ => True, ⟨fun _ => trivial, fun h => h, fun h1 _ => h1⟩⟩
    le_top := fun _ _ _ _ => trivial
    bot := ⟨(· = ·), ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩
    bot_le := fun r x _ h => h ▸ r.2.1 x }

@[simp, grind =]
/--
theorem `top_def` / 定理 `top_def`

English:
theorem top_def
  statement: ⇑(⊤ : Setoid α) = ⊤
  proof: rfl

@[simp, grind =]

中文:
定理 top_def
  结论: ⇑(⊤ : 集合等价关系 α) = ⊤
  证明: rfl

@[simp, grind =]
-/
theorem top_def : ⇑(⊤ : Setoid α) = ⊤ :=
  rfl

@[simp, grind =]
/--
theorem `bot_def` / 定理 `bot_def`

English:
theorem bot_def
  statement: ⇑(⊥ : Setoid α) = (· = ·)
  proof: rfl

中文:
定理 bot_def
  结论: ⇑(⊥ : 集合等价关系 α) = (· = ·)
  证明: rfl
-/
theorem bot_def : ⇑(⊥ : Setoid α) = (· = ·) :=
  rfl

/--
lemma `mk_eq_top` / 引理 `mk_eq_top`

English:
lemma mk_eq_top
  given: {r : α -> α -> Prop} (iseqv)
  statement: mk r iseqv = ⊤ ↔ r = ⊤
  proof: by
  simp [eq_iff_rel_eq]

中文:
引理 mk_eq_top
  条件: {r : α -> α -> 命题} (iseqv)
  结论: mk r iseqv = ⊤ ↔ r = ⊤
  证明: by
  simp [eq_iff_rel_eq]
-/
@[simp] lemma mk_eq_top {r : α -> α -> Prop} (iseqv) : mk r iseqv = ⊤ ↔ r = ⊤ := by
  simp [eq_iff_rel_eq]

/--
lemma `mk_eq_bot` / 引理 `mk_eq_bot`

English:
lemma mk_eq_bot
  given: {r : α -> α -> Prop} (iseqv)
  statement: mk r iseqv = ⊥ ↔ r = (· = ·)
  proof: by
  simp [eq_iff_rel_eq]

中文:
引理 mk_eq_bot
  条件: {r : α -> α -> 命题} (iseqv)
  结论: mk r iseqv = ⊥ ↔ r = (· = ·)
  证明: by
  simp [eq_iff_rel_eq]
-/
@[simp] lemma mk_eq_bot {r : α -> α -> Prop} (iseqv) : mk r iseqv = ⊥ ↔ r = (· = ·) := by
  simp [eq_iff_rel_eq]

/--
theorem `eq_top_iff` / 定理 `eq_top_iff`

English:
theorem eq_top_iff
  given: {s : Setoid α}
  statement: s = (⊤ : Setoid α) ↔ forall x y : α, s x y
  proof: by
  rw [_root_.eq_top_iff]; rw [Setoid.le_def]; rw [Setoid.top_def]
  simp only [Pi.top_apply, Prop.top_eq_true, forall_true_left]

@[simp]

中文:
定理 eq_top_iff
  条件: {s : 集合等价关系 α}
  结论: s = (⊤ : 集合等价关系 α) ↔ 对任意 x y : α, s x y
  证明: by
  rw [_root_.eq_top_iff]; rw [Setoid.le_def]; rw [Setoid.top_def]
  simp only [Pi.top_apply, Prop.top_eq_true, forall_true_left]

@[simp]

Depends on / 依赖: Pi.top_apply, Prop.top_eq_true, Setoid, Setoid.le_def, Setoid.top_def, _root_, _root_.eq_top_iff, eq_top_iff, forall_true_left, le_def, top_apply, top_def, top_eq_true
-/
theorem eq_top_iff {s : Setoid α} : s = (⊤ : Setoid α) ↔ forall x y : α, s x y := by
  rw [_root_.eq_top_iff]; rw [Setoid.le_def]; rw [Setoid.top_def]
  simp only [Pi.top_apply, Prop.top_eq_true, forall_true_left]

@[simp]
/--
theorem `ker_eq_bot_iff` / 定理 `ker_eq_bot_iff`

English:
theorem ker_eq_bot_iff
  given: {f : α -> β}
  statement: ker f = ⊥ ↔ f.Injective
  proof: le_bot_iff.symm

中文:
定理 ker_eq_bot_iff
  条件: {f : α -> β}
  结论: ker f = ⊥ ↔ f.单射
  证明: le_bot_iff.symm

Depends on / 依赖: le_bot_iff, le_bot_iff.symm
-/
theorem ker_eq_bot_iff {f : α -> β} : ker f = ⊥ ↔ f.Injective := le_bot_iff.symm

/--
lemma `sInf_equiv` / 引理 `sInf_equiv`

English:
lemma sInf_equiv
  given: {S : Set (Setoid α)} {x y : α}
  proof: sInf S
    x ≈ y ↔ forall s in S, s x y := Iff.rfl

中文:
引理 sInf_equiv
  条件: {S : 集合 (集合等价关系 α)} {x y : α}
  证明: sInf S
    x ≈ y ↔ forall s in S, s x y := Iff.rfl
-/
lemma sInf_equiv {S : Set (Setoid α)} {x y : α} :
    letI := sInf S
    x ≈ y ↔ forall s in S, s x y := Iff.rfl

/--
lemma `sInf_iff` / 引理 `sInf_iff`

English:
lemma sInf_iff
  given: {S : Set (Setoid α)} {x y : α}
  proof: Iff.rfl

中文:
引理 sInf_iff
  条件: {S : 集合 (集合等价关系 α)} {x y : α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma sInf_iff {S : Set (Setoid α)} {x y : α} :
    sInf S x y ↔ forall s in S, s x y := Iff.rfl

/--
lemma `quotient_mk_sInf_eq` / 引理 `quotient_mk_sInf_eq`

English:
lemma quotient_mk_sInf_eq
  given: {S : Set (Setoid α)} {x y : α}
  proof: by
  simp [sInf_iff, Quotient.eq]

中文:
引理 quotient_mk_sInf_eq
  条件: {S : 集合 (集合等价关系 α)} {x y : α}
  证明: by
  simp [sInf_iff, Quotient.eq]

Depends on / 依赖: Quotient, Quotient.eq, sInf_iff
-/
lemma quotient_mk_sInf_eq {S : Set (Setoid α)} {x y : α} :
    Quotient.mk (sInf S) x = Quotient.mk (sInf S) y ↔ forall s in S, s x y := by
  simp [sInf_iff, Quotient.eq]

/--
Definition of `map_of_le` / `map_of_le` 的定义

English:
definition map_of_le
  signature: {s t : Setoid α} (h : s <= t)
  body: Quotient.map' id h

中文:
定义 map_of_le
  签名: {s t : 集合等价关系 α} (h : s <= t)
  定义体: Quotient.map' id h

Depends on / 依赖: Quotient, Quotient.map
-/
def map_of_le {s t : Setoid α} (h : s <= t) : Quotient s -> Quotient t :=
  Quotient.map' id h

/--
Definition of `map_sInf` / `map_sInf` 的定义

English:
definition map_sInf
  signature: {S : Set (Setoid α)} {s : Setoid α} (h : s in S)
  body: Setoid.map_of_le fun _ _ a => a s h

中文:
定义 map_sInf
  签名: {S : 集合 (集合等价关系 α)} {s : 集合等价关系 α} (h : s in S)
  定义体: Setoid.map_of_le fun _ _ a => a s h

Depends on / 依赖: Setoid, Setoid.map_of_le, map_of_le
-/
def map_sInf {S : Set (Setoid α)} {s : Setoid α} (h : s in S) :
    Quotient (sInf S) -> Quotient s :=
  Setoid.map_of_le fun _ _ a => a s h

/--
Definition of `quotientBotEquiv` / `quotientBotEquiv` 的定义

English:
definition quotientBotEquiv
  signature: :
  body: Quotient.lift id (fun _ _ => id)
  invFun := Quotient.mk''
  left_inv := Quotient.ind fun _ => rfl
  right_inv := fun _ => rfl

中文:
定义 quotientBotEquiv
  签名: :
  定义体: Quotient.lift id (fun _ _ => id)
  invFun := Quotient.mk''
  left_inv := Quotient.ind fun _ => rfl
  right_inv := fun _ => rfl

Depends on / 依赖: Quotient, Quotient.lift
-/
def quotientBotEquiv :
    Quotient (⊥ : Setoid α) ≃ α where
  toFun := Quotient.lift id (fun _ _ => id)
  invFun := Quotient.mk''
  left_inv := Quotient.ind fun _ => rfl
  right_inv := fun _ => rfl

section EqvGen

open Relation

/--
theorem `eqvGen_eq` / 定理 `eqvGen_eq`

English:
theorem eqvGen_eq
  given: (r : α -> α -> Prop)
  proof: le_antisymm
    (fun _ _ H =>
      EqvGen.rec (fun _ _ h _ hs => hs h) (refl' _) (fun _ _ _ => symm' _)
        (fun _ _ _ _ _ => trans' _) H)
    (sInf_le fun _ _ h => EqvGen.rel _ _ h)

中文:
定理 eqvGen_eq
  条件: (r : α -> α -> 命题)
  证明: le_antisymm
    (fun _ _ H =>
      EqvGen.rec (fun _ _ h _ hs => hs h) (refl' _) (fun _ _ _ => symm' _)
        (fun _ _ _ _ _ => trans' _) H)
    (sInf_le fun _ _ h => EqvGen.rel _ _ h)

Depends on / 依赖: EqvGen, EqvGen.rec, EqvGen.rel, le_antisymm, sInf_le
-/
theorem eqvGen_eq (r : α -> α -> Prop) :
    EqvGen.setoid r = sInf { s : Setoid α | forall ⦃x y⦄, r x y -> s x y } :=
  le_antisymm
    (fun _ _ H =>
      EqvGen.rec (fun _ _ h _ hs => hs h) (refl' _) (fun _ _ _ => symm' _)
        (fun _ _ _ _ _ => trans' _) H)
    (sInf_le fun _ _ h => EqvGen.rel _ _ h)

/--
theorem `sup_eq_eqvGen` / 定理 `sup_eq_eqvGen`

English:
theorem sup_eq_eqvGen
  given: (r s : Setoid α)
  proof: by
  rw [eqvGen_eq]
  apply congr_arg sInf
  simp only [le_def, or_imp, ← forall_and]

中文:
定理 sup_eq_eqvGen
  条件: (r s : 集合等价关系 α)
  证明: by
  rw [eqvGen_eq]
  apply congr_arg sInf
  simp only [le_def, or_imp, ← forall_and]

Depends on / 依赖: congr_arg, eqvGen_eq, forall_and, le_def, or_imp
-/
theorem sup_eq_eqvGen (r s : Setoid α) :
    r ⊔ s = EqvGen.setoid fun x y => r x y ∨ s x y := by
  rw [eqvGen_eq]
  apply congr_arg sInf
  simp only [le_def, or_imp, ← forall_and]

/--
theorem `sup_def` / 定理 `sup_def`

English:
theorem sup_def
  given: {r s : Setoid α}
  statement: r ⊔ s = EqvGen.setoid (⇑r ⊔ ⇑s)
  proof: by
  rw [sup_eq_eqvGen]; rfl

中文:
定理 sup_def
  条件: {r s : 集合等价关系 α}
  结论: r ⊔ s = EqvGen.setoid (⇑r ⊔ ⇑s)
  证明: by
  rw [sup_eq_eqvGen]; rfl

Depends on / 依赖: sup_eq_eqvGen
-/
theorem sup_def {r s : Setoid α} : r ⊔ s = EqvGen.setoid (⇑r ⊔ ⇑s) := by
  rw [sup_eq_eqvGen]; rfl

/--
theorem `sSup_eq_eqvGen` / 定理 `sSup_eq_eqvGen`

English:
theorem sSup_eq_eqvGen
  given: (S : Set (Setoid α))
  proof: by
  rw [eqvGen_eq]
  apply congr_arg sInf
  simp only [upperBounds, le_def, and_imp, exists_imp]
  ext
  exact ⟨fun H x y r hr => H hr, fun H r hr x y => H r hr⟩

中文:
定理 sSup_eq_eqvGen
  条件: (S : 集合 (集合等价关系 α))
  证明: by
  rw [eqvGen_eq]
  apply congr_arg sInf
  simp only [upperBounds, le_def, and_imp, exists_imp]
  ext
  exact ⟨fun H x y r hr => H hr, fun H r hr x y => H r hr⟩

Depends on / 依赖: and_imp, congr_arg, eqvGen_eq, exists_imp, le_def, upperBounds
-/
theorem sSup_eq_eqvGen (S : Set (Setoid α)) :
    sSup S = EqvGen.setoid fun x y => exists r : Setoid α, r in S ∧ r x y := by
  rw [eqvGen_eq]
  apply congr_arg sInf
  simp only [upperBounds, le_def, and_imp, exists_imp]
  ext
  exact ⟨fun H x y r hr => H hr, fun H r hr x y => H r hr⟩

/--
theorem `sSup_def` / 定理 `sSup_def`

English:
theorem sSup_def
  given: {s : Set (Setoid α)}
  statement: sSup s = EqvGen.setoid (sSup ((⇑) '' s))
  proof: by
  rw [sSup_eq_eqvGen]; rw [sSup_image]
  congr with (x y)
  simp only [iSup_apply, iSup_Prop_eq, exists_prop]

中文:
定理 sSup_def
  条件: {s : 集合 (集合等价关系 α)}
  结论: sSup s = EqvGen.setoid (sSup ((⇑) '' s))
  证明: by
  rw [sSup_eq_eqvGen]; rw [sSup_image]
  congr with (x y)
  simp only [iSup_apply, iSup_Prop_eq, exists_prop]

Depends on / 依赖: exists_prop, iSup_Prop_eq, iSup_apply, sSup_eq_eqvGen, sSup_image
-/
theorem sSup_def {s : Set (Setoid α)} : sSup s = EqvGen.setoid (sSup ((⇑) '' s)) := by
  rw [sSup_eq_eqvGen]; rw [sSup_image]
  congr with (x y)
  simp only [iSup_apply, iSup_Prop_eq, exists_prop]

/-- The equivalence closure of an equivalence relation r is r. -/
@[simp]
/--
theorem `eqvGen_of_setoid` / 定理 `eqvGen_of_setoid`

English:
theorem eqvGen_of_setoid
  given: (r : Setoid α)
  statement: EqvGen.setoid r.r = r
  proof: le_antisymm (by rw [eqvGen_eq]; exact sInf_le fun _ _ => id) EqvGen.rel

中文:
定理 eqvGen_of_setoid
  条件: (r : 集合等价关系 α)
  结论: EqvGen.setoid r.r = r
  证明: le_antisymm (by rw [eqvGen_eq]; exact sInf_le fun _ _ => id) EqvGen.rel

Depends on / 依赖: EqvGen, EqvGen.rel, eqvGen_eq, le_antisymm, sInf_le
-/
theorem eqvGen_of_setoid (r : Setoid α) : EqvGen.setoid r.r = r :=
  le_antisymm (by rw [eqvGen_eq]; exact sInf_le fun _ _ => id) EqvGen.rel

/--
theorem `eqvGen_idem` / 定理 `eqvGen_idem`

English:
theorem eqvGen_idem
  given: (r : α -> α -> Prop)
  statement: EqvGen.setoid (EqvGen.setoid r) = EqvGen.setoid r
  proof: eqvGen_of_setoid _

中文:
定理 eqvGen_idem
  条件: (r : α -> α -> 命题)
  结论: EqvGen.setoid (EqvGen.setoid r) = EqvGen.setoid r
  证明: eqvGen_of_setoid _

Depends on / 依赖: eqvGen_of_setoid
-/
theorem eqvGen_idem (r : α -> α -> Prop) : EqvGen.setoid (EqvGen.setoid r) = EqvGen.setoid r :=
  eqvGen_of_setoid _

/--
theorem `eqvGen_le` / 定理 `eqvGen_le`

English:
theorem eqvGen_le
  given: {r : α -> α -> Prop} {s : Setoid α} (h : forall x y, r x y -> s x y)
  proof: by rw [eqvGen_eq]; exact sInf_le h

中文:
定理 eqvGen_le
  条件: {r : α -> α -> 命题} {s : 集合等价关系 α} (h : 对任意 x y, r x y -> s x y)
  证明: by rw [eqvGen_eq]; exact sInf_le h

Depends on / 依赖: eqvGen_eq, sInf_le
-/
theorem eqvGen_le {r : α -> α -> Prop} {s : Setoid α} (h : forall x y, r x y -> s x y) :
    EqvGen.setoid r <= s := by rw [eqvGen_eq]; exact sInf_le h

/--
theorem `eqvGen_mono` / 定理 `eqvGen_mono`

English:
theorem eqvGen_mono
  given: {r s : α -> α -> Prop} (h : forall x y, r x y -> s x y)
  proof: eqvGen_le fun _ _ hr => EqvGen.rel _ _ h _ _ hr

中文:
定理 eqvGen_mono
  条件: {r s : α -> α -> 命题} (h : 对任意 x y, r x y -> s x y)
  证明: eqvGen_le fun _ _ hr => EqvGen.rel _ _ h _ _ hr

Depends on / 依赖: EqvGen, EqvGen.rel, eqvGen_le
-/
theorem eqvGen_mono {r s : α -> α -> Prop} (h : forall x y, r x y -> s x y) :
    EqvGen.setoid r <= EqvGen.setoid s :=
eqvGen_le fun _ _ hr => EqvGen.rel _ _ h _ _ hr

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : @GaloisInsertion (α -> α -> Prop) (Setoid α) _ _ EqvGen.setoid (⇑) where
  body: EqvGen.setoid r
gc _ s := ⟨fun H _ _ h => H EqvGen.rel _ _ h, fun H => eqvGen_of_setoid s ▸ eqvGen_mono H⟩
  le_l_u x := (eqvGen_of_setoid x).symm ▸ le_refl x
  choice_eq _ _ := rfl

中文:
定义 gi
  签名: : @Galois嵌入 (α -> α -> 命题) (集合等价关系 α) _ _ EqvGen.setoid (⇑) where
  定义体: EqvGen.setoid r
gc _ s := ⟨fun H _ _ h => H EqvGen.rel _ _ h, fun H => eqvGen_of_setoid s ▸ eqvGen_mono H⟩
  le_l_u x := (eqvGen_of_setoid x).symm ▸ le_refl x
  choice_eq _ _ := rfl

Depends on / 依赖: EqvGen, EqvGen.setoid, setoid
-/
def gi : @GaloisInsertion (α -> α -> Prop) (Setoid α) _ _ EqvGen.setoid (⇑) where
  choice r _ := EqvGen.setoid r
gc _ s := ⟨fun H _ _ h => H EqvGen.rel _ _ h, fun H => eqvGen_of_setoid s ▸ eqvGen_mono H⟩
  le_l_u x := (eqvGen_of_setoid x).symm ▸ le_refl x
  choice_eq _ _ := rfl

end EqvGen

open Function

/--
theorem `injective_iff_ker_bot` / 定理 `injective_iff_ker_bot`

English:
theorem injective_iff_ker_bot
  given: (f : α -> β)
  statement: Injective f ↔ ker f = ⊥
  proof: (@eq_bot_iff (Setoid α) _ _ (ker f)).symm

中文:
定理 injective_iff_ker_bot
  条件: (f : α -> β)
  结论: 单射 f ↔ ker f = ⊥
  证明: (@eq_bot_iff (Setoid α) _ _ (ker f)).symm

Depends on / 依赖: Setoid, eq_bot_iff
-/
theorem injective_iff_ker_bot (f : α -> β) : Injective f ↔ ker f = ⊥ :=
  (@eq_bot_iff (Setoid α) _ _ (ker f)).symm

/--
theorem `ker_iff_mem_preimage` / 定理 `ker_iff_mem_preimage`

English:
theorem ker_iff_mem_preimage
  given: {f : α -> β} {x y}
  statement: ker f x y ↔ x in f ⁻¹' {f y}
  proof: Iff.rfl

中文:
定理 ker_iff_mem_preimage
  条件: {f : α -> β} {x y}
  结论: ker f x y ↔ x in f ⁻¹' {f y}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem ker_iff_mem_preimage {f : α -> β} {x y} : ker f x y ↔ x in f ⁻¹' {f y} :=
  Iff.rfl

/--
Definition of `liftEquiv` / `liftEquiv` 的定义

English:
definition liftEquiv
  signature: (r : Setoid α)
  body: Quotient.lift (f : α -> β) f.2
  invFun f := ⟨f ∘ Quotient.mk'', fun x y h => by simp [ker_def, Quotient.sound' h]⟩
  right_inv _ := funext fun x => Quotient.inductionOn' x fun _ => rfl

中文:
定义 liftEquiv
  签名: (r : 集合等价关系 α)
  定义体: Quotient.lift (f : α -> β) f.2
  invFun f := ⟨f ∘ Quotient.mk'', fun x y h => by simp [ker_def, Quotient.sound' h]⟩
  right_inv _ := funext fun x => Quotient.inductionOn' x fun _ => rfl

Depends on / 依赖: Quotient, Quotient.lift
-/
def liftEquiv (r : Setoid α) : { f : α -> β // r <= ker f } ≃ (Quotient r -> β) where
  toFun f := Quotient.lift (f : α -> β) f.2
  invFun f := ⟨f ∘ Quotient.mk'', fun x y h => by simp [ker_def, Quotient.sound' h]⟩
  right_inv _ := funext fun x => Quotient.inductionOn' x fun _ => rfl

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  statement: {r : Setoid α} {f : α -> β} (H : r <= ker f) (g : Quotient r -> β)
  proof: by
  ext ⟨x⟩
  rw [← Quotient.mk]; rw [Quotient.lift_mk f H]; rw [Hg]; rw [Function.comp_apply]; rw [Quotient.mk''_eq_mk]

中文:
定理 lift_unique
  结论: {r : 集合等价关系 α} {f : α -> β} (H : r <= ker f) (g : 商 r -> β)
  证明: by
  ext ⟨x⟩
  rw [← Quotient.mk]; rw [Quotient.lift_mk f H]; rw [Hg]; rw [Function.comp_apply]; rw [Quotient.mk''_eq_mk]

Depends on / 依赖: Function, Function.comp_apply, Quotient, Quotient.lift_mk, Quotient.mk, _eq_mk, comp_apply, lift_mk
-/
theorem lift_unique {r : Setoid α} {f : α -> β} (H : r <= ker f) (g : Quotient r -> β)
    (Hg : f = g ∘ Quotient.mk'') : Quotient.lift f H = g := by
  ext ⟨x⟩
  rw [← Quotient.mk]; rw [Quotient.lift_mk f H]; rw [Hg]; rw [Function.comp_apply]; rw [Quotient.mk''_eq_mk]

/--
Definition of `kerLift` / `kerLift` 的定义

English:
definition kerLift
  signature: (f : α -> β)
  body: Quotient.lift f fun _ _ => id

@[simp]

中文:
定义 kerLift
  签名: (f : α -> β)
  定义体: Quotient.lift f fun _ _ => id

@[simp]

Depends on / 依赖: Quotient, Quotient.lift
-/
def kerLift (f : α -> β) : Quotient (ker f) -> β :=
  Quotient.lift f fun _ _ => id

@[simp]
/--
theorem `kerLift_mk` / 定理 `kerLift_mk`

English:
theorem kerLift_mk
  given: (f : α -> β) (x : α)
  statement: kerLift f ⟦x⟧ = f x
  proof: rfl

中文:
定理 kerLift_mk
  条件: (f : α -> β) (x : α)
  结论: kerLift f ⟦x⟧ = f x
  证明: rfl
-/
theorem kerLift_mk (f : α -> β) (x : α) : kerLift f ⟦x⟧ = f x :=
  rfl

/--
theorem `kerLift_injective` / 定理 `kerLift_injective`

English:
theorem kerLift_injective
  given: (f : α -> β)
  statement: Injective kerLift f
  proof: fun x y => Quotient.inductionOn₂' x y fun _ _ h => Quotient.sound' h

中文:
定理 kerLift_injective
  条件: (f : α -> β)
  结论: 单射 kerLift f
  证明: fun x y => Quotient.inductionOn₂' x y fun _ _ h => Quotient.sound' h

Depends on / 依赖: Quotient, Quotient.inductionOn, Quotient.sound
-/
theorem kerLift_injective (f : α -> β) : Injective kerLift f :=
  fun x y => Quotient.inductionOn₂' x y fun _ _ h => Quotient.sound' h

/--
theorem `ker_eq_lift_of_injective` / 定理 `ker_eq_lift_of_injective`

English:
theorem ker_eq_lift_of_injective
  statement: {r : Setoid α} (f : α -> β) (H : r <= ker f)
  proof: le_antisymm
    (fun x y hk =>
Quotient.exact h show Quotient.lift f H ⟦x⟧ = Quotient.lift f H ⟦y⟧ from hk)
    H

中文:
定理 ker_eq_lift_of_injective
  结论: {r : 集合等价关系 α} (f : α -> β) (H : r <= ker f)
  证明: le_antisymm
    (fun x y hk =>
Quotient.exact h show Quotient.lift f H ⟦x⟧ = Quotient.lift f H ⟦y⟧ from hk)
    H

Depends on / 依赖: Quotient, Quotient.exact, Quotient.lift, le_antisymm
-/
theorem ker_eq_lift_of_injective {r : Setoid α} (f : α -> β) (H : r <= ker f)
    (h : Injective (Quotient.lift f H)) : ker f = r :=
  le_antisymm
    (fun x y hk =>
Quotient.exact h show Quotient.lift f H ⟦x⟧ = Quotient.lift f H ⟦y⟧ from hk)
    H

/--
theorem `lift_injective_iff_ker_eq_of_le` / 定理 `lift_injective_iff_ker_eq_of_le`

English:
theorem lift_injective_iff_ker_eq_of_le
  statement: {r : Setoid α} {f : α -> β}
  proof: ⟨ker_eq_lift_of_injective f hle, fun h => h ▸ kerLift_injective _⟩

中文:
定理 lift_injective_iff_ker_eq_of_le
  结论: {r : 集合等价关系 α} {f : α -> β}
  证明: ⟨ker_eq_lift_of_injective f hle, fun h => h ▸ kerLift_injective _⟩

Depends on / 依赖: kerLift_injective, ker_eq_lift_of_injective
-/
theorem lift_injective_iff_ker_eq_of_le {r : Setoid α} {f : α -> β}
    (hle : r <= ker f) : Injective (Quotient.lift f hle) ↔ ker f = r :=
  ⟨ker_eq_lift_of_injective f hle, fun h => h ▸ kerLift_injective _⟩

variable (r : Setoid α) (f : α -> β)

/--
theorem `range_kerLift_eq_range` / 定理 `range_kerLift_eq_range`

English:
theorem range_kerLift_eq_range
  statement: Set.range (kerLift f) = Set.range f
  proof: Set.range_quotient_lift (s := ker f) _

中文:
定理 range_kerLift_eq_range
  结论: 集合.range (kerLift f) = 集合.range f
  证明: Set.range_quotient_lift (s := ker f) _
-/
@[simp] theorem range_kerLift_eq_range : Set.range (kerLift f) = Set.range f :=
  Set.range_quotient_lift (s := ker f) _

/--
Definition of `quotientKerEquivRangeKerLift` / `quotientKerEquivRangeKerLift` 的定义

English:
definition quotientKerEquivRangeKerLift
  signature: : Quotient (ker f) ≃ Set.range (kerLift f)
  body: .ofInjective _ kerLift_injective _

中文:
定义 quotientKerEquivRangeKerLift
  签名: : 商 (ker f) ≃ 集合.range (kerLift f)
  定义体: .ofInjective _ kerLift_injective _

Depends on / 依赖: kerLift_injective, ofInjective
-/
noncomputable def quotientKerEquivRangeKerLift : Quotient (ker f) ≃ Set.range (kerLift f) :=
.ofInjective _ kerLift_injective _

/--
Definition of `quotientKerEquivRange` / `quotientKerEquivRange` 的定义

English:
definition quotientKerEquivRange
  signature: : Quotient (ker f) ≃ Set.range f
  body: .trans .setCongr range_kerLift_eq_range _ quotientKerEquivRangeKerLift _

中文:
定义 quotientKerEquivRange
  签名: : 商 (ker f) ≃ 集合.range f
  定义体: .trans .setCongr range_kerLift_eq_range _ quotientKerEquivRangeKerLift _

Depends on / 依赖: quotientKerEquivRangeKerLift, range_kerLift_eq_range, setCongr
-/
noncomputable def quotientKerEquivRange : Quotient (ker f) ≃ Set.range f :=
.trans .setCongr range_kerLift_eq_range _ quotientKerEquivRangeKerLift _

/-- If `f` has a computable right-inverse, then the quotient by its kernel is equivalent to its
domain. -/
@[simps]
/--
Definition of `quotientKerEquivOfRightInverse` / `quotientKerEquivOfRightInverse` 的定义

English:
definition quotientKerEquivOfRightInverse
  signature: (g : β -> α) (hf : Function.RightInverse g f)
  body: kerLift f
  invFun b := Quotient.mk'' (g b)
left_inv a := Quotient.inductionOn' a fun a => Quotient.sound' hf (f a)
  right_inv := hf

中文:
定义 quotientKerEquivOfRightInverse
  签名: (g : β -> α) (hf : 函数.右逆 g f)
  定义体: kerLift f
  invFun b := Quotient.mk'' (g b)
left_inv a := Quotient.inductionOn' a fun a => Quotient.sound' hf (f a)
  right_inv := hf

Depends on / 依赖: kerLift
-/
def quotientKerEquivOfRightInverse (g : β -> α) (hf : Function.RightInverse g f) :
    Quotient (ker f) ≃ β where
  toFun := kerLift f
  invFun b := Quotient.mk'' (g b)
left_inv a := Quotient.inductionOn' a fun a => Quotient.sound' hf (f a)
  right_inv := hf

/--
Definition of `quotientKerEquivOfSurjective` / `quotientKerEquivOfSurjective` 的定义

English:
definition quotientKerEquivOfSurjective
  signature: (hf : Surjective f)
  body: quotientKerEquivOfRightInverse _ (Function.surjInv hf) (rightInverse_surjInv hf)

中文:
定义 quotientKerEquivOfSurjective
  签名: (hf : 满射 f)
  定义体: quotientKerEquivOfRightInverse _ (Function.surjInv hf) (rightInverse_surjInv hf)

Depends on / 依赖: Function, Function.surjInv, quotientKerEquivOfRightInverse, rightInverse_surjInv, surjInv
-/
noncomputable def quotientKerEquivOfSurjective (hf : Surjective f) : Quotient (ker f) ≃ β :=
  quotientKerEquivOfRightInverse _ (Function.surjInv hf) (rightInverse_surjInv hf)

variable {r f}

/-- Given a function `f : α → β` and equivalence relation `r` on `α`, the equivalence
closure of the relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are
related to the elements of `f⁻¹(y)` by `r`.' -/
@[instance_reducible]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (r : Setoid α) (f : α -> β)
  body: Relation.EqvGen.setoid (Relation.Map r f f)

中文:
定义 map
  签名: (r : 集合等价关系 α) (f : α -> β)
  定义体: Relation.EqvGen.setoid (Relation.Map r f f)

Depends on / 依赖: EqvGen, Relation, Relation.EqvGen.setoid, Relation.Map, setoid
-/
def map (r : Setoid α) (f : α -> β) : Setoid β :=
  Relation.EqvGen.setoid (Relation.Map r f f)

/--
theorem `coe_map_of_ker_le` / 定理 `coe_map_of_ker_le`

English:
theorem coe_map_of_ker_le
  given: (r : Setoid α) (f : α -> β) (hf : ker f <= r)
  proof: by
  refine le_antisymm ?_ (sup_le Relation.EqvGen.rel (by rintro _ _ rfl; exact .refl _))
  rintro _ _ hxy
  induction hxy with
  | rel _ _ hab => exact .inl hab
  | refl _ => exact .inr rfl
  | symm _ _ _ ih => exact ih.imp (Std.Symm.symm _ _) (Std.Symm.symm _ _)
  | trans _ _ _ _ _ ih1 ih2 =>
   

中文:
定理 coe_map_of_ker_le
  条件: (r : 集合等价关系 α) (f : α -> β) (hf : ker f <= r)
  证明: by
  refine le_antisymm ?_ (sup_le Relation.EqvGen.rel (by rintro _ _ rfl; exact .refl _))
  rintro _ _ hxy
  induction hxy with
  | rel _ _ hab => exact .inl hab
  | refl _ => exact .inr rfl
  | symm _ _ _ ih => exact ih.imp (Std.Symm.symm _ _) (Std.Symm.symm _ _)
  | trans _ _ _ _ _ ih1 ih2 =>
   

Depends on / 依赖: EqvGen, Relation, Relation.EqvGen.rel, Std.Symm.symm, ih.imp, isTrans, le_antisymm, r.iseqv.isTrans.map, sup_le
-/
theorem coe_map_of_ker_le (r : Setoid α) (f : α -> β) (hf : ker f <= r) :
    ⇑(map r f) = Relation.Map r f f ⊔ (· = ·) := by
  refine le_antisymm ?_ (sup_le Relation.EqvGen.rel (by rintro _ _ rfl; exact .refl _))
  rintro _ _ hxy
  induction hxy with
  | rel _ _ hab => exact .inl hab
  | refl _ => exact .inr rfl
  | symm _ _ _ ih => exact ih.imp (Std.Symm.symm _ _) (Std.Symm.symm _ _)
  | trans _ _ _ _ _ ih1 ih2 =>
    rcases ih1 with ih1 | rfl
    · rcases ih2 with ih2 | rfl
· exact .inl .trans _ _ _ ih1 ih2 r.iseqv.isTrans.map hf
      · exact .inl ih1
    · exact ih2

/-- Given a surjective function f whose kernel is contained in an equivalence relation r, the
equivalence relation on f's codomain defined by x ≈ y ↔ the elements of f⁻¹(x) are related to
the elements of f⁻¹(y) by r. -/
@[instance_reducible]
/--
Definition of `mapOfSurjective` / `mapOfSurjective` 的定义

English:
definition mapOfSurjective
  signature: (r : Setoid α) (f : α -> β) (h : ker f <= r) (hf : Surjective f)
  body: ⟨Relation.Map r f f, Relation.map_equivalence r.iseqv f hf h⟩

中文:
定义 mapOfSurjective
  签名: (r : 集合等价关系 α) (f : α -> β) (h : ker f <= r) (hf : 满射 f)
  定义体: ⟨Relation.Map r f f, Relation.map_equivalence r.iseqv f hf h⟩

Depends on / 依赖: Relation, Relation.Map, Relation.map_equivalence, map_equivalence, r.iseqv
-/
def mapOfSurjective (r : Setoid α) (f : α -> β) (h : ker f <= r) (hf : Surjective f) : Setoid β :=
  ⟨Relation.Map r f f, Relation.map_equivalence r.iseqv f hf h⟩

/--
theorem `mapOfSurjective_eq_map` / 定理 `mapOfSurjective_eq_map`

English:
theorem mapOfSurjective_eq_map
  given: (h : ker f <= r) (hf : Surjective f)
  proof: by
  rw [← eqvGen_of_setoid (mapOfSurjective r f h hf)]; rfl

中文:
定理 mapOfSurjective_eq_map
  条件: (h : ker f <= r) (hf : 满射 f)
  证明: by
  rw [← eqvGen_of_setoid (mapOfSurjective r f h hf)]; rfl

Depends on / 依赖: eqvGen_of_setoid, mapOfSurjective
-/
theorem mapOfSurjective_eq_map (h : ker f <= r) (hf : Surjective f) :
    map r f = mapOfSurjective r f h hf := by
  rw [← eqvGen_of_setoid (mapOfSurjective r f h hf)]; rfl

/--
Definition of `comap` / `comap` 的定义

English:
abbreviation comap
  signature: (f : α -> β) (r : Setoid β)
  body: ⟨r on f, r.iseqv.comap _⟩

中文:
缩写 comap
  签名: (f : α -> β) (r : 集合等价关系 β)
  定义体: ⟨r on f, r.iseqv.comap _⟩

Depends on / 依赖: r.iseqv.comap
-/
abbrev comap (f : α -> β) (r : Setoid β) : Setoid α :=
  ⟨r on f, r.iseqv.comap _⟩

/--
theorem `comap_rel_eq` / 定理 `comap_rel_eq`

English:
theorem comap_rel_eq
  given: (f : α -> β) (r : Setoid β)
  statement: ⇑(comap f r) = (⇑r on f)
  proof: rfl

中文:
定理 comap_rel_eq
  条件: (f : α -> β) (r : 集合等价关系 β)
  结论: ⇑(comap f r) = (⇑r on f)
  证明: rfl
-/
theorem comap_rel_eq (f : α -> β) (r : Setoid β) : ⇑(comap f r) = (⇑r on f) :=
  rfl

/--
theorem `comap_rel` / 定理 `comap_rel`

English:
theorem comap_rel
  given: (f : α -> β) (r : Setoid β) (x y : α)
  statement: comap f r x y ↔ r (f x) (f y)
  proof: Iff.rfl

中文:
定理 comap_rel
  条件: (f : α -> β) (r : 集合等价关系 β) (x y : α)
  结论: comap f r x y ↔ r (f x) (f y)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem comap_rel (f : α -> β) (r : Setoid β) (x y : α) : comap f r x y ↔ r (f x) (f y) :=
  Iff.rfl

/--
theorem `comap_eq` / 定理 `comap_eq`

English:
theorem comap_eq
  given: {f : α -> β} {r : Setoid β}
  statement: comap f r = ker (@Quotient.mk'' _ r ∘ f)
  proof: ext fun x y => show _ ↔ ⟦_⟧ = ⟦_⟧ by rw [Quotient.eq]; rfl

@[simp]

中文:
定理 comap_eq
  条件: {f : α -> β} {r : 集合等价关系 β}
  结论: comap f r = ker (@商.mk'' _ r ∘ f)
  证明: ext fun x y => show _ ↔ ⟦_⟧ = ⟦_⟧ by rw [Quotient.eq]; rfl

@[simp]

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem comap_eq {f : α -> β} {r : Setoid β} : comap f r = ker (@Quotient.mk'' _ r ∘ f) :=
  ext fun x y => show _ ↔ ⟦_⟧ = ⟦_⟧ by rw [Quotient.eq]; rfl

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  given: (c : Setoid α)
  statement: c.comap id = c
  proof: rfl

@[simp]

中文:
定理 comap_id
  条件: (c : 集合等价关系 α)
  结论: c.comap id = c
  证明: rfl

@[simp]
-/
theorem comap_id (c : Setoid α) : c.comap id = c := rfl

@[simp]
/--
theorem `comap_comp` / 定理 `comap_comp`

English:
theorem comap_comp
  given: (c : Setoid γ) (g : β -> γ) (f : α -> β)
  statement: c.comap (g ∘ f) = (c.comap g).comap f
  proof: rfl

中文:
定理 comap_comp
  条件: (c : 集合等价关系 γ) (g : β -> γ) (f : α -> β)
  结论: c.comap (g ∘ f) = (c.comap g).comap f
  证明: rfl
-/
theorem comap_comp (c : Setoid γ) (g : β -> γ) (f : α -> β) : c.comap (g ∘ f) = (c.comap g).comap f :=
  rfl

/--
theorem `comap_injective` / 定理 `comap_injective`

English:
theorem comap_injective
  given: (f : α -> β) (hf : Function.Surjective f)
  proof: fun _ _ h => ext hf.forall₂.2 Setoid.ext_iff.1 h

中文:
定理 comap_injective
  条件: (f : α -> β) (hf : 函数.满射 f)
  证明: fun _ _ h => ext hf.forall₂.2 Setoid.ext_iff.1 h

Depends on / 依赖: Setoid, Setoid.ext_iff, ext_iff, hf.forall
-/
theorem comap_injective (f : α -> β) (hf : Function.Surjective f) :
    Function.Injective (comap f) :=
fun _ _ h => ext hf.forall₂.2 Setoid.ext_iff.1 h

/--
theorem `le_comap_map` / 定理 `le_comap_map`

English:
theorem le_comap_map
  given: {r : Setoid α} {f : α -> β}
  statement: r <= comap f (r.map f)
  proof: fun _ _ h => Relation.EqvGen.rel _ _ ⟨_, _, h, rfl, rfl⟩

中文:
定理 le_comap_map
  条件: {r : 集合等价关系 α} {f : α -> β}
  结论: r <= comap f (r.map f)
  证明: fun _ _ h => Relation.EqvGen.rel _ _ ⟨_, _, h, rfl, rfl⟩

Depends on / 依赖: EqvGen, Relation, Relation.EqvGen.rel
-/
theorem le_comap_map {r : Setoid α} {f : α -> β} : r <= comap f (r.map f) :=
  fun _ _ h => Relation.EqvGen.rel _ _ ⟨_, _, h, rfl, rfl⟩

/--
theorem `comap_map_of_ker_le` / 定理 `comap_map_of_ker_le`

English:
theorem comap_map_of_ker_le
  given: (f : α -> β) (r : Setoid α) (hf : ker f <= r)
  proof: by
  apply le_antisymm _ le_comap_map
  rw [le_iff_rel_le]; rw [comap_rel_eq]; rw [coe_map_of_ker_le _ _ hf]
  rintro x y (⟨a, b, h, ha, hb⟩ | h)
  · replace ha := hf ha
    replace hb := hf hb
    exact trans (symm ha) (trans h hb)
  · exact hf h

中文:
定理 comap_map_of_ker_le
  条件: (f : α -> β) (r : 集合等价关系 α) (hf : ker f <= r)
  证明: by
  apply le_antisymm _ le_comap_map
  rw [le_iff_rel_le]; rw [comap_rel_eq]; rw [coe_map_of_ker_le _ _ hf]
  rintro x y (⟨a, b, h, ha, hb⟩ | h)
  · replace ha := hf ha
    replace hb := hf hb
    exact trans (symm ha) (trans h hb)
  · exact hf h

Depends on / 依赖: coe_map_of_ker_le, comap_rel_eq, le_antisymm, le_comap_map, le_iff_rel_le, replace
-/
theorem comap_map_of_ker_le (f : α -> β) (r : Setoid α) (hf : ker f <= r) :
    comap f (r.map f) = r := by
  apply le_antisymm _ le_comap_map
  rw [le_iff_rel_le]; rw [comap_rel_eq]; rw [coe_map_of_ker_le _ _ hf]
  rintro x y (⟨a, b, h, ha, hb⟩ | h)
  · replace ha := hf ha
    replace hb := hf hb
    exact trans (symm ha) (trans h hb)
  · exact hf h

/--
theorem `comap_map_eq` / 定理 `comap_map_eq`

English:
theorem comap_map_eq
  given: (f : α -> β) (r : Setoid α) (hf : f.Injective)
  statement: comap f (r.map f) = r
  proof: comap_map_of_ker_le f r ker_eq_bot_iff.2 hf ▸ bot_le

中文:
定理 comap_map_eq
  条件: (f : α -> β) (r : 集合等价关系 α) (hf : f.单射)
  结论: comap f (r.map f) = r
  证明: comap_map_of_ker_le f r ker_eq_bot_iff.2 hf ▸ bot_le

Depends on / 依赖: bot_le, comap_map_of_ker_le, ker_eq_bot_iff
-/
theorem comap_map_eq (f : α -> β) (r : Setoid α) (hf : f.Injective) : comap f (r.map f) = r :=
comap_map_of_ker_le f r ker_eq_bot_iff.2 hf ▸ bot_le

/--
theorem `comap_surjective` / 定理 `comap_surjective`

English:
theorem comap_surjective
  given: (f : α -> β) (hf : Function.Injective f)
  proof: fun r => ⟨_, comap_map_eq f r hf⟩

中文:
定理 comap_surjective
  条件: (f : α -> β) (hf : 函数.单射 f)
  证明: fun r => ⟨_, comap_map_eq f r hf⟩

Depends on / 依赖: comap_map_eq
-/
theorem comap_surjective (f : α -> β) (hf : Function.Injective f) :
    Function.Surjective (Setoid.comap f) :=
  fun r => ⟨_, comap_map_eq f r hf⟩

/--
Definition of `comapQuotientEquiv` / `comapQuotientEquiv` 的定义

English:
definition comapQuotientEquiv
  signature: (f : α -> β) (r : Setoid β)
  body: (Quotient.congrRight <| Setoid.ext_iff.1 comap_eq).trans quotientKerEquivRange
    Quotient.mk'' ∘ f

中文:
定义 comapQuotientEquiv
  签名: (f : α -> β) (r : 集合等价关系 β)
  定义体: (Quotient.congrRight <| Setoid.ext_iff.1 comap_eq).trans quotientKerEquivRange
    Quotient.mk'' ∘ f

Depends on / 依赖: Quotient, Quotient.congrRight, Quotient.mk, Setoid, Setoid.ext_iff, comap_eq, congrRight, ext_iff, quotientKerEquivRange
-/
noncomputable def comapQuotientEquiv (f : α -> β) (r : Setoid β) :
    Quotient (comap f r) ≃ Set.range (@Quotient.mk'' _ r ∘ f) :=
(Quotient.congrRight <| Setoid.ext_iff.1 comap_eq).trans quotientKerEquivRange
    Quotient.mk'' ∘ f

variable (r f)

/--
Definition of `quotientQuotientEquivQuotient` / `quotientQuotientEquivQuotient` 的定义

English:
definition quotientQuotientEquivQuotient
  signature: (s : Setoid α) (h : r <= s)
  body: (Quotient.liftOn' x fun w =>
(Quotient.liftOn' w (@Quotient.mk'' _ s)) fun _ _ H => Quotient.sound h H)
      fun x y => Quotient.inductionOn₂' x y fun _ _ H => show @Quot.mk _ _ _ = @Quot.mk _ _ _ from H
  invFun x :=
    (Quotient.liftOn' x fun w => @Quotient.mk'' _ (ker <| Quot.mapRight h) <| @Qu

中文:
定义 quotientQuotientEquivQuotient
  签名: (s : 集合等价关系 α) (h : r <= s)
  定义体: (Quotient.liftOn' x fun w =>
(Quotient.liftOn' w (@Quotient.mk'' _ s)) fun _ _ H => Quotient.sound h H)
      fun x y => Quotient.inductionOn₂' x y fun _ _ H => show @Quot.mk _ _ _ = @Quot.mk _ _ _ from H
  invFun x :=
    (Quotient.liftOn' x fun w => @Quotient.mk'' _ (ker <| Quot.mapRight h) <| @Qu

Depends on / 依赖: Quot.mapRight, Quot.mk, Quotient, Quotient.inductionOn, Quotient.liftOn, Quotient.mk, Quotient.sound, inductionOn, invFun, left_inv, liftOn, mapRight
-/
def quotientQuotientEquivQuotient (s : Setoid α) (h : r <= s) :
    Quotient (ker (Quot.mapRight h)) ≃ Quotient s where
  toFun x :=
    (Quotient.liftOn' x fun w =>
(Quotient.liftOn' w (@Quotient.mk'' _ s)) fun _ _ H => Quotient.sound h H)
      fun x y => Quotient.inductionOn₂' x y fun _ _ H => show @Quot.mk _ _ _ = @Quot.mk _ _ _ from H
  invFun x :=
    (Quotient.liftOn' x fun w => @Quotient.mk'' _ (ker <| Quot.mapRight h) <| @Quotient.mk'' _ r w)
fun _ _ H => Quotient.sound' show @Quot.mk _ _ _ = @Quot.mk _ _ _ from Quotient.sound H
  left_inv x :=
    Quotient.inductionOn' x fun y => Quotient.inductionOn' y fun w => by change ⟦_⟧ = _; rfl
  right_inv x := Quotient.inductionOn' x fun y => by change ⟦_⟧ = _; rfl

variable {r f}

open Quotient

/--
Definition of `correspondence` / `correspondence` 的定义

English:
definition correspondence
  signature: (r : Setoid α)
  body: ⟨Quotient.lift₂ s.1.1 fun _ _ _ _ h₁ h₂ => Eq.propIntro
      (fun h => s.1.trans' (s.1.trans' (s.1.symm' (s.2 h₁)) h) (s.2 h₂))
      (fun h => s.1.trans' (s.1.trans' (s.2 h₁) h) (s.1.symm' (s.2 h₂))),
    ⟨Quotient.ind s.1.2.1, fun {x y} => Quotient.inductionOn₂ x y fun _ _ => s.1.2.2,
      fun {

中文:
定义 correspondence
  签名: (r : 集合等价关系 α)
  定义体: ⟨Quotient.lift₂ s.1.1 fun _ _ _ _ h₁ h₂ => Eq.propIntro
      (fun h => s.1.trans' (s.1.trans' (s.1.symm' (s.2 h₁)) h) (s.2 h₂))
      (fun h => s.1.trans' (s.1.trans' (s.2 h₁) h) (s.1.symm' (s.2 h₂))),
    ⟨Quotient.ind s.1.2.1, fun {x y} => Quotient.inductionOn₂ x y fun _ _ => s.1.2.2,
      fun {

Depends on / 依赖: Eq.propIntro, Quotient, Quotient.lift, propIntro
-/
def correspondence (r : Setoid α) : { s // r <= s } ≃o Setoid (Quotient r) where
  toFun s := ⟨Quotient.lift₂ s.1.1 fun _ _ _ _ h₁ h₂ => Eq.propIntro
      (fun h => s.1.trans' (s.1.trans' (s.1.symm' (s.2 h₁)) h) (s.2 h₂))
      (fun h => s.1.trans' (s.1.trans' (s.2 h₁) h) (s.1.symm' (s.2 h₂))),
    ⟨Quotient.ind s.1.2.1, fun {x y} => Quotient.inductionOn₂ x y fun _ _ => s.1.2.2,
      fun {x y z} => Quotient.inductionOn₃ x y z fun _ _ _ => s.1.2.3⟩⟩
  invFun s := ⟨comap Quotient.mk' s, fun x y h => by rw [comap_rel, Quotient.eq'.2 h]⟩
  right_inv _ := ext fun x y => Quotient.inductionOn₂ x y fun _ _ => Iff.rfl
  map_rel_iff' :=
    ⟨fun h x y hs => @h ⟦x⟧ ⟦y⟧ hs, fun h x y => Quotient.inductionOn₂ x y fun _ _ hs => h hs⟩

/--
Definition of `sigmaQuotientEquivOfLe` / `sigmaQuotientEquivOfLe` 的定义

English:
definition sigmaQuotientEquivOfLe
  signature: {r s : Setoid α} (hle : r <= s)
  body: .trans (.symm <| .sigmaCongrRight fun _ => .subtypeQuotientEquivQuotientSubtype
      (s₁ := r) (s₂ := r.comap Subtype.val) _ _ (fun _ => Iff.rfl) fun _ _ => Iff.rfl)
    (.sigmaFiberEquiv fun a => a.lift (Quotient.mk s) fun _ _ h => Quotient.sound <| hle h)

中文:
定义 sigmaQuotientEquivOfLe
  签名: {r s : 集合等价关系 α} (hle : r <= s)
  定义体: .trans (.symm <| .sigmaCongrRight fun _ => .subtypeQuotientEquivQuotientSubtype
      (s₁ := r) (s₂ := r.comap Subtype.val) _ _ (fun _ => Iff.rfl) fun _ _ => Iff.rfl)
    (.sigmaFiberEquiv fun a => a.lift (Quotient.mk s) fun _ _ h => Quotient.sound <| hle h)

Depends on / 依赖: Iff.rfl, Quotient, Quotient.mk, Quotient.sound, Subtype, Subtype.val, a.lift, r.comap, sigmaCongrRight, sigmaFiberEquiv, subtypeQuotientEquivQuotientSubtype
-/
def sigmaQuotientEquivOfLe {r s : Setoid α} (hle : r <= s) :
    (Σ q : Quotient s, Quotient (r.comap (Subtype.val : Quotient.mk s ⁻¹' {q} -> α))) ≃
      Quotient r :=
  .trans (.symm <| .sigmaCongrRight fun _ => .subtypeQuotientEquivQuotientSubtype
      (s₁ := r) (s₂ := r.comap Subtype.val) _ _ (fun _ => Iff.rfl) fun _ _ => Iff.rfl)
    (.sigmaFiberEquiv fun a => a.lift (Quotient.mk s) fun _ _ h => Quotient.sound <| hle h)

end Setoid

@[simp]
/--
theorem `Quotient.subsingleton_iff` / 定理 `Quotient.subsingleton_iff`

English:
theorem Quotient.subsingleton_iff
  given: {s : Setoid α}
  statement: Subsingleton (Quotient s) ↔ s = ⊤
  proof: by
  simp only [_root_.subsingleton_iff, eq_top_iff, Setoid.le_def, Setoid.top_def, Pi.top_apply]
  refine Quotient.mk'_surjective.forall.trans (forall_congr' fun a => ?_)
  refine Quotient.mk'_surjective.forall.trans (forall_congr' fun b => ?_)
  simp_rw [Prop.top_eq_true, true_implies, Quotient.eq

中文:
定理 商.subsingleton_iff
  条件: {s : 集合等价关系 α}
  结论: 子单例 (商 s) ↔ s = ⊤
  证明: by
  simp only [_root_.subsingleton_iff, eq_top_iff, Setoid.le_def, Setoid.top_def, Pi.top_apply]
  refine Quotient.mk'_surjective.forall.trans (forall_congr' fun a => ?_)
  refine Quotient.mk'_surjective.forall.trans (forall_congr' fun b => ?_)
  simp_rw [Prop.top_eq_true, true_implies, Quotient.eq

Depends on / 依赖: Pi.top_apply, Prop.top_eq_true, Quotient, Quotient.eq, Quotient.mk, Setoid, Setoid.le_def, Setoid.top_def, _root_, _root_.subsingleton_iff, _surjective, _surjective.forall.trans, eq_top_iff, forall_congr, le_def, simp_rw, subsingleton_iff, top_apply, top_def, top_eq_true
-/
theorem Quotient.subsingleton_iff {s : Setoid α} : Subsingleton (Quotient s) ↔ s = ⊤ := by
  simp only [_root_.subsingleton_iff, eq_top_iff, Setoid.le_def, Setoid.top_def, Pi.top_apply]
  refine Quotient.mk'_surjective.forall.trans (forall_congr' fun a => ?_)
  refine Quotient.mk'_surjective.forall.trans (forall_congr' fun b => ?_)
  simp_rw [Prop.top_eq_true, true_implies, Quotient.eq']

/--
theorem `Quot.subsingleton_iff` / 定理 `Quot.subsingleton_iff`

English:
theorem Quot.subsingleton_iff
  given: (r : α -> α -> Prop)
  proof: by
  simp only [_root_.subsingleton_iff, _root_.eq_top_iff, Pi.le_def, Pi.top_apply]
  refine Quot.mk_surjective.forall.trans (forall_congr' fun a => ?_)
  refine Quot.mk_surjective.forall.trans (forall_congr' fun b => ?_)
  rw [Quot.eq]
  simp

中文:
定理 商.subsingleton_iff
  条件: (r : α -> α -> 命题)
  证明: by
  simp only [_root_.subsingleton_iff, _root_.eq_top_iff, Pi.le_def, Pi.top_apply]
  refine Quot.mk_surjective.forall.trans (forall_congr' fun a => ?_)
  refine Quot.mk_surjective.forall.trans (forall_congr' fun b => ?_)
  rw [Quot.eq]
  simp

Depends on / 依赖: Pi.le_def, Pi.top_apply, Quot.eq, Quot.mk_surjective.forall.trans, _root_, _root_.eq_top_iff, _root_.subsingleton_iff, eq_top_iff, forall_congr, le_def, mk_surjective, subsingleton_iff, top_apply
-/
theorem Quot.subsingleton_iff (r : α -> α -> Prop) :
    Subsingleton (Quot r) ↔ Relation.EqvGen r = ⊤ := by
  simp only [_root_.subsingleton_iff, _root_.eq_top_iff, Pi.le_def, Pi.top_apply]
  refine Quot.mk_surjective.forall.trans (forall_congr' fun a => ?_)
  refine Quot.mk_surjective.forall.trans (forall_congr' fun b => ?_)
  rw [Quot.eq]
  simp
