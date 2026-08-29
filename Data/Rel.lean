/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.Set.Prod
public import Mathlib.Order.RelIso.Basic
public import Mathlib.Order.SetNotation

/-!
# Relations as sets of pairs

This file provides API to regard relations between `α` and `β` as sets of pairs `Set (α × β)`.

This is in particular useful in the study of uniform spaces, which are topological spaces equipped
with a *uniformity*, namely a filter of pairs `α × α` whose elements can be viewed as "proximity"
relations.

## Main declarations

* `SetRel α β`: Type of relations between `α` and `β`.
* `SetRel.inv`: Turn `R : SetRel α β` into `R.inv : SetRel β α` by swapping the arguments.
* `SetRel.dom`: Domain of a relation. `a ∈ R.dom` iff there exists `b` such that `a ~[R] b`.
* `SetRel.cod`: Codomain of a relation. `b ∈ R.cod` iff there exists `a` such that `a ~[R] b`.
* `SetRel.id`: The identity relation `SetRel α α`.
* `SetRel.comp`: SetRel composition. Note that the arguments order follows the category theory
  convention, namely `(R ○ S) a c ↔ ∃ b, a ~[R] b ∧ b ~[S] c`.
* `SetRel.image`: Image of a set under a relation. `b ∈ image R s` iff there exists `a ∈ s`
  such that `a ~[R] b`.
  If `R` is the graph of `f` (`a ~[R] b ↔ f a = b`), then `R.image = Set.image f`.
* `SetRel.preimage`: Preimage of a set under a relation. `a ∈ preimage R t` iff there exists
  `b ∈ t` such that `a ~[R] b`.
  If `R` is the graph of `f` (`a ~[R] b ↔ f a = b`), then `R.preimage = Set.preimage f`.
* `SetRel.core`: Core of a set. For `t : Set β`, `a ∈ R.core t` iff all `b` related to `a` are in
  `t`.
* `SetRel.restrictDomain`: Domain-restriction of a relation to a subtype.
* `Function.graph`: Graph of a function as a relation.

## Implementation notes

There is tension throughout the library between considering relations between `α` and `β` simply as
`α → β → Prop`, or as a bundled object `SetRel α β` with dedicated operations and API.

The former approach is used almost everywhere as it is very lightweight and has arguably native
support from core Lean features, but it cracks at the seams whenever one starts talking about
operations on relations. For example:
* composition of relations `R : α → β → Prop`, `S : β → γ → Prop` is
  `Relation.Comp R S := fun a c ↦ ∃ b, R a b ∧ S b c`
* map of a relation `R : α → β → Prop` under `f : α → γ`, `g : β → δ` is
  `Relation.Map R f g := fun c d ↦ ∃ a b, r a b ∧ f a = c ∧ g b = d`.

The latter approach is embodied by `SetRel α β`, with the dedicated notation `○` for composition.
(Note that `○` is _not_ the same as function composition `∘`.)

Previously, `SetRel` suffered from the leakage of its definition as
```
def SetRel (α β : Type*) := α → β → Prop
```
The fact that `SetRel` wasn't an `abbrev` confuses automation.
But simply making it an `abbrev` would have killed the point of having a separate less see-through
type to perform relation operations on. So we instead redefined it as
```
abbrev SetRel (α β : Type*) := Set (α × β)
```
This extra level of indirection guides automation correctly and prevents (some kinds of) leakage.

Simultaneously, uniform spaces need a theory of relations on a type `α` as elements of
`Set (α × α)`, and the new definition of `SetRel` fulfills this role quite well.
-/

@[expose] public section

variable {α β γ δ : Type*} {ι : Sort*}

/--
Definition of `SetRel` / `SetRel` 的定义

English:
abbreviation SetRel
  signature: (α β : Type*)
  body: Set (α × β)

中文:
缩写 SetRel
  签名: (α β : 类型)
  定义体: Set (α × β)
-/
abbrev SetRel (α β : Type*) := Set (α × β)

namespace SetRel
variable {R R₁ R₂ : SetRel α β} {S : SetRel β γ} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {u : Set γ}
  {a a₁ a₂ : α} {b : β} {c : γ}

/-- Notation for apply a relation `R : SetRel α β` to `a : α`, `b : β`,
scoped to the `SetRel` namespace.

Since `SetRel α β := Set (α × β)`, `a ~[R] b` is simply notation for `(a, b) ∈ R`, but this should
be considered an implementation detail. -/
scoped notation:50 a:50 " ~[" R "] " b:50 => (a, b) in R

variable (R) in
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: (R : SetRel α β)
  body: Prod.swap ⁻¹' R

中文:
定义 inv
  签名: (R : SetRel α β)
  定义体: Prod.swap ⁻¹' R

Depends on / 依赖: Prod.swap, euclideanHausdorffMeasure_def, infer_instance
-/
def inv (R : SetRel α β) : SetRel β α := Prod.swap ⁻¹' R

/--
lemma `mem_inv` / 引理 `mem_inv`

English:
lemma mem_inv
  statement: b ~[R.inv] a ↔ a ~[R] b
  proof: .rfl

中文:
引理 mem_inv
  结论: b ~[R.inv] a ↔ a ~[R] b
  证明: .rfl
-/
@[simp] lemma mem_inv : b ~[R.inv] a ↔ a ~[R] b := .rfl

/--
lemma `inv_inv` / 引理 `inv_inv`

English:
lemma inv_inv
  statement: R.inv.inv = R
  proof: rfl

中文:
引理 inv_inv
  结论: R.inv.inv = R
  证明: rfl
-/
@[simp] lemma inv_inv : R.inv.inv = R := rfl

/--
lemma `inv_mono` / 引理 `inv_mono`

English:
lemma inv_mono
  given: (h : R₁ subseteq R₂)
  statement: R₁.inv subseteq R₂.inv
  proof: fun (_a, _b) hab => h hab

中文:
引理 inv_mono
  条件: (h : R₁ subseteq R₂)
  结论: R₁.inv subseteq R₂.inv
  证明: fun (_a, _b) hab => h hab
-/
@[gcongr] lemma inv_mono (h : R₁ subseteq R₂) : R₁.inv subseteq R₂.inv := fun (_a, _b) hab => h hab

/--
lemma `inv_empty` / 引理 `inv_empty`

English:
lemma inv_empty
  statement: (∅ : SetRel α β).inv = ∅
  proof: rfl

中文:
引理 inv_empty
  结论: (∅ : SetRel α β).inv = ∅
  证明: rfl
-/
@[simp] lemma inv_empty : (∅ : SetRel α β).inv = ∅ := rfl
/--
lemma `inv_univ` / 引理 `inv_univ`

English:
lemma inv_univ
  statement: inv (.univ : SetRel α β) = .univ
  proof: rfl

中文:
引理 inv_univ
  结论: inv (.univ : SetRel α β) = .univ
  证明: rfl
-/
@[simp] lemma inv_univ : inv (.univ : SetRel α β) = .univ := rfl

variable (R) in
/--
Definition of `dom` / `dom` 的定义

English:
definition dom
  signature: : Set α
  body: {a | exists b, a ~[R] b}

中文:
定义 dom
  签名: : 集合 α
  定义体: {a | exists b, a ~[R] b}
-/
def dom : Set α := {a | exists b, a ~[R] b}

variable (R) in
/--
Definition of `cod` / `cod` 的定义

English:
definition cod
  signature: : Set β
  body: {b | exists a, a ~[R] b}

中文:
定义 cod
  签名: : 集合 β
  定义体: {b | exists a, a ~[R] b}
-/
def cod : Set β := {b | exists a, a ~[R] b}

/--
lemma `mem_dom` / 引理 `mem_dom`

English:
lemma mem_dom
  statement: a in R.dom ↔ exists b, a ~[R] b
  proof: .rfl

中文:
引理 mem_dom
  结论: a in R.dom ↔ 存在 b, a ~[R] b
  证明: .rfl
-/
@[simp] lemma mem_dom : a in R.dom ↔ exists b, a ~[R] b := .rfl
/--
lemma `mem_cod` / 引理 `mem_cod`

English:
lemma mem_cod
  statement: b in R.cod ↔ exists a, a ~[R] b
  proof: .rfl

中文:
引理 mem_cod
  结论: b in R.cod ↔ 存在 a, a ~[R] b
  证明: .rfl
-/
@[simp] lemma mem_cod : b in R.cod ↔ exists a, a ~[R] b := .rfl

/--
lemma `dom_mono` / 引理 `dom_mono`

English:
lemma dom_mono
  given: (h : R₁ <= R₂)
  statement: R₁.dom subseteq R₂.dom
  proof: fun _a ⟨b, hab⟩ => ⟨b, h hab⟩

中文:
引理 dom_mono
  条件: (h : R₁ <= R₂)
  结论: R₁.dom subseteq R₂.dom
  证明: fun _a ⟨b, hab⟩ => ⟨b, h hab⟩
-/
@[gcongr] lemma dom_mono (h : R₁ <= R₂) : R₁.dom subseteq R₂.dom := fun _a ⟨b, hab⟩ => ⟨b, h hab⟩
/--
lemma `cod_mono` / 引理 `cod_mono`

English:
lemma cod_mono
  given: (h : R₁ <= R₂)
  statement: R₁.cod subseteq R₂.cod
  proof: fun _b ⟨a, hab⟩ => ⟨a, h hab⟩

中文:
引理 cod_mono
  条件: (h : R₁ <= R₂)
  结论: R₁.cod subseteq R₂.cod
  证明: fun _b ⟨a, hab⟩ => ⟨a, h hab⟩
-/
@[gcongr] lemma cod_mono (h : R₁ <= R₂) : R₁.cod subseteq R₂.cod := fun _b ⟨a, hab⟩ => ⟨a, h hab⟩

/--
lemma `dom_empty` / 引理 `dom_empty`

English:
lemma dom_empty
  statement: (∅ : SetRel α β).dom = ∅
  proof: by aesop

中文:
引理 dom_empty
  结论: (∅ : SetRel α β).dom = ∅
  证明: by aesop
-/
@[simp] lemma dom_empty : (∅ : SetRel α β).dom = ∅ := by aesop
/--
lemma `cod_empty` / 引理 `cod_empty`

English:
lemma cod_empty
  statement: (∅ : SetRel α β).cod = ∅
  proof: by aesop

中文:
引理 cod_empty
  结论: (∅ : SetRel α β).cod = ∅
  证明: by aesop
-/
@[simp] lemma cod_empty : (∅ : SetRel α β).cod = ∅ := by aesop

/--
lemma `dom_eq_empty_iff` / 引理 `dom_eq_empty_iff`

English:
lemma dom_eq_empty_iff
  statement: R.dom = ∅ ↔ R = (∅ : SetRel α β)
  proof: ⟨fun h => Set.eq_empty_iff_forall_notMem.mpr by simp_all [Set.eq_empty_iff_forall_notMem],
   (· ▸ dom_empty)⟩

中文:
引理 dom_eq_empty_iff
  结论: R.dom = ∅ ↔ R = (∅ : SetRel α β)
  证明: ⟨fun h => Set.eq_empty_iff_forall_notMem.mpr by simp_all [Set.eq_empty_iff_forall_notMem],
   (· ▸ dom_empty)⟩

Depends on / 依赖: s.topSpaceM, topSpaceM
-/
@[simp] lemma dom_eq_empty_iff : R.dom = ∅ ↔ R = (∅ : SetRel α β) :=
⟨fun h => Set.eq_empty_iff_forall_notMem.mpr by simp_all [Set.eq_empty_iff_forall_notMem],
   (· ▸ dom_empty)⟩

/--
lemma `cod_eq_empty_iff` / 引理 `cod_eq_empty_iff`

English:
lemma cod_eq_empty_iff
  statement: R.cod = ∅ ↔ R = (∅ : SetRel α β)
  proof: ⟨fun h => Set.eq_empty_iff_forall_notMem.mpr by simp_all [Set.eq_empty_iff_forall_notMem],
   (· ▸ cod_empty)⟩

中文:
引理 cod_eq_empty_iff
  结论: R.cod = ∅ ↔ R = (∅ : SetRel α β)
  证明: ⟨fun h => Set.eq_empty_iff_forall_notMem.mpr by simp_all [Set.eq_empty_iff_forall_notMem],
   (· ▸ cod_empty)⟩

Depends on / 依赖: chartedSpace, s.chartedSpace
-/
@[simp] lemma cod_eq_empty_iff : R.cod = ∅ ↔ R = (∅ : SetRel α β) :=
⟨fun h => Set.eq_empty_iff_forall_notMem.mpr by simp_all [Set.eq_empty_iff_forall_notMem],
   (· ▸ cod_empty)⟩

/--
lemma `dom_univ` / 引理 `dom_univ`

English:
lemma dom_univ
  given: [Nonempty β]
  statement: dom (.univ : SetRel α β) = .univ
  proof: by aesop

中文:
引理 dom_univ
  条件: [非空 β]
  结论: dom (.univ : SetRel α β) = .univ
  证明: by aesop

Depends on / 依赖: isManifold, s.isManifold
-/
@[simp] lemma dom_univ [Nonempty β] : dom (.univ : SetRel α β) = .univ := by aesop
/--
lemma `cod_univ` / 引理 `cod_univ`

English:
lemma cod_univ
  given: [Nonempty α]
  statement: cod (.univ : SetRel α β) = .univ
  proof: by aesop

中文:
引理 cod_univ
  条件: [非空 α]
  结论: cod (.univ : SetRel α β) = .univ
  证明: by aesop

Depends on / 依赖: compactSpace, s.compactSpace
-/
@[simp] lemma cod_univ [Nonempty α] : cod (.univ : SetRel α β) = .univ := by aesop

/--
lemma `cod_inv` / 引理 `cod_inv`

English:
lemma cod_inv
  statement: R.inv.cod = R.dom
  proof: rfl

中文:
引理 cod_inv
  结论: R.inv.cod = R.dom
  证明: rfl

Depends on / 依赖: boundaryless, s.boundaryless
-/
@[simp] lemma cod_inv : R.inv.cod = R.dom := rfl
/--
lemma `dom_inv` / 引理 `dom_inv`

English:
lemma dom_inv
  statement: R.inv.dom = R.cod
  proof: rfl

中文:
引理 dom_inv
  结论: R.inv.dom = R.cod
  证明: rfl
-/
@[simp] lemma dom_inv : R.inv.dom = R.cod := rfl

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : SetRel α α
  body: {(a₁, a₂) | a₁ = a₂}

中文:
定义 id
  签名: : SetRel α α
  定义体: {(a₁, a₂) | a₁ = a₂}
-/
protected def id : SetRel α α := {(a₁, a₂) | a₁ = a₂}

/--
lemma `mem_id` / 引理 `mem_id`

English:
lemma mem_id
  statement: a₁ ~[SetRel.id] a₂ ↔ a₁ = a₂
  proof: .rfl

中文:
引理 mem_id
  结论: a₁ ~[SetRel.id] a₂ ↔ a₁ = a₂
  证明: .rfl
-/
@[simp] lemma mem_id : a₁ ~[SetRel.id] a₂ ↔ a₁ = a₂ := .rfl

-- Not simp because `SetRel.inv_eq_self` already proves it
/--
lemma `inv_id` / 引理 `inv_id`

English:
lemma inv_id
  statement: (.id : SetRel α α).inv = .id
  proof: by aesop

中文:
引理 inv_id
  结论: (.id : SetRel α α).inv = .id
  证明: by aesop
-/
lemma inv_id : (.id : SetRel α α).inv = .id := by aesop

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (R : SetRel α β) (S : SetRel β γ)
  body: {(a, c) | exists b, a ~[R] b ∧ b ~[S] c}

@[inherit_doc] scoped infixl:62 " ○ " => comp

中文:
定义 comp
  签名: (R : SetRel α β) (S : SetRel β γ)
  定义体: {(a, c) | exists b, a ~[R] b ∧ b ~[S] c}

@[inherit_doc] scoped infixl:62 " ○ " => comp
-/
def comp (R : SetRel α β) (S : SetRel β γ) : SetRel α γ := {(a, c) | exists b, a ~[R] b ∧ b ~[S] c}

@[inherit_doc] scoped infixl:62 " ○ " => comp

/--
lemma `mem_comp` / 引理 `mem_comp`

English:
lemma mem_comp
  statement: a ~[R ○ S] c ↔ exists b, a ~[R] b ∧ b ~[S] c
  proof: .rfl

中文:
引理 mem_comp
  结论: a ~[R ○ S] c ↔ 存在 b, a ~[R] b ∧ b ~[S] c
  证明: .rfl
-/
@[simp] lemma mem_comp : a ~[R ○ S] c ↔ exists b, a ~[R] b ∧ b ~[S] c := .rfl

/--
lemma `prodMk_mem_comp` / 引理 `prodMk_mem_comp`

English:
lemma prodMk_mem_comp
  given: (hab : a ~[R] b) (hbc : b ~[S] c)
  statement: a ~[R ○ S] c
  proof: ⟨b, hab, hbc⟩

中文:
引理 prodMk_mem_comp
  条件: (hab : a ~[R] b) (hbc : b ~[S] c)
  结论: a ~[R ○ S] c
  证明: ⟨b, hab, hbc⟩
-/
lemma prodMk_mem_comp (hab : a ~[R] b) (hbc : b ~[S] c) : a ~[R ○ S] c := ⟨b, hab, hbc⟩

/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  given: (R : SetRel α β) (S : SetRel β γ) (t : SetRel γ δ)
  proof: by aesop

中文:
引理 comp_assoc
  条件: (R : SetRel α β) (S : SetRel β γ) (t : SetRel γ δ)
  证明: by aesop
-/
lemma comp_assoc (R : SetRel α β) (S : SetRel β γ) (t : SetRel γ δ) :
    (R ○ S) ○ t = R ○ (S ○ t) := by aesop

/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  given: (R : SetRel α β)
  statement: R ○ .id = R
  proof: by aesop

中文:
引理 comp_id
  条件: (R : SetRel α β)
  结论: R ○ .id = R
  证明: by aesop
-/
@[simp] lemma comp_id (R : SetRel α β) : R ○ .id = R := by aesop
/--
lemma `id_comp` / 引理 `id_comp`

English:
lemma id_comp
  given: (R : SetRel α β)
  statement: .id ○ R = R
  proof: by aesop

中文:
引理 id_comp
  条件: (R : SetRel α β)
  结论: .id ○ R = R
  证明: by aesop
-/
@[simp] lemma id_comp (R : SetRel α β) : .id ○ R = R := by aesop

/--
lemma `inv_comp` / 引理 `inv_comp`

English:
lemma inv_comp
  given: (R : SetRel α β) (S : SetRel β γ)
  statement: (R ○ S).inv = S.inv ○ R.inv
  proof: by aesop

中文:
引理 inv_comp
  条件: (R : SetRel α β) (S : SetRel β γ)
  结论: (R ○ S).inv = S.inv ○ R.inv
  证明: by aesop
-/
@[simp] lemma inv_comp (R : SetRel α β) (S : SetRel β γ) : (R ○ S).inv = S.inv ○ R.inv := by aesop

/--
lemma `comp_empty` / 引理 `comp_empty`

English:
lemma comp_empty
  given: (R : SetRel α β)
  statement: R ○ (∅ : SetRel β γ) = ∅
  proof: by aesop

中文:
引理 comp_empty
  条件: (R : SetRel α β)
  结论: R ○ (∅ : SetRel β γ) = ∅
  证明: by aesop
-/
@[simp] lemma comp_empty (R : SetRel α β) : R ○ (∅ : SetRel β γ) = ∅ := by aesop
/--
lemma `empty_comp` / 引理 `empty_comp`

English:
lemma empty_comp
  given: (S : SetRel β γ)
  statement: (∅ : SetRel α β) ○ S = ∅
  proof: by aesop

中文:
引理 empty_comp
  条件: (S : SetRel β γ)
  结论: (∅ : SetRel α β) ○ S = ∅
  证明: by aesop
-/
@[simp] lemma empty_comp (S : SetRel β γ) : (∅ : SetRel α β) ○ S = ∅ := by aesop

/--
lemma `comp_univ` / 引理 `comp_univ`

English:
lemma comp_univ
  given: (R : SetRel α β)
  proof: by
  aesop

中文:
引理 comp_univ
  条件: (R : SetRel α β)
  证明: by
  aesop
-/
@[simp] lemma comp_univ (R : SetRel α β) :
    R ○ (.univ : SetRel β γ) = {(a, _c) : α × γ | a in R.dom} := by
  aesop

/--
lemma `univ_comp` / 引理 `univ_comp`

English:
lemma univ_comp
  given: (S : SetRel β γ)
  proof: by
  aesop

中文:
引理 univ_comp
  条件: (S : SetRel β γ)
  证明: by
  aesop
-/
@[simp] lemma univ_comp (S : SetRel β γ) :
    (.univ : SetRel α β) ○ S = {(_b, c) : α × γ | c in S.cod} := by
  aesop

/--
lemma `comp_iUnion` / 引理 `comp_iUnion`

English:
lemma comp_iUnion
  given: (R : SetRel α β) (S : ι -> SetRel β γ)
  statement: R ○ ⋃ i, S i = ⋃ i, R ○ S i
  proof: by aesop

中文:
引理 comp_iUnion
  条件: (R : SetRel α β) (S : ι -> SetRel β γ)
  结论: R ○ ⋃ i, S i = ⋃ i, R ○ S i
  证明: by aesop
-/
lemma comp_iUnion (R : SetRel α β) (S : ι -> SetRel β γ) : R ○ ⋃ i, S i = ⋃ i, R ○ S i := by aesop
/--
lemma `iUnion_comp` / 引理 `iUnion_comp`

English:
lemma iUnion_comp
  given: (R : ι -> SetRel α β) (S : SetRel β γ)
  statement: (⋃ i, R i) ○ S = ⋃ i, R i ○ S
  proof: by aesop

中文:
引理 iUnion_comp
  条件: (R : ι -> SetRel α β) (S : SetRel β γ)
  结论: (⋃ i, R i) ○ S = ⋃ i, R i ○ S
  证明: by aesop
-/
lemma iUnion_comp (R : ι -> SetRel α β) (S : SetRel β γ) : (⋃ i, R i) ○ S = ⋃ i, R i ○ S := by aesop
/--
lemma `comp_sUnion` / 引理 `comp_sUnion`

English:
lemma comp_sUnion
  given: (R : SetRel α β) (𝒮 : Set (SetRel β γ))
  statement: R ○ ⋃₀ 𝒮 = ⋃ S in 𝒮, R ○ S
  proof: by aesop

中文:
引理 comp_sUnion
  条件: (R : SetRel α β) (𝒮 : 集合 (SetRel β γ))
  结论: R ○ ⋃₀ 𝒮 = ⋃ S in 𝒮, R ○ S
  证明: by aesop
-/
lemma comp_sUnion (R : SetRel α β) (𝒮 : Set (SetRel β γ)) : R ○ ⋃₀ 𝒮 = ⋃ S in 𝒮, R ○ S := by aesop
/--
lemma `sUnion_comp` / 引理 `sUnion_comp`

English:
lemma sUnion_comp
  given: (ℛ : Set (SetRel α β)) (S : SetRel β γ)
  statement: ⋃₀ ℛ ○ S = ⋃ R in ℛ, R ○ S
  proof: by aesop

@[gcongr]

中文:
引理 sUnion_comp
  条件: (ℛ : 集合 (SetRel α β)) (S : SetRel β γ)
  结论: ⋃₀ ℛ ○ S = ⋃ R in ℛ, R ○ S
  证明: by aesop

@[gcongr]
-/
lemma sUnion_comp (ℛ : Set (SetRel α β)) (S : SetRel β γ) : ⋃₀ ℛ ○ S = ⋃ R in ℛ, R ○ S := by aesop

@[gcongr]
/--
lemma `comp_subset_comp` / 引理 `comp_subset_comp`

English:
lemma comp_subset_comp
  given: {S₁ S₂ : SetRel β γ} (hR : R₁ subseteq R₂) (hS : S₁ subseteq S₂)
  statement: R₁ ○ S₁ subseteq R₂ ○ S₂
  proof: fun _ => .imp fun _ => .imp (@hR _) (@hS _)

@[gcongr]

中文:
引理 comp_subset_comp
  条件: {S₁ S₂ : SetRel β γ} (hR : R₁ subseteq R₂) (hS : S₁ subseteq S₂)
  结论: R₁ ○ S₁ subseteq R₂ ○ S₂
  证明: fun _ => .imp fun _ => .imp (@hR _) (@hS _)

@[gcongr]
-/
lemma comp_subset_comp {S₁ S₂ : SetRel β γ} (hR : R₁ subseteq R₂) (hS : S₁ subseteq S₂) : R₁ ○ S₁ subseteq R₂ ○ S₂ :=
  fun _ => .imp fun _ => .imp (@hR _) (@hS _)

@[gcongr]
/--
lemma `comp_subset_comp_left` / 引理 `comp_subset_comp_left`

English:
lemma comp_subset_comp_left
  given: {S : SetRel β γ} (hR : R₁ subseteq R₂)
  statement: R₁ ○ S subseteq R₂ ○ S
  proof: comp_subset_comp hR .rfl

@[gcongr]

中文:
引理 comp_subset_comp_left
  条件: {S : SetRel β γ} (hR : R₁ subseteq R₂)
  结论: R₁ ○ S subseteq R₂ ○ S
  证明: comp_subset_comp hR .rfl

@[gcongr]

Depends on / 依赖: comp_subset_comp
-/
lemma comp_subset_comp_left {S : SetRel β γ} (hR : R₁ subseteq R₂) : R₁ ○ S subseteq R₂ ○ S :=
  comp_subset_comp hR .rfl

@[gcongr]
/--
lemma `comp_subset_comp_right` / 引理 `comp_subset_comp_right`

English:
lemma comp_subset_comp_right
  given: {S₁ S₂ : SetRel β γ} (hS : S₁ subseteq S₂)
  statement: R ○ S₁ subseteq R ○ S₂
  proof: comp_subset_comp .rfl hS

中文:
引理 comp_subset_comp_right
  条件: {S₁ S₂ : SetRel β γ} (hS : S₁ subseteq S₂)
  结论: R ○ S₁ subseteq R ○ S₂
  证明: comp_subset_comp .rfl hS

Depends on / 依赖: comp_subset_comp
-/
lemma comp_subset_comp_right {S₁ S₂ : SetRel β γ} (hS : S₁ subseteq S₂) : R ○ S₁ subseteq R ○ S₂ :=
  comp_subset_comp .rfl hS

/--
lemma `_root_.Monotone.relComp` / 引理 `_root_.Monotone.relComp`

English:
lemma _root_.Monotone.relComp
  statement: {ι : Type*} [Preorder ι] {f : ι -> SetRel α β}
  proof: fun _i _j hij ⟨_a, _c⟩ ⟨b, hab, hbc⟩ => ⟨b, hf hij hab, hg hij hbc⟩

中文:
引理 _root_.递增.relComp
  结论: {ι : 类型} [预序 ι] {f : ι -> SetRel α β}
  证明: fun _i _j hij ⟨_a, _c⟩ ⟨b, hab, hbc⟩ => ⟨b, hf hij hab, hg hij hbc⟩
-/
protected lemma _root_.Monotone.relComp {ι : Type*} [Preorder ι] {f : ι -> SetRel α β}
    {g : ι -> SetRel β γ} (hf : Monotone f) (hg : Monotone g) : Monotone fun x => f x ○ g x :=
  fun _i _j hij ⟨_a, _c⟩ ⟨b, hab, hbc⟩ => ⟨b, hf hij hab, hg hij hbc⟩

/--
lemma `prod_comp_prod_of_inter_nonempty` / 引理 `prod_comp_prod_of_inter_nonempty`

English:
lemma prod_comp_prod_of_inter_nonempty
  given: (ht : (t₁ inter t₂).Nonempty) (s : Set α) (u : Set γ)
  proof: by aesop

中文:
引理 prod_comp_prod_of_inter_nonempty
  条件: (ht : (t₁ inter t₂).非空) (s : 集合 α) (u : 集合 γ)
  证明: by aesop
-/
lemma prod_comp_prod_of_inter_nonempty (ht : (t₁ inter t₂).Nonempty) (s : Set α) (u : Set γ) :
    s ×ˢ t₁ ○ t₂ ×ˢ u = s ×ˢ u := by aesop

/--
lemma `prod_comp_prod_of_disjoint` / 引理 `prod_comp_prod_of_disjoint`

English:
lemma prod_comp_prod_of_disjoint
  given: (ht : Disjoint t₁ t₂) (s : Set α) (u : Set γ)
  proof: Set.eq_empty_of_forall_notMem fun _ ⟨_z, ⟨_, hzs⟩, hzu, _⟩ => Set.disjoint_left.1 ht hzs hzu

中文:
引理 prod_comp_prod_of_disjoint
  条件: (ht : Disjoint t₁ t₂) (s : 集合 α) (u : 集合 γ)
  证明: Set.eq_empty_of_forall_notMem fun _ ⟨_z, ⟨_, hzs⟩, hzu, _⟩ => Set.disjoint_left.1 ht hzs hzu

Depends on / 依赖: Set.disjoint_left, Set.eq_empty_of_forall_notMem, disjoint_left, eq_empty_of_forall_notMem
-/
lemma prod_comp_prod_of_disjoint (ht : Disjoint t₁ t₂) (s : Set α) (u : Set γ) :
    s ×ˢ t₁ ○ t₂ ×ˢ u = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_z, ⟨_, hzs⟩, hzu, _⟩ => Set.disjoint_left.1 ht hzs hzu

/--
lemma `prod_comp_prod` / 引理 `prod_comp_prod`

English:
lemma prod_comp_prod
  given: (s : Set α) (t₁ t₂ : Set β) (u : Set γ) [Decidable (Disjoint t₁ t₂)]
  proof: by
  split_ifs with hst
  · exact prod_comp_prod_of_disjoint hst ..
  · rw [prod_comp_prod_of_inter_nonempty <| Set.not_disjoint_iff_nonempty_inter.1 hst]

中文:
引理 prod_comp_prod
  条件: (s : 集合 α) (t₁ t₂ : 集合 β) (u : 集合 γ) [可判定 (Disjoint t₁ t₂)]
  证明: by
  split_ifs with hst
  · exact prod_comp_prod_of_disjoint hst ..
  · rw [prod_comp_prod_of_inter_nonempty <| Set.not_disjoint_iff_nonempty_inter.1 hst]

Depends on / 依赖: Set.not_disjoint_iff_nonempty_inter, not_disjoint_iff_nonempty_inter, prod_comp_prod_of_disjoint, prod_comp_prod_of_inter_nonempty, split_ifs
-/
lemma prod_comp_prod (s : Set α) (t₁ t₂ : Set β) (u : Set γ) [Decidable (Disjoint t₁ t₂)] :
    s ×ˢ t₁ ○ t₂ ×ˢ u = if Disjoint t₁ t₂ then ∅ else s ×ˢ u := by
  split_ifs with hst
  · exact prod_comp_prod_of_disjoint hst ..
  · rw [prod_comp_prod_of_inter_nonempty <| Set.not_disjoint_iff_nonempty_inter.1 hst]

variable (R s) in
/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: : Set β
  body: {b | exists a in s, a ~[R] b}

中文:
定义 像
  签名: : 集合 β
  定义体: {b | exists a in s, a ~[R] b}
-/
def image : Set β := {b | exists a in s, a ~[R] b}

variable (R t) in
/--
Definition of `preimage` / `preimage` 的定义

English:
definition preimage
  signature: : Set α
  body: {a | exists b in t, a ~[R] b}

中文:
定义 原像
  签名: : 集合 α
  定义体: {a | exists b in t, a ~[R] b}
-/
def preimage : Set α := {a | exists b in t, a ~[R] b}

/--
lemma `mem_image` / 引理 `mem_image`

English:
lemma mem_image
  statement: b in image R s ↔ exists a in s, a ~[R] b
  proof: .rfl

中文:
引理 mem_image
  结论: b in 像 R s ↔ 存在 a in s, a ~[R] b
  证明: .rfl
-/
@[simp] lemma mem_image : b in image R s ↔ exists a in s, a ~[R] b := .rfl
/--
lemma `mem_preimage` / 引理 `mem_preimage`

English:
lemma mem_preimage
  statement: a in preimage R t ↔ exists b in t, a ~[R] b
  proof: .rfl

中文:
引理 mem_preimage
  结论: a in 原像 R t ↔ 存在 b in t, a ~[R] b
  证明: .rfl
-/
@[simp] lemma mem_preimage : a in preimage R t ↔ exists b in t, a ~[R] b := .rfl

/--
lemma `image_subset_image` / 引理 `image_subset_image`

English:
lemma image_subset_image
  given: (hs : s₁ subseteq s₂)
  statement: image R s₁ subseteq image R s₂
  proof: fun _ ⟨a, ha, hab⟩ => ⟨a, hs ha, hab⟩

中文:
引理 image_subset_image
  条件: (hs : s₁ subseteq s₂)
  结论: 像 R s₁ subseteq 像 R s₂
  证明: fun _ ⟨a, ha, hab⟩ => ⟨a, hs ha, hab⟩
-/
@[gcongr] lemma image_subset_image (hs : s₁ subseteq s₂) : image R s₁ subseteq image R s₂ :=
  fun _ ⟨a, ha, hab⟩ => ⟨a, hs ha, hab⟩

/--
lemma `image_subset_image_left` / 引理 `image_subset_image_left`

English:
lemma image_subset_image_left
  given: (hR : R₁ subseteq R₂)
  statement: image R₁ s subseteq image R₂ s
  proof: fun _ ⟨a, ha, hab⟩ => ⟨a, ha, hR hab⟩

中文:
引理 image_subset_image_left
  条件: (hR : R₁ subseteq R₂)
  结论: 像 R₁ s subseteq 像 R₂ s
  证明: fun _ ⟨a, ha, hab⟩ => ⟨a, ha, hR hab⟩
-/
@[gcongr] lemma image_subset_image_left (hR : R₁ subseteq R₂) : image R₁ s subseteq image R₂ s :=
  fun _ ⟨a, ha, hab⟩ => ⟨a, ha, hR hab⟩

/--
lemma `preimage_subset_preimage` / 引理 `preimage_subset_preimage`

English:
lemma preimage_subset_preimage
  given: (ht : t₁ subseteq t₂)
  statement: preimage R t₁ subseteq preimage R t₂
  proof: fun _ ⟨a, ha, hab⟩ => ⟨a, ht ha, hab⟩

中文:
引理 preimage_subset_preimage
  条件: (ht : t₁ subseteq t₂)
  结论: 原像 R t₁ subseteq 原像 R t₂
  证明: fun _ ⟨a, ha, hab⟩ => ⟨a, ht ha, hab⟩
-/
@[gcongr] lemma preimage_subset_preimage (ht : t₁ subseteq t₂) : preimage R t₁ subseteq preimage R t₂ :=
  fun _ ⟨a, ha, hab⟩ => ⟨a, ht ha, hab⟩

/--
lemma `preimage_subset_preimage_left` / 引理 `preimage_subset_preimage_left`

English:
lemma preimage_subset_preimage_left
  given: (hR : R₁ subseteq R₂)
  statement: preimage R₁ t subseteq preimage R₂ t
  proof: fun _ ⟨a, ha, hab⟩ => ⟨a, ha, hR hab⟩

中文:
引理 preimage_subset_preimage_left
  条件: (hR : R₁ subseteq R₂)
  结论: 原像 R₁ t subseteq 原像 R₂ t
  证明: fun _ ⟨a, ha, hab⟩ => ⟨a, ha, hR hab⟩
-/
@[gcongr] lemma preimage_subset_preimage_left (hR : R₁ subseteq R₂) : preimage R₁ t subseteq preimage R₂ t :=
  fun _ ⟨a, ha, hab⟩ => ⟨a, ha, hR hab⟩

variable (R t) in
/--
lemma `image_inv` / 引理 `image_inv`

English:
lemma image_inv
  statement: R.inv.image t = preimage R t
  proof: rfl

中文:
引理 image_inv
  结论: R.inv.像 t = 原像 R t
  证明: rfl
-/
@[simp] lemma image_inv : R.inv.image t = preimage R t := rfl

variable (R s) in
/--
lemma `preimage_inv` / 引理 `preimage_inv`

English:
lemma preimage_inv
  statement: R.inv.preimage s = image R s
  proof: rfl

中文:
引理 preimage_inv
  结论: R.inv.原像 s = 像 R s
  证明: rfl
-/
@[simp] lemma preimage_inv : R.inv.preimage s = image R s := rfl

/--
lemma `image_mono` / 引理 `image_mono`

English:
lemma image_mono
  statement: Monotone R.image
  proof: fun _ _ => image_subset_image

中文:
引理 image_mono
  结论: 递增 R.像
  证明: fun _ _ => image_subset_image

Depends on / 依赖: image_subset_image
-/
lemma image_mono : Monotone R.image := fun _ _ => image_subset_image
/--
lemma `preimage_mono` / 引理 `preimage_mono`

English:
lemma preimage_mono
  statement: Monotone R.preimage
  proof: fun _ _ => preimage_subset_preimage

中文:
引理 preimage_mono
  结论: 递增 R.原像
  证明: fun _ _ => preimage_subset_preimage

Depends on / 依赖: preimage_subset_preimage
-/
lemma preimage_mono : Monotone R.preimage := fun _ _ => preimage_subset_preimage

/--
lemma `image_empty_right` / 引理 `image_empty_right`

English:
lemma image_empty_right
  statement: image R ∅ = ∅
  proof: by aesop

中文:
引理 image_empty_right
  结论: 像 R ∅ = ∅
  证明: by aesop
-/
@[simp] lemma image_empty_right : image R ∅ = ∅ := by aesop
/--
lemma `preimage_empty_right` / 引理 `preimage_empty_right`

English:
lemma preimage_empty_right
  statement: preimage R ∅ = ∅
  proof: by aesop

中文:
引理 preimage_empty_right
  结论: 原像 R ∅ = ∅
  证明: by aesop
-/
@[simp] lemma preimage_empty_right : preimage R ∅ = ∅ := by aesop

/--
lemma `image_univ_right` / 引理 `image_univ_right`

English:
lemma image_univ_right
  statement: image R .univ = R.cod
  proof: by aesop

中文:
引理 image_univ_right
  结论: 像 R .univ = R.cod
  证明: by aesop
-/
@[simp] lemma image_univ_right : image R .univ = R.cod := by aesop
/--
lemma `preimage_univ_right` / 引理 `preimage_univ_right`

English:
lemma preimage_univ_right
  statement: preimage R .univ = R.dom
  proof: by aesop

中文:
引理 preimage_univ_right
  结论: 原像 R .univ = R.dom
  证明: by aesop
-/
@[simp] lemma preimage_univ_right : preimage R .univ = R.dom := by aesop

variable (R) in
/--
lemma `image_inter_subset` / 引理 `image_inter_subset`

English:
lemma image_inter_subset
  statement: image R (s₁ inter s₂) subseteq image R s₁ inter image R s₂
  proof: image_mono.map_inf_le ..

中文:
引理 image_inter_subset
  结论: 像 R (s₁ inter s₂) subseteq 像 R s₁ inter 像 R s₂
  证明: image_mono.map_inf_le ..

Depends on / 依赖: image_mono, image_mono.map_inf_le, map_inf_le
-/
lemma image_inter_subset : image R (s₁ inter s₂) subseteq image R s₁ inter image R s₂ := image_mono.map_inf_le ..

variable (R) in
/--
lemma `preimage_inter_subset` / 引理 `preimage_inter_subset`

English:
lemma preimage_inter_subset
  statement: preimage R (t₁ inter t₂) subseteq preimage R t₁ inter preimage R t₂
  proof: preimage_mono.map_inf_le ..

中文:
引理 preimage_inter_subset
  结论: 原像 R (t₁ inter t₂) subseteq 原像 R t₁ inter 原像 R t₂
  证明: preimage_mono.map_inf_le ..

Depends on / 依赖: map_inf_le, preimage_mono, preimage_mono.map_inf_le
-/
lemma preimage_inter_subset : preimage R (t₁ inter t₂) subseteq preimage R t₁ inter preimage R t₂ :=
  preimage_mono.map_inf_le ..

variable (R s₁ s₂) in
/--
lemma `image_union` / 引理 `image_union`

English:
lemma image_union
  statement: image R (s₁ union s₂) = image R s₁ union image R s₂
  proof: by aesop

中文:
引理 image_union
  结论: 像 R (s₁ union s₂) = 像 R s₁ union 像 R s₂
  证明: by aesop
-/
lemma image_union : image R (s₁ union s₂) = image R s₁ union image R s₂ := by aesop

variable (R) in
/--
lemma `image_iUnion` / 引理 `image_iUnion`

English:
lemma image_iUnion
  given: (s : ι -> Set α)
  statement: image R (⋃ i, s i) = ⋃ i, image R (s i)
  proof: by aesop

中文:
引理 image_iUnion
  条件: (s : ι -> 集合 α)
  结论: 像 R (⋃ i, s i) = ⋃ i, 像 R (s i)
  证明: by aesop
-/
lemma image_iUnion (s : ι -> Set α) : image R (⋃ i, s i) = ⋃ i, image R (s i) := by aesop

variable (R) in
/--
lemma `image_sUnion` / 引理 `image_sUnion`

English:
lemma image_sUnion
  given: (S : Set (Set α))
  statement: image R (⋃₀ S) = ⋃ s in S, image R s
  proof: by aesop

中文:
引理 image_sUnion
  条件: (S : 集合 (集合 α))
  结论: 像 R (⋃₀ S) = ⋃ s in S, 像 R s
  证明: by aesop
-/
lemma image_sUnion (S : Set (Set α)) : image R (⋃₀ S) = ⋃ s in S, image R s := by aesop

variable (R t₁ t₂) in
/--
lemma `preimage_union` / 引理 `preimage_union`

English:
lemma preimage_union
  statement: preimage R (t₁ union t₂) = preimage R t₁ union preimage R t₂
  proof: by aesop

中文:
引理 preimage_union
  结论: 原像 R (t₁ union t₂) = 原像 R t₁ union 原像 R t₂
  证明: by aesop
-/
lemma preimage_union : preimage R (t₁ union t₂) = preimage R t₁ union preimage R t₂ := by aesop

variable (R) in
/--
lemma `preimage_iUnion` / 引理 `preimage_iUnion`

English:
lemma preimage_iUnion
  given: (t : ι -> Set β)
  statement: preimage R (⋃ i, t i) = ⋃ i, preimage R (t i)
  proof: by aesop

中文:
引理 preimage_iUnion
  条件: (t : ι -> 集合 β)
  结论: 原像 R (⋃ i, t i) = ⋃ i, 原像 R (t i)
  证明: by aesop
-/
lemma preimage_iUnion (t : ι -> Set β) : preimage R (⋃ i, t i) = ⋃ i, preimage R (t i) := by aesop

variable (R) in
/--
lemma `preimage_sUnion` / 引理 `preimage_sUnion`

English:
lemma preimage_sUnion
  given: (T : Set (Set β))
  statement: preimage R (⋃₀ T) = ⋃ t in T, preimage R t
  proof: by aesop

中文:
引理 preimage_sUnion
  条件: (T : 集合 (集合 β))
  结论: 原像 R (⋃₀ T) = ⋃ t in T, 原像 R t
  证明: by aesop
-/
lemma preimage_sUnion (T : Set (Set β)) : preimage R (⋃₀ T) = ⋃ t in T, preimage R t := by aesop

variable (s) in
/--
lemma `image_id` / 引理 `image_id`

English:
lemma image_id
  statement: image .id s = s
  proof: by aesop

中文:
引理 image_id
  结论: 像 .id s = s
  证明: by aesop
-/
@[simp] lemma image_id : image .id s = s := by aesop

variable (s) in
/--
lemma `preimage_id` / 引理 `preimage_id`

English:
lemma preimage_id
  statement: preimage .id s = s
  proof: by aesop

中文:
引理 preimage_id
  结论: 原像 .id s = s
  证明: by aesop
-/
@[simp] lemma preimage_id : preimage .id s = s := by aesop

variable (R S s) in
/--
lemma `image_comp` / 引理 `image_comp`

English:
lemma image_comp
  statement: image (R ○ S) s = image S (image R s)
  proof: by aesop

中文:
引理 image_comp
  结论: 像 (R ○ S) s = 像 S (像 R s)
  证明: by aesop
-/
lemma image_comp : image (R ○ S) s = image S (image R s) := by aesop

variable (R S u) in
/--
lemma `preimage_comp` / 引理 `preimage_comp`

English:
lemma preimage_comp
  statement: preimage (R ○ S) u = preimage R (preimage S u)
  proof: by aesop

中文:
引理 preimage_comp
  结论: 原像 (R ○ S) u = 原像 R (原像 S u)
  证明: by aesop
-/
lemma preimage_comp : preimage (R ○ S) u = preimage R (preimage S u) := by aesop

variable (s) in
/--
lemma `image_empty_left` / 引理 `image_empty_left`

English:
lemma image_empty_left
  statement: image (∅ : SetRel α β) s = ∅
  proof: by aesop

中文:
引理 image_empty_left
  结论: 像 (∅ : SetRel α β) s = ∅
  证明: by aesop
-/
@[simp] lemma image_empty_left : image (∅ : SetRel α β) s = ∅ := by aesop

variable (t) in
/--
lemma `preimage_empty_left` / 引理 `preimage_empty_left`

English:
lemma preimage_empty_left
  statement: preimage (∅ : SetRel α β) t = ∅
  proof: by aesop

中文:
引理 preimage_empty_left
  结论: 原像 (∅ : SetRel α β) t = ∅
  证明: by aesop
-/
@[simp] lemma preimage_empty_left : preimage (∅ : SetRel α β) t = ∅ := by aesop

/--
lemma `image_univ_left` / 引理 `image_univ_left`

English:
lemma image_univ_left
  given: (hs : s.Nonempty)
  statement: image (.univ : SetRel α β) s = .univ
  proof: by aesop

中文:
引理 image_univ_left
  条件: (hs : s.非空)
  结论: 像 (.univ : SetRel α β) s = .univ
  证明: by aesop
-/
@[simp] lemma image_univ_left (hs : s.Nonempty) : image (.univ : SetRel α β) s = .univ := by aesop
/--
lemma `preimage_univ_left` / 引理 `preimage_univ_left`

English:
lemma preimage_univ_left
  given: (ht : t.Nonempty)
  statement: preimage (.univ : SetRel α β) t = .univ
  proof: by
  aesop

中文:
引理 preimage_univ_left
  条件: (ht : t.非空)
  结论: 原像 (.univ : SetRel α β) t = .univ
  证明: by
  aesop
-/
@[simp] lemma preimage_univ_left (ht : t.Nonempty) : preimage (.univ : SetRel α β) t = .univ := by
  aesop

/--
lemma `image_eq_cod_of_dom_subset` / 引理 `image_eq_cod_of_dom_subset`

English:
lemma image_eq_cod_of_dom_subset
  given: (h : R.dom subseteq s)
  statement: R.image s = R.cod
  proof: by aesop

中文:
引理 image_eq_cod_of_dom_subset
  条件: (h : R.dom subseteq s)
  结论: R.像 s = R.cod
  证明: by aesop
-/
lemma image_eq_cod_of_dom_subset (h : R.dom subseteq s) : R.image s = R.cod := by aesop
/--
lemma `preimage_eq_dom_of_cod_subset` / 引理 `preimage_eq_dom_of_cod_subset`

English:
lemma preimage_eq_dom_of_cod_subset
  given: (h : R.cod subseteq t)
  statement: R.preimage t = R.dom
  proof: by aesop

中文:
引理 preimage_eq_dom_of_cod_subset
  条件: (h : R.cod subseteq t)
  结论: R.原像 t = R.dom
  证明: by aesop
-/
lemma preimage_eq_dom_of_cod_subset (h : R.cod subseteq t) : R.preimage t = R.dom := by aesop

variable (R s) in
/--
lemma `image_inter_dom` / 引理 `image_inter_dom`

English:
lemma image_inter_dom
  statement: image R (s inter R.dom) = image R s
  proof: by aesop

中文:
引理 image_inter_dom
  结论: 像 R (s inter R.dom) = 像 R s
  证明: by aesop
-/
@[simp] lemma image_inter_dom : image R (s inter R.dom) = image R s := by aesop

variable (R t) in
/--
lemma `preimage_inter_cod` / 引理 `preimage_inter_cod`

English:
lemma preimage_inter_cod
  statement: preimage R (t inter R.cod) = preimage R t
  proof: by aesop

中文:
引理 preimage_inter_cod
  结论: 原像 R (t inter R.cod) = 原像 R t
  证明: by aesop
-/
@[simp] lemma preimage_inter_cod : preimage R (t inter R.cod) = preimage R t := by aesop

/--
lemma `inter_dom_subset_preimage_image` / 引理 `inter_dom_subset_preimage_image`

English:
lemma inter_dom_subset_preimage_image
  statement: s inter R.dom subseteq R.preimage (image R s)
  proof: by
  aesop (add simp [Set.subset_def])

中文:
引理 inter_dom_subset_preimage_image
  结论: s inter R.dom subseteq R.原像 (像 R s)
  证明: by
  aesop (add simp [Set.subset_def])

Depends on / 依赖: Set.subset_def, subset_def
-/
lemma inter_dom_subset_preimage_image : s inter R.dom subseteq R.preimage (image R s) := by
  aesop (add simp [Set.subset_def])

/--
lemma `inter_cod_subset_image_preimage` / 引理 `inter_cod_subset_image_preimage`

English:
lemma inter_cod_subset_image_preimage
  statement: t inter R.cod subseteq image R (R.preimage t)
  proof: by
  aesop (add simp [Set.subset_def])

中文:
引理 inter_cod_subset_image_preimage
  结论: t inter R.cod subseteq 像 R (R.原像 t)
  证明: by
  aesop (add simp [Set.subset_def])

Depends on / 依赖: Set.subset_def, subset_def
-/
lemma inter_cod_subset_image_preimage : t inter R.cod subseteq image R (R.preimage t) := by
  aesop (add simp [Set.subset_def])

/--
lemma `image_eq_biUnion` / 引理 `image_eq_biUnion`

English:
lemma image_eq_biUnion
  statement: R.image s = ⋃ x in s, {y | x ~[R] y}
  proof: by aesop

中文:
引理 image_eq_biUnion
  结论: R.像 s = ⋃ x in s, {y | x ~[R] y}
  证明: by aesop
-/
lemma image_eq_biUnion : R.image s = ⋃ x in s, {y | x ~[R] y} := by aesop

/--
lemma `preimage_eq_biUnion` / 引理 `preimage_eq_biUnion`

English:
lemma preimage_eq_biUnion
  statement: R.preimage t = ⋃ y in t, {x | x ~[R] y}
  proof: by aesop

中文:
引理 preimage_eq_biUnion
  结论: R.原像 t = ⋃ y in t, {x | x ~[R] y}
  证明: by aesop
-/
lemma preimage_eq_biUnion : R.preimage t = ⋃ y in t, {x | x ~[R] y} := by aesop

variable (R t) in
/--
Definition of `core` / `core` 的定义

English:
definition core
  signature: : Set α
  body: {a | forall ⦃b⦄, a ~[R] b -> b in t}

中文:
定义 core
  签名: : 集合 α
  定义体: {a | forall ⦃b⦄, a ~[R] b -> b in t}
-/
def core : Set α := {a | forall ⦃b⦄, a ~[R] b -> b in t}

/--
lemma `mem_core` / 引理 `mem_core`

English:
lemma mem_core
  statement: a in R.core t ↔ forall ⦃b⦄, a ~[R] b -> b in t
  proof: .rfl

@[gcongr]

中文:
引理 mem_core
  结论: a in R.core t ↔ 对任意 ⦃b⦄, a ~[R] b -> b in t
  证明: .rfl

@[gcongr]
-/
@[simp] lemma mem_core : a in R.core t ↔ forall ⦃b⦄, a ~[R] b -> b in t := .rfl

@[gcongr]
/--
lemma `core_subset_core` / 引理 `core_subset_core`

English:
lemma core_subset_core
  given: (ht : t₁ subseteq t₂)
  statement: R.core t₁ subseteq R.core t₂
  proof: fun _a ha _b hab => ht ha hab

中文:
引理 core_subset_core
  条件: (ht : t₁ subseteq t₂)
  结论: R.core t₁ subseteq R.core t₂
  证明: fun _a ha _b hab => ht ha hab
-/
lemma core_subset_core (ht : t₁ subseteq t₂) : R.core t₁ subseteq R.core t₂ := fun _a ha _b hab => ht ha hab

/--
lemma `core_mono` / 引理 `core_mono`

English:
lemma core_mono
  statement: Monotone R.core
  proof: fun _ _ => core_subset_core

中文:
引理 core_mono
  结论: 递增 R.core
  证明: fun _ _ => core_subset_core

Depends on / 依赖: core_subset_core
-/
lemma core_mono : Monotone R.core := fun _ _ => core_subset_core

variable (R t₁ t₂) in
/--
lemma `core_inter` / 引理 `core_inter`

English:
lemma core_inter
  statement: R.core (t₁ inter t₂) = R.core t₁ inter R.core t₂
  proof: by aesop

中文:
引理 core_inter
  结论: R.core (t₁ inter t₂) = R.core t₁ inter R.core t₂
  证明: by aesop
-/
lemma core_inter : R.core (t₁ inter t₂) = R.core t₁ inter R.core t₂ := by aesop

/--
lemma `core_union_subset` / 引理 `core_union_subset`

English:
lemma core_union_subset
  statement: R.core t₁ union R.core t₂ subseteq R.core (t₁ union t₂)
  proof: core_mono.le_map_sup ..

中文:
引理 core_union_subset
  结论: R.core t₁ union R.core t₂ subseteq R.core (t₁ union t₂)
  证明: core_mono.le_map_sup ..

Depends on / 依赖: core_mono, core_mono.le_map_sup, le_map_sup
-/
lemma core_union_subset : R.core t₁ union R.core t₂ subseteq R.core (t₁ union t₂) := core_mono.le_map_sup ..

/--
lemma `core_univ` / 引理 `core_univ`

English:
lemma core_univ
  statement: R.core Set.univ = Set.univ
  proof: by aesop

中文:
引理 core_univ
  结论: R.core 集合.univ = 集合.univ
  证明: by aesop
-/
@[simp] lemma core_univ : R.core Set.univ = Set.univ := by aesop

variable (t) in
/--
lemma `core_id` / 引理 `core_id`

English:
lemma core_id
  statement: core .id t = t
  proof: by aesop

中文:
引理 core_id
  结论: core .id t = t
  证明: by aesop
-/
@[simp] lemma core_id : core .id t = t := by aesop

variable (R S u) in
/--
lemma `core_comp` / 引理 `core_comp`

English:
lemma core_comp
  statement: core (R ○ S) u = core R (core S u)
  proof: by aesop

中文:
引理 core_comp
  结论: core (R ○ S) u = core R (core S u)
  证明: by aesop
-/
lemma core_comp : core (R ○ S) u = core R (core S u) := by aesop

/--
lemma `image_subset_iff` / 引理 `image_subset_iff`

English:
lemma image_subset_iff
  statement: image R s subseteq t ↔ s subseteq core R t
  proof: by aesop (add simp [Set.subset_def])

中文:
引理 image_subset_iff
  结论: 像 R s subseteq t ↔ s subseteq core R t
  证明: by aesop (add simp [Set.subset_def])

Depends on / 依赖: Set.subset_def, subset_def
-/
lemma image_subset_iff : image R s subseteq t ↔ s subseteq core R t := by aesop (add simp [Set.subset_def])

/--
lemma `image_core_gc` / 引理 `image_core_gc`

English:
lemma image_core_gc
  statement: GaloisConnection R.image R.core
  proof: fun _ _ => image_subset_iff

中文:
引理 image_core_gc
  结论: GaloisConnection R.像 R.core
  证明: fun _ _ => image_subset_iff

Depends on / 依赖: image_subset_iff
-/
lemma image_core_gc : GaloisConnection R.image R.core := fun _ _ => image_subset_iff

variable (R s) in
/--
Definition of `restrictDomain` / `restrictDomain` 的定义

English:
definition restrictDomain
  signature: : SetRel s β
  body: {(a, b) | ↑a ~[R] b}

中文:
定义 restrictDomain
  签名: : SetRel s β
  定义体: {(a, b) | ↑a ~[R] b}
-/
def restrictDomain : SetRel s β := {(a, b) | ↑a ~[R] b}

variable {R R₁ R₂ : SetRel α α} {S : SetRel β β} {a b c : α}

/-! ### Reflexive relations -/

variable (R) in
/--
Definition of `IsRefl` / `IsRefl` 的定义

English:
abbreviation IsRefl
  signature: : Prop
  body: Std.Refl (· ~[R] ·)

中文:
缩写 IsRefl
  签名: : 命题
  定义体: Std.Refl (· ~[R] ·)
-/
protected abbrev IsRefl : Prop := Std.Refl (· ~[R] ·)

variable (R) in
/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: [R.IsRefl] (a : α)
  statement: a ~[R] a
  proof: refl_of (· ~[R] ·) a

中文:
引理 refl
  条件: [R.IsRefl] (a : α)
  结论: a ~[R] a
  证明: refl_of (· ~[R] ·) a
-/
protected lemma refl [R.IsRefl] (a : α) : a ~[R] a := refl_of (· ~[R] ·) a

variable (R) in
/--
lemma `rfl` / 引理 `rfl`

English:
lemma rfl
  given: [R.IsRefl]
  statement: a ~[R] a
  proof: R.refl a

中文:
引理 rfl
  条件: [R.IsRefl]
  结论: a ~[R] a
  证明: R.refl a
-/
protected lemma rfl [R.IsRefl] : a ~[R] a := R.refl a

/--
lemma `id_subset` / 引理 `id_subset`

English:
lemma id_subset
  given: [R.IsRefl]
  statement: .id subseteq R
  proof: by rintro ⟨_, _⟩ rfl; exact R.rfl

中文:
引理 id_subset
  条件: [R.IsRefl]
  结论: .id subseteq R
  证明: by rintro ⟨_, _⟩ rfl; exact R.rfl

Depends on / 依赖: R.rfl, TopologicalSpace
-/
lemma id_subset [R.IsRefl] : .id subseteq R := by rintro ⟨_, _⟩ rfl; exact R.rfl

/--
lemma `id_subset_iff` / 引理 `id_subset_iff`

English:
lemma id_subset_iff
  statement: .id subseteq R ↔ R.IsRefl where
  proof: ⟨fun _ => h rfl⟩
  mpr _ := id_subset

中文:
引理 id_subset_iff
  结论: .id subseteq R ↔ R.IsRefl where
  证明: ⟨fun _ => h rfl⟩
  mpr _ := id_subset
-/
lemma id_subset_iff : .id subseteq R ↔ R.IsRefl where
  mp h := ⟨fun _ => h rfl⟩
  mpr _ := id_subset

/--
Instance `isRefl_univ` / 实例 `isRefl_univ`

English:
instance isRefl_univ
  signature: : SetRel.IsRefl (.univ : SetRel α α) where
  body: trivial

中文:
实例 isRefl_univ
  签名: : SetRel.IsRefl (.univ : SetRel α α) where
  定义体: trivial
-/
instance isRefl_univ : SetRel.IsRefl (.univ : SetRel α α) where
  refl _ := trivial

/--
Instance `isRefl_inter` / 实例 `isRefl_inter`

English:
instance isRefl_inter
  signature: [R₁.IsRefl] [R₂.IsRefl]
  body: ⟨R₁.rfl, R₂.rfl⟩

中文:
实例 isRefl_inter
  签名: [R₁.IsRefl] [R₂.IsRefl]
  定义体: ⟨R₁.rfl, R₂.rfl⟩
-/
instance isRefl_inter [R₁.IsRefl] [R₂.IsRefl] : (R₁ inter R₂).IsRefl where
  refl _ := ⟨R₁.rfl, R₂.rfl⟩

/--
Instance `IsRefl.comp` / 实例 `IsRefl.comp`

English:
instance IsRefl.comp
  signature: [R₁.IsRefl] [R₂.IsRefl]
  body: ⟨_, R₁.rfl, R₂.rfl⟩

中文:
实例 IsRefl.comp
  签名: [R₁.IsRefl] [R₂.IsRefl]
  定义体: ⟨_, R₁.rfl, R₂.rfl⟩
-/
instance IsRefl.comp [R₁.IsRefl] [R₂.IsRefl] : (R₁.comp R₂).IsRefl where
  refl _ := ⟨_, R₁.rfl, R₂.rfl⟩

/--
lemma `IsRefl.sInter` / 引理 `IsRefl.sInter`

English:
lemma IsRefl.sInter
  given: {ℛ : Set <| SetRel α α} (hℛ : forall R in ℛ, R.IsRefl)
  proof: (hℛ R hR).refl _

中文:
引理 IsRefl.集合交集
  条件: {ℛ : 集合 <| SetRel α α} (hℛ : 对任意 R in ℛ, R.IsRefl)
  证明: (hℛ R hR).refl _
-/
protected lemma IsRefl.sInter {ℛ : Set <| SetRel α α} (hℛ : forall R in ℛ, R.IsRefl) :
    SetRel.IsRefl (⋂₀ ℛ) where
  refl _a R hR := (hℛ R hR).refl _

/--
Instance `isRefl_iInter` / 实例 `isRefl_iInter`

English:
instance isRefl_iInter
  signature: {R : ι -> SetRel α α} [forall i, (R i).IsRefl]
  body: .sInter by simpa

中文:
实例 isRefl_i整数er
  签名: {R : ι -> SetRel α α} [对任意 i, (R i).IsRefl]
  定义体: .sInter by simpa

Depends on / 依赖: sInter
-/
instance isRefl_iInter {R : ι -> SetRel α α} [forall i, (R i).IsRefl] :
SetRel.IsRefl (⋂ i, R i) := .sInter by simpa

/--
Instance `isRefl_preimage` / 实例 `isRefl_preimage`

English:
instance isRefl_preimage
  signature: {f : β -> α} [R.IsRefl]
  body: R.rfl

中文:
实例 isRefl_preimage
  签名: {f : β -> α} [R.IsRefl]
  定义体: R.rfl

Depends on / 依赖: R.rfl
-/
instance isRefl_preimage {f : β -> α} [R.IsRefl] : SetRel.IsRefl (Prod.map f f ⁻¹' R) where
  refl _ := R.rfl

/--
lemma `isRefl_mono` / 引理 `isRefl_mono`

English:
lemma isRefl_mono
  given: [R₁.IsRefl] (hR : R₁ subseteq R₂)
  statement: R₂.IsRefl where refl _
  proof: hR R₁.rfl

中文:
引理 isRefl_mono
  条件: [R₁.IsRefl] (hR : R₁ subseteq R₂)
  结论: R₂.IsRefl where refl _
  证明: hR R₁.rfl
-/
lemma isRefl_mono [R₁.IsRefl] (hR : R₁ subseteq R₂) : R₂.IsRefl where refl _ := hR R₁.rfl

/--
lemma `left_subset_comp` / 引理 `left_subset_comp`

English:
lemma left_subset_comp
  given: {R : SetRel α β} [S.IsRefl]
  statement: R subseteq R ○ S
  proof: by
  simpa using comp_subset_comp_right id_subset

中文:
引理 left_subset_comp
  条件: {R : SetRel α β} [S.IsRefl]
  结论: R subseteq R ○ S
  证明: by
  simpa using comp_subset_comp_right id_subset

Depends on / 依赖: comp_subset_comp_right, id_subset
-/
lemma left_subset_comp {R : SetRel α β} [S.IsRefl] : R subseteq R ○ S := by
  simpa using comp_subset_comp_right id_subset

/--
lemma `right_subset_comp` / 引理 `right_subset_comp`

English:
lemma right_subset_comp
  given: [R.IsRefl] {S : SetRel α β}
  statement: S subseteq R ○ S
  proof: by
  simpa using comp_subset_comp_left id_subset

中文:
引理 right_subset_comp
  条件: [R.IsRefl] {S : SetRel α β}
  结论: S subseteq R ○ S
  证明: by
  simpa using comp_subset_comp_left id_subset

Depends on / 依赖: comp_subset_comp_left, id_subset
-/
lemma right_subset_comp [R.IsRefl] {S : SetRel α β} : S subseteq R ○ S := by
  simpa using comp_subset_comp_left id_subset

/--
lemma `subset_iterate_comp` / 引理 `subset_iterate_comp`

English:
lemma subset_iterate_comp
  given: [R.IsRefl] {S : SetRel α β}
  statement: forall {n}, S subseteq (R ○ ·)^[n] S

中文:
引理 subset_iterate_comp
  条件: [R.IsRefl] {S : SetRel α β}
  结论: 对任意 {n}, S subseteq (R ○ ·)^[n] S
-/
lemma subset_iterate_comp [R.IsRefl] {S : SetRel α β} : forall {n}, S subseteq (R ○ ·)^[n] S
  | 0 => .rfl
  | _n + 1 => right_subset_comp.trans subset_iterate_comp

/--
lemma `self_subset_image` / 引理 `self_subset_image`

English:
lemma self_subset_image
  given: [R.IsRefl] (s : Set α)
  statement: s subseteq R.image s
  proof: fun x hx => ⟨x, hx, R.rfl⟩

中文:
引理 self_subset_image
  条件: [R.IsRefl] (s : 集合 α)
  结论: s subseteq R.像 s
  证明: fun x hx => ⟨x, hx, R.rfl⟩

Depends on / 依赖: R.rfl
-/
lemma self_subset_image [R.IsRefl] (s : Set α) : s subseteq R.image s :=
  fun x hx => ⟨x, hx, R.rfl⟩

/--
lemma `self_subset_preimage` / 引理 `self_subset_preimage`

English:
lemma self_subset_preimage
  given: [R.IsRefl] (s : Set α)
  statement: s subseteq R.preimage s
  proof: fun x hx => ⟨x, hx, R.rfl⟩

中文:
引理 self_subset_preimage
  条件: [R.IsRefl] (s : 集合 α)
  结论: s subseteq R.原像 s
  证明: fun x hx => ⟨x, hx, R.rfl⟩

Depends on / 依赖: R.rfl
-/
lemma self_subset_preimage [R.IsRefl] (s : Set α) : s subseteq R.preimage s :=
  fun x hx => ⟨x, hx, R.rfl⟩

/--
lemma `exists_eq_singleton_of_prod_subset_id` / 引理 `exists_eq_singleton_of_prod_subset_id`

English:
lemma exists_eq_singleton_of_prod_subset_id
  statement: {s t : Set α} (hs : s.Nonempty) (ht : t.Nonempty)
  proof: by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  simp only [Set.prod_subset_iff, mem_id] at hst
  obtain rfl := hst _ ha _ hb
  simp only [Set.eq_singleton_iff_unique_mem, and_assoc]
  exact ⟨a, ha, (hst · · _ hb), hb, (hst _ ha · · |>.symm)⟩

中文:
引理 存在_eq_singleton_of_prod_subset_id
  结论: {s t : 集合 α} (hs : s.非空) (ht : t.非空)
  证明: by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  simp only [Set.prod_subset_iff, mem_id] at hst
  obtain rfl := hst _ ha _ hb
  simp only [Set.eq_singleton_iff_unique_mem, and_assoc]
  exact ⟨a, ha, (hst · · _ hb), hb, (hst _ ha · · |>.symm)⟩

Depends on / 依赖: Set.eq_singleton_iff_unique_mem, Set.prod_subset_iff, and_assoc, eq_singleton_iff_unique_mem, mem_id, prod_subset_iff
-/
lemma exists_eq_singleton_of_prod_subset_id {s t : Set α} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ×ˢ t subseteq SetRel.id) : exists x, s = {x} ∧ t = {x} := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  simp only [Set.prod_subset_iff, mem_id] at hst
  obtain rfl := hst _ ha _ hb
  simp only [Set.eq_singleton_iff_unique_mem, and_assoc]
  exact ⟨a, ha, (hst · · _ hb), hb, (hst _ ha · · |>.symm)⟩

/-! ### Symmetric relations -/

variable (R) in
/--
Definition of `IsSymm` / `IsSymm` 的定义

English:
abbreviation IsSymm
  signature: : Prop
  body: Std.Symm (· ~[R] ·)

中文:
缩写 是Symm
  签名: : 命题
  定义体: Std.Symm (· ~[R] ·)
-/
protected abbrev IsSymm : Prop := Std.Symm (· ~[R] ·)

variable (R) in
/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: [R.IsSymm] (hab : a ~[R] b)
  statement: b ~[R] a
  proof: symm_of (· ~[R] ·) hab

中文:
引理 symm
  条件: [R.是Symm] (hab : a ~[R] b)
  结论: b ~[R] a
  证明: symm_of (· ~[R] ·) hab
-/
protected lemma symm [R.IsSymm] (hab : a ~[R] b) : b ~[R] a := symm_of (· ~[R] ·) hab

variable (R) in
/--
lemma `comm` / 引理 `comm`

English:
lemma comm
  given: [R.IsSymm]
  statement: a ~[R] b ↔ b ~[R] a
  proof: comm_of (· ~[R] ·)

中文:
引理 comm
  条件: [R.是Symm]
  结论: a ~[R] b ↔ b ~[R] a
  证明: comm_of (· ~[R] ·)
-/
protected lemma comm [R.IsSymm] : a ~[R] b ↔ b ~[R] a := comm_of (· ~[R] ·)

variable (R) in
/--
lemma `inv_eq_self` / 引理 `inv_eq_self`

English:
lemma inv_eq_self
  given: [R.IsSymm]
  statement: R.inv = R
  proof: by ext; exact R.comm

中文:
引理 inv_eq_self
  条件: [R.是Symm]
  结论: R.inv = R
  证明: by ext; exact R.comm
-/
@[simp] lemma inv_eq_self [R.IsSymm] : R.inv = R := by ext; exact R.comm

/--
lemma `inv_eq_self_iff` / 引理 `inv_eq_self_iff`

English:
lemma inv_eq_self_iff
  statement: R.inv = R ↔ R.IsSymm where
  proof: ⟨fun a b hab => by rwa [← hR]⟩
  mpr _ := inv_eq_self _

中文:
引理 inv_eq_self_iff
  结论: R.inv = R ↔ R.是Symm where
  证明: ⟨fun a b hab => by rwa [← hR]⟩
  mpr _ := inv_eq_self _
-/
lemma inv_eq_self_iff : R.inv = R ↔ R.IsSymm where
  mp hR := ⟨fun a b hab => by rwa [← hR]⟩
  mpr _ := inv_eq_self _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [R.IsSymm]
  signature: : R.inv.IsSymm
  body: by simpa

中文:
实例 [R.是Symm]
  签名: : R.inv.是Symm
  定义体: by simpa
-/
instance [R.IsSymm] : R.inv.IsSymm := by simpa

/--
Instance `isSymm_empty` / 实例 `isSymm_empty`

English:
instance isSymm_empty
  signature: : (∅ : SetRel α α).IsSymm where symm _ _
  body: by simp

中文:
实例 isSymm_empty
  签名: : (∅ : SetRel α α).是Symm where symm _ _
  定义体: by simp
-/
instance isSymm_empty : (∅ : SetRel α α).IsSymm where symm _ _ := by simp
/--
Instance `isSymm_univ` / 实例 `isSymm_univ`

English:
instance isSymm_univ
  signature: : SetRel.IsSymm (Set.univ : SetRel α α) where symm _ _
  body: by simp

中文:
实例 isSymm_univ
  签名: : SetRel.是Symm (集合.univ : SetRel α α) where symm _ _
  定义体: by simp
-/
instance isSymm_univ : SetRel.IsSymm (Set.univ : SetRel α α) where symm _ _ := by simp

/--
Instance `isSymm_inter` / 实例 `isSymm_inter`

English:
instance isSymm_inter
  signature: [R₁.IsSymm] [R₂.IsSymm]
  body: .imp R₁.symm R₂.symm

中文:
实例 isSymm_inter
  签名: [R₁.是Symm] [R₂.是Symm]
  定义体: .imp R₁.symm R₂.symm
-/
instance isSymm_inter [R₁.IsSymm] [R₂.IsSymm] : (R₁ inter R₂).IsSymm where
  symm _ _ := .imp R₁.symm R₂.symm

/--
lemma `IsSymm.sInter` / 引理 `IsSymm.sInter`

English:
lemma IsSymm.sInter
  given: {ℛ : Set <| SetRel α α} (hℛ : forall R in ℛ, R.IsSymm)
  proof: (hℛ R hR).symm _ _ hab R hR

中文:
引理 是Symm.集合交集
  条件: {ℛ : 集合 <| SetRel α α} (hℛ : 对任意 R in ℛ, R.是Symm)
  证明: (hℛ R hR).symm _ _ hab R hR
-/
protected lemma IsSymm.sInter {ℛ : Set <| SetRel α α} (hℛ : forall R in ℛ, R.IsSymm) :
    SetRel.IsSymm (⋂₀ ℛ) where
symm _a _b hab R hR := (hℛ R hR).symm _ _ hab R hR

/--
Instance `isSymm_iInter` / 实例 `isSymm_iInter`

English:
instance isSymm_iInter
  signature: {R : ι -> SetRel α α} [forall i, (R i).IsSymm]
  body: .sInter by simpa

中文:
实例 isSymm_i整数er
  签名: {R : ι -> SetRel α α} [对任意 i, (R i).是Symm]
  定义体: .sInter by simpa

Depends on / 依赖: sInter
-/
instance isSymm_iInter {R : ι -> SetRel α α} [forall i, (R i).IsSymm] :
SetRel.IsSymm (⋂ i, R i) := .sInter by simpa

/--
Instance `isSymm_id` / 实例 `isSymm_id`

English:
instance isSymm_id
  signature: : (SetRel.id : SetRel α α).IsSymm where symm _ _
  body: .symm

中文:
实例 isSymm_id
  签名: : (SetRel.id : SetRel α α).是Symm where symm _ _
  定义体: .symm
-/
instance isSymm_id : (SetRel.id : SetRel α α).IsSymm where symm _ _ := .symm

/--
Instance `isSymm_preimage` / 实例 `isSymm_preimage`

English:
instance isSymm_preimage
  signature: {f : β -> α} [R.IsSymm]
  body: R.symm

中文:
实例 isSymm_preimage
  签名: {f : β -> α} [R.是Symm]
  定义体: R.symm

Depends on / 依赖: R.symm
-/
instance isSymm_preimage {f : β -> α} [R.IsSymm] : SetRel.IsSymm (Prod.map f f ⁻¹' R) where
  symm _ _ := R.symm

/--
Instance `isSymm_image` / 实例 `isSymm_image`

English:
instance isSymm_image
  signature: {f : α -> β} [R.IsSymm]
  body: by
    simp only [Set.mem_image, Prod.exists, Prod.map_apply, Prod.mk.injEq, forall_exists_index,
      and_imp]
    rintro _ _ a₁ a₂ ha rfl rfl
    exact ⟨_, _, R.symm ha, rfl, rfl⟩

中文:
实例 isSymm_image
  签名: {f : α -> β} [R.是Symm]
  定义体: by
    simp only [Set.mem_image, Prod.exists, Prod.map_apply, Prod.mk.injEq, forall_exists_index,
      and_imp]
    rintro _ _ a₁ a₂ ha rfl rfl
    exact ⟨_, _, R.symm ha, rfl, rfl⟩

Depends on / 依赖: Prod.exists, Prod.map_apply, Prod.mk.injEq, R.symm, Set.mem_image, and_imp, forall_exists_index, map_apply, mem_image
-/
instance isSymm_image {f : α -> β} [R.IsSymm] : SetRel.IsSymm (Prod.map f f '' R) where
  symm := by
    simp only [Set.mem_image, Prod.exists, Prod.map_apply, Prod.mk.injEq, forall_exists_index,
      and_imp]
    rintro _ _ a₁ a₂ ha rfl rfl
    exact ⟨_, _, R.symm ha, rfl, rfl⟩

/--
Instance `isSymm_comp_inv` / 实例 `isSymm_comp_inv`

English:
instance isSymm_comp_inv
  signature: : (R ○ R.inv).IsSymm where
  body: by rintro ⟨b, hab, hbc⟩; exact ⟨b, hbc, hab⟩

中文:
实例 isSymm_comp_inv
  签名: : (R ○ R.inv).是Symm where
  定义体: by rintro ⟨b, hab, hbc⟩; exact ⟨b, hbc, hab⟩
-/
instance isSymm_comp_inv : (R ○ R.inv).IsSymm where
  symm a c := by rintro ⟨b, hab, hbc⟩; exact ⟨b, hbc, hab⟩

/--
Instance `isSymm_inv_comp` / 实例 `isSymm_inv_comp`

English:
instance isSymm_inv_comp
  signature: : (R.inv ○ R).IsSymm
  body: isSymm_comp_inv

中文:
实例 isSymm_inv_comp
  签名: : (R.inv ○ R).是Symm
  定义体: isSymm_comp_inv

Depends on / 依赖: isSymm_comp_inv
-/
instance isSymm_inv_comp : (R.inv ○ R).IsSymm := isSymm_comp_inv

/--
Instance `isSymm_comp_self` / 实例 `isSymm_comp_self`

English:
instance isSymm_comp_self
  signature: [R.IsSymm]
  body: by simpa using R.isSymm_comp_inv

中文:
实例 isSymm_comp_self
  签名: [R.是Symm]
  定义体: by simpa using R.isSymm_comp_inv

Depends on / 依赖: R.isSymm_comp_inv, isSymm_comp_inv
-/
instance isSymm_comp_self [R.IsSymm] : (R ○ R).IsSymm := by simpa using R.isSymm_comp_inv

/--
lemma `prod_subset_comm` / 引理 `prod_subset_comm`

English:
lemma prod_subset_comm
  given: [R.IsSymm]
  statement: s₁ ×ˢ s₂ subseteq R ↔ s₂ ×ˢ s₁ subseteq R
  proof: by
  rw [← R.inv_eq_self]; rw [SetRel.inv]; rw [← Set.image_subset_iff]; rw [Set.image_swap_prod]; rw [← SetRel.inv]; rw [R.inv_eq_self]

中文:
引理 prod_subset_comm
  条件: [R.是Symm]
  结论: s₁ ×ˢ s₂ subseteq R ↔ s₂ ×ˢ s₁ subseteq R
  证明: by
  rw [← R.inv_eq_self]; rw [SetRel.inv]; rw [← Set.image_subset_iff]; rw [Set.image_swap_prod]; rw [← SetRel.inv]; rw [R.inv_eq_self]

Depends on / 依赖: R.inv_eq_self, Set.image_subset_iff, Set.image_swap_prod, SetRel, SetRel.inv, image_subset_iff, image_swap_prod, inv_eq_self
-/
lemma prod_subset_comm [R.IsSymm] : s₁ ×ˢ s₂ subseteq R ↔ s₂ ×ˢ s₁ subseteq R := by
  rw [← R.inv_eq_self]; rw [SetRel.inv]; rw [← Set.image_subset_iff]; rw [Set.image_swap_prod]; rw [← SetRel.inv]; rw [R.inv_eq_self]

/--
lemma `preimage_eq_image` / 引理 `preimage_eq_image`

English:
lemma preimage_eq_image
  given: [R.IsSymm]
  statement: R.preimage s = R.image s
  proof: by
  rw [← preimage_inv]; rw [inv_eq_self]

中文:
引理 preimage_eq_image
  条件: [R.是Symm]
  结论: R.原像 s = R.像 s
  证明: by
  rw [← preimage_inv]; rw [inv_eq_self]

Depends on / 依赖: inv_eq_self, preimage_inv
-/
lemma preimage_eq_image [R.IsSymm] : R.preimage s = R.image s := by
  rw [← preimage_inv]; rw [inv_eq_self]

variable (R) in
/--
Definition of `symmetrize` / `symmetrize` 的定义

English:
definition symmetrize
  signature: : SetRel α α
  body: R inter R.inv

中文:
定义 symmetrize
  签名: : SetRel α α
  定义体: R inter R.inv

Depends on / 依赖: R.inv
-/
def symmetrize : SetRel α α := R inter R.inv

/--
Instance `isSymm_symmetrize` / 实例 `isSymm_symmetrize`

English:
instance isSymm_symmetrize
  signature: : R.symmetrize.IsSymm where symm _ _
  body: .symm

中文:
实例 isSymm_symmetrize
  签名: : R.symmetrize.是Symm where symm _ _
  定义体: .symm
-/
instance isSymm_symmetrize : R.symmetrize.IsSymm where symm _ _ := .symm

/--
lemma `symmetrize_subset_self` / 引理 `symmetrize_subset_self`

English:
lemma symmetrize_subset_self
  statement: R.symmetrize subseteq R
  proof: Set.inter_subset_left

中文:
引理 symmetrize_subset_self
  结论: R.symmetrize subseteq R
  证明: Set.inter_subset_left

Depends on / 依赖: Set.inter_subset_left, inter_subset_left
-/
lemma symmetrize_subset_self : R.symmetrize subseteq R := Set.inter_subset_left
/--
lemma `symmetrize_subset_inv` / 引理 `symmetrize_subset_inv`

English:
lemma symmetrize_subset_inv
  statement: R.symmetrize subseteq R.inv
  proof: Set.inter_subset_right

中文:
引理 symmetrize_subset_inv
  结论: R.symmetrize subseteq R.inv
  证明: Set.inter_subset_right

Depends on / 依赖: Set.inter_subset_right, inter_subset_right
-/
lemma symmetrize_subset_inv : R.symmetrize subseteq R.inv := Set.inter_subset_right
/--
lemma `subset_symmetrize` / 引理 `subset_symmetrize`

English:
lemma subset_symmetrize
  given: {S : SetRel α α}
  statement: S subseteq R.symmetrize ↔ S subseteq R ∧ S subseteq R.inv
  proof: Set.subset_inter_iff

@[gcongr]

中文:
引理 subset_symmetrize
  条件: {S : SetRel α α}
  结论: S subseteq R.symmetrize ↔ S subseteq R ∧ S subseteq R.inv
  证明: Set.subset_inter_iff

@[gcongr]

Depends on / 依赖: Set.subset_inter_iff, subset_inter_iff
-/
lemma subset_symmetrize {S : SetRel α α} : S subseteq R.symmetrize ↔ S subseteq R ∧ S subseteq R.inv :=
  Set.subset_inter_iff

@[gcongr]
/--
lemma `symmetrize_mono` / 引理 `symmetrize_mono`

English:
lemma symmetrize_mono
  given: (h : R₁ subseteq R₂)
  statement: R₁.symmetrize subseteq R₂.symmetrize
  proof: Set.inter_subset_inter h Set.preimage_mono h

中文:
引理 symmetrize_mono
  条件: (h : R₁ subseteq R₂)
  结论: R₁.symmetrize subseteq R₂.symmetrize
  证明: Set.inter_subset_inter h Set.preimage_mono h

Depends on / 依赖: Set.inter_subset_inter, Set.preimage_mono, inter_subset_inter, preimage_mono
-/
lemma symmetrize_mono (h : R₁ subseteq R₂) : R₁.symmetrize subseteq R₂.symmetrize :=
Set.inter_subset_inter h Set.preimage_mono h

/-! ### Transitive relations -/

variable (R) in
/--
Definition of `IsTrans` / `IsTrans` 的定义

English:
abbreviation IsTrans
  signature: : Prop
  body: IsTrans α (· ~[R] ·)

中文:
缩写 是Trans
  签名: : 命题
  定义体: IsTrans α (· ~[R] ·)
-/
protected abbrev IsTrans : Prop := IsTrans α (· ~[R] ·)

variable (R) in
/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  given: [R.IsTrans] (hab : a ~[R] b) (hbc : b ~[R] c)
  statement: a ~[R] c
  proof: trans_of (· ~[R] ·) hab hbc

中文:
引理 trans
  条件: [R.是Trans] (hab : a ~[R] b) (hbc : b ~[R] c)
  结论: a ~[R] c
  证明: trans_of (· ~[R] ·) hab hbc
-/
protected lemma trans [R.IsTrans] (hab : a ~[R] b) (hbc : b ~[R] c) : a ~[R] c :=
  trans_of (· ~[R] ·) hab hbc

instance {R : α -> α -> Prop} [IsTrans α R] : SetRel.IsTrans {(a, b) | R a b} := ‹_›

/--
lemma `comp_subset_self` / 引理 `comp_subset_self`

English:
lemma comp_subset_self
  given: [R.IsTrans]
  statement: R ○ R subseteq R
  proof: fun ⟨_, _⟩ ⟨_, hab, hbc⟩ => R.trans hab hbc

中文:
引理 comp_subset_self
  条件: [R.是Trans]
  结论: R ○ R subseteq R
  证明: fun ⟨_, _⟩ ⟨_, hab, hbc⟩ => R.trans hab hbc

Depends on / 依赖: R.trans
-/
lemma comp_subset_self [R.IsTrans] : R ○ R subseteq R := fun ⟨_, _⟩ ⟨_, hab, hbc⟩ => R.trans hab hbc

/--
lemma `comp_eq_self` / 引理 `comp_eq_self`

English:
lemma comp_eq_self
  given: [R.IsRefl] [R.IsTrans]
  statement: R ○ R = R
  proof: subset_antisymm comp_subset_self left_subset_comp

中文:
引理 comp_eq_self
  条件: [R.IsRefl] [R.是Trans]
  结论: R ○ R = R
  证明: subset_antisymm comp_subset_self left_subset_comp

Depends on / 依赖: comp_subset_self, left_subset_comp, subset_antisymm
-/
lemma comp_eq_self [R.IsRefl] [R.IsTrans] : R ○ R = R :=
  subset_antisymm comp_subset_self left_subset_comp

/--
lemma `isTrans_iff_comp_subset_self` / 引理 `isTrans_iff_comp_subset_self`

English:
lemma isTrans_iff_comp_subset_self
  statement: R.IsTrans ↔ R ○ R subseteq R where
  proof: comp_subset_self
  mpr h := ⟨fun _ _ _ hx hy => h ⟨_, hx, hy⟩⟩

中文:
引理 isTrans_iff_comp_subset_self
  结论: R.是Trans ↔ R ○ R subseteq R where
  证明: comp_subset_self
  mpr h := ⟨fun _ _ _ hx hy => h ⟨_, hx, hy⟩⟩

Depends on / 依赖: comp_subset_self
-/
lemma isTrans_iff_comp_subset_self : R.IsTrans ↔ R ○ R subseteq R where
  mp _ := comp_subset_self
  mpr h := ⟨fun _ _ _ hx hy => h ⟨_, hx, hy⟩⟩

/--
Instance `isTrans_empty` / 实例 `isTrans_empty`

English:
instance isTrans_empty
  signature: : (∅ : SetRel α α).IsTrans where trans _ _ _
  body: by simp

中文:
实例 isTrans_empty
  签名: : (∅ : SetRel α α).是Trans where trans _ _ _
  定义体: by simp
-/
instance isTrans_empty : (∅ : SetRel α α).IsTrans where trans _ _ _ := by simp
/--
Instance `isTrans_univ` / 实例 `isTrans_univ`

English:
instance isTrans_univ
  signature: : SetRel.IsTrans (Set.univ : SetRel α α) where trans _ _ _
  body: by simp

中文:
实例 isTrans_univ
  签名: : SetRel.是Trans (集合.univ : SetRel α α) where trans _ _ _
  定义体: by simp
-/
instance isTrans_univ : SetRel.IsTrans (Set.univ : SetRel α α) where trans _ _ _ := by simp
/--
Instance `isTrans_singleton` / 实例 `isTrans_singleton`

English:
instance isTrans_singleton
  signature: (x : α × α)
  body: by aesop

中文:
实例 isTrans_singleton
  签名: (x : α × α)
  定义体: by aesop
-/
instance isTrans_singleton (x : α × α) : SetRel.IsTrans {x} where trans _ _ _ := by aesop

/--
Instance `isTrans_inter` / 实例 `isTrans_inter`

English:
instance isTrans_inter
  signature: [R₁.IsTrans] [R₂.IsTrans]
  body: ⟨R₁.trans hab.1 hbc.1, R₂.trans hab.2 hbc.2⟩

中文:
实例 isTrans_inter
  签名: [R₁.是Trans] [R₂.是Trans]
  定义体: ⟨R₁.trans hab.1 hbc.1, R₂.trans hab.2 hbc.2⟩
-/
instance isTrans_inter [R₁.IsTrans] [R₂.IsTrans] : (R₁ inter R₂).IsTrans where
  trans _a _b _c hab hbc := ⟨R₁.trans hab.1 hbc.1, R₂.trans hab.2 hbc.2⟩

/--
lemma `IsTrans.sInter` / 引理 `IsTrans.sInter`

English:
lemma IsTrans.sInter
  given: {ℛ : Set <| SetRel α α} (hℛ : forall R in ℛ, R.IsTrans)
  proof: (hℛ R hR).trans _ _ _ (hab R hR) hbc R hR

中文:
引理 是Trans.集合交集
  条件: {ℛ : 集合 <| SetRel α α} (hℛ : 对任意 R in ℛ, R.是Trans)
  证明: (hℛ R hR).trans _ _ _ (hab R hR) hbc R hR
-/
protected lemma IsTrans.sInter {ℛ : Set <| SetRel α α} (hℛ : forall R in ℛ, R.IsTrans) :
    SetRel.IsTrans (⋂₀ ℛ) where
trans _a _b _c hab hbc R hR := (hℛ R hR).trans _ _ _ (hab R hR) hbc R hR

/--
Instance `isTrans_iInter` / 实例 `isTrans_iInter`

English:
instance isTrans_iInter
  signature: {R : ι -> SetRel α α} [forall i, (R i).IsTrans]
  body: .sInter by simpa

中文:
实例 isTrans_i整数er
  签名: {R : ι -> SetRel α α} [对任意 i, (R i).是Trans]
  定义体: .sInter by simpa

Depends on / 依赖: sInter
-/
instance isTrans_iInter {R : ι -> SetRel α α} [forall i, (R i).IsTrans] :
SetRel.IsTrans (⋂ i, R i) := .sInter by simpa

/--
Instance `isTrans_id` / 实例 `isTrans_id`

English:
instance isTrans_id
  signature: : (.id : SetRel α α).IsTrans where trans _ _ _
  body: .trans

中文:
实例 isTrans_id
  签名: : (.id : SetRel α α).是Trans where trans _ _ _
  定义体: .trans
-/
instance isTrans_id : (.id : SetRel α α).IsTrans where trans _ _ _ := .trans

/--
Instance `isTrans_preimage` / 实例 `isTrans_preimage`

English:
instance isTrans_preimage
  signature: {f : β -> α} [R.IsTrans]
  body: R.trans

中文:
实例 isTrans_preimage
  签名: {f : β -> α} [R.是Trans]
  定义体: R.trans

Depends on / 依赖: R.trans
-/
instance isTrans_preimage {f : β -> α} [R.IsTrans] : SetRel.IsTrans (Prod.map f f ⁻¹' R) where
  trans _ _ _ := R.trans

/--
Instance `isTrans_symmetrize` / 实例 `isTrans_symmetrize`

English:
instance isTrans_symmetrize
  signature: [R.IsTrans]
  body: ⟨R.trans hab.1 hbc.1, R.trans hbc.2 hab.2⟩

中文:
实例 isTrans_symmetrize
  签名: [R.是Trans]
  定义体: ⟨R.trans hab.1 hbc.1, R.trans hbc.2 hab.2⟩

Depends on / 依赖: R.trans
-/
instance isTrans_symmetrize [R.IsTrans] : R.symmetrize.IsTrans where
  trans _a _b _c hab hbc := ⟨R.trans hab.1 hbc.1, R.trans hbc.2 hab.2⟩

variable (R) in
/--
Definition of `IsIrrefl` / `IsIrrefl` 的定义

English:
abbreviation IsIrrefl
  signature: : Prop
  body: Std.Irrefl (· ~[R] ·)

中文:
缩写 IsIrrefl
  签名: : 命题
  定义体: Std.Irrefl (· ~[R] ·)
-/
protected abbrev IsIrrefl : Prop := Std.Irrefl (· ~[R] ·)

variable (R a) in
/--
lemma `irrefl` / 引理 `irrefl`

English:
lemma irrefl
  given: [R.IsIrrefl]
  statement: ¬ a ~[R] a
  proof: irrefl_of (· ~[R] ·) _

中文:
引理 irrefl
  条件: [R.IsIrrefl]
  结论: ¬ a ~[R] a
  证明: irrefl_of (· ~[R] ·) _
-/
protected lemma irrefl [R.IsIrrefl] : ¬ a ~[R] a := irrefl_of (· ~[R] ·) _

instance {R : α -> α -> Prop} [Std.Irrefl R] : SetRel.IsIrrefl {(a, b) | R a b} := ‹_›

variable (R) in
/--
Definition of `IsWellFounded` / `IsWellFounded` 的定义

English:
abbreviation IsWellFounded
  signature: : Prop
  body: WellFounded (· ~[R] ·)

中文:
缩写 是良基
  签名: : 命题
  定义体: WellFounded (· ~[R] ·)

Depends on / 依赖: WellFounded
-/
abbrev IsWellFounded : Prop := WellFounded (· ~[R] ·)

variable (R S) in
/--
Definition of `Hom` / `Hom` 的定义

English:
abbreviation Hom
  body: (· ~[R] ·) ->r (· ~[S] ·)

中文:
缩写 态射
  定义体: (· ~[R] ·) ->r (· ~[S] ·)
-/
abbrev Hom := (· ~[R] ·) ->r (· ~[S] ·)

end SetRel

open Set
open scoped SetRel

namespace Function
variable {f : α -> β} {a : α} {b : β}

/--
Definition of `graph` / `graph` 的定义

English:
definition graph
  signature: (f : α -> β)
  body: {(a, b) | f a = b}

中文:
定义 graph
  签名: (f : α -> β)
  定义体: {(a, b) | f a = b}
-/
def graph (f : α -> β) : SetRel α β := {(a, b) | f a = b}

/--
lemma `mem_graph` / 引理 `mem_graph`

English:
lemma mem_graph
  statement: a ~[f.graph] b ↔ f a = b
  proof: .rfl

中文:
引理 mem_graph
  结论: a ~[f.graph] b ↔ f a = b
  证明: .rfl

Depends on / 依赖: Algebra
-/
@[simp] lemma mem_graph : a ~[f.graph] b ↔ f a = b := .rfl

/--
theorem `graph_injective` / 定理 `graph_injective`

English:
theorem graph_injective
  statement: Injective (graph : (α -> β) -> SetRel α β)
  proof: by
  aesop (add simp [Injective, Set.ext_iff])

中文:
定理 graph_injective
  结论: 单射 (graph : (α -> β) -> SetRel α β)
  证明: by
  aesop (add simp [Injective, Set.ext_iff])

Depends on / 依赖: Injective, IsScalarTower, IsScalarTower.right, Set.ext_iff, ext_iff
-/
theorem graph_injective : Injective (graph : (α -> β) -> SetRel α β) := by
  aesop (add simp [Injective, Set.ext_iff])

/--
lemma `graph_inj` / 引理 `graph_inj`

English:
lemma graph_inj
  given: {f g : α -> β}
  statement: f.graph = g.graph ↔ f = g
  proof: graph_injective.eq_iff

中文:
引理 graph_inj
  条件: {f g : α -> β}
  结论: f.graph = g.graph ↔ f = g
  证明: graph_injective.eq_iff
-/
@[simp] lemma graph_inj {f g : α -> β} : f.graph = g.graph ↔ f = g := graph_injective.eq_iff

/--
lemma `graph_id` / 引理 `graph_id`

English:
lemma graph_id
  statement: graph (id : α -> α) = .id
  proof: by aesop

中文:
引理 graph_id
  结论: graph (id : α -> α) = .id
  证明: by aesop
-/
@[simp] lemma graph_id : graph (id : α -> α) = .id := by aesop

/--
theorem `graph_comp` / 定理 `graph_comp`

English:
theorem graph_comp
  given: (f : β -> γ) (g : α -> β)
  statement: graph (f ∘ g) = graph g ○ graph f
  proof: by aesop

中文:
定理 graph_comp
  条件: (f : β -> γ) (g : α -> β)
  结论: graph (f ∘ g) = graph g ○ graph f
  证明: by aesop
-/
theorem graph_comp (f : β -> γ) (g : α -> β) : graph (f ∘ g) = graph g ○ graph f := by aesop

/--
Definition of `tupleGraph` / `tupleGraph` 的定义

English:
definition tupleGraph
  signature: (f : (α -> β) -> β)
  body: { v | f (v ∘ some) = v none }

中文:
定义 tupleGraph
  签名: (f : (α -> β) -> β)
  定义体: { v | f (v ∘ some) = v none }

Depends on / 依赖: ContMDiffMap, ContMDiffMap.coe_smul, Pi.smul_apply, coe_smul, mul_assoc, smul_apply, smul_def, smul_eq_mul
-/
def tupleGraph (f : (α -> β) -> β) : Set (Option α -> β) :=
  { v | f (v ∘ some) = v none }

end Function

/--
theorem `Equiv.graph_inv` / 定理 `Equiv.graph_inv`

English:
theorem Equiv.graph_inv
  given: (f : α ≃ β)
  statement: (f.symm : β -> α).graph = SetRel.inv (f : α -> β).graph
  proof: by
  aesop

中文:
定理 等价.graph_inv
  条件: (f : α ≃ β)
  结论: (f.symm : β -> α).graph = SetRel.inv (f : α -> β).graph
  证明: by
  aesop
-/
theorem Equiv.graph_inv (f : α ≃ β) : (f.symm : β -> α).graph = SetRel.inv (f : α -> β).graph := by
  aesop

/--
lemma `SetRel.exists_graph_eq_iff` / 引理 `SetRel.exists_graph_eq_iff`

English:
lemma SetRel.exists_graph_eq_iff
  given: (R : SetRel α β)
  proof: by
  constructor
  · rintro ⟨f, rfl, _⟩ x
    simp
  intro h
  choose f hf using fun x => (h x).exists
  refine ⟨f, ?_, by aesop⟩
  ext ⟨a, b⟩
  constructor
  · aesop
  · exact (h _).unique (hf _)

中文:
引理 SetRel.存在_graph_eq_iff
  条件: (R : SetRel α β)
  证明: by
  constructor
  · rintro ⟨f, rfl, _⟩ x
    simp
  intro h
  choose f hf using fun x => (h x).exists
  refine ⟨f, ?_, by aesop⟩
  ext ⟨a, b⟩
  constructor
  · aesop
  · exact (h _).unique (hf _)

Depends on / 依赖: unique
-/
lemma SetRel.exists_graph_eq_iff (R : SetRel α β) :
    (exists! f, Function.graph f = R) ↔ forall a, exists! b, a ~[R] b := by
  constructor
  · rintro ⟨f, rfl, _⟩ x
    simp
  intro h
  choose f hf using fun x => (h x).exists
  refine ⟨f, ?_, by aesop⟩
  ext ⟨a, b⟩
  constructor
  · aesop
  · exact (h _).unique (hf _)

namespace Set

/--
theorem `image_eq` / 定理 `image_eq`

English:
theorem image_eq
  given: (f : α -> β) (s : Set α)
  statement: f '' s = (Function.graph f).image s
  proof: by
  rfl

中文:
定理 image_eq
  条件: (f : α -> β) (s : 集合 α)
  结论: f '' s = (函数.graph f).像 s
  证明: by
  rfl
-/
theorem image_eq (f : α -> β) (s : Set α) : f '' s = (Function.graph f).image s := by
  rfl

/--
theorem `preimage_eq` / 定理 `preimage_eq`

English:
theorem preimage_eq
  given: (f : α -> β) (s : Set β)
  statement: f ⁻¹' s = (Function.graph f).preimage s
  proof: by
  simp [Set.preimage, SetRel.preimage]

中文:
定理 preimage_eq
  条件: (f : α -> β) (s : 集合 β)
  结论: f ⁻¹' s = (函数.graph f).原像 s
  证明: by
  simp [Set.preimage, SetRel.preimage]

Depends on / 依赖: Set.preimage, SetRel, SetRel.preimage, preimage
-/
theorem preimage_eq (f : α -> β) (s : Set β) : f ⁻¹' s = (Function.graph f).preimage s := by
  simp [Set.preimage, SetRel.preimage]

/--
theorem `preimage_eq_core` / 定理 `preimage_eq_core`

English:
theorem preimage_eq_core
  given: (f : α -> β) (s : Set β)
  statement: f ⁻¹' s = (Function.graph f).core s
  proof: by
  simp [Set.preimage, SetRel.core]

中文:
定理 preimage_eq_core
  条件: (f : α -> β) (s : 集合 β)
  结论: f ⁻¹' s = (函数.graph f).core s
  证明: by
  simp [Set.preimage, SetRel.core]

Depends on / 依赖: Set.preimage, SetRel, SetRel.core, preimage
-/
theorem preimage_eq_core (f : α -> β) (s : Set β) : f ⁻¹' s = (Function.graph f).core s := by
  simp [Set.preimage, SetRel.core]

end Set

/--
Definition of `Rel` / `Rel` 的定义

English:
abbreviation Rel
  signature: (α β : Type*)
  body: α -> β -> Prop

中文:
缩写 关系
  签名: (α β : 类型)
  定义体: α -> β -> Prop
-/
abbrev Rel (α β : Type*) : Type _ := α -> β -> Prop
