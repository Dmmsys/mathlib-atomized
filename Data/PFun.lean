/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jeremy Avigad, Simon Hudon
-/
module

public import Batteries.Tactic.GeneralizeProofs
public import Mathlib.Data.Part
public import Mathlib.Data.Rel

/-!
# Partial functions

This file defines partial functions. Partial functions are like functions, except they can also be
"undefined" on some inputs. We define them as functions `α → Part β`.

## Definitions

* `PFun α β`: Type of partial functions from `α` to `β`. Defined as `α → Part β` and denoted
  `α →. β`.
* `PFun.Dom`: Domain of a partial function. Set of values on which it is defined. Not to be confused
  with the domain of a function `α → β`, which is a type (`α` presently).
* `PFun.fn`: Evaluation of a partial function. Takes in an element and a proof it belongs to the
  partial function's `Dom`.
* `PFun.asSubtype`: Returns a partial function as a function from its `Dom`.
* `PFun.toSubtype`: Restricts the codomain of a function to a subtype.
* `PFun.evalOpt`: Returns a partial function with a decidable `Dom` as a function `a → Option β`.
* `PFun.lift`: Turns a function into a partial function.
* `PFun.id`: The identity as a partial function.
* `PFun.comp`: Composition of partial functions.
* `PFun.restrict`: Restriction of a partial function to a smaller `Dom`.
* `PFun.res`: Turns a function into a partial function with a prescribed domain.
* `PFun.fix` : First return map of a partial function `f : α →. β ⊕ α`.
* `PFun.fixInduction`: A recursion principle for `PFun.fix`.

### Partial functions as relations

Partial functions can be considered as relations, so we specialize some `Rel` definitions to `PFun`:
* `PFun.image`: Image of a set under a partial function.
* `PFun.ran`: Range of a partial function.
* `PFun.preimage`: Preimage of a set under a partial function.
* `PFun.core`: Core of a set under a partial function.
* `PFun.graph`: Graph of a partial function `a →. β` as a `Set (α × β)`.
* `PFun.graph'`: Graph of a partial function `a →. β` as a `Rel α β`.

### `PFun α` as a monad

Monad operations:
* `PFun.pure`: The monad `pure` function, the constant `x` function.
* `PFun.bind`: The monad `bind` function, pointwise `Part.bind`
* `PFun.map`: The monad `map` function, pointwise `Part.map`.
-/

@[expose] public section

open Function

/--
Definition of `PFun` / `PFun` 的定义

English:
definition PFun
  signature: (α β : Type*)
  body: α -> Part β

中文:
定义 PFun
  签名: (α β : 类型)
  定义体: α -> Part β
-/
def PFun (α β : Type*) :=
  α -> Part β

/-- `α →. β` is notation for the type `PFun α β` of partial functions from `α` to `β`. -/
infixr:25 " ->. " => PFun

namespace PFun

variable {α β γ δ ε ι : Type*}

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (α ->. β)
  body: ⟨fun _ => Part.none⟩

中文:
实例 inhabited
  签名: : 可居 (α ->. β)
  定义体: ⟨fun _ => Part.none⟩

Depends on / 依赖: Part.none
-/
instance inhabited : Inhabited (α ->. β) :=
  ⟨fun _ => Part.none⟩

/--
Definition of `Dom` / `Dom` 的定义

English:
definition Dom
  signature: (f : α ->. β)
  body: {a | (f a).Dom}

@[simp]

中文:
定义 Dom
  签名: (f : α ->. β)
  定义体: {a | (f a).Dom}

@[simp]
-/
def Dom (f : α ->. β) : Set α :=
  {a | (f a).Dom}

@[simp]
/--
theorem `mem_dom` / 定理 `mem_dom`

English:
theorem mem_dom
  given: (f : α ->. β) (x : α)
  statement: x in Dom f ↔ exists y, y in f x
  proof: by simp [Dom, Part.dom_iff_mem]

@[simp]

中文:
定理 mem_dom
  条件: (f : α ->. β) (x : α)
  结论: x in Dom f ↔ 存在 y, y in f x
  证明: by simp [Dom, Part.dom_iff_mem]

@[simp]

Depends on / 依赖: Part.dom_iff_mem, dom_iff_mem
-/
theorem mem_dom (f : α ->. β) (x : α) : x in Dom f ↔ exists y, y in f x := by simp [Dom, Part.dom_iff_mem]

@[simp]
/--
theorem `dom_mk` / 定理 `dom_mk`

English:
theorem dom_mk
  given: (p : α -> Prop) (f : forall a, p a -> β)
  statement: (PFun.Dom fun x => ⟨p x, f x⟩) = { x | p x }
  proof: rfl

中文:
定理 dom_mk
  条件: (p : α -> 命题) (f : 对任意 a, p a -> β)
  结论: (PFun.Dom fun x => ⟨p x, f x⟩) = { x | p x }
  证明: rfl
-/
theorem dom_mk (p : α -> Prop) (f : forall a, p a -> β) : (PFun.Dom fun x => ⟨p x, f x⟩) = { x | p x } :=
  rfl

/--
theorem `dom_eq` / 定理 `dom_eq`

English:
theorem dom_eq
  given: (f : α ->. β)
  statement: Dom f = { x | exists y, y in f x }
  proof: Set.ext (mem_dom f)

中文:
定理 dom_eq
  条件: (f : α ->. β)
  结论: Dom f = { x | 存在 y, y in f x }
  证明: Set.ext (mem_dom f)

Depends on / 依赖: Set.ext, mem_dom
-/
theorem dom_eq (f : α ->. β) : Dom f = { x | exists y, y in f x } :=
  Set.ext (mem_dom f)

/--
Definition of `fn` / `fn` 的定义

English:
definition fn
  signature: (f : α ->. β) (a : α)
  body: (f a).get

@[simp]

中文:
定义 fn
  签名: (f : α ->. β) (a : α)
  定义体: (f a).get

@[simp]
-/
def fn (f : α ->. β) (a : α) : a in Dom f -> β :=
  (f a).get

@[simp]
/--
theorem `fn_apply` / 定理 `fn_apply`

English:
theorem fn_apply
  given: (f : α ->. β) (a : α)
  statement: f.fn a = (f a).get
  proof: rfl

中文:
定理 fn_apply
  条件: (f : α ->. β) (a : α)
  结论: f.fn a = (f a).get
  证明: rfl
-/
theorem fn_apply (f : α ->. β) (a : α) : f.fn a = (f a).get :=
  rfl

/--
Definition of `evalOpt` / `evalOpt` 的定义

English:
definition evalOpt
  signature: (f : α ->. β) [D : DecidablePred (· in Dom f)] (x : α)
  body: @Part.toOption _ _ (D x)

中文:
定义 evalOpt
  签名: (f : α ->. β) [D : DecidablePred (· in Dom f)] (x : α)
  定义体: @Part.toOption _ _ (D x)

Depends on / 依赖: Part.toOption, toOption
-/
def evalOpt (f : α ->. β) [D : DecidablePred (· in Dom f)] (x : α) : Option β :=
  @Part.toOption _ _ (D x)

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: {f g : α ->. β} (H1 : forall a, a in Dom f ↔ a in Dom g) (H2 : forall a p q, f.fn a p = g.fn a q)
  proof: funext fun a => Part.ext' (H1 a) (H2 a)

@[ext]

中文:
定理 ext'
  条件: {f g : α ->. β} (H1 : 对任意 a, a in Dom f ↔ a in Dom g) (H2 : 对任意 a p q, f.fn a p = g.fn a q)
  证明: funext fun a => Part.ext' (H1 a) (H2 a)

@[ext]

Depends on / 依赖: Part.ext
-/
theorem ext' {f g : α ->. β} (H1 : forall a, a in Dom f ↔ a in Dom g) (H2 : forall a p q, f.fn a p = g.fn a q) :
    f = g :=
  funext fun a => Part.ext' (H1 a) (H2 a)

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : α ->. β} (H : forall a b, b in f a ↔ b in g a)
  statement: f = g
  proof: funext fun a => Part.ext (H a)

中文:
定理 ext
  条件: {f g : α ->. β} (H : 对任意 a b, b in f a ↔ b in g a)
  结论: f = g
  证明: funext fun a => Part.ext (H a)

Depends on / 依赖: Part.ext
-/
theorem ext {f g : α ->. β} (H : forall a b, b in f a ↔ b in g a) : f = g :=
  funext fun a => Part.ext (H a)

/--
Definition of `asSubtype` / `asSubtype` 的定义

English:
definition asSubtype
  signature: (f : α ->. β) (s : f.Dom)
  body: f.fn s s.2

中文:
定义 asSubtype
  签名: (f : α ->. β) (s : f.Dom)
  定义体: f.fn s s.2

Depends on / 依赖: f.fn
-/
def asSubtype (f : α ->. β) (s : f.Dom) : β :=
  f.fn s s.2

/--
Definition of `equivSubtype` / `equivSubtype` 的定义

English:
definition equivSubtype
  signature: : (α ->. β) ≃ Σ p : α -> Prop, Subtype p -> β
  body: ⟨fun f => ⟨fun a => (f a).Dom, asSubtype f⟩, fun f x => ⟨f.1 x, fun h => f.2 ⟨x, h⟩⟩, fun _ =>
    funext fun _ => Part.eta _, fun ⟨p, f⟩ => by dsimp; congr⟩

中文:
定义 equivSubtype
  签名: : (α ->. β) ≃ Σ p : α -> 命题, 子类型 p -> β
  定义体: ⟨fun f => ⟨fun a => (f a).Dom, asSubtype f⟩, fun f x => ⟨f.1 x, fun h => f.2 ⟨x, h⟩⟩, fun _ =>
    funext fun _ => Part.eta _, fun ⟨p, f⟩ => by dsimp; congr⟩

Depends on / 依赖: Part.eta, asSubtype
-/
def equivSubtype : (α ->. β) ≃ Σ p : α -> Prop, Subtype p -> β :=
  ⟨fun f => ⟨fun a => (f a).Dom, asSubtype f⟩, fun f x => ⟨f.1 x, fun h => f.2 ⟨x, h⟩⟩, fun _ =>
    funext fun _ => Part.eta _, fun ⟨p, f⟩ => by dsimp; congr⟩

/--
theorem `asSubtype_eq_of_mem` / 定理 `asSubtype_eq_of_mem`

English:
theorem asSubtype_eq_of_mem
  given: {f : α ->. β} {x : α} {y : β} (fxy : y in f x) (domx : x in f.Dom)
  proof: Part.mem_unique (Part.get_mem _) fxy

中文:
定理 asSubtype_eq_of_mem
  条件: {f : α ->. β} {x : α} {y : β} (fxy : y in f x) (domx : x in f.Dom)
  证明: Part.mem_unique (Part.get_mem _) fxy

Depends on / 依赖: Part.get_mem, Part.mem_unique, get_mem, mem_unique
-/
theorem asSubtype_eq_of_mem {f : α ->. β} {x : α} {y : β} (fxy : y in f x) (domx : x in f.Dom) :
    f.asSubtype ⟨x, domx⟩ = y :=
  Part.mem_unique (Part.get_mem _) fxy

/-- Turn a total function into a partial function. -/
@[coe]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : α -> β)
  body: fun a => Part.some (f a)

中文:
定义 lift
  签名: (f : α -> β)
  定义体: fun a => Part.some (f a)
-/
protected def lift (f : α -> β) : α ->. β := fun a => Part.some (f a)

/--
Instance `coe` / 实例 `coe`

English:
instance coe
  signature: : Coe (α -> β) (α ->. β)
  body: ⟨PFun.lift⟩

@[simp]

中文:
实例 coe
  签名: : Coe (α -> β) (α ->. β)
  定义体: ⟨PFun.lift⟩

@[simp]

Depends on / 依赖: PFun.lift
-/
instance coe : Coe (α -> β) (α ->. β) :=
  ⟨PFun.lift⟩

@[simp]
/--
theorem `coe_val` / 定理 `coe_val`

English:
theorem coe_val
  given: (f : α -> β) (a : α)
  statement: (f : α ->. β) a = Part.some (f a)
  proof: rfl

@[simp]

中文:
定理 coe_val
  条件: (f : α -> β) (a : α)
  结论: (f : α ->. β) a = Part.some (f a)
  证明: rfl

@[simp]
-/
theorem coe_val (f : α -> β) (a : α) : (f : α ->. β) a = Part.some (f a) :=
  rfl

@[simp]
/--
theorem `dom_coe` / 定理 `dom_coe`

English:
theorem dom_coe
  given: (f : α -> β)
  statement: (f : α ->. β).Dom = Set.univ
  proof: rfl

中文:
定理 dom_coe
  条件: (f : α -> β)
  结论: (f : α ->. β).Dom = 集合.univ
  证明: rfl
-/
theorem dom_coe (f : α -> β) : (f : α ->. β).Dom = Set.univ :=
  rfl

/--
theorem `lift_injective` / 定理 `lift_injective`

English:
theorem lift_injective
  statement: Injective (PFun.lift : (α -> β) -> α ->. β)
  proof: fun _ _ h =>
funext fun a => Part.some_injective congr_fun h a

中文:
定理 lift_injective
  结论: 单射 (PFun.lift : (α -> β) -> α ->. β)
  证明: fun _ _ h =>
funext fun a => Part.some_injective congr_fun h a
-/
theorem lift_injective : Injective (PFun.lift : (α -> β) -> α ->. β) := fun _ _ h =>
funext fun a => Part.some_injective congr_fun h a

/--
Definition of `graph` / `graph` 的定义

English:
definition graph
  signature: (f : α ->. β)
  body: { p | p.2 in f p.1 }

中文:
定义 graph
  签名: (f : α ->. β)
  定义体: { p | p.2 in f p.1 }
-/
def graph (f : α ->. β) : Set (α × β) :=
  { p | p.2 in f p.1 }

/--
Definition of `graph'` / `graph'` 的定义

English:
definition graph'
  signature: (f : α ->. β)
  body: {(x, y) : α × β | y in f x}

中文:
定义 graph'
  签名: (f : α ->. β)
  定义体: {(x, y) : α × β | y in f x}
-/
def graph' (f : α ->. β) : SetRel α β := {(x, y) : α × β | y in f x}

/--
Definition of `ran` / `ran` 的定义

English:
definition ran
  signature: (f : α ->. β)
  body: { b | exists a, b in f a }

中文:
定义 ran
  签名: (f : α ->. β)
  定义体: { b | exists a, b in f a }
-/
def ran (f : α ->. β) : Set β :=
  { b | exists a, b in f a }

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (f : α ->. β) {p : Set α} (H : p subseteq f.Dom)
  body: fun x =>
  (f x).restrict (x in p) (@H x)

中文:
定义 restrict
  签名: (f : α ->. β) {p : 集合 α} (H : p subseteq f.Dom)
  定义体: fun x =>
  (f x).restrict (x in p) (@H x)
-/
def restrict (f : α ->. β) {p : Set α} (H : p subseteq f.Dom) : α ->. β := fun x =>
  (f x).restrict (x in p) (@H x)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mem_restrict` / 定理 `mem_restrict`

English:
theorem mem_restrict
  given: {f : α ->. β} {s : Set α} (h : s subseteq f.Dom) (a : α) (b : β)
  proof: by simp [restrict]

中文:
定理 mem_restrict
  条件: {f : α ->. β} {s : 集合 α} (h : s subseteq f.Dom) (a : α) (b : β)
  证明: by simp [restrict]

Depends on / 依赖: restrict
-/
theorem mem_restrict {f : α ->. β} {s : Set α} (h : s subseteq f.Dom) (a : α) (b : β) :
    b in f.restrict h a ↔ a in s ∧ b in f a := by simp [restrict]

/--
Definition of `res` / `res` 的定义

English:
definition res
  signature: (f : α -> β) (s : Set α)
  body: (PFun.lift f).restrict s.subset_univ

中文:
定义 res
  签名: (f : α -> β) (s : 集合 α)
  定义体: (PFun.lift f).restrict s.subset_univ

Depends on / 依赖: PFun.lift, restrict, s.subset_univ, subset_univ
-/
def res (f : α -> β) (s : Set α) : α ->. β :=
  (PFun.lift f).restrict s.subset_univ

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_res` / 定理 `mem_res`

English:
theorem mem_res
  given: (f : α -> β) (s : Set α) (a : α) (b : β)
  statement: b in res f s a ↔ a in s ∧ f a = b
  proof: by
  simp [res, @eq_comm _ b]

中文:
定理 mem_res
  条件: (f : α -> β) (s : 集合 α) (a : α) (b : β)
  结论: b in res f s a ↔ a in s ∧ f a = b
  证明: by
  simp [res, @eq_comm _ b]

Depends on / 依赖: eq_comm
-/
theorem mem_res (f : α -> β) (s : Set α) (a : α) (b : β) : b in res f s a ↔ a in s ∧ f a = b := by
  simp [res, @eq_comm _ b]

/--
theorem `res_univ` / 定理 `res_univ`

English:
theorem res_univ
  given: (f : α -> β)
  statement: PFun.res f Set.univ = f
  proof: rfl

中文:
定理 res_univ
  条件: (f : α -> β)
  结论: PFun.res f 集合.univ = f
  证明: rfl
-/
theorem res_univ (f : α -> β) : PFun.res f Set.univ = f :=
  rfl

/--
theorem `dom_iff_graph` / 定理 `dom_iff_graph`

English:
theorem dom_iff_graph
  given: (f : α ->. β) (x : α)
  statement: x in f.Dom ↔ exists y, (x, y) in f.graph
  proof: Part.dom_iff_mem

中文:
定理 dom_iff_graph
  条件: (f : α ->. β) (x : α)
  结论: x in f.Dom ↔ 存在 y, (x, y) in f.graph
  证明: Part.dom_iff_mem

Depends on / 依赖: Part.dom_iff_mem, dom_iff_mem
-/
theorem dom_iff_graph (f : α ->. β) (x : α) : x in f.Dom ↔ exists y, (x, y) in f.graph :=
  Part.dom_iff_mem

/--
theorem `lift_graph` / 定理 `lift_graph`

English:
theorem lift_graph
  given: {f : α -> β} {a b}
  statement: (a, b) in (f : α ->. β).graph ↔ f a = b
  proof: show (exists _ : True, f a = b) ↔ f a = b by simp

中文:
定理 lift_graph
  条件: {f : α -> β} {a b}
  结论: (a, b) in (f : α ->. β).graph ↔ f a = b
  证明: show (exists _ : True, f a = b) ↔ f a = b by simp
-/
theorem lift_graph {f : α -> β} {a b} : (a, b) in (f : α ->. β).graph ↔ f a = b :=
  show (exists _ : True, f a = b) ↔ f a = b by simp

/--
Definition of `pure` / `pure` 的定义

English:
definition pure
  signature: (x : β)
  body: fun _ => Part.some x

中文:
定义 pure
  签名: (x : β)
  定义体: fun _ => Part.some x
-/
protected def pure (x : β) : α ->. β := fun _ => Part.some x

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (f : α ->. β) (g : β -> α ->. γ)
  body: fun a => (f a).bind fun b => g b a

@[simp]

中文:
定义 bind
  签名: (f : α ->. β) (g : β -> α ->. γ)
  定义体: fun a => (f a).bind fun b => g b a

@[simp]
-/
def bind (f : α ->. β) (g : β -> α ->. γ) : α ->. γ := fun a => (f a).bind fun b => g b a

@[simp]
/--
theorem `bind_apply` / 定理 `bind_apply`

English:
theorem bind_apply
  given: (f : α ->. β) (g : β -> α ->. γ) (a : α)
  statement: f.bind g a = (f a).bind fun b => g b a
  proof: rfl

中文:
定理 bind_apply
  条件: (f : α ->. β) (g : β -> α ->. γ) (a : α)
  结论: f.bind g a = (f a).bind fun b => g b a
  证明: rfl
-/
theorem bind_apply (f : α ->. β) (g : β -> α ->. γ) (a : α) : f.bind g a = (f a).bind fun b => g b a :=
  rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : β -> γ) (g : α ->. β)
  body: fun a => (g a).map f

中文:
定义 map
  签名: (f : β -> γ) (g : α ->. β)
  定义体: fun a => (g a).map f
-/
def map (f : β -> γ) (g : α ->. β) : α ->. γ := fun a => (g a).map f

/--
Instance `monad` / 实例 `monad`

English:
instance monad
  signature: : Monad (PFun α) where
  body: PFun.pure
  bind := PFun.bind
  map := PFun.map

中文:
实例 monad
  签名: : 单子 (PFun α) where
  定义体: PFun.pure
  bind := PFun.bind
  map := PFun.map

Depends on / 依赖: PFun.pure
-/
instance monad : Monad (PFun α) where
  pure := PFun.pure
  bind := PFun.bind
  map := PFun.map

/--
Instance `lawfulMonad` / 实例 `lawfulMonad`

English:
instance lawfulMonad
  signature: : LawfulMonad (PFun α)
  body: LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => funext fun _ => Part.bind_some_eq_map _ _)
  (id_map := fun f => by funext a; dsimp [Functor.map, PFun.map]; cases f a; rfl)
  (pure_bind := fun x f => funext fun _ => Part.bind_some _ (f x))
  (bind_assoc := fun f g k => funext fun a => (f a).bind_assoc (fun b => g b a) fun b => k b a)

中文:
实例 lawfulMonad
  签名: : 合法单子 (PFun α)
  定义体: LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => funext fun _ => Part.bind_some_eq_map _ _)
  (id_map := fun f => by funext a; dsimp [Functor.map, PFun.map]; cases f a; rfl)
  (pure_bind := fun x f => funext fun _ => Part.bind_some _ (f x))
  (bind_assoc := fun f g k => funext fun a => (f a).bind_assoc (fun b => g b a) fun b => k b a)

Depends on / 依赖: LawfulMonad, LawfulMonad.mk
-/
instance lawfulMonad : LawfulMonad (PFun α) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => funext fun _ => Part.bind_some_eq_map _ _)
  (id_map := fun f => by funext a; dsimp [Functor.map, PFun.map]; cases f a; rfl)
  (pure_bind := fun x f => funext fun _ => Part.bind_some _ (f x))
  (bind_assoc := fun f g k => funext fun a => (f a).bind_assoc (fun b => g b a) fun b => k b a)

/--
theorem `pure_defined` / 定理 `pure_defined`

English:
theorem pure_defined
  given: (p : Set α) (x : β)
  statement: p subseteq (@PFun.pure α _ x).Dom
  proof: p.subset_univ

中文:
定理 pure_defined
  条件: (p : 集合 α) (x : β)
  结论: p subseteq (@PFun.pure α _ x).Dom
  证明: p.subset_univ

Depends on / 依赖: p.subset_univ, subset_univ
-/
theorem pure_defined (p : Set α) (x : β) : p subseteq (@PFun.pure α _ x).Dom :=
  p.subset_univ

/--
theorem `bind_defined` / 定理 `bind_defined`

English:
theorem bind_defined
  statement: {α β γ} (p : Set α) {f : α ->. β} {g : β -> α ->. γ} (H1 : p subseteq f.Dom)
  proof: fun a ha =>
  (⟨H1 ha, H2 _ ha⟩ : a in (f >>= g).Dom)

中文:
定理 bind_defined
  结论: {α β γ} (p : 集合 α) {f : α ->. β} {g : β -> α ->. γ} (H1 : p subseteq f.Dom)
  证明: fun a ha =>
  (⟨H1 ha, H2 _ ha⟩ : a in (f >>= g).Dom)
-/
theorem bind_defined {α β γ} (p : Set α) {f : α ->. β} {g : β -> α ->. γ} (H1 : p subseteq f.Dom)
    (H2 : forall x, p subseteq (g x).Dom) : p subseteq (f >>= g).Dom := fun a ha =>
  (⟨H1 ha, H2 _ ha⟩ : a in (f >>= g).Dom)

/--
Definition of `fix` / `fix` 的定义

English:
definition fix
  signature: (f : α ->. β oplus α)
  body: fun a =>
  Part.assert (Acc (fun x y => Sum.inr x in f y) a) fun h =>
    WellFounded.fixF
      (fun a IH =>
        Part.assert (f a).Dom fun hf =>
          match e : (f a).get hf with
          | Sum.inl b => Part.some b
          | Sum.inr a' => IH a' ⟨hf, e⟩)
      a h

中文:
定义 fix
  签名: (f : α ->. β oplus α)
  定义体: fun a =>
  Part.assert (Acc (fun x y => Sum.inr x in f y) a) fun h =>
    WellFounded.fixF
      (fun a IH =>
        Part.assert (f a).Dom fun hf =>
          match e : (f a).get hf with
          | Sum.inl b => Part.some b
          | Sum.inr a' => IH a' ⟨hf, e⟩)
      a h
-/
def fix (f : α ->. β oplus α) : α ->. β := fun a =>
  Part.assert (Acc (fun x y => Sum.inr x in f y) a) fun h =>
    WellFounded.fixF
      (fun a IH =>
        Part.assert (f a).Dom fun hf =>
          match e : (f a).get hf with
          | Sum.inl b => Part.some b
          | Sum.inr a' => IH a' ⟨hf, e⟩)
      a h

/--
theorem `dom_of_mem_fix` / 定理 `dom_of_mem_fix`

English:
theorem dom_of_mem_fix
  given: {f : α ->. β oplus α} {a : α} {b : β} (h : b in f.fix a)
  statement: (f a).Dom
  proof: by
  let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
  rw [WellFounded.fixF_eq] at h₂; exact h₂.fst.fst

中文:
定理 dom_of_mem_fix
  条件: {f : α ->. β oplus α} {a : α} {b : β} (h : b in f.fix a)
  结论: (f a).Dom
  证明: by
  let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
  rw [WellFounded.fixF_eq] at h₂; exact h₂.fst.fst

Depends on / 依赖: Part.mem_assert_iff, WellFounded, WellFounded.fixF_eq, fixF_eq, fst.fst, mem_assert_iff
-/
theorem dom_of_mem_fix {f : α ->. β oplus α} {a : α} {b : β} (h : b in f.fix a) : (f a).Dom := by
  let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
  rw [WellFounded.fixF_eq] at h₂; exact h₂.fst.fst

/--
theorem `mem_fix_iff` / 定理 `mem_fix_iff`

English:
theorem mem_fix_iff
  given: {f : α ->. β oplus α} {a : α} {b : β}
  proof: ⟨fun h => by
    let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
    rw [WellFounded.fixF_eq] at h₂
    simp only [Part.mem_assert_iff] at h₂
    obtain ⟨h₂, h₃⟩ := h₂
    split at h₃
    next e => simp only [Part.mem_some_iff] at h₃; subst b; exact Or.inl ⟨h₂, e⟩
    next e => exact Or.inr ⟨_, ⟨_, e⟩, Part.mem_assert _ h₃⟩,
   fun h => by
    simp only [fix, Part.mem_assert_iff]
    rcases h with (⟨h₁, h₂⟩ | ⟨a', h, h₃⟩)
    · refine ⟨⟨_, fun y h' => ?_⟩, ?_⟩
      · injection Part.mem_unique ⟨h₁, h₂⟩ h'
      · rw [WellFounded.fixF_eq]
        -- Porting note: used to be simp [h₁, h₂]
        apply Part.mem_assert h₁
        split
        next e =>
          injection h₂.symm.trans e with h; simp [h]
        next e =>
          injection h₂.symm.trans e
    · simp only [fix, Part.mem_assert_iff] at h₃
      obtain ⟨h₃, h₄⟩ := h₃
      refine ⟨⟨_, fun y h' => ?_⟩, ?_⟩
      · injection Part.mem_unique h h' with e
        exact e ▸ h₃
      · obtain ⟨h₁, h₂⟩ := h
        grind [WellFounded.fixF_eq]⟩

中文:
定理 mem_fix_iff
  条件: {f : α ->. β oplus α} {a : α} {b : β}
  证明: ⟨fun h => by
    let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
    rw [WellFounded.fixF_eq] at h₂
    simp only [Part.mem_assert_iff] at h₂
    obtain ⟨h₂, h₃⟩ := h₂
    split at h₃
    next e => simp only [Part.mem_some_iff] at h₃; subst b; exact Or.inl ⟨h₂, e⟩
    next e => exact Or.inr ⟨_, ⟨_, e⟩, Part.mem_assert _ h₃⟩,
   fun h => by
    simp only [fix, Part.mem_assert_iff]
    rcases h with (⟨h₁, h₂⟩ | ⟨a', h, h₃⟩)
    · refine ⟨⟨_, fun y h' => ?_⟩, ?_⟩
      · injection Part.mem_unique ⟨h₁, h₂⟩ h'
      · rw [WellFounded.fixF_eq]
        -- Porting note: used to be simp [h₁, h₂]
        apply Part.mem_assert h₁
        split
        next e =>
          injection h₂.symm.trans e with h; simp [h]
        next e =>
          injection h₂.symm.trans e
    · simp only [fix, Part.mem_assert_iff] at h₃
      obtain ⟨h₃, h₄⟩ := h₃
      refine ⟨⟨_, fun y h' => ?_⟩, ?_⟩
      · injection Part.mem_unique h h' with e
        exact e ▸ h₃
      · obtain ⟨h₁, h₂⟩ := h
        grind [WellFounded.fixF_eq]⟩

Depends on / 依赖: Or.inl, Or.inr, Part.mem_assert, Part.mem_assert_iff, Part.mem_some_iff, Part.mem_unique, WellFounded, WellFounded.fixF_eq, fixF_eq, injection, mem_assert, mem_assert_iff, mem_some_iff, mem_unique
-/
theorem mem_fix_iff {f : α ->. β oplus α} {a : α} {b : β} :
    b in f.fix a ↔ Sum.inl b in f a ∨ exists a', Sum.inr a' in f a ∧ b in f.fix a' :=
  ⟨fun h => by
    let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
    rw [WellFounded.fixF_eq] at h₂
    simp only [Part.mem_assert_iff] at h₂
    obtain ⟨h₂, h₃⟩ := h₂
    split at h₃
    next e => simp only [Part.mem_some_iff] at h₃; subst b; exact Or.inl ⟨h₂, e⟩
    next e => exact Or.inr ⟨_, ⟨_, e⟩, Part.mem_assert _ h₃⟩,
   fun h => by
    simp only [fix, Part.mem_assert_iff]
    rcases h with (⟨h₁, h₂⟩ | ⟨a', h, h₃⟩)
    · refine ⟨⟨_, fun y h' => ?_⟩, ?_⟩
      · injection Part.mem_unique ⟨h₁, h₂⟩ h'
      · rw [WellFounded.fixF_eq]
        -- Porting note: used to be simp [h₁, h₂]
        apply Part.mem_assert h₁
        split
        next e =>
          injection h₂.symm.trans e with h; simp [h]
        next e =>
          injection h₂.symm.trans e
    · simp only [fix, Part.mem_assert_iff] at h₃
      obtain ⟨h₃, h₄⟩ := h₃
      refine ⟨⟨_, fun y h' => ?_⟩, ?_⟩
      · injection Part.mem_unique h h' with e
        exact e ▸ h₃
      · obtain ⟨h₁, h₂⟩ := h
        grind [WellFounded.fixF_eq]⟩

/--
theorem `fix_stop` / 定理 `fix_stop`

English:
theorem fix_stop
  given: {f : α ->. β oplus α} {b : β} {a : α} (hb : Sum.inl b in f a)
  statement: b in f.fix a
  proof: by
  rw [PFun.mem_fix_iff]
  exact Or.inl hb

中文:
定理 fix_stop
  条件: {f : α ->. β oplus α} {b : β} {a : α} (hb : 和.inl b in f a)
  结论: b in f.fix a
  证明: by
  rw [PFun.mem_fix_iff]
  exact Or.inl hb

Depends on / 依赖: Or.inl, PFun.mem_fix_iff, mem_fix_iff
-/
theorem fix_stop {f : α ->. β oplus α} {b : β} {a : α} (hb : Sum.inl b in f a) : b in f.fix a := by
  rw [PFun.mem_fix_iff]
  exact Or.inl hb

/--
theorem `fix_fwd_eq` / 定理 `fix_fwd_eq`

English:
theorem fix_fwd_eq
  given: {f : α ->. β oplus α} {a a' : α} (ha' : Sum.inr a' in f a)
  statement: f.fix a = f.fix a'
  proof: by
  ext b; constructor
  · intro h
    obtain h' | ⟨a, h', e'⟩ := mem_fix_iff.1 h <;> cases Part.mem_unique ha' h'
    exact e'
  · intro h
    rw [PFun.mem_fix_iff]
    exact Or.inr ⟨a', ha', h⟩

中文:
定理 fix_fwd_eq
  条件: {f : α ->. β oplus α} {a a' : α} (ha' : 和.inr a' in f a)
  结论: f.fix a = f.fix a'
  证明: by
  ext b; constructor
  · intro h
    obtain h' | ⟨a, h', e'⟩ := mem_fix_iff.1 h <;> cases Part.mem_unique ha' h'
    exact e'
  · intro h
    rw [PFun.mem_fix_iff]
    exact Or.inr ⟨a', ha', h⟩

Depends on / 依赖: Or.inr, PFun.mem_fix_iff, Part.mem_unique, mem_fix_iff, mem_unique
-/
theorem fix_fwd_eq {f : α ->. β oplus α} {a a' : α} (ha' : Sum.inr a' in f a) : f.fix a = f.fix a' := by
  ext b; constructor
  · intro h
    obtain h' | ⟨a, h', e'⟩ := mem_fix_iff.1 h <;> cases Part.mem_unique ha' h'
    exact e'
  · intro h
    rw [PFun.mem_fix_iff]
    exact Or.inr ⟨a', ha', h⟩

/--
theorem `fix_fwd` / 定理 `fix_fwd`

English:
theorem fix_fwd
  given: {f : α ->. β oplus α} {b : β} {a a' : α} (hb : b in f.fix a) (ha' : Sum.inr a' in f a)
  proof: by rwa [← fix_fwd_eq ha']

中文:
定理 fix_fwd
  条件: {f : α ->. β oplus α} {b : β} {a a' : α} (hb : b in f.fix a) (ha' : 和.inr a' in f a)
  证明: by rwa [← fix_fwd_eq ha']

Depends on / 依赖: fix_fwd_eq
-/
theorem fix_fwd {f : α ->. β oplus α} {b : β} {a a' : α} (hb : b in f.fix a) (ha' : Sum.inr a' in f a) :
    b in f.fix a' := by rwa [← fix_fwd_eq ha']

/-- A recursion principle for `PFun.fix`. -/
@[elab_as_elim]
/--
Definition of `fixInduction` / `fixInduction` 的定义

English:
definition fixInduction
  signature: {C : α -> Sort*} {f : α ->. β oplus α} {b : β} {a : α} (h : b in f.fix a)
  body: by
  have h₂ := (Part.mem_assert_iff.1 h).snd
  generalize_proofs at h₂
  clear h
  induction ‹Acc (Sum.inr · in f ·) a› with | intro a ha IH => _
  have h : b in f.fix a := Part.mem_assert_iff.2 ⟨⟨a, ha⟩, h₂⟩
  exact H a h fun a' fa' => IH a' fa' (Part.mem_assert_iff.1 (fix_fwd h fa')).snd

中文:
定义 fixInduction
  签名: {C : α -> 类型层*} {f : α ->. β oplus α} {b : β} {a : α} (h : b in f.fix a)
  定义体: by
  have h₂ := (Part.mem_assert_iff.1 h).snd
  generalize_proofs at h₂
  clear h
  induction ‹Acc (Sum.inr · in f ·) a› with | intro a ha IH => _
  have h : b in f.fix a := Part.mem_assert_iff.2 ⟨⟨a, ha⟩, h₂⟩
  exact H a h fun a' fa' => IH a' fa' (Part.mem_assert_iff.1 (fix_fwd h fa')).snd

Depends on / 依赖: Part.mem_assert_iff, Sum.inr, f.fix, fix_fwd, generalize_proofs, mem_assert_iff
-/
def fixInduction {C : α -> Sort*} {f : α ->. β oplus α} {b : β} {a : α} (h : b in f.fix a)
    (H : forall a', b in f.fix a' -> (forall a'', Sum.inr a'' in f a' -> C a'') -> C a') : C a := by
  have h₂ := (Part.mem_assert_iff.1 h).snd
  generalize_proofs at h₂
  clear h
  induction ‹Acc (Sum.inr · in f ·) a› with | intro a ha IH => _
  have h : b in f.fix a := Part.mem_assert_iff.2 ⟨⟨a, ha⟩, h₂⟩
  exact H a h fun a' fa' => IH a' fa' (Part.mem_assert_iff.1 (fix_fwd h fa')).snd

/--
theorem `fixInduction_spec` / 定理 `fixInduction_spec`

English:
theorem fixInduction_spec
  statement: {C : α -> Sort*} {f : α ->. β oplus α} {b : β} {a : α} (h : b in f.fix a)
  proof: by
  unfold fixInduction
  generalize_proofs
  induction ‹Acc _ _›
  rfl

中文:
定理 fixInduction_spec
  结论: {C : α -> 类型层*} {f : α ->. β oplus α} {b : β} {a : α} (h : b in f.fix a)
  证明: by
  unfold fixInduction
  generalize_proofs
  induction ‹Acc _ _›
  rfl

Depends on / 依赖: fixInduction, generalize_proofs
-/
theorem fixInduction_spec {C : α -> Sort*} {f : α ->. β oplus α} {b : β} {a : α} (h : b in f.fix a)
    (H : forall a', b in f.fix a' -> (forall a'', Sum.inr a'' in f a' -> C a'') -> C a') :
    @fixInduction _ _ C _ _ _ h H = H a h fun _ h' => fixInduction (fix_fwd h h') H := by
  unfold fixInduction
  generalize_proofs
  induction ‹Acc _ _›
  rfl

/-- Another induction lemma for `b ∈ f.fix a` which allows one to prove a predicate `P` holds for
`a` given that `f a` inherits `P` from `a` and `P` holds for preimages of `b`.
-/
@[elab_as_elim]
/--
Definition of `fixInduction'` / `fixInduction'` 的定义

English:
definition fixInduction'
  signature: {C : α -> Sort*} {f : α ->. β oplus α} {b : β} {a : α}
  body: by
  refine fixInduction h fun a' h ih => ?_
  rcases e : (f a').get (dom_of_mem_fix h) with b' | a'' <;> replace e : _ in f a' := ⟨_, e⟩
  · apply hbase
    convert! e
    exact Part.mem_unique h (fix_stop e)
  · exact hind _ _ (fix_fwd h e) e (ih _ e)

中文:
定义 fixInduction'
  签名: {C : α -> 类型层*} {f : α ->. β oplus α} {b : β} {a : α}
  定义体: by
  refine fixInduction h fun a' h ih => ?_
  rcases e : (f a').get (dom_of_mem_fix h) with b' | a'' <;> replace e : _ in f a' := ⟨_, e⟩
  · apply hbase
    convert! e
    exact Part.mem_unique h (fix_stop e)
  · exact hind _ _ (fix_fwd h e) e (ih _ e)

Depends on / 依赖: Part.mem_unique, convert, dom_of_mem_fix, fixInduction, fix_fwd, fix_stop, mem_unique, replace
-/
def fixInduction' {C : α -> Sort*} {f : α ->. β oplus α} {b : β} {a : α}
    (h : b in f.fix a) (hbase : forall a_final : α, Sum.inl b in f a_final -> C a_final)
    (hind : forall a₀ a₁ : α, b in f.fix a₁ -> Sum.inr a₁ in f a₀ -> C a₁ -> C a₀) : C a := by
  refine fixInduction h fun a' h ih => ?_
  rcases e : (f a').get (dom_of_mem_fix h) with b' | a'' <;> replace e : _ in f a' := ⟨_, e⟩
  · apply hbase
    convert! e
    exact Part.mem_unique h (fix_stop e)
  · exact hind _ _ (fix_fwd h e) e (ih _ e)

/--
theorem `fixInduction'_stop` / 定理 `fixInduction'_stop`

English:
theorem fixInduction'_stop
  statement: {C : α -> Sort*} {f : α ->. β oplus α} {b : β} {a : α} (h : b in f.fix a)
  proof: by
  unfold fixInduction'
  rw [fixInduction_spec]
  -- Porting note: the explicit motive required because `simp` does not apply `Part.get_eq_of_mem`
  refine Eq.rec (motive := fun x e =>
      Sum.casesOn x ?_ ?_ (Eq.trans (Part.get_eq_of_mem fa (dom_of_mem_fix h)) e) = hbase a fa) ?_
    (Part.get_eq_of_mem fa (dom_of_mem_fix h)).symm
  simp

中文:
定理 fixInduction'_stop
  结论: {C : α -> 类型层*} {f : α ->. β oplus α} {b : β} {a : α} (h : b in f.fix a)
  证明: by
  unfold fixInduction'
  rw [fixInduction_spec]
  -- Porting note: the explicit motive required because `simp` does not apply `Part.get_eq_of_mem`
  refine Eq.rec (motive := fun x e =>
      Sum.casesOn x ?_ ?_ (Eq.trans (Part.get_eq_of_mem fa (dom_of_mem_fix h)) e) = hbase a fa) ?_
    (Part.get_eq_of_mem fa (dom_of_mem_fix h)).symm
  simp
-/
theorem fixInduction'_stop {C : α -> Sort*} {f : α ->. β oplus α} {b : β} {a : α} (h : b in f.fix a)
    (fa : Sum.inl b in f a) (hbase : forall a_final : α, Sum.inl b in f a_final -> C a_final)
    (hind : forall a₀ a₁ : α, b in f.fix a₁ -> Sum.inr a₁ in f a₀ -> C a₁ -> C a₀) :
    @fixInduction' _ _ C _ _ _ h hbase hind = hbase a fa := by
  unfold fixInduction'
  rw [fixInduction_spec]
  -- Porting note: the explicit motive required because `simp` does not apply `Part.get_eq_of_mem`
  refine Eq.rec (motive := fun x e =>
      Sum.casesOn x ?_ ?_ (Eq.trans (Part.get_eq_of_mem fa (dom_of_mem_fix h)) e) = hbase a fa) ?_
    (Part.get_eq_of_mem fa (dom_of_mem_fix h)).symm
  simp

/--
theorem `fixInduction'_fwd` / 定理 `fixInduction'_fwd`

English:
theorem fixInduction'_fwd
  statement: {C : α -> Sort*} {f : α ->. β oplus α} {b : β} {a a' : α} (h : b in f.fix a)
  proof: by
  unfold fixInduction'
  rw [fixInduction_spec]
  -- Porting note: the explicit motive required because `simp` does not apply `Part.get_eq_of_mem`
  refine Eq.rec (motive := fun x e =>
      Sum.casesOn (motive := fun y => (f a).get (dom_of_mem_fix h) = y -> C a) x ?_ ?_
      (Eq.trans (Part.get_eq_of_mem fa (dom_of_mem_fix h)) e) = _) ?_
    (Part.get_eq_of_mem fa (dom_of_mem_fix h)).symm
  simp

中文:
定理 fixInduction'_fwd
  结论: {C : α -> 类型层*} {f : α ->. β oplus α} {b : β} {a a' : α} (h : b in f.fix a)
  证明: by
  unfold fixInduction'
  rw [fixInduction_spec]
  -- Porting note: the explicit motive required because `simp` does not apply `Part.get_eq_of_mem`
  refine Eq.rec (motive := fun x e =>
      Sum.casesOn (motive := fun y => (f a).get (dom_of_mem_fix h) = y -> C a) x ?_ ?_
      (Eq.trans (Part.get_eq_of_mem fa (dom_of_mem_fix h)) e) = _) ?_
    (Part.get_eq_of_mem fa (dom_of_mem_fix h)).symm
  simp
-/
theorem fixInduction'_fwd {C : α -> Sort*} {f : α ->. β oplus α} {b : β} {a a' : α} (h : b in f.fix a)
    (h' : b in f.fix a') (fa : Sum.inr a' in f a)
    (hbase : forall a_final : α, Sum.inl b in f a_final -> C a_final)
    (hind : forall a₀ a₁ : α, b in f.fix a₁ -> Sum.inr a₁ in f a₀ -> C a₁ -> C a₀) :
    @fixInduction' _ _ C _ _ _ h hbase hind = hind a a' h' fa (fixInduction' h' hbase hind) := by
  unfold fixInduction'
  rw [fixInduction_spec]
  -- Porting note: the explicit motive required because `simp` does not apply `Part.get_eq_of_mem`
  refine Eq.rec (motive := fun x e =>
      Sum.casesOn (motive := fun y => (f a).get (dom_of_mem_fix h) = y -> C a) x ?_ ?_
      (Eq.trans (Part.get_eq_of_mem fa (dom_of_mem_fix h)) e) = _) ?_
    (Part.get_eq_of_mem fa (dom_of_mem_fix h)).symm
  simp

variable (f : α ->. β)

/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: (s : Set α)
  body: f.graph'.image s

中文:
定义 像
  签名: (s : 集合 α)
  定义体: f.graph'.image s

Depends on / 依赖: f.graph
-/
def image (s : Set α) : Set β :=
  f.graph'.image s

/--
theorem `image_def` / 定理 `image_def`

English:
theorem image_def
  given: (s : Set α)
  statement: f.image s = { y | exists x in s, y in f x }
  proof: rfl

中文:
定理 image_def
  条件: (s : 集合 α)
  结论: f.像 s = { y | 存在 x in s, y in f x }
  证明: rfl
-/
theorem image_def (s : Set α) : f.image s = { y | exists x in s, y in f x } :=
  rfl

/--
theorem `mem_image` / 定理 `mem_image`

English:
theorem mem_image
  given: (y : β) (s : Set α)
  statement: y in f.image s ↔ exists x in s, y in f x
  proof: Iff.rfl

中文:
定理 mem_image
  条件: (y : β) (s : 集合 α)
  结论: y in f.像 s ↔ 存在 x in s, y in f x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_image (y : β) (s : Set α) : y in f.image s ↔ exists x in s, y in f x :=
  Iff.rfl

/--
theorem `image_mono` / 定理 `image_mono`

English:
theorem image_mono
  given: {s t : Set α} (h : s subseteq t)
  statement: f.image s subseteq f.image t
  proof: SetRel.image_mono h

中文:
定理 image_mono
  条件: {s t : 集合 α} (h : s subseteq t)
  结论: f.像 s subseteq f.像 t
  证明: SetRel.image_mono h

Depends on / 依赖: SetRel, SetRel.image_mono, image_mono
-/
theorem image_mono {s t : Set α} (h : s subseteq t) : f.image s subseteq f.image t :=
  SetRel.image_mono h

/--
theorem `image_inter` / 定理 `image_inter`

English:
theorem image_inter
  given: (s t : Set α)
  statement: f.image (s inter t) subseteq f.image s inter f.image t
  proof: SetRel.image_inter_subset _

中文:
定理 image_inter
  条件: (s t : 集合 α)
  结论: f.像 (s inter t) subseteq f.像 s inter f.像 t
  证明: SetRel.image_inter_subset _

Depends on / 依赖: SetRel, SetRel.image_inter_subset, image_inter_subset
-/
theorem image_inter (s t : Set α) : f.image (s inter t) subseteq f.image s inter f.image t :=
  SetRel.image_inter_subset _

/--
theorem `image_union` / 定理 `image_union`

English:
theorem image_union
  given: (s t : Set α)
  statement: f.image (s union t) = f.image s union f.image t
  proof: SetRel.image_union _ s t

中文:
定理 image_union
  条件: (s t : 集合 α)
  结论: f.像 (s union t) = f.像 s union f.像 t
  证明: SetRel.image_union _ s t

Depends on / 依赖: SetRel, SetRel.image_union, SplittingFieldAux, SplittingFieldAux.adjoin_rootSet, SplittingFieldAux.splits, adjoin_rootSet, image_union, splits
-/
theorem image_union (s t : Set α) : f.image (s union t) = f.image s union f.image t :=
  SetRel.image_union _ s t

/--
Definition of `preimage` / `preimage` 的定义

English:
definition preimage
  signature: (s : Set β)
  body: f.graph'.preimage s

中文:
定义 原像
  签名: (s : 集合 β)
  定义体: f.graph'.preimage s

Depends on / 依赖: f.graph, preimage
-/
def preimage (s : Set β) : Set α := f.graph'.preimage s

/--
theorem `Preimage_def` / 定理 `Preimage_def`

English:
theorem Preimage_def
  given: (s : Set β)
  statement: f.preimage s = { x | exists y in s, y in f x }
  proof: rfl

@[simp, grind =]

中文:
定理 Preimage_def
  条件: (s : 集合 β)
  结论: f.原像 s = { x | 存在 y in s, y in f x }
  证明: rfl

@[simp, grind =]
-/
theorem Preimage_def (s : Set β) : f.preimage s = { x | exists y in s, y in f x } :=
  rfl

@[simp, grind =]
/--
theorem `mem_preimage` / 定理 `mem_preimage`

English:
theorem mem_preimage
  given: (s : Set β) (x : α)
  statement: x in f.preimage s ↔ exists y in s, y in f x
  proof: Iff.rfl

中文:
定理 mem_preimage
  条件: (s : 集合 β) (x : α)
  结论: x in f.原像 s ↔ 存在 y in s, y in f x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_preimage (s : Set β) (x : α) : x in f.preimage s ↔ exists y in s, y in f x :=
  Iff.rfl

/--
theorem `preimage_subset_dom` / 定理 `preimage_subset_dom`

English:
theorem preimage_subset_dom
  given: (s : Set β)
  statement: f.preimage s subseteq f.Dom
  proof: fun _ ⟨y, _, fxy⟩ =>
  Part.dom_iff_mem.mpr ⟨y, fxy⟩

中文:
定理 preimage_subset_dom
  条件: (s : 集合 β)
  结论: f.原像 s subseteq f.Dom
  证明: fun _ ⟨y, _, fxy⟩ =>
  Part.dom_iff_mem.mpr ⟨y, fxy⟩
-/
theorem preimage_subset_dom (s : Set β) : f.preimage s subseteq f.Dom := fun _ ⟨y, _, fxy⟩ =>
  Part.dom_iff_mem.mpr ⟨y, fxy⟩

/--
theorem `preimage_mono` / 定理 `preimage_mono`

English:
theorem preimage_mono
  given: {s t : Set β} (h : s subseteq t)
  statement: f.preimage s subseteq f.preimage t
  proof: SetRel.preimage_mono h

中文:
定理 preimage_mono
  条件: {s t : 集合 β} (h : s subseteq t)
  结论: f.原像 s subseteq f.原像 t
  证明: SetRel.preimage_mono h

Depends on / 依赖: SetRel, SetRel.preimage_mono, preimage_mono
-/
theorem preimage_mono {s t : Set β} (h : s subseteq t) : f.preimage s subseteq f.preimage t :=
  SetRel.preimage_mono h

/--
theorem `preimage_inter` / 定理 `preimage_inter`

English:
theorem preimage_inter
  given: (s t : Set β)
  statement: f.preimage (s inter t) subseteq f.preimage s inter f.preimage t
  proof: SetRel.preimage_inter_subset _

中文:
定理 preimage_inter
  条件: (s t : 集合 β)
  结论: f.原像 (s inter t) subseteq f.原像 s inter f.原像 t
  证明: SetRel.preimage_inter_subset _

Depends on / 依赖: SetRel, SetRel.preimage_inter_subset, preimage_inter_subset
-/
theorem preimage_inter (s t : Set β) : f.preimage (s inter t) subseteq f.preimage s inter f.preimage t :=
  SetRel.preimage_inter_subset _

/--
theorem `preimage_union` / 定理 `preimage_union`

English:
theorem preimage_union
  given: (s t : Set β)
  statement: f.preimage (s union t) = f.preimage s union f.preimage t
  proof: SetRel.preimage_union _ s t

中文:
定理 preimage_union
  条件: (s t : 集合 β)
  结论: f.原像 (s union t) = f.原像 s union f.原像 t
  证明: SetRel.preimage_union _ s t

Depends on / 依赖: SetRel, SetRel.preimage_union, preimage_union
-/
theorem preimage_union (s t : Set β) : f.preimage (s union t) = f.preimage s union f.preimage t :=
  SetRel.preimage_union _ s t

/--
theorem `preimage_univ` / 定理 `preimage_univ`

English:
theorem preimage_univ
  statement: f.preimage Set.univ = f.Dom
  proof: by ext; simp [mem_preimage, mem_dom]

中文:
定理 preimage_univ
  结论: f.原像 集合.univ = f.Dom
  证明: by ext; simp [mem_preimage, mem_dom]

Depends on / 依赖: mem_dom, mem_preimage
-/
theorem preimage_univ : f.preimage Set.univ = f.Dom := by ext; simp [mem_preimage, mem_dom]

/--
theorem `coe_preimage` / 定理 `coe_preimage`

English:
theorem coe_preimage
  given: (f : α -> β) (s : Set β)
  statement: (f : α ->. β).preimage s = f ⁻¹' s
  proof: by ext; simp

中文:
定理 coe_preimage
  条件: (f : α -> β) (s : 集合 β)
  结论: (f : α ->. β).原像 s = f ⁻¹' s
  证明: by ext; simp
-/
theorem coe_preimage (f : α -> β) (s : Set β) : (f : α ->. β).preimage s = f ⁻¹' s := by ext; simp

/--
Definition of `core` / `core` 的定义

English:
definition core
  signature: (s : Set β)
  body: f.graph'.core s

中文:
定义 core
  签名: (s : 集合 β)
  定义体: f.graph'.core s

Depends on / 依赖: f.graph
-/
def core (s : Set β) : Set α :=
  f.graph'.core s

/--
theorem `core_def` / 定理 `core_def`

English:
theorem core_def
  given: (s : Set β)
  statement: f.core s = { x | forall y, y in f x -> y in s }
  proof: rfl

@[simp]

中文:
定理 core_def
  条件: (s : 集合 β)
  结论: f.core s = { x | 对任意 y, y in f x -> y in s }
  证明: rfl

@[simp]
-/
theorem core_def (s : Set β) : f.core s = { x | forall y, y in f x -> y in s } :=
  rfl

@[simp]
/--
theorem `mem_core` / 定理 `mem_core`

English:
theorem mem_core
  given: (x : α) (s : Set β)
  statement: x in f.core s ↔ forall y, y in f x -> y in s
  proof: Iff.rfl

中文:
定理 mem_core
  条件: (x : α) (s : 集合 β)
  结论: x in f.core s ↔ 对任意 y, y in f x -> y in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_core (x : α) (s : Set β) : x in f.core s ↔ forall y, y in f x -> y in s :=
  Iff.rfl

/--
theorem `compl_dom_subset_core` / 定理 `compl_dom_subset_core`

English:
theorem compl_dom_subset_core
  given: (s : Set β)
  statement: f.Domᶜ subseteq f.core s
  proof: fun x hx y fxy =>
  absurd ((mem_dom f x).mpr ⟨y, fxy⟩) hx

中文:
定理 compl_dom_subset_core
  条件: (s : 集合 β)
  结论: f.Domᶜ subseteq f.core s
  证明: fun x hx y fxy =>
  absurd ((mem_dom f x).mpr ⟨y, fxy⟩) hx

Depends on / 依赖: SplittingField, f.SplittingField, finiteDimensional
-/
theorem compl_dom_subset_core (s : Set β) : f.Domᶜ subseteq f.core s := fun x hx y fxy =>
  absurd ((mem_dom f x).mpr ⟨y, fxy⟩) hx

/--
theorem `core_mono` / 定理 `core_mono`

English:
theorem core_mono
  given: {s t : Set β} (h : s subseteq t)
  statement: f.core s subseteq f.core t
  proof: SetRel.core_mono h

中文:
定理 core_mono
  条件: {s t : 集合 β} (h : s subseteq t)
  结论: f.core s subseteq f.core t
  证明: SetRel.core_mono h

Depends on / 依赖: SetRel, SetRel.core_mono, core_mono
-/
theorem core_mono {s t : Set β} (h : s subseteq t) : f.core s subseteq f.core t :=
  SetRel.core_mono h

/--
theorem `core_inter` / 定理 `core_inter`

English:
theorem core_inter
  given: (s t : Set β)
  statement: f.core (s inter t) = f.core s inter f.core t
  proof: SetRel.core_inter _ s t

中文:
定理 core_inter
  条件: (s t : 集合 β)
  结论: f.core (s inter t) = f.core s inter f.core t
  证明: SetRel.core_inter _ s t

Depends on / 依赖: SetRel, SetRel.core_inter, core_inter
-/
theorem core_inter (s t : Set β) : f.core (s inter t) = f.core s inter f.core t :=
  SetRel.core_inter _ s t

/--
theorem `mem_core_res` / 定理 `mem_core_res`

English:
theorem mem_core_res
  given: (f : α -> β) (s : Set α) (t : Set β) (x : α)
  proof: by simp [mem_core, mem_res]

中文:
定理 mem_core_res
  条件: (f : α -> β) (s : 集合 α) (t : 集合 β) (x : α)
  证明: by simp [mem_core, mem_res]

Depends on / 依赖: mem_core, mem_res
-/
theorem mem_core_res (f : α -> β) (s : Set α) (t : Set β) (x : α) :
    x in (res f s).core t ↔ x in s -> f x in t := by simp [mem_core, mem_res]

/--
theorem `core_res` / 定理 `core_res`

English:
theorem core_res
  given: (f : α -> β) (s : Set α) (t : Set β)
  statement: (res f s).core t = sᶜ union f ⁻¹' t
  proof: by
  ext x
  rw [mem_core_res]
  by_cases h : x in s <;> simp [h]

中文:
定理 core_res
  条件: (f : α -> β) (s : 集合 α) (t : 集合 β)
  结论: (res f s).core t = sᶜ union f ⁻¹' t
  证明: by
  ext x
  rw [mem_core_res]
  by_cases h : x in s <;> simp [h]

Depends on / 依赖: mem_core_res
-/
theorem core_res (f : α -> β) (s : Set α) (t : Set β) : (res f s).core t = sᶜ union f ⁻¹' t := by
  ext x
  rw [mem_core_res]
  by_cases h : x in s <;> simp [h]

/--
theorem `core_restrict` / 定理 `core_restrict`

English:
theorem core_restrict
  given: (f : α -> β) (s : Set β)
  statement: (f : α ->. β).core s = s.preimage f
  proof: by
  ext x; simp [core_def]

中文:
定理 core_restrict
  条件: (f : α -> β) (s : 集合 β)
  结论: (f : α ->. β).core s = s.原像 f
  证明: by
  ext x; simp [core_def]

Depends on / 依赖: core_def
-/
theorem core_restrict (f : α -> β) (s : Set β) : (f : α ->. β).core s = s.preimage f := by
  ext x; simp [core_def]

/--
theorem `preimage_subset_core` / 定理 `preimage_subset_core`

English:
theorem preimage_subset_core
  given: (f : α ->. β) (s : Set β)
  statement: f.preimage s subseteq f.core s
  proof: fun _ ⟨y, ys, fxy⟩ y' fxy' =>
  have : y = y' := Part.mem_unique fxy fxy'
  this ▸ ys

中文:
定理 preimage_subset_core
  条件: (f : α ->. β) (s : 集合 β)
  结论: f.原像 s subseteq f.core s
  证明: fun _ ⟨y, ys, fxy⟩ y' fxy' =>
  have : y = y' := Part.mem_unique fxy fxy'
  this ▸ ys

Depends on / 依赖: Part.mem_unique, mem_unique
-/
theorem preimage_subset_core (f : α ->. β) (s : Set β) : f.preimage s subseteq f.core s :=
  fun _ ⟨y, ys, fxy⟩ y' fxy' =>
  have : y = y' := Part.mem_unique fxy fxy'
  this ▸ ys

/--
theorem `preimage_eq` / 定理 `preimage_eq`

English:
theorem preimage_eq
  given: (f : α ->. β) (s : Set β)
  statement: f.preimage s = f.core s inter f.Dom
  proof: Set.eq_of_subset_of_subset (Set.subset_inter (f.preimage_subset_core s) (f.preimage_subset_dom s))
    fun x ⟨xcore, xdom⟩ =>
    let y := (f x).get xdom
    have ys : y in s := xcore (Part.get_mem _)
    show x in f.preimage s from ⟨(f x).get xdom, ys, Part.get_mem _⟩

中文:
定理 preimage_eq
  条件: (f : α ->. β) (s : 集合 β)
  结论: f.原像 s = f.core s inter f.Dom
  证明: Set.eq_of_subset_of_subset (Set.subset_inter (f.preimage_subset_core s) (f.preimage_subset_dom s))
    fun x ⟨xcore, xdom⟩ =>
    let y := (f x).get xdom
    have ys : y in s := xcore (Part.get_mem _)
    show x in f.preimage s from ⟨(f x).get xdom, ys, Part.get_mem _⟩

Depends on / 依赖: Part.get_mem, Set.eq_of_subset_of_subset, Set.subset_inter, eq_of_subset_of_subset, f.preimage, f.preimage_subset_core, f.preimage_subset_dom, get_mem, preimage, preimage_subset_core, preimage_subset_dom, subset_inter
-/
theorem preimage_eq (f : α ->. β) (s : Set β) : f.preimage s = f.core s inter f.Dom :=
  Set.eq_of_subset_of_subset (Set.subset_inter (f.preimage_subset_core s) (f.preimage_subset_dom s))
    fun x ⟨xcore, xdom⟩ =>
    let y := (f x).get xdom
    have ys : y in s := xcore (Part.get_mem _)
    show x in f.preimage s from ⟨(f x).get xdom, ys, Part.get_mem _⟩

/--
theorem `core_eq` / 定理 `core_eq`

English:
theorem core_eq
  given: (f : α ->. β) (s : Set β)
  statement: f.core s = f.preimage s union f.Domᶜ
  proof: by
  rw [preimage_eq]; rw [Set.inter_union_distrib_right]; rw [Set.union_comm (Dom f)]; rw [Set.compl_union_self]; rw [Set.inter_univ]; rw [Set.union_eq_self_of_subset_right (f.compl_dom_subset_core s)]

中文:
定理 core_eq
  条件: (f : α ->. β) (s : 集合 β)
  结论: f.core s = f.原像 s union f.Domᶜ
  证明: by
  rw [preimage_eq]; rw [Set.inter_union_distrib_right]; rw [Set.union_comm (Dom f)]; rw [Set.compl_union_self]; rw [Set.inter_univ]; rw [Set.union_eq_self_of_subset_right (f.compl_dom_subset_core s)]

Depends on / 依赖: Set.compl_union_self, Set.inter_union_distrib_right, Set.inter_univ, Set.union_comm, Set.union_eq_self_of_subset_right, compl_dom_subset_core, compl_union_self, f.compl_dom_subset_core, inter_union_distrib_right, inter_univ, preimage_eq, union_comm, union_eq_self_of_subset_right
-/
theorem core_eq (f : α ->. β) (s : Set β) : f.core s = f.preimage s union f.Domᶜ := by
  rw [preimage_eq]; rw [Set.inter_union_distrib_right]; rw [Set.union_comm (Dom f)]; rw [Set.compl_union_self]; rw [Set.inter_univ]; rw [Set.union_eq_self_of_subset_right (f.compl_dom_subset_core s)]

/--
theorem `preimage_asSubtype` / 定理 `preimage_asSubtype`

English:
theorem preimage_asSubtype
  given: (f : α ->. β) (s : Set β)
  proof: by
  ext x
  simp only [Set.mem_preimage, PFun.asSubtype, PFun.mem_preimage]
  show f.fn x.val _ in s ↔ exists y in s, y in f x.val
  exact
    Iff.intro (fun h => ⟨_, h, Part.get_mem _⟩) fun ⟨y, ys, fxy⟩ =>
      have : f.fn x.val x.property in f x.val := Part.get_mem _
      Part.mem_unique fxy this ▸ ys

中文:
定理 preimage_asSubtype
  条件: (f : α ->. β) (s : 集合 β)
  证明: by
  ext x
  simp only [Set.mem_preimage, PFun.asSubtype, PFun.mem_preimage]
  show f.fn x.val _ in s ↔ exists y in s, y in f x.val
  exact
    Iff.intro (fun h => ⟨_, h, Part.get_mem _⟩) fun ⟨y, ys, fxy⟩ =>
      have : f.fn x.val x.property in f x.val := Part.get_mem _
      Part.mem_unique fxy this ▸ ys

Depends on / 依赖: Iff.intro, PFun.asSubtype, PFun.mem_preimage, Part.get_mem, Part.mem_unique, Set.mem_preimage, asSubtype, f.fn, get_mem, mem_preimage, mem_unique, property, x.property, x.val
-/
theorem preimage_asSubtype (f : α ->. β) (s : Set β) :
    f.asSubtype ⁻¹' s = Subtype.val ⁻¹' f.preimage s := by
  ext x
  simp only [Set.mem_preimage, PFun.asSubtype, PFun.mem_preimage]
  show f.fn x.val _ in s ↔ exists y in s, y in f x.val
  exact
    Iff.intro (fun h => ⟨_, h, Part.get_mem _⟩) fun ⟨y, ys, fxy⟩ =>
      have : f.fn x.val x.property in f x.val := Part.get_mem _
      Part.mem_unique fxy this ▸ ys

/--
Definition of `toSubtype` / `toSubtype` 的定义

English:
definition toSubtype
  signature: (p : β -> Prop) (f : α -> β)
  body: fun a => ⟨p (f a), Subtype.mk _⟩

@[simp]

中文:
定义 toSubtype
  签名: (p : β -> 命题) (f : α -> β)
  定义体: fun a => ⟨p (f a), Subtype.mk _⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.mk
-/
def toSubtype (p : β -> Prop) (f : α -> β) : α ->. Subtype p := fun a => ⟨p (f a), Subtype.mk _⟩

@[simp]
/--
theorem `dom_toSubtype` / 定理 `dom_toSubtype`

English:
theorem dom_toSubtype
  given: (p : β -> Prop) (f : α -> β)
  statement: (toSubtype p f).Dom = { a | p (f a) }
  proof: rfl

@[simp]

中文:
定理 dom_toSubtype
  条件: (p : β -> 命题) (f : α -> β)
  结论: (toSubtype p f).Dom = { a | p (f a) }
  证明: rfl

@[simp]
-/
theorem dom_toSubtype (p : β -> Prop) (f : α -> β) : (toSubtype p f).Dom = { a | p (f a) } :=
  rfl

@[simp]
/--
theorem `toSubtype_apply` / 定理 `toSubtype_apply`

English:
theorem toSubtype_apply
  given: (p : β -> Prop) (f : α -> β) (a : α)
  proof: rfl

中文:
定理 toSubtype_apply
  条件: (p : β -> 命题) (f : α -> β) (a : α)
  证明: rfl
-/
theorem toSubtype_apply (p : β -> Prop) (f : α -> β) (a : α) :
    toSubtype p f a = ⟨p (f a), Subtype.mk _⟩ :=
  rfl

/--
theorem `dom_toSubtype_apply_iff` / 定理 `dom_toSubtype_apply_iff`

English:
theorem dom_toSubtype_apply_iff
  given: {p : β -> Prop} {f : α -> β} {a : α}
  proof: Iff.rfl

中文:
定理 dom_toSubtype_apply_iff
  条件: {p : β -> 命题} {f : α -> β} {a : α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem dom_toSubtype_apply_iff {p : β -> Prop} {f : α -> β} {a : α} :
    (toSubtype p f a).Dom ↔ p (f a) :=
  Iff.rfl

/--
theorem `mem_toSubtype_iff` / 定理 `mem_toSubtype_iff`

English:
theorem mem_toSubtype_iff
  given: {p : β -> Prop} {f : α -> β} {a : α} {b : Subtype p}
  proof: by
  rw [toSubtype_apply]; rw [Part.mem_mk_iff]; rw [exists_subtype_mk_eq_iff]; rw [eq_comm]

中文:
定理 mem_toSubtype_iff
  条件: {p : β -> 命题} {f : α -> β} {a : α} {b : 子类型 p}
  证明: by
  rw [toSubtype_apply]; rw [Part.mem_mk_iff]; rw [exists_subtype_mk_eq_iff]; rw [eq_comm]

Depends on / 依赖: Part.mem_mk_iff, eq_comm, exists_subtype_mk_eq_iff, mem_mk_iff, toSubtype_apply
-/
theorem mem_toSubtype_iff {p : β -> Prop} {f : α -> β} {a : α} {b : Subtype p} :
    b in toSubtype p f a ↔ ↑b = f a := by
  rw [toSubtype_apply]; rw [Part.mem_mk_iff]; rw [exists_subtype_mk_eq_iff]; rw [eq_comm]

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (α : Type*)
  body: Part.some

@[simp, norm_cast]

中文:
定义 id
  签名: (α : 类型)
  定义体: Part.some

@[simp, norm_cast]
-/
protected def id (α : Type*) : α ->. α :=
  Part.some

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  given: (α : Type*)
  statement: ((id : α -> α) : α ->. α) = PFun.id α
  proof: rfl

@[simp]

中文:
定理 coe_id
  条件: (α : 类型)
  结论: ((id : α -> α) : α ->. α) = PFun.id α
  证明: rfl

@[simp]
-/
theorem coe_id (α : Type*) : ((id : α -> α) : α ->. α) = PFun.id α :=
  rfl

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: PFun.id α a = Part.some a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: PFun.id α a = Part.some a
  证明: rfl
-/
theorem id_apply (a : α) : PFun.id α a = Part.some a :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : β ->. γ) (g : α ->. β)
  body: fun a => (g a).bind f

@[simp, grind =]

中文:
定义 comp
  签名: (f : β ->. γ) (g : α ->. β)
  定义体: fun a => (g a).bind f

@[simp, grind =]
-/
def comp (f : β ->. γ) (g : α ->. β) : α ->. γ := fun a => (g a).bind f

@[simp, grind =]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : β ->. γ) (g : α ->. β) (a : α)
  statement: f.comp g a = (g a).bind f
  proof: rfl

中文:
定理 comp_apply
  条件: (f : β ->. γ) (g : α ->. β) (a : α)
  结论: f.comp g a = (g a).bind f
  证明: rfl
-/
theorem comp_apply (f : β ->. γ) (g : α ->. β) (a : α) : f.comp g a = (g a).bind f :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : α ->. β)
  statement: (PFun.id β).comp f = f
  proof: ext fun _ _ => by simp

中文:
定理 id_comp
  条件: (f : α ->. β)
  结论: (PFun.id β).comp f = f
  证明: ext fun _ _ => by simp
-/
theorem id_comp (f : α ->. β) : (PFun.id β).comp f = f :=
  ext fun _ _ => by simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : α ->. β)
  statement: f.comp (PFun.id α) = f
  proof: ext fun _ _ => by simp

中文:
定理 comp_id
  条件: (f : α ->. β)
  结论: f.comp (PFun.id α) = f
  证明: ext fun _ _ => by simp
-/
theorem comp_id (f : α ->. β) : f.comp (PFun.id α) = f :=
  ext fun _ _ => by simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `dom_comp` / 定理 `dom_comp`

English:
theorem dom_comp
  given: (f : β ->. γ) (g : α ->. β)
  statement: (f.comp g).Dom = g.preimage f.Dom
  proof: by
  ext
  simp
  grind

@[simp]

中文:
定理 dom_comp
  条件: (f : β ->. γ) (g : α ->. β)
  结论: (f.comp g).Dom = g.原像 f.Dom
  证明: by
  ext
  simp
  grind

@[simp]
-/
theorem dom_comp (f : β ->. γ) (g : α ->. β) : (f.comp g).Dom = g.preimage f.Dom := by
  ext
  simp
  grind

@[simp]
/--
theorem `preimage_comp` / 定理 `preimage_comp`

English:
theorem preimage_comp
  given: (f : β ->. γ) (g : α ->. β) (s : Set γ)
  proof: by
  grind

@[simp]

中文:
定理 preimage_comp
  条件: (f : β ->. γ) (g : α ->. β) (s : 集合 γ)
  证明: by
  grind

@[simp]
-/
theorem preimage_comp (f : β ->. γ) (g : α ->. β) (s : Set γ) :
    (f.comp g).preimage s = g.preimage (f.preimage s) := by
  grind

@[simp]
/--
theorem `Part.bind_comp` / 定理 `Part.bind_comp`

English:
theorem Part.bind_comp
  given: (f : β ->. γ) (g : α ->. β) (a : Part α)
  proof: by
  ext
  grind

@[simp]

中文:
定理 Part.bind_comp
  条件: (f : β ->. γ) (g : α ->. β) (a : Part α)
  证明: by
  ext
  grind

@[simp]
-/
theorem Part.bind_comp (f : β ->. γ) (g : α ->. β) (a : Part α) :
    a.bind (f.comp g) = (a.bind g).bind f := by
  ext
  grind

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : γ ->. δ) (g : β ->. γ) (h : α ->. β)
  statement: (f.comp g).comp h = f.comp (g.comp h)
  proof: ext fun _ _ => by simp only [comp_apply, Part.bind_comp]

中文:
定理 comp_assoc
  条件: (f : γ ->. δ) (g : β ->. γ) (h : α ->. β)
  结论: (f.comp g).comp h = f.comp (g.comp h)
  证明: ext fun _ _ => by simp only [comp_apply, Part.bind_comp]

Depends on / 依赖: Part.bind_comp, bind_comp, comp_apply
-/
theorem comp_assoc (f : γ ->. δ) (g : β ->. γ) (h : α ->. β) : (f.comp g).comp h = f.comp (g.comp h) :=
  ext fun _ _ => by simp only [comp_apply, Part.bind_comp]

set_option backward.isDefEq.respectTransparency false in
-- This can't be `simp`
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (g : β -> γ) (f : α -> β)
  statement: ((g ∘ f : α -> γ) : α ->. γ) = (g : β ->. γ).comp f
  proof: ext fun _ _ => by simp only [coe_val, comp_apply, Function.comp, Part.bind_some]

中文:
定理 coe_comp
  条件: (g : β -> γ) (f : α -> β)
  结论: ((g ∘ f : α -> γ) : α ->. γ) = (g : β ->. γ).comp f
  证明: ext fun _ _ => by simp only [coe_val, comp_apply, Function.comp, Part.bind_some]

Depends on / 依赖: Function, Function.comp, Part.bind_some, bind_some, coe_val, comp_apply
-/
theorem coe_comp (g : β -> γ) (f : α -> β) : ((g ∘ f : α -> γ) : α ->. γ) = (g : β ->. γ).comp f :=
  ext fun _ _ => by simp only [coe_val, comp_apply, Function.comp, Part.bind_some]

/--
Definition of `prodLift` / `prodLift` 的定义

English:
definition prodLift
  signature: (f : α ->. β) (g : α ->. γ)
  body: fun x =>
  ⟨(f x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩

@[simp]

中文:
定义 prodLift
  签名: (f : α ->. β) (g : α ->. γ)
  定义体: fun x =>
  ⟨(f x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩

@[simp]
-/
def prodLift (f : α ->. β) (g : α ->. γ) : α ->. β × γ := fun x =>
  ⟨(f x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩

@[simp]
/--
theorem `dom_prodLift` / 定理 `dom_prodLift`

English:
theorem dom_prodLift
  given: (f : α ->. β) (g : α ->. γ)
  proof: rfl

中文:
定理 dom_prodLift
  条件: (f : α ->. β) (g : α ->. γ)
  证明: rfl
-/
theorem dom_prodLift (f : α ->. β) (g : α ->. γ) :
    (f.prodLift g).Dom = { x | (f x).Dom ∧ (g x).Dom } :=
  rfl

/--
theorem `get_prodLift` / 定理 `get_prodLift`

English:
theorem get_prodLift
  given: (f : α ->. β) (g : α ->. γ) (x : α) (h)
  proof: rfl

@[simp]

中文:
定理 get_prodLift
  条件: (f : α ->. β) (g : α ->. γ) (x : α) (h)
  证明: rfl

@[simp]
-/
theorem get_prodLift (f : α ->. β) (g : α ->. γ) (x : α) (h) :
    (f.prodLift g x).get h = ((f x).get h.1, (g x).get h.2) :=
  rfl

@[simp]
/--
theorem `prodLift_apply` / 定理 `prodLift_apply`

English:
theorem prodLift_apply
  given: (f : α ->. β) (g : α ->. γ) (x : α)
  proof: rfl

中文:
定理 prodLift_apply
  条件: (f : α ->. β) (g : α ->. γ) (x : α)
  证明: rfl
-/
theorem prodLift_apply (f : α ->. β) (g : α ->. γ) (x : α) :
    f.prodLift g x = ⟨(f x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩ :=
  rfl

/--
theorem `mem_prodLift` / 定理 `mem_prodLift`

English:
theorem mem_prodLift
  given: {f : α ->. β} {g : α ->. γ} {x : α} {y : β × γ}
  proof: by
  trans exists hp hq, (f x).get hp = y.1 ∧ (g x).get hq = y.2
  · simp only [prodLift, Part.mem_mk_iff, And.exists, Prod.ext_iff]
  · simp only [exists_and_left, exists_and_right, Membership.mem, Part.Mem]

中文:
定理 mem_prodLift
  条件: {f : α ->. β} {g : α ->. γ} {x : α} {y : β × γ}
  证明: by
  trans exists hp hq, (f x).get hp = y.1 ∧ (g x).get hq = y.2
  · simp only [prodLift, Part.mem_mk_iff, And.exists, Prod.ext_iff]
  · simp only [exists_and_left, exists_and_right, Membership.mem, Part.Mem]

Depends on / 依赖: And.exists, Membership, Membership.mem, Part.Mem, Part.mem_mk_iff, Prod.ext_iff, exists_and_left, exists_and_right, ext_iff, mem_mk_iff, prodLift
-/
theorem mem_prodLift {f : α ->. β} {g : α ->. γ} {x : α} {y : β × γ} :
    y in f.prodLift g x ↔ y.1 in f x ∧ y.2 in g x := by
  trans exists hp hq, (f x).get hp = y.1 ∧ (g x).get hq = y.2
  · simp only [prodLift, Part.mem_mk_iff, And.exists, Prod.ext_iff]
  · simp only [exists_and_left, exists_and_right, Membership.mem, Part.Mem]

/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: (f : α ->. γ) (g : β ->. δ)
  body: fun x =>
  ⟨(f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩

@[simp]

中文:
定义 prodMap
  签名: (f : α ->. γ) (g : β ->. δ)
  定义体: fun x =>
  ⟨(f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩

@[simp]
-/
def prodMap (f : α ->. γ) (g : β ->. δ) : α × β ->. γ × δ := fun x =>
  ⟨(f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩

@[simp]
/--
theorem `dom_prodMap` / 定理 `dom_prodMap`

English:
theorem dom_prodMap
  given: (f : α ->. γ) (g : β ->. δ)
  proof: rfl

中文:
定理 dom_prodMap
  条件: (f : α ->. γ) (g : β ->. δ)
  证明: rfl
-/
theorem dom_prodMap (f : α ->. γ) (g : β ->. δ) :
    (f.prodMap g).Dom = { x | (f x.1).Dom ∧ (g x.2).Dom } :=
  rfl

/--
theorem `get_prodMap` / 定理 `get_prodMap`

English:
theorem get_prodMap
  given: (f : α ->. γ) (g : β ->. δ) (x : α × β) (h)
  proof: rfl

@[simp]

中文:
定理 get_prodMap
  条件: (f : α ->. γ) (g : β ->. δ) (x : α × β) (h)
  证明: rfl

@[simp]
-/
theorem get_prodMap (f : α ->. γ) (g : β ->. δ) (x : α × β) (h) :
    (f.prodMap g x).get h = ((f x.1).get h.1, (g x.2).get h.2) :=
  rfl

@[simp]
/--
theorem `prodMap_apply` / 定理 `prodMap_apply`

English:
theorem prodMap_apply
  given: (f : α ->. γ) (g : β ->. δ) (x : α × β)
  proof: rfl

中文:
定理 prodMap_apply
  条件: (f : α ->. γ) (g : β ->. δ) (x : α × β)
  证明: rfl
-/
theorem prodMap_apply (f : α ->. γ) (g : β ->. δ) (x : α × β) :
    f.prodMap g x = ⟨(f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩ :=
  rfl

/--
theorem `mem_prodMap` / 定理 `mem_prodMap`

English:
theorem mem_prodMap
  given: {f : α ->. γ} {g : β ->. δ} {x : α × β} {y : γ × δ}
  proof: by
  trans exists hp hq, (f x.1).get hp = y.1 ∧ (g x.2).get hq = y.2
  · simp only [prodMap, Part.mem_mk_iff, And.exists, Prod.ext_iff]
  · simp only [exists_and_left, exists_and_right, Membership.mem, Part.Mem]

中文:
定理 mem_prodMap
  条件: {f : α ->. γ} {g : β ->. δ} {x : α × β} {y : γ × δ}
  证明: by
  trans exists hp hq, (f x.1).get hp = y.1 ∧ (g x.2).get hq = y.2
  · simp only [prodMap, Part.mem_mk_iff, And.exists, Prod.ext_iff]
  · simp only [exists_and_left, exists_and_right, Membership.mem, Part.Mem]

Depends on / 依赖: And.exists, Membership, Membership.mem, Part.Mem, Part.mem_mk_iff, Prod.ext_iff, exists_and_left, exists_and_right, ext_iff, mem_mk_iff, prodMap
-/
theorem mem_prodMap {f : α ->. γ} {g : β ->. δ} {x : α × β} {y : γ × δ} :
    y in f.prodMap g x ↔ y.1 in f x.1 ∧ y.2 in g x.2 := by
  trans exists hp hq, (f x.1).get hp = y.1 ∧ (g x.2).get hq = y.2
  · simp only [prodMap, Part.mem_mk_iff, And.exists, Prod.ext_iff]
  · simp only [exists_and_left, exists_and_right, Membership.mem, Part.Mem]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `prodLift_fst_comp_snd_comp` / 定理 `prodLift_fst_comp_snd_comp`

English:
theorem prodLift_fst_comp_snd_comp
  given: (f : α ->. γ) (g : β ->. δ)
  proof: by
  aesop

@[simp]

中文:
定理 prodLift_fst_comp_snd_comp
  条件: (f : α ->. γ) (g : β ->. δ)
  证明: by
  aesop

@[simp]
-/
theorem prodLift_fst_comp_snd_comp (f : α ->. γ) (g : β ->. δ) :
    prodLift (f.comp ((Prod.fst : α × β -> α) : α × β ->. α))
        (g.comp ((Prod.snd : α × β -> β) : α × β ->. β)) =
      prodMap f g := by
  aesop

@[simp]
/--
theorem `prodMap_id_id` / 定理 `prodMap_id_id`

English:
theorem prodMap_id_id
  statement: (PFun.id α).prodMap (PFun.id β) = PFun.id _
  proof: by
  aesop

@[simp]

中文:
定理 prodMap_id_id
  结论: (PFun.id α).prodMap (PFun.id β) = PFun.id _
  证明: by
  aesop

@[simp]
-/
theorem prodMap_id_id : (PFun.id α).prodMap (PFun.id β) = PFun.id _ := by
  aesop

@[simp]
/--
theorem `prodMap_comp_comp` / 定理 `prodMap_comp_comp`

English:
theorem prodMap_comp_comp
  given: (f₁ : α ->. β) (f₂ : β ->. γ) (g₁ : δ ->. ε) (g₂ : ε ->. ι)
  proof: -- `aesop` can prove this but takes over a second, so we do it manually
ext fun ⟨_, _⟩ ⟨_, _⟩ =>
  ⟨fun ⟨⟨⟨h1l1, h1l2⟩, ⟨h1r1, h1r2⟩⟩, h2⟩ => ⟨⟨⟨h1l1, h1r1⟩, ⟨h1l2, h1r2⟩⟩, h2⟩,
   fun ⟨⟨⟨h1l1, h1r1⟩, ⟨h1l2, h1r2⟩⟩, h2⟩ => ⟨⟨⟨h1l1, h1l2⟩, ⟨h1r1, h1r2⟩⟩, h2⟩⟩

中文:
定理 prodMap_comp_comp
  条件: (f₁ : α ->. β) (f₂ : β ->. γ) (g₁ : δ ->. ε) (g₂ : ε ->. ι)
  证明: -- `aesop` can prove this but takes over a second, so we do it manually
ext fun ⟨_, _⟩ ⟨_, _⟩ =>
  ⟨fun ⟨⟨⟨h1l1, h1l2⟩, ⟨h1r1, h1r2⟩⟩, h2⟩ => ⟨⟨⟨h1l1, h1r1⟩, ⟨h1l2, h1r2⟩⟩, h2⟩,
   fun ⟨⟨⟨h1l1, h1r1⟩, ⟨h1l2, h1r2⟩⟩, h2⟩ => ⟨⟨⟨h1l1, h1l2⟩, ⟨h1r1, h1r2⟩⟩, h2⟩⟩
-/
theorem prodMap_comp_comp (f₁ : α ->. β) (f₂ : β ->. γ) (g₁ : δ ->. ε) (g₂ : ε ->. ι) :
    (f₂.comp f₁).prodMap (g₂.comp g₁) = (f₂.prodMap g₂).comp (f₁.prodMap g₁) :=
  -- `aesop` can prove this but takes over a second, so we do it manually
ext fun ⟨_, _⟩ ⟨_, _⟩ =>
  ⟨fun ⟨⟨⟨h1l1, h1l2⟩, ⟨h1r1, h1r2⟩⟩, h2⟩ => ⟨⟨⟨h1l1, h1r1⟩, ⟨h1l2, h1r2⟩⟩, h2⟩,
   fun ⟨⟨⟨h1l1, h1r1⟩, ⟨h1l2, h1r2⟩⟩, h2⟩ => ⟨⟨⟨h1l1, h1l2⟩, ⟨h1r1, h1r2⟩⟩, h2⟩⟩

end PFun
