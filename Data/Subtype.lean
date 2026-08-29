/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.AdaptationNote
public import Mathlib.Tactic.Simps.Basic

/-!
# Subtypes

This file provides basic API for subtypes, which are defined in core.

A subtype is a type made from restricting another type, say `α`, to its elements that satisfy some
predicate, say `p : α → Prop`. Specifically, it is the type of pairs `⟨val, property⟩` where
`val : α` and `property : p val`. It is denoted `Subtype p` and notation `{val : α // p val}` is
available.

A subtype has a natural coercion to the parent type, by coercing `⟨val, property⟩` to `val`. As
such, subtypes can be thought of as bundled sets, the difference being that elements of a set are
still of type `α` while elements of a subtype aren't.
-/

@[expose] public section


open Function

namespace Subtype

variable {α β γ : Sort*} {p q : α -> Prop}

attribute [coe] Subtype.val

initialize_simps_projections Subtype (val -> coe)

-- This is a leftover from Lean 3: it is identical to `Subtype.property`, and should be deprecated.
/--
theorem `prop` / 定理 `prop`

English:
theorem prop
  given: (x : Subtype p)
  statement: p x
  proof: x.2

中文:
定理 prop
  条件: (x : Subtype p)
  结论: p x
  证明: x.2
-/
theorem prop (x : Subtype p) : p x :=
  x.2

/--
theorem `forall'` / 定理 `forall'`

English:
theorem forall'
  given: {q : forall x, p x -> Prop}
  statement: (forall x h, q x h) ↔ forall x : { a // p a }, q x x.2
  proof: (@Subtype.forall _ _ fun x => q x.1 x.2).symm

中文:
定理 forall'
  条件: {q : 对任意 x, p x -> 命题}
  结论: (对任意 x h, q x h) ↔ 对任意 x : { a // p a }, q x x.2
  证明: (@Subtype.forall _ _ fun x => q x.1 x.2).symm
-/
protected theorem forall' {q : forall x, p x -> Prop} : (forall x h, q x h) ↔ forall x : { a // p a }, q x x.2 :=
  (@Subtype.forall _ _ fun x => q x.1 x.2).symm

/--
theorem `exists'` / 定理 `exists'`

English:
theorem exists'
  given: {q : forall x, p x -> Prop}
  statement: (exists x h, q x h) ↔ exists x : { a // p a }, q x x.2
  proof: (@Subtype.exists _ _ fun x => q x.1 x.2).symm

中文:
定理 exists'
  条件: {q : 对任意 x, p x -> 命题}
  结论: (存在 x h, q x h) ↔ 存在 x : { a // p a }, q x x.2
  证明: (@Subtype.exists _ _ fun x => q x.1 x.2).symm
-/
protected theorem exists' {q : forall x, p x -> Prop} : (exists x h, q x h) ↔ exists x : { a // p a }, q x x.2 :=
  (@Subtype.exists _ _ fun x => q x.1 x.2).symm

/--
theorem `heq_iff_coe_eq` / 定理 `heq_iff_coe_eq`

English:
theorem heq_iff_coe_eq
  given: (h : forall x, p x ↔ q x) {a1 : { x // p x }} {a2 : { x // q x }}
  proof: Eq.rec
    (motive := fun (pp : (α -> Prop)) _ => forall a2' : {x // pp x}, a1 ≍ a2' ↔ (a1 : α) = (a2' : α))
    (by grind) (funext <| fun x => propext (h x)) a2

中文:
定理 heq_iff_coe_eq
  条件: (h : 对任意 x, p x ↔ q x) {a1 : { x // p x }} {a2 : { x // q x }}
  证明: Eq.rec
    (motive := fun (pp : (α -> Prop)) _ => forall a2' : {x // pp x}, a1 ≍ a2' ↔ (a1 : α) = (a2' : α))
    (by grind) (funext <| fun x => propext (h x)) a2

Depends on / 依赖: Eq.rec, motive, propext
-/
theorem heq_iff_coe_eq (h : forall x, p x ↔ q x) {a1 : { x // p x }} {a2 : { x // q x }} :
    a1 ≍ a2 ↔ (a1 : α) = (a2 : α) :=
  Eq.rec
    (motive := fun (pp : (α -> Prop)) _ => forall a2' : {x // pp x}, a1 ≍ a2' ↔ (a1 : α) = (a2' : α))
    (by grind) (funext <| fun x => propext (h x)) a2

/--
lemma `heq_iff_coe_heq` / 引理 `heq_iff_coe_heq`

English:
lemma heq_iff_coe_heq
  statement: {α β : Sort _} {p : α -> Prop} {q : β -> Prop} {a : {x // p x}}
  proof: by grind

@[simp]

中文:
引理 heq_iff_coe_heq
  结论: {α β : Sort _} {p : α -> 命题} {q : β -> 命题} {a : {x // p x}}
  证明: by grind

@[simp]
-/
lemma heq_iff_coe_heq {α β : Sort _} {p : α -> Prop} {q : β -> Prop} {a : {x // p x}}
    {b : {y // q y}} (h : α = β) (h' : p ≍ q) : a ≍ b ↔ (a : α) ≍ (b : β) := by grind

@[simp]
/--
theorem `coe_eta` / 定理 `coe_eta`

English:
theorem coe_eta
  given: (a : { a // p a }) (h : p a)
  statement: mk (↑a) h = a
  proof: Subtype.ext rfl

中文:
定理 coe_eta
  条件: (a : { a // p a }) (h : p a)
  结论: mk (↑a) h = a
  证明: Subtype.ext rfl

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a :=
  Subtype.ext rfl

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (a h)
  statement: (@mk α p a h : α) = a
  proof: rfl

中文:
定理 coe_mk
  条件: (a h)
  结论: (@mk α p a h : α) = a
  证明: rfl
-/
theorem coe_mk (a h) : (@mk α p a h : α) = a :=
  rfl

/--
theorem `mk_eq_mk` / 定理 `mk_eq_mk`

English:
theorem mk_eq_mk
  given: {a h a' h'}
  statement: @mk α p a h = @mk α p a' h' ↔ a = a'
  proof: by simp

中文:
定理 mk_eq_mk
  条件: {a h a' h'}
  结论: @mk α p a h = @mk α p a' h' ↔ a = a'
  证明: by simp
-/
theorem mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a = a' := by simp

/--
theorem `coe_eq_of_eq_mk` / 定理 `coe_eq_of_eq_mk`

English:
theorem coe_eq_of_eq_mk
  given: {a : { a // p a }} {b : α} (h : ↑a = b)
  statement: a = ⟨b, h ▸ a.2⟩
  proof: Subtype.ext h

中文:
定理 coe_eq_of_eq_mk
  条件: {a : { a // p a }} {b : α} (h : ↑a = b)
  结论: a = ⟨b, h ▸ a.2⟩
  证明: Subtype.ext h

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem coe_eq_of_eq_mk {a : { a // p a }} {b : α} (h : ↑a = b) : a = ⟨b, h ▸ a.2⟩ :=
  Subtype.ext h

/--
theorem `coe_eq_iff` / 定理 `coe_eq_iff`

English:
theorem coe_eq_iff
  given: {a : { a // p a }} {b : α}
  statement: ↑a = b ↔ exists h, a = ⟨b, h⟩
  proof: by grind

中文:
定理 coe_eq_iff
  条件: {a : { a // p a }} {b : α}
  结论: ↑a = b ↔ 存在 h, a = ⟨b, h⟩
  证明: by grind
-/
theorem coe_eq_iff {a : { a // p a }} {b : α} : ↑a = b ↔ exists h, a = ⟨b, h⟩ := by grind

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective (fun (a : Subtype p) => (a : α))
  proof: fun _ _ => Subtype.ext

中文:
定理 coe_injective
  结论: Injective (fun (a : Subtype p) => (a : α))
  证明: fun _ _ => Subtype.ext

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem coe_injective : Injective (fun (a : Subtype p) => (a : α)) := fun _ _ => Subtype.ext

/--
theorem `val_injective` / 定理 `val_injective`

English:
theorem val_injective
  statement: Injective (@val _ p)
  proof: coe_injective

中文:
定理 val_injective
  结论: Injective (@val _ p)
  证明: coe_injective
-/
@[simp] theorem val_injective : Injective (@val _ p) :=
  coe_injective

/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {a b : Subtype p}
  statement: (a : α) = b ↔ a = b
  proof: coe_injective.eq_iff

中文:
定理 coe_inj
  条件: {a b : Subtype p}
  结论: (a : α) = b ↔ a = b
  证明: coe_injective.eq_iff

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff
-/
theorem coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b :=
  coe_injective.eq_iff

/--
theorem `val_inj` / 定理 `val_inj`

English:
theorem val_inj
  given: {a b : Subtype p}
  statement: a.val = b.val ↔ a = b
  proof: coe_inj

中文:
定理 val_inj
  条件: {a b : Subtype p}
  结论: a.val = b.val ↔ a = b
  证明: coe_inj

Depends on / 依赖: coe_inj
-/
theorem val_inj {a b : Subtype p} : a.val = b.val ↔ a = b :=
  coe_inj

/--
lemma `coe_ne_coe` / 引理 `coe_ne_coe`

English:
lemma coe_ne_coe
  given: {a b : Subtype p}
  statement: (a : α) != b ↔ a != b
  proof: coe_injective.ne_iff

@[simp]

中文:
引理 coe_ne_coe
  条件: {a b : Subtype p}
  结论: (a : α) != b ↔ a != b
  证明: coe_injective.ne_iff

@[simp]

Depends on / 依赖: coe_injective, coe_injective.ne_iff, ne_iff
-/
lemma coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b := coe_injective.ne_iff

@[simp]
/--
theorem `_root_.exists_eq_subtype_mk_iff` / 定理 `_root_.exists_eq_subtype_mk_iff`

English:
theorem _root_.exists_eq_subtype_mk_iff
  given: {a : Subtype p} {b : α}
  proof: coe_eq_iff.symm

@[simp]

中文:
定理 _root_.exists_eq_subtype_mk_iff
  条件: {a : Subtype p} {b : α}
  证明: coe_eq_iff.symm

@[simp]

Depends on / 依赖: coe_eq_iff, coe_eq_iff.symm
-/
theorem _root_.exists_eq_subtype_mk_iff {a : Subtype p} {b : α} :
    (exists h : p b, a = Subtype.mk b h) ↔ ↑a = b :=
  coe_eq_iff.symm

@[simp]
/--
theorem `_root_.exists_subtype_mk_eq_iff` / 定理 `_root_.exists_subtype_mk_eq_iff`

English:
theorem _root_.exists_subtype_mk_eq_iff
  given: {a : Subtype p} {b : α}
  proof: by grind

中文:
定理 _root_.exists_subtype_mk_eq_iff
  条件: {a : Subtype p} {b : α}
  证明: by grind
-/
theorem _root_.exists_subtype_mk_eq_iff {a : Subtype p} {b : α} :
    (exists h : p b, Subtype.mk b h = a) ↔ b = a := by grind

/--
theorem `_root_.Function.extend_val_apply` / 定理 `_root_.Function.extend_val_apply`

English:
theorem _root_.Function.extend_val_apply
  statement: {p : β -> Prop} {g : {x // p x} -> γ} {j : β -> γ}
  proof: val_injective.extend_apply g j ⟨b, hb⟩

中文:
定理 _root_.Function.extend_val_apply
  结论: {p : β -> 命题} {g : {x // p x} -> γ} {j : β -> γ}
  证明: val_injective.extend_apply g j ⟨b, hb⟩

Depends on / 依赖: extend_apply, val_injective, val_injective.extend_apply
-/
theorem _root_.Function.extend_val_apply {p : β -> Prop} {g : {x // p x} -> γ} {j : β -> γ}
    {b : β} (hb : p b) : val.extend g j b = g ⟨b, hb⟩ :=
  val_injective.extend_apply g j ⟨b, hb⟩

/--
theorem `_root_.Function.extend_val_apply'` / 定理 `_root_.Function.extend_val_apply'`

English:
theorem _root_.Function.extend_val_apply'
  statement: {p : β -> Prop} {g : {x // p x} -> γ} {j : β -> γ}
  proof: by
  grind [Function.extend]

中文:
定理 _root_.Function.extend_val_apply'
  结论: {p : β -> 命题} {g : {x // p x} -> γ} {j : β -> γ}
  证明: by
  grind [Function.extend]

Depends on / 依赖: Function, Function.extend, extend
-/
theorem _root_.Function.extend_val_apply' {p : β -> Prop} {g : {x // p x} -> γ} {j : β -> γ}
    {b : β} (hb : ¬p b) : val.extend g j b = j b := by
  grind [Function.extend]

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: {α} {β : α -> Type*} (p : α -> Prop) (f : forall x, β x) (x : Subtype p)
  body: f x

@[simp, grind =]

中文:
定义 restrict
  签名: {α} {β : α -> 类型} (p : α -> 命题) (f : 对任意 x, β x) (x : Subtype p)
  定义体: f x

@[simp, grind =]
-/
def restrict {α} {β : α -> Type*} (p : α -> Prop) (f : forall x, β x) (x : Subtype p) : β x.1 :=
  f x

@[simp, grind =]
/--
theorem `restrict_apply` / 定理 `restrict_apply`

English:
theorem restrict_apply
  given: {α} {β : α -> Type*} (f : forall x, β x) (p : α -> Prop) (x : Subtype p)
  proof: by
  rfl

中文:
定理 restrict_apply
  条件: {α} {β : α -> 类型} (f : 对任意 x, β x) (p : α -> 命题) (x : Subtype p)
  证明: by
  rfl
-/
theorem restrict_apply {α} {β : α -> Type*} (f : forall x, β x) (p : α -> Prop) (x : Subtype p) :
    restrict p f x = f x.1 := by
  rfl

/--
theorem `restrict_def` / 定理 `restrict_def`

English:
theorem restrict_def
  given: {α β} (f : α -> β) (p : α -> Prop)
  proof: rfl

中文:
定理 restrict_def
  条件: {α β} (f : α -> β) (p : α -> 命题)
  证明: rfl
-/
theorem restrict_def {α β} (f : α -> β) (p : α -> Prop) :
    restrict p f = f ∘ (fun (a : Subtype p) => a) := rfl

/--
theorem `restrict_injective` / 定理 `restrict_injective`

English:
theorem restrict_injective
  given: {α β} {f : α -> β} (p : α -> Prop) (h : Injective f)
  proof: h.comp coe_injective

中文:
定理 restrict_injective
  条件: {α β} {f : α -> β} (p : α -> 命题) (h : Injective f)
  证明: h.comp coe_injective

Depends on / 依赖: coe_injective, h.comp
-/
theorem restrict_injective {α β} {f : α -> β} (p : α -> Prop) (h : Injective f) :
    Injective (restrict p f) :=
  h.comp coe_injective

/--
theorem `surjective_restrict` / 定理 `surjective_restrict`

English:
theorem surjective_restrict
  given: {α} {β : α -> Type*} [ne : forall a, Nonempty (β a)] (p : α -> Prop)
  proof: by
  classical
  exact fun f => ⟨fun x => if h : p x then f ⟨x, h⟩ else Nonempty.some (ne x), by grind⟩

中文:
定理 surjective_restrict
  条件: {α} {β : α -> 类型} [ne : 对任意 a, Nonempty (β a)] (p : α -> 命题)
  证明: by
  classical
  exact fun f => ⟨fun x => if h : p x then f ⟨x, h⟩ else Nonempty.some (ne x), by grind⟩

Depends on / 依赖: Nonempty, Nonempty.some, classical
-/
theorem surjective_restrict {α} {β : α -> Type*} [ne : forall a, Nonempty (β a)] (p : α -> Prop) :
    Surjective fun f : forall x, β x => restrict p f := by
  classical
  exact fun f => ⟨fun x => if h : p x then f ⟨x, h⟩ else Nonempty.some (ne x), by grind⟩

/-- Defining a map into a subtype, this can be seen as a "coinduction principle" of `Subtype` -/
@[simps]
/--
Definition of `coind` / `coind` 的定义

English:
definition coind
  signature: {α β} (f : α -> β) {p : β -> Prop} (h : forall a, p (f a))
  body: fun a => ⟨f a, h a⟩

中文:
定义 coind
  签名: {α β} (f : α -> β) {p : β -> 命题} (h : 对任意 a, p (f a))
  定义体: fun a => ⟨f a, h a⟩
-/
def coind {α β} (f : α -> β) {p : β -> Prop} (h : forall a, p (f a)) : α -> Subtype p := fun a => ⟨f a, h a⟩

/--
theorem `coind_injective` / 定理 `coind_injective`

English:
theorem coind_injective
  given: {α β} {f : α -> β} {p : β -> Prop} (h : forall a, p (f a)) (hf : Injective f)
  proof: fun x y hxy => hf by apply congr_arg Subtype.val hxy

中文:
定理 coind_injective
  条件: {α β} {f : α -> β} {p : β -> 命题} (h : 对任意 a, p (f a)) (hf : Injective f)
  证明: fun x y hxy => hf by apply congr_arg Subtype.val hxy

Depends on / 依赖: Subtype, Subtype.val, congr_arg
-/
theorem coind_injective {α β} {f : α -> β} {p : β -> Prop} (h : forall a, p (f a)) (hf : Injective f) :
Injective (coind f h) := fun x y hxy => hf by apply congr_arg Subtype.val hxy

/--
theorem `coind_injective_iff` / 定理 `coind_injective_iff`

English:
theorem coind_injective_iff
  given: {α β} {f : α -> β} {p : β -> Prop} (h : forall a, p (f a))
  proof: ⟨Subtype.coe_injective.comp, coind_injective h⟩

中文:
定理 coind_injective_iff
  条件: {α β} {f : α -> β} {p : β -> 命题} (h : 对任意 a, p (f a))
  证明: ⟨Subtype.coe_injective.comp, coind_injective h⟩
-/
@[simp] theorem coind_injective_iff {α β} {f : α -> β} {p : β -> Prop} (h : forall a, p (f a)) :
    Injective (coind f h) ↔ Injective f :=
  ⟨Subtype.coe_injective.comp, coind_injective h⟩

/-- Restriction of a function to a function on subtypes. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {p : α -> Prop} {q : β -> Prop} (f : α -> β) (h : forall a, p a -> q (f a))
  body: fun x => ⟨f x, h x x.prop⟩

中文:
定义 map
  签名: {p : α -> 命题} {q : β -> 命题} (f : α -> β) (h : 对任意 a, p a -> q (f a))
  定义体: fun x => ⟨f x, h x x.prop⟩

Depends on / 依赖: x.prop
-/
def map {p : α -> Prop} {q : β -> Prop} (f : α -> β) (h : forall a, p a -> q (f a)) :
    Subtype p -> Subtype q :=
  fun x => ⟨f x, h x x.prop⟩

/--
theorem `map_def` / 定理 `map_def`

English:
theorem map_def
  given: {p : α -> Prop} {q : β -> Prop} (f : α -> β) (h : forall a, p a -> q (f a))
  proof: rfl

中文:
定理 map_def
  条件: {p : α -> 命题} {q : β -> 命题} (f : α -> β) (h : 对任意 a, p a -> q (f a))
  证明: rfl
-/
theorem map_def {p : α -> Prop} {q : β -> Prop} (f : α -> β) (h : forall a, p a -> q (f a)) :
    map f h = fun x => ⟨f x, h x x.prop⟩ :=
  rfl

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} {x : Subtype p}
  proof: rfl

中文:
定理 map_comp
  结论: {p : α -> 命题} {q : β -> 命题} {r : γ -> 命题} {x : Subtype p}
  证明: rfl
-/
theorem map_comp {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} {x : Subtype p}
    (f : α -> β) (h : forall a, p a -> q (f a)) (g : β -> γ) (l : forall a, q a -> r (g a)) :
    map g l (map f h x) = map (g ∘ f) (fun a ha => l (f a) <| h a ha) x :=
  rfl

/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: {p : α -> Prop} {h : forall a, p a -> p (id a)}
  statement: map (@id α) h = id
  proof: funext fun _ => rfl

中文:
定理 map_id
  条件: {p : α -> 命题} {h : 对任意 a, p a -> p (id a)}
  结论: map (@id α) h = id
  证明: funext fun _ => rfl
-/
theorem map_id {p : α -> Prop} {h : forall a, p a -> p (id a)} : map (@id α) h = id :=
  funext fun _ => rfl

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  statement: {p : α -> Prop} {q : β -> Prop} {f : α -> β} (h : forall a, p a -> q (f a))
  proof: coind_injective _ hf.comp coe_injective

中文:
定理 map_injective
  结论: {p : α -> 命题} {q : β -> 命题} {f : α -> β} (h : 对任意 a, p a -> q (f a))
  证明: coind_injective _ hf.comp coe_injective

Depends on / 依赖: coe_injective, coind_injective, hf.comp
-/
theorem map_injective {p : α -> Prop} {q : β -> Prop} {f : α -> β} (h : forall a, p a -> q (f a))
    (hf : Injective f) : Injective (map f h) :=
coind_injective _ hf.comp coe_injective

/--
theorem `map_involutive` / 定理 `map_involutive`

English:
theorem map_involutive
  statement: {p : α -> Prop} {f : α -> α} (h : forall a, p a -> p (f a))
  proof: fun x => Subtype.ext (hf x)

中文:
定理 map_involutive
  结论: {p : α -> 命题} {f : α -> α} (h : 对任意 a, p a -> p (f a))
  证明: fun x => Subtype.ext (hf x)

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem map_involutive {p : α -> Prop} {f : α -> α} (h : forall a, p a -> p (f a))
    (hf : Involutive f) : Involutive (map f h) :=
  fun x => Subtype.ext (hf x)

/--
theorem `map_eq` / 定理 `map_eq`

English:
theorem map_eq
  statement: {p : α -> Prop} {q : β -> Prop} {f g : α -> β}
  proof: Subtype.ext_iff

中文:
定理 map_eq
  结论: {p : α -> 命题} {q : β -> 命题} {f g : α -> β}
  证明: Subtype.ext_iff

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem map_eq {p : α -> Prop} {q : β -> Prop} {f g : α -> β}
    (h₁ : forall a : α, p a -> q (f a)) (h₂ : forall a : α, p a -> q (g a))
    {x y : Subtype p} :
    map f h₁ x = map g h₂ y ↔ f x = g y :=
  Subtype.ext_iff

/--
theorem `map_ne` / 定理 `map_ne`

English:
theorem map_ne
  statement: {p : α -> Prop} {q : β -> Prop} {f g : α -> β}
  proof: .not map_eq h₁ h₂

中文:
定理 map_ne
  结论: {p : α -> 命题} {q : β -> 命题} {f g : α -> β}
  证明: .not map_eq h₁ h₂

Depends on / 依赖: map_eq
-/
theorem map_ne {p : α -> Prop} {q : β -> Prop} {f g : α -> β}
    (h₁ : forall a : α, p a -> q (f a)) (h₂ : forall a : α, p a -> q (g a))
    {x y : Subtype p} :
    map f h₁ x != map g h₂ y ↔ f x != g y :=
.not map_eq h₁ h₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasEquiv
  signature: α] (p
  body: ⟨fun s t => (s : α) ≈ (t : α)⟩

中文:
实例 [HasEquiv
  签名: α] (p
  定义体: ⟨fun s t => (s : α) ≈ (t : α)⟩
-/
instance [HasEquiv α] (p : α -> Prop) : HasEquiv (Subtype p) :=
  ⟨fun s t => (s : α) ≈ (t : α)⟩

/--
theorem `equiv_iff` / 定理 `equiv_iff`

English:
theorem equiv_iff
  given: [HasEquiv α] {p : α -> Prop} {s t : Subtype p}
  statement: s ≈ t ↔ (s : α) ≈ (t : α)
  proof: Iff.rfl

中文:
定理 equiv_iff
  条件: [HasEquiv α] {p : α -> 命题} {s t : Subtype p}
  结论: s ≈ t ↔ (s : α) ≈ (t : α)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem equiv_iff [HasEquiv α] {p : α -> Prop} {s t : Subtype p} : s ≈ t ↔ (s : α) ≈ (t : α) :=
  Iff.rfl

variable [Setoid α]

/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (s : Subtype p)
  statement: s ≈ s
  proof: Setoid.refl _

中文:
定理 refl
  条件: (s : Subtype p)
  结论: s ≈ s
  证明: Setoid.refl _
-/
protected theorem refl (s : Subtype p) : s ≈ s :=
  Setoid.refl _

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: {s t : Subtype p} (h : s ≈ t)
  statement: t ≈ s
  proof: Setoid.symm h

中文:
定理 symm
  条件: {s t : Subtype p} (h : s ≈ t)
  结论: t ≈ s
  证明: Setoid.symm h
-/
protected theorem symm {s t : Subtype p} (h : s ≈ t) : t ≈ s :=
  Setoid.symm h

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: {s t u : Subtype p} (h₁ : s ≈ t) (h₂ : t ≈ u)
  statement: s ≈ u
  proof: Setoid.trans h₁ h₂

中文:
定理 trans
  条件: {s t u : Subtype p} (h₁ : s ≈ t) (h₂ : t ≈ u)
  结论: s ≈ u
  证明: Setoid.trans h₁ h₂
-/
protected theorem trans {s t u : Subtype p} (h₁ : s ≈ t) (h₂ : t ≈ u) : s ≈ u :=
  Setoid.trans h₁ h₂

/--
theorem `equivalence` / 定理 `equivalence`

English:
theorem equivalence
  given: (p : α -> Prop)
  statement: Equivalence (@HasEquiv.Equiv (Subtype p) _)
  proof: .mk (Subtype.refl) (@Subtype.symm _ p _) (@Subtype.trans _ p _)

中文:
定理 equivalence
  条件: (p : α -> 命题)
  结论: Equivalence (@HasEquiv.Equiv (Subtype p) _)
  证明: .mk (Subtype.refl) (@Subtype.symm _ p _) (@Subtype.trans _ p _)

Depends on / 依赖: Subtype, Subtype.refl, Subtype.symm, Subtype.trans
-/
theorem equivalence (p : α -> Prop) : Equivalence (@HasEquiv.Equiv (Subtype p) _) :=
  .mk (Subtype.refl) (@Subtype.symm _ p _) (@Subtype.trans _ p _)

instance (p : α -> Prop) : Setoid (Subtype p) :=
  Setoid.mk (· ≈ ·) (equivalence p)

end Subtype

namespace Subtype

/-! Some facts about sets, which require that `α` is a type. -/
variable {α : Type*}

@[simp]
/--
theorem `coe_prop` / 定理 `coe_prop`

English:
theorem coe_prop
  given: {S : Set α} (a : { a // a in S })
  statement: ↑a in S
  proof: a.prop

中文:
定理 coe_prop
  条件: {S : Set α} (a : { a // a in S })
  结论: ↑a in S
  证明: a.prop

Depends on / 依赖: a.prop
-/
theorem coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S :=
  a.prop

/--
theorem `val_prop` / 定理 `val_prop`

English:
theorem val_prop
  given: {S : Set α} (a : { a // a in S })
  statement: a.val in S
  proof: a.prop

中文:
定理 val_prop
  条件: {S : Set α} (a : { a // a in S })
  结论: a.val in S
  证明: a.prop

Depends on / 依赖: a.prop
-/
theorem val_prop {S : Set α} (a : { a // a in S }) : a.val in S :=
  a.prop

end Subtype
