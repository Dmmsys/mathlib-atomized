/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Control.Combinators
public import Mathlib.Data.Option.Defs
public import Mathlib.Logic.IsEmpty.Basic
public import Mathlib.Logic.Relator
public import Mathlib.Util.CompileInductive
public import Aesop
public import Batteries.Tactic.Lint.Simp

/-!
# Option of a type

This file develops the basic theory of option types.

If `α` is a type, then `Option α` can be understood as the type with one more element than `α`.
`Option α` has terms `some a`, where `a : α`, and `none`, which is the added element.
This is useful in multiple ways:
* It is the prototype of addition of terms to a type. See for example `WithBot α` which uses
  `none` as an element smaller than all others.
* It can be used to define failsafe partial functions, which return `some the_result_we_expect`
  if we can find `the_result_we_expect`, and `none` if there is no meaningful result. This forces
  any subsequent use of the partial function to explicitly deal with the exceptions that make it
  return `none`.
* `Option` is a monad. We love monads.

`Part` is an alternative to `Option` that can be seen as the type of `True`/`False` values
along with a term `a : α` if the value is `True`.

-/

@[expose] public section

universe u

namespace Option

variable {α β γ δ : Type*}

/--
theorem `coe_def` / 定理 `coe_def`

English:
theorem coe_def
  statement: (fun a => ↑a : α -> Option α) = some
  proof: rfl

中文:
定理 coe_def
  结论: (fun a => ↑a : α -> Option α) = some
  证明: rfl
-/
theorem coe_def : (fun a => ↑a : α -> Option α) = some :=
  rfl

/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : α -> β} {y : β} {o : Option α}
  statement: y in o.map f ↔ exists x in o, f x = y
  proof: by simp

@[simp 1100]

中文:
定理 mem_map
  条件: {f : α -> β} {y : β} {o : Option α}
  结论: y in o.map f ↔ 存在 x in o, f x = y
  证明: by simp

@[simp 1100]
-/
theorem mem_map {f : α -> β} {y : β} {o : Option α} : y in o.map f ↔ exists x in o, f x = y := by simp

@[simp 1100]
/--
theorem `mem_map_of_injective` / 定理 `mem_map_of_injective`

English:
theorem mem_map_of_injective
  given: {f : α -> β} (H : Function.Injective f) {a : α} {o : Option α}
  proof: by
  aesop

中文:
定理 mem_map_of_injective
  条件: {f : α -> β} (H : Function.Injective f) {a : α} {o : Option α}
  证明: by
  aesop
-/
theorem mem_map_of_injective {f : α -> β} (H : Function.Injective f) {a : α} {o : Option α} :
    f a in o.map f ↔ a in o := by
  aesop

/--
theorem `forall_mem_map` / 定理 `forall_mem_map`

English:
theorem forall_mem_map
  given: {f : α -> β} {o : Option α} {p : β -> Prop}
  proof: by simp

中文:
定理 forall_mem_map
  条件: {f : α -> β} {o : Option α} {p : β -> 命题}
  证明: by simp
-/
theorem forall_mem_map {f : α -> β} {o : Option α} {p : β -> Prop} :
    (forall y in o.map f, p y) ↔ forall x in o, p (f x) := by simp

/--
theorem `exists_mem_map` / 定理 `exists_mem_map`

English:
theorem exists_mem_map
  given: {f : α -> β} {o : Option α} {p : β -> Prop}
  proof: by simp

中文:
定理 exists_mem_map
  条件: {f : α -> β} {o : Option α} {p : β -> 命题}
  证明: by simp
-/
theorem exists_mem_map {f : α -> β} {o : Option α} {p : β -> Prop} :
    (exists y in o.map f, p y) ↔ exists x in o, p (f x) := by simp

/--
theorem `coe_get` / 定理 `coe_get`

English:
theorem coe_get
  given: {o : Option α} (h : o.isSome)
  statement: ((Option.get _ h : α) : Option α) = o
  proof: Option.some_get h

中文:
定理 coe_get
  条件: {o : Option α} (h : o.isSome)
  结论: ((Option.get _ h : α) : Option α) = o
  证明: Option.some_get h

Depends on / 依赖: Option.some_get, some_get
-/
theorem coe_get {o : Option α} (h : o.isSome) : ((Option.get _ h : α) : Option α) = o :=
  Option.some_get h

/--
theorem `eq_of_mem_of_mem` / 定理 `eq_of_mem_of_mem`

English:
theorem eq_of_mem_of_mem
  given: {a : α} {o1 o2 : Option α} (h1 : a in o1) (h2 : a in o2)
  statement: o1 = o2
  proof: h1.trans h2.symm

中文:
定理 eq_of_mem_of_mem
  条件: {a : α} {o1 o2 : Option α} (h1 : a in o1) (h2 : a in o2)
  结论: o1 = o2
  证明: h1.trans h2.symm

Depends on / 依赖: h1.trans, h2.symm
-/
theorem eq_of_mem_of_mem {a : α} {o1 o2 : Option α} (h1 : a in o1) (h2 : a in o2) : o1 = o2 :=
  h1.trans h2.symm

/--
theorem `Mem.leftUnique` / 定理 `Mem.leftUnique`

English:
theorem Mem.leftUnique
  statement: Relator.LeftUnique ((· in ·) : α -> Option α -> Prop)
  proof: fun _ _ _ => mem_unique

中文:
定理 Mem.leftUnique
  结论: Relator.LeftUnique ((· in ·) : α -> Option α -> 命题)
  证明: fun _ _ _ => mem_unique

Depends on / 依赖: mem_unique
-/
theorem Mem.leftUnique : Relator.LeftUnique ((· in ·) : α -> Option α -> Prop) :=
  fun _ _ _ => mem_unique

/--
theorem `some_injective` / 定理 `some_injective`

English:
theorem some_injective
  given: (α : Type*)
  statement: Function.Injective (@some α)
  proof: fun _ _ => some_inj.mp

@[simp]

中文:
定理 some_injective
  条件: (α : 类型)
  结论: Function.Injective (@some α)
  证明: fun _ _ => some_inj.mp

@[simp]

Depends on / 依赖: some_inj, some_inj.mp
-/
theorem some_injective (α : Type*) : Function.Injective (@some α) := fun _ _ => some_inj.mp

@[simp]
/--
theorem `map_comp_some` / 定理 `map_comp_some`

English:
theorem map_comp_some
  given: (f : α -> β)
  statement: Option.map f ∘ some = some ∘ f
  proof: rfl

@[congr]

中文:
定理 map_comp_some
  条件: (f : α -> β)
  结论: Option.map f ∘ some = some ∘ f
  证明: rfl

@[congr]
-/
theorem map_comp_some (f : α -> β) : Option.map f ∘ some = some ∘ f :=
  rfl

@[congr]
/--
theorem `bind_congr'` / 定理 `bind_congr'`

English:
theorem bind_congr'
  statement: {f g : α -> Option β} {x y : Option α} (hx : x = y)
  proof: hx.symm ▸ bind_congr hf

中文:
定理 bind_congr'
  结论: {f g : α -> Option β} {x y : Option α} (hx : x = y)
  证明: hx.symm ▸ bind_congr hf

Depends on / 依赖: bind_congr, hx.symm
-/
theorem bind_congr' {f g : α -> Option β} {x y : Option α} (hx : x = y)
    (hf : forall a in y, f a = g a) : x.bind f = y.bind g :=
  hx.symm ▸ bind_congr hf

/--
theorem `joinM_eq_join` / 定理 `joinM_eq_join`

English:
theorem joinM_eq_join
  statement: joinM = @join α
  proof: funext fun _ => rfl

中文:
定理 joinM_eq_join
  结论: joinM = @join α
  证明: funext fun _ => rfl
-/
theorem joinM_eq_join : joinM = @join α :=
  funext fun _ => rfl

/--
theorem `bind_eq_bind'` / 定理 `bind_eq_bind'`

English:
theorem bind_eq_bind'
  given: {α β : Type u} {f : α -> Option β} {x : Option α}
  statement: x >>= f = x.bind f
  proof: rfl

中文:
定理 bind_eq_bind'
  条件: {α β : 类型u} {f : α -> Option β} {x : Option α}
  结论: x >>= f = x.bind f
  证明: rfl
-/
theorem bind_eq_bind' {α β : Type u} {f : α -> Option β} {x : Option α} : x >>= f = x.bind f :=
  rfl

/--
theorem `map_coe` / 定理 `map_coe`

English:
theorem map_coe
  given: {α β} {a : α} {f : α -> β}
  statement: f < > (a : Option α) = ↑(f a)
  proof: rfl

@[simp]

中文:
定理 map_coe
  条件: {α β} {a : α} {f : α -> β}
  结论: f < > (a : Option α) = ↑(f a)
  证明: rfl

@[simp]
-/
theorem map_coe {α β} {a : α} {f : α -> β} : f < > (a : Option α) = ↑(f a) :=
  rfl

@[simp]
/--
theorem `map_coe'` / 定理 `map_coe'`

English:
theorem map_coe'
  given: {a : α} {f : α -> β}
  statement: Option.map f (a : Option α) = ↑(f a)
  proof: rfl

中文:
定理 map_coe'
  条件: {a : α} {f : α -> β}
  结论: Option.map f (a : Option α) = ↑(f a)
  证明: rfl
-/
theorem map_coe' {a : α} {f : α -> β} : Option.map f (a : Option α) = ↑(f a) :=
  rfl

/--
theorem `map_injective'` / 定理 `map_injective'`

English:
theorem map_injective'
  statement: Function.Injective (@Option.map α β)
  proof: fun f g h =>
funext fun x => some_injective _ by simp only [← map_some, h]

@[simp]

中文:
定理 map_injective'
  结论: Function.Injective (@Option.map α β)
  证明: fun f g h =>
funext fun x => some_injective _ by simp only [← map_some, h]

@[simp]
-/
theorem map_injective' : Function.Injective (@Option.map α β) := fun f g h =>
funext fun x => some_injective _ by simp only [← map_some, h]

@[simp]
/--
theorem `map_inj` / 定理 `map_inj`

English:
theorem map_inj
  given: {f g : α -> β}
  statement: Option.map f = Option.map g ↔ f = g
  proof: map_injective'.eq_iff

@[simp]

中文:
定理 map_inj
  条件: {f g : α -> β}
  结论: Option.map f = Option.map g ↔ f = g
  证明: map_injective'.eq_iff

@[simp]

Depends on / 依赖: eq_iff, map_injective
-/
theorem map_inj {f g : α -> β} : Option.map f = Option.map g ↔ f = g :=
  map_injective'.eq_iff

@[simp]
/--
theorem `map_eq_id` / 定理 `map_eq_id`

English:
theorem map_eq_id
  given: {f : α -> α}
  statement: Option.map f = id ↔ f = id
  proof: map_injective'.eq_iff' map_id

中文:
定理 map_eq_id
  条件: {f : α -> α}
  结论: Option.map f = id ↔ f = id
  证明: map_injective'.eq_iff' map_id

Depends on / 依赖: eq_iff, map_id, map_injective
-/
theorem map_eq_id {f : α -> α} : Option.map f = id ↔ f = id :=
  map_injective'.eq_iff' map_id

/--
theorem `map_comm` / 定理 `map_comm`

English:
theorem map_comm
  statement: {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ : γ -> δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂)
  proof: by rw [map_map, h, ← map_map]

中文:
定理 map_comm
  结论: {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ : γ -> δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂)
  证明: by rw [map_map, h, ← map_map]

Depends on / 依赖: map_map
-/
theorem map_comm {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ : γ -> δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂)
    (a : α) :
    (Option.map f₁ a).map g₁ = (Option.map f₂ a).map g₂ := by rw [map_map, h, ← map_map]

section pmap

variable {p : α -> Prop} (f : forall a : α, p a -> β) (x : Option α)

/--
theorem `mem_pmem` / 定理 `mem_pmem`

English:
theorem mem_pmem
  given: {a : α} (h : forall a in x, p a) (ha : a in x)
  statement: f a (h a ha) in pmap f x h
  proof: by
  rw [mem_def] at ha ⊢
  subst ha
  rfl

中文:
定理 mem_pmem
  条件: {a : α} (h : 对任意 a in x, p a) (ha : a in x)
  结论: f a (h a ha) in pmap f x h
  证明: by
  rw [mem_def] at ha ⊢
  subst ha
  rfl

Depends on / 依赖: mem_def
-/
theorem mem_pmem {a : α} (h : forall a in x, p a) (ha : a in x) : f a (h a ha) in pmap f x h := by
  rw [mem_def] at ha ⊢
  subst ha
  rfl

/--
theorem `pmap_bind` / 定理 `pmap_bind`

English:
theorem pmap_bind
  statement: {α β γ} {x : Option α} {g : α -> Option β} {p : β -> Prop} {f : forall b, p b -> γ} (H)
  proof: by
  grind [cases Option]

中文:
定理 pmap_bind
  结论: {α β γ} {x : Option α} {g : α -> Option β} {p : β -> 命题} {f : 对任意 b, p b -> γ} (H)
  证明: by
  grind [cases Option]
-/
theorem pmap_bind {α β γ} {x : Option α} {g : α -> Option β} {p : β -> Prop} {f : forall b, p b -> γ} (H)
    (H' : forall (a : α), forall b in g a, b in x >>= g) :
    pmap f (x >>= g) H = x >>= fun a => pmap f (g a) fun _ h => H _ (H' a _ h) := by
  grind [cases Option]

/--
theorem `bind_pmap` / 定理 `bind_pmap`

English:
theorem bind_pmap
  given: {α β γ} {p : α -> Prop} (f : forall a, p a -> β) (x : Option α) (g : β -> Option γ) (H)
  proof: by
  grind [cases Option, pmap]

中文:
定理 bind_pmap
  条件: {α β γ} {p : α -> 命题} (f : 对任意 a, p a -> β) (x : Option α) (g : β -> Option γ) (H)
  证明: by
  grind [cases Option, pmap]
-/
theorem bind_pmap {α β γ} {p : α -> Prop} (f : forall a, p a -> β) (x : Option α) (g : β -> Option γ) (H) :
    pmap f x H >>= g = x.pbind fun a h => g (f a (H _ h)) := by
  grind [cases Option, pmap]

variable {f x}

/--
theorem `pbind_eq_none` / 定理 `pbind_eq_none`

English:
theorem pbind_eq_none
  statement: {f : forall a : α, a in x -> Option β}
  proof: by
  grind [cases Option]

中文:
定理 pbind_eq_none
  结论: {f : 对任意 a : α, a in x -> Option β}
  证明: by
  grind [cases Option]
-/
theorem pbind_eq_none {f : forall a : α, a in x -> Option β}
    (h' : forall a (H : a in x), f a H = none -> x = none) : x.pbind f = none ↔ x = none := by
  grind [cases Option]

/--
theorem `join_pmap_eq_pmap_join` / 定理 `join_pmap_eq_pmap_join`

English:
theorem join_pmap_eq_pmap_join
  given: {f : forall a, p a -> β} {x : Option (Option α)} (H)
  proof: by
  grind [cases Option]

中文:
定理 join_pmap_eq_pmap_join
  条件: {f : 对任意 a, p a -> β} {x : Option (Option α)} (H)
  证明: by
  grind [cases Option]
-/
theorem join_pmap_eq_pmap_join {f : forall a, p a -> β} {x : Option (Option α)} (H) :
    (pmap (pmap f) x H).join = pmap f x.join fun a h => H (some a) (mem_of_mem_join h) _ rfl := by
  grind [cases Option]

/--
theorem `pmap_bind_id_eq_pmap_join` / 定理 `pmap_bind_id_eq_pmap_join`

English:
theorem pmap_bind_id_eq_pmap_join
  given: {f : forall a, p a -> β} {x : Option (Option α)} (H)
  proof: by
  grind [cases Option]

中文:
定理 pmap_bind_id_eq_pmap_join
  条件: {f : 对任意 a, p a -> β} {x : Option (Option α)} (H)
  证明: by
  grind [cases Option]
-/
theorem pmap_bind_id_eq_pmap_join {f : forall a, p a -> β} {x : Option (Option α)} (H) :
    ((pmap (pmap f) x H).bind fun a => a) =
      pmap f x.join fun a h => H (some a) (mem_of_mem_join h) _ rfl := by
  grind [cases Option]

end pmap

@[simp]
/--
theorem `seq_some` / 定理 `seq_some`

English:
theorem seq_some
  given: {α β} {a : α} {f : α -> β}
  statement: some f <*> some a = some (f a)
  proof: rfl

@[deprecated "Use `Option.get` with proof of `isSome`." (since := "2026-01-05")]

中文:
定理 seq_some
  条件: {α β} {a : α} {f : α -> β}
  结论: some f <*> some a = some (f a)
  证明: rfl

@[deprecated "Use `Option.get` with proof of `isSome`." (since := "2026-01-05")]
-/
theorem seq_some {α β} {a : α} {f : α -> β} : some f <*> some a = some (f a) :=
  rfl

@[deprecated "Use `Option.get` with proof of `isSome`." (since := "2026-01-05")]
/--
theorem `iget_mem` / 定理 `iget_mem`

English:
theorem iget_mem
  given: [Inhabited α]
  statement: forall {o : Option α}, isSome o -> o.iget in o

中文:
定理 iget_mem
  条件: [Inhabited α]
  结论: 对任意 {o : Option α}, isSome o -> o.iget in o
-/
theorem iget_mem [Inhabited α] : forall {o : Option α}, isSome o -> o.iget in o
  | some _, _ => rfl

@[deprecated "Use `Option.getD`." (since := "2026-01-05")]
/--
theorem `iget_of_mem` / 定理 `iget_of_mem`

English:
theorem iget_of_mem
  given: [Inhabited α] {a : α}
  statement: forall {o : Option α}, a in o -> o.iget = a

中文:
定理 iget_of_mem
  条件: [Inhabited α] {a : α}
  结论: 对任意 {o : Option α}, a in o -> o.iget = a
-/
theorem iget_of_mem [Inhabited α] {a : α} : forall {o : Option α}, a in o -> o.iget = a
  | _, rfl => rfl

@[deprecated "Use `Option.getD` directly." (since := "2026-01-05")]
/--
theorem `getD_default_eq_iget` / 定理 `getD_default_eq_iget`

English:
theorem getD_default_eq_iget
  given: [Inhabited α] (o : Option α)
  proof: by cases o <;> rfl

@[simp, grind =]

中文:
定理 getD_default_eq_iget
  条件: [Inhabited α] (o : Option α)
  证明: by cases o <;> rfl

@[simp, grind =]
-/
theorem getD_default_eq_iget [Inhabited α] (o : Option α) :
    o.getD default = o.iget := by cases o <;> rfl

@[simp, grind =]
/--
theorem `failure_eq_none` / 定理 `failure_eq_none`

English:
theorem failure_eq_none
  given: {α}
  statement: failure = (none : Option α)
  proof: rfl

@[simp]

中文:
定理 failure_eq_none
  条件: {α}
  结论: failure = (none : Option α)
  证明: rfl

@[simp]
-/
theorem failure_eq_none {α} : failure = (none : Option α) := rfl

@[simp]
/--
theorem `guard_eq_some'` / 定理 `guard_eq_some'`

English:
theorem guard_eq_some'
  given: {p : Prop} [Decidable p] (u)
  statement: _root_.guard p = some u ↔ p
  proof: by
  grind [cases Option, _root_.guard]

中文:
定理 guard_eq_some'
  条件: {p : 命题} [Decidable p] (u)
  结论: _root_.guard p = some u ↔ p
  证明: by
  grind [cases Option, _root_.guard]

Depends on / 依赖: _root_, _root_.guard
-/
theorem guard_eq_some' {p : Prop} [Decidable p] (u) : _root_.guard p = some u ↔ p := by
  grind [cases Option, _root_.guard]

/--
Definition of `casesOn'` / `casesOn'` 的定义

English:
definition casesOn'
  signature: : Option α -> β -> (α -> β) -> β

中文:
定义 casesOn'
  签名: : Option α -> β -> (α -> β) -> β
-/
def casesOn' : Option α -> β -> (α -> β) -> β
  | none, n, _ => n
  | some a, _, s => s a

@[simp]
/--
theorem `casesOn'_none` / 定理 `casesOn'_none`

English:
theorem casesOn'_none
  given: (x : β) (f : α -> β)
  statement: casesOn' none x f = x
  proof: rfl

@[simp]

中文:
定理 casesOn'_none
  条件: (x : β) (f : α -> β)
  结论: casesOn' none x f = x
  证明: rfl

@[simp]
-/
theorem casesOn'_none (x : β) (f : α -> β) : casesOn' none x f = x :=
  rfl

@[simp]
/--
theorem `casesOn'_some` / 定理 `casesOn'_some`

English:
theorem casesOn'_some
  given: (x : β) (f : α -> β) (a : α)
  statement: casesOn' (some a) x f = f a
  proof: rfl

@[simp]

中文:
定理 casesOn'_some
  条件: (x : β) (f : α -> β) (a : α)
  结论: casesOn' (some a) x f = f a
  证明: rfl

@[simp]
-/
theorem casesOn'_some (x : β) (f : α -> β) (a : α) : casesOn' (some a) x f = f a :=
  rfl

@[simp]
/--
theorem `casesOn'_coe` / 定理 `casesOn'_coe`

English:
theorem casesOn'_coe
  given: (x : β) (f : α -> β) (a : α)
  statement: casesOn' (a : Option α) x f = f a
  proof: rfl

@[simp]

中文:
定理 casesOn'_coe
  条件: (x : β) (f : α -> β) (a : α)
  结论: casesOn' (a : Option α) x f = f a
  证明: rfl

@[simp]
-/
theorem casesOn'_coe (x : β) (f : α -> β) (a : α) : casesOn' (a : Option α) x f = f a :=
  rfl

@[simp]
/--
theorem `casesOn'_none_coe` / 定理 `casesOn'_none_coe`

English:
theorem casesOn'_none_coe
  given: (f : Option α -> β) (o : Option α)
  proof: by cases o <;> rfl

中文:
定理 casesOn'_none_coe
  条件: (f : Option α -> β) (o : Option α)
  证明: by cases o <;> rfl
-/
theorem casesOn'_none_coe (f : Option α -> β) (o : Option α) :
    casesOn' o (f none) (f ∘ (fun a => ↑a)) = f o := by cases o <;> rfl

/--
lemma `casesOn'_eq_elim` / 引理 `casesOn'_eq_elim`

English:
lemma casesOn'_eq_elim
  given: (b : β) (f : α -> β) (a : Option α)
  proof: by cases a <;> rfl

中文:
引理 casesOn'_eq_elim
  条件: (b : β) (f : α -> β) (a : Option α)
  证明: by cases a <;> rfl
-/
lemma casesOn'_eq_elim (b : β) (f : α -> β) (a : Option α) :
    Option.casesOn' a b f = Option.elim a b f := by cases a <;> rfl

/--
theorem `orElse_eq_some` / 定理 `orElse_eq_some`

English:
theorem orElse_eq_some
  given: (o o' : Option α) (x : α)
  proof: by
  simp

中文:
定理 orElse_eq_some
  条件: (o o' : Option α) (x : α)
  证明: by
  simp
-/
theorem orElse_eq_some (o o' : Option α) (x : α) :
    (o <|> o') = some x ↔ o = some x ∨ o = none ∧ o' = some x := by
  simp

/--
theorem `orElse_eq_none` / 定理 `orElse_eq_none`

English:
theorem orElse_eq_none
  given: (o o' : Option α)
  statement: (o <|> o') = none ↔ o = none ∧ o' = none
  proof: by
  simp

中文:
定理 orElse_eq_none
  条件: (o o' : Option α)
  结论: (o <|> o') = none ↔ o = none ∧ o' = none
  证明: by
  simp
-/
theorem orElse_eq_none (o o' : Option α) : (o <|> o') = none ↔ o = none ∧ o' = none := by
  simp

section

/--
theorem `choice_eq_none` / 定理 `choice_eq_none`

English:
theorem choice_eq_none
  given: (α : Type*) [IsEmpty α]
  statement: choice α = none
  proof: choice_eq_none_iff_not_nonempty.mpr (not_nonempty_iff_imp_false.mpr isEmptyElim)

中文:
定理 choice_eq_none
  条件: (α : 类型) [IsEmpty α]
  结论: choice α = none
  证明: choice_eq_none_iff_not_nonempty.mpr (not_nonempty_iff_imp_false.mpr isEmptyElim)

Depends on / 依赖: choice_eq_none_iff_not_nonempty, choice_eq_none_iff_not_nonempty.mpr, isEmptyElim, not_nonempty_iff_imp_false, not_nonempty_iff_imp_false.mpr
-/
theorem choice_eq_none (α : Type*) [IsEmpty α] : choice α = none :=
  choice_eq_none_iff_not_nonempty.mpr (not_nonempty_iff_imp_false.mpr isEmptyElim)

end

@[simp]
/--
theorem `elim_none_some` / 定理 `elim_none_some`

English:
theorem elim_none_some
  given: (f : Option α -> β) (i : Option α)
  statement: i.elim (f none) (f ∘ some) = f i
  proof: by
  cases i <;> rfl

中文:
定理 elim_none_some
  条件: (f : Option α -> β) (i : Option α)
  结论: i.elim (f none) (f ∘ some) = f i
  证明: by
  cases i <;> rfl
-/
theorem elim_none_some (f : Option α -> β) (i : Option α) : i.elim (f none) (f ∘ some) = f i := by
  cases i <;> rfl

/--
theorem `elim_comp` / 定理 `elim_comp`

English:
theorem elim_comp
  given: (h : α -> β) {f : γ -> α} {x : α} {i : Option γ}
  proof: by cases i <;> rfl

中文:
定理 elim_comp
  条件: (h : α -> β) {f : γ -> α} {x : α} {i : Option γ}
  证明: by cases i <;> rfl
-/
theorem elim_comp (h : α -> β) {f : γ -> α} {x : α} {i : Option γ} :
    (i.elim (h x) fun j => h (f j)) = h (i.elim x f) := by cases i <;> rfl

/--
theorem `elim_comp₂` / 定理 `elim_comp₂`

English:
theorem elim_comp₂
  statement: (h : α -> β -> γ) {f : γ -> α} {x : α} {g : γ -> β} {y : β}
  proof: by
  cases i <;> rfl

中文:
定理 elim_comp₂
  结论: (h : α -> β -> γ) {f : γ -> α} {x : α} {g : γ -> β} {y : β}
  证明: by
  cases i <;> rfl
-/
theorem elim_comp₂ (h : α -> β -> γ) {f : γ -> α} {x : α} {g : γ -> β} {y : β}
    {i : Option γ} : (i.elim (h x y) fun j => h (f j) (g j)) = h (i.elim x f) (i.elim y g) := by
  cases i <;> rfl

/--
theorem `elim_apply` / 定理 `elim_apply`

English:
theorem elim_apply
  given: {f : γ -> α -> β} {x : α -> β} {i : Option γ} {y : α}
  proof: by rw [elim_comp fun f : α -> β => f y]

中文:
定理 elim_apply
  条件: {f : γ -> α -> β} {x : α -> β} {i : Option γ} {y : α}
  证明: by rw [elim_comp fun f : α -> β => f y]

Depends on / 依赖: elim_comp
-/
theorem elim_apply {f : γ -> α -> β} {x : α -> β} {i : Option γ} {y : α} :
    i.elim x f y = i.elim (x y) fun j => f j y := by rw [elim_comp fun f : α -> β => f y]

open Function in
@[simp]
/--
lemma `elim'_update` / 引理 `elim'_update`

English:
lemma elim'_update
  statement: {α : Type*} {β : Type*} [DecidableEq α]
  proof: -- Can't reuse `Option.rec_update` as `Option.elim'` is not defeq.
  Function.rec_update (α := fun _ => β) (@Option.some.inj _) (Option.elim' f) (fun _ _ => rfl) (fun
    | _, _, some _, h => (h _ rfl).elim
    | _, _, none, _ => rfl) _ _ _

@[simp]

中文:
引理 elim'_update
  结论: {α : 类型} {β : 类型} [DecidableEq α]
  证明: -- Can't reuse `Option.rec_update` as `Option.elim'` is not defeq.
  Function.rec_update (α := fun _ => β) (@Option.some.inj _) (Option.elim' f) (fun _ _ => rfl) (fun
    | _, _, some _, h => (h _ rfl).elim
    | _, _, none, _ => rfl) _ _ _

@[simp]
-/
lemma elim'_update {α : Type*} {β : Type*} [DecidableEq α]
    (f : β) (g : α -> β) (a : α) (x : β) :
    Option.elim' f (update g a x) = update (Option.elim' f g) (some a) x :=
  -- Can't reuse `Option.rec_update` as `Option.elim'` is not defeq.
  Function.rec_update (α := fun _ => β) (@Option.some.inj _) (Option.elim' f) (fun _ _ => rfl) (fun
    | _, _, some _, h => (h _ rfl).elim
    | _, _, none, _ => rfl) _ _ _

@[simp]
/--
lemma `getD_comp_some` / 引理 `getD_comp_some`

English:
lemma getD_comp_some
  given: (d : α)
  statement: (fun x => x.getD d) ∘ some = id
  proof: by
  ext
  simp only [Function.comp_apply, getD_some, id_eq]

@[simp]

中文:
引理 getD_comp_some
  条件: (d : α)
  结论: (fun x => x.getD d) ∘ some = id
  证明: by
  ext
  simp only [Function.comp_apply, getD_some, id_eq]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, getD_some, id_eq
-/
lemma getD_comp_some (d : α) : (fun x => x.getD d) ∘ some = id := by
  ext
  simp only [Function.comp_apply, getD_some, id_eq]

@[simp]
/--
theorem `none_eq_map_iff` / 定理 `none_eq_map_iff`

English:
theorem none_eq_map_iff
  given: {x : Option α} {f : α -> β}
  statement: none = x.map f ↔ x = none
  proof: by
  rw [eq_comm]; rw [map_eq_none_iff]

@[simp]

中文:
定理 none_eq_map_iff
  条件: {x : Option α} {f : α -> β}
  结论: none = x.map f ↔ x = none
  证明: by
  rw [eq_comm]; rw [map_eq_none_iff]

@[simp]

Depends on / 依赖: eq_comm, map_eq_none_iff
-/
theorem none_eq_map_iff {x : Option α} {f : α -> β} : none = x.map f ↔ x = none := by
  rw [eq_comm]; rw [map_eq_none_iff]

@[simp]
/--
theorem `some_eq_map_iff` / 定理 `some_eq_map_iff`

English:
theorem some_eq_map_iff
  given: {b : β} {x : Option α} {f : α -> β}
  proof: by
  rw [eq_comm]; rw [map_eq_some_iff]

中文:
定理 some_eq_map_iff
  条件: {b : β} {x : Option α} {f : α -> β}
  证明: by
  rw [eq_comm]; rw [map_eq_some_iff]

Depends on / 依赖: eq_comm, map_eq_some_iff
-/
theorem some_eq_map_iff {b : β} {x : Option α} {f : α -> β} :
    some b = x.map f ↔ exists (a : α), x = some a ∧ f a = b := by
  rw [eq_comm]; rw [map_eq_some_iff]

end Option
