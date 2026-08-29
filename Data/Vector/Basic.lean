/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.List.Nodup
public import Mathlib.Control.Applicative
public import Mathlib.Control.Traversable.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Batteries.Data.Fin.Lemmas
public import Mathlib.Data.Fin.SuccPred

/-!
# Additional theorems and definitions about the `Vector` type

This file introduces the infix notation `::ᵥ` for `Vector.cons`.
-/

@[expose] public section

universe u

variable {α β γ σ φ : Type*} {m n : Nat}

namespace List.Vector

@[inherit_doc]
infixr:67 " ::ᵥ " => Vector.cons

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (Vector α n)
  body: ⟨ofFn default⟩

中文:
实例 [可居
  签名: α] : 可居 (Vector α n)
  定义体: ⟨ofFn default⟩
-/
instance [Inhabited α] : Inhabited (Vector α n) :=
  ⟨ofFn default⟩

/--
theorem `toList_injective` / 定理 `toList_injective`

English:
theorem toList_injective
  statement: Function.Injective (@toList α n)
  proof: Subtype.val_injective

中文:
定理 toList_injective
  结论: 函数.单射 (@toList α n)
  证明: Subtype.val_injective

Depends on / 依赖: Subtype, Subtype.val_injective, val_injective
-/
theorem toList_injective : Function.Injective (@toList α n) :=
  Subtype.val_injective

/-- Two `v w : Vector α n` are equal iff they are equal at every single index. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: forall {v w : Vector α n} (_ : forall m : Fin n, Vector.get v m = Vector.get w m), v = w

中文:
定理 ext
  结论: 对任意 {v w : Vector α n} (_ : 对任意 m : 有限集 n, Vector.get v m = Vector.get w m), v = w
-/
theorem ext : forall {v w : Vector α n} (_ : forall m : Fin n, Vector.get v m = Vector.get w m), v = w
  | ⟨v, hv⟩, ⟨w, hw⟩, h =>
    Subtype.ext (List.ext_get (by rw [hv, hw]) fun m hm _ => h ⟨m, hv ▸ hm⟩)

/--
Instance `zero_subsingleton` / 实例 `zero_subsingleton`

English:
instance zero_subsingleton
  signature: : Subsingleton (Vector α 0)
  body: ⟨fun _ _ => Vector.ext fun m => Fin.elim0 m⟩

@[simp]

中文:
实例 zero_subsingleton
  签名: : 子单例 (Vector α 0)
  定义体: ⟨fun _ _ => Vector.ext fun m => Fin.elim0 m⟩

@[simp]

Depends on / 依赖: Fin.elim0, Vector, Vector.ext
-/
instance zero_subsingleton : Subsingleton (Vector α 0) :=
  ⟨fun _ _ => Vector.ext fun m => Fin.elim0 m⟩

@[simp]
/--
theorem `cons_val` / 定理 `cons_val`

English:
theorem cons_val
  given: (a : α)
  statement: forall v : Vector α n, (a ::ᵥ v).val = a :: v.val

中文:
定理 cons_val
  条件: (a : α)
  结论: 对任意 v : Vector α n, (a ::ᵥ v).val = a :: v.val
-/
theorem cons_val (a : α) : forall v : Vector α n, (a ::ᵥ v).val = a :: v.val
  | ⟨_, _⟩ => rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eq_cons_iff` / 定理 `eq_cons_iff`

English:
theorem eq_cons_iff
  given: (a : α) (v : Vector α n.succ) (v' : Vector α n)
  proof: ⟨fun h => h.symm ▸ ⟨head_cons a v', tail_cons a v'⟩, fun h =>
    _root_.trans (cons_head_tail v).symm (by rw [h.1, h.2])⟩

中文:
定理 eq_cons_iff
  条件: (a : α) (v : Vector α n.succ) (v' : Vector α n)
  证明: ⟨fun h => h.symm ▸ ⟨head_cons a v', tail_cons a v'⟩, fun h =>
    _root_.trans (cons_head_tail v).symm (by rw [h.1, h.2])⟩

Depends on / 依赖: _root_, _root_.trans, cons_head_tail, h.symm, head_cons, tail_cons
-/
theorem eq_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v = a ::ᵥ v' ↔ v.head = a ∧ v.tail = v' :=
  ⟨fun h => h.symm ▸ ⟨head_cons a v', tail_cons a v'⟩, fun h =>
    _root_.trans (cons_head_tail v).symm (by rw [h.1, h.2])⟩

/--
theorem `ne_cons_iff` / 定理 `ne_cons_iff`

English:
theorem ne_cons_iff
  given: (a : α) (v : Vector α n.succ) (v' : Vector α n)
  proof: by rw [Ne, eq_cons_iff a v v', not_and_or]

中文:
定理 ne_cons_iff
  条件: (a : α) (v : Vector α n.succ) (v' : Vector α n)
  证明: by rw [Ne, eq_cons_iff a v v', not_and_or]

Depends on / 依赖: eq_cons_iff, not_and_or
-/
theorem ne_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v != a ::ᵥ v' ↔ v.head != a ∨ v.tail != v' := by rw [Ne, eq_cons_iff a v v', not_and_or]

/--
theorem `exists_eq_cons` / 定理 `exists_eq_cons`

English:
theorem exists_eq_cons
  given: (v : Vector α n.succ)
  statement: exists (a : α) (as : Vector α n), v = a ::ᵥ as
  proof: ⟨v.head, v.tail, (eq_cons_iff v.head v v.tail).2 ⟨rfl, rfl⟩⟩

@[simp]

中文:
定理 存在_eq_cons
  条件: (v : Vector α n.succ)
  结论: 存在 (a : α) (as : Vector α n), v = a ::ᵥ as
  证明: ⟨v.head, v.tail, (eq_cons_iff v.head v v.tail).2 ⟨rfl, rfl⟩⟩

@[simp]

Depends on / 依赖: eq_cons_iff, v.head, v.tail
-/
theorem exists_eq_cons (v : Vector α n.succ) : exists (a : α) (as : Vector α n), v = a ::ᵥ as :=
  ⟨v.head, v.tail, (eq_cons_iff v.head v v.tail).2 ⟨rfl, rfl⟩⟩

@[simp]
/--
theorem `toList_ofFn` / 定理 `toList_ofFn`

English:
theorem toList_ofFn
  statement: forall {n} (f : Fin n -> α), toList (ofFn f) = List.ofFn f

中文:
定理 toList_ofFn
  结论: 对任意 {n} (f : 有限集 n -> α), toList (ofFn f) = 列表.ofFn f
-/
theorem toList_ofFn : forall {n} (f : Fin n -> α), toList (ofFn f) = List.ofFn f
  | 0, f => by rw [ofFn, List.ofFn_zero, toList, nil]
  | n + 1, f => by rw [ofFn, List.ofFn_succ, toList_cons, toList_ofFn]

@[simp]
/--
theorem `mk_toList` / 定理 `mk_toList`

English:
theorem mk_toList
  statement: forall (v : Vector α n) (h), (⟨toList v, h⟩ : Vector α n) = v

中文:
定理 mk_toList
  结论: 对任意 (v : Vector α n) (h), (⟨toList v, h⟩ : Vector α n) = v
-/
theorem mk_toList : forall (v : Vector α n) (h), (⟨toList v, h⟩ : Vector α n) = v
  | ⟨_, _⟩, _ => rfl


/--
theorem `length_val` / 定理 `length_val`

English:
theorem length_val
  given: (v : Vector α n)
  statement: v.val.length = n
  proof: v.2

@[simp]

中文:
定理 length_val
  条件: (v : Vector α n)
  结论: v.val.length = n
  证明: v.2

@[simp]
-/
@[simp] theorem length_val (v : Vector α n) : v.val.length = n := v.2

@[simp]
/--
theorem `pmap_cons` / 定理 `pmap_cons`

English:
theorem pmap_cons
  statement: {p : α -> Prop} (f : (a : α) -> p a -> β) (a : α) (v : Vector α n)
  proof: rfl

中文:
定理 pmap_cons
  结论: {p : α -> 命题} (f : (a : α) -> p a -> β) (a : α) (v : Vector α n)
  证明: rfl
-/
theorem pmap_cons {p : α -> Prop} (f : (a : α) -> p a -> β) (a : α) (v : Vector α n)
    (hp : forall x in (cons a v).toList, p x) :
    (cons a v).pmap f hp = cons (f a (by
      simp only [Nat.succ_eq_add_one, toList_cons, List.mem_cons, forall_eq_or_imp] at hp
      exact hp.1))
      (v.pmap f (by
        simp only [Nat.succ_eq_add_one, toList_cons, List.mem_cons, forall_eq_or_imp] at hp
        exact hp.2)) := rfl

/--
theorem `pmap_cons'` / 定理 `pmap_cons'`

English:
theorem pmap_cons'
  statement: {p : α -> Prop} (f : (a : α) -> p a -> β) (a : α) (v : Vector α n)
  proof: rfl

@[simp]

中文:
定理 pmap_cons'
  结论: {p : α -> 命题} (f : (a : α) -> p a -> β) (a : α) (v : Vector α n)
  证明: rfl

@[simp]
-/
theorem pmap_cons' {p : α -> Prop} (f : (a : α) -> p a -> β) (a : α) (v : Vector α n)
    (ha : p a) (hp : forall x in v.toList, p x) :
    cons (f a ha) (v.pmap f hp) = (cons a v).pmap f (by simpa [ha]) := rfl

@[simp]
/--
theorem `toList_map` / 定理 `toList_map`

English:
theorem toList_map
  given: {β : Type*} (v : Vector α n) (f : α -> β)
  proof: by cases v; rfl

@[simp]

中文:
定理 toList_map
  条件: {β : 类型} (v : Vector α n) (f : α -> β)
  证明: by cases v; rfl

@[simp]
-/
theorem toList_map {β : Type*} (v : Vector α n) (f : α -> β) :
    (v.map f).toList = v.toList.map f := by cases v; rfl

@[simp]
/--
theorem `head_map` / 定理 `head_map`

English:
theorem head_map
  given: {β : Type*} (v : Vector α (n + 1)) (f : α -> β)
  statement: (v.map f).head = f v.head
  proof: by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  rw [h]; rw [map_cons]; rw [head_cons]; rw [head_cons]

中文:
定理 head_map
  条件: {β : 类型} (v : Vector α (n + 1)) (f : α -> β)
  结论: (v.map f).head = f v.head
  证明: by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  rw [h]; rw [map_cons]; rw [head_cons]; rw [head_cons]

Depends on / 依赖: Vector, Vector.exists_eq_cons, exists_eq_cons, head_cons, map_cons
-/
theorem head_map {β : Type*} (v : Vector α (n + 1)) (f : α -> β) : (v.map f).head = f v.head := by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  rw [h]; rw [map_cons]; rw [head_cons]; rw [head_cons]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `tail_map` / 定理 `tail_map`

English:
theorem tail_map
  given: {β : Type*} (v : Vector α (n + 1)) (f : α -> β)
  proof: by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  rw [h]; rw [map_cons]; rw [tail_cons]; rw [tail_cons]

@[simp]

中文:
定理 tail_map
  条件: {β : 类型} (v : Vector α (n + 1)) (f : α -> β)
  证明: by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  rw [h]; rw [map_cons]; rw [tail_cons]; rw [tail_cons]

@[simp]

Depends on / 依赖: Vector, Vector.exists_eq_cons, exists_eq_cons, map_cons, tail_cons
-/
theorem tail_map {β : Type*} (v : Vector α (n + 1)) (f : α -> β) :
    (v.map f).tail = v.tail.map f := by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  rw [h]; rw [map_cons]; rw [tail_cons]; rw [tail_cons]

@[simp]
/--
theorem `getElem_map` / 定理 `getElem_map`

English:
theorem getElem_map
  given: {β : Type*} (v : Vector α n) (f : α -> β) {i : Nat} (hi : i < n)
  proof: by
  simp only [getElem_def, toList_map, List.getElem_map]

@[simp]

中文:
定理 getElem_map
  条件: {β : 类型} (v : Vector α n) (f : α -> β) {i : 自然数} (hi : i < n)
  证明: by
  simp only [getElem_def, toList_map, List.getElem_map]

@[simp]

Depends on / 依赖: List.getElem_map, getElem_def, getElem_map, toList_map
-/
theorem getElem_map {β : Type*} (v : Vector α n) (f : α -> β) {i : Nat} (hi : i < n) :
    (v.map f)[i] = f v[i] := by
  simp only [getElem_def, toList_map, List.getElem_map]

@[simp]
/--
theorem `toList_pmap` / 定理 `toList_pmap`

English:
theorem toList_pmap
  statement: {p : α -> Prop} (f : (a : α) -> p a -> β) (v : Vector α n)
  proof: by cases v; rfl

中文:
定理 toList_pmap
  结论: {p : α -> 命题} (f : (a : α) -> p a -> β) (v : Vector α n)
  证明: by cases v; rfl
-/
theorem toList_pmap {p : α -> Prop} (f : (a : α) -> p a -> β) (v : Vector α n)
    (hp : forall x in v.toList, p x) :
    (v.pmap f hp).toList = v.toList.pmap f hp := by cases v; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `head_pmap` / 定理 `head_pmap`

English:
theorem head_pmap
  statement: {p : α -> Prop} (f : (a : α) -> p a -> β) (v : Vector α (n + 1))
  proof: by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  simp_rw [h, pmap_cons, head_cons]

中文:
定理 head_pmap
  结论: {p : α -> 命题} (f : (a : α) -> p a -> β) (v : Vector α (n + 1))
  证明: by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  simp_rw [h, pmap_cons, head_cons]

Depends on / 依赖: Vector, Vector.exists_eq_cons, exists_eq_cons, head_cons, pmap_cons, simp_rw
-/
theorem head_pmap {p : α -> Prop} (f : (a : α) -> p a -> β) (v : Vector α (n + 1))
    (hp : forall x in v.toList, p x) :
    (v.pmap f hp).head = f v.head (hp _ <| by
      rw [← cons_head_tail v]; rw [toList_cons]; rw [head_cons]; rw [List.mem_cons]; exact .inl rfl) := by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  simp_rw [h, pmap_cons, head_cons]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `tail_pmap` / 定理 `tail_pmap`

English:
theorem tail_pmap
  statement: {p : α -> Prop} (f : (a : α) -> p a -> β) (v : Vector α (n + 1))
  proof: by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  simp_rw [h, pmap_cons, tail_cons]

@[simp]

中文:
定理 tail_pmap
  结论: {p : α -> 命题} (f : (a : α) -> p a -> β) (v : Vector α (n + 1))
  证明: by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  simp_rw [h, pmap_cons, tail_cons]

@[simp]

Depends on / 依赖: Vector, Vector.exists_eq_cons, exists_eq_cons, pmap_cons, simp_rw, tail_cons
-/
theorem tail_pmap {p : α -> Prop} (f : (a : α) -> p a -> β) (v : Vector α (n + 1))
    (hp : forall x in v.toList, p x) :
    (v.pmap f hp).tail = v.tail.pmap f (fun x hx => hp _ <| by
      rw [← cons_head_tail v]; rw [toList_cons]; rw [List.mem_cons]; exact .inr hx) := by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  simp_rw [h, pmap_cons, tail_cons]

@[simp]
/--
theorem `getElem_pmap` / 定理 `getElem_pmap`

English:
theorem getElem_pmap
  statement: {p : α -> Prop} (f : (a : α) -> p a -> β) (v : Vector α n)
  proof: by
  simp only [getElem_def, toList_pmap, List.getElem_pmap]

中文:
定理 getElem_pmap
  结论: {p : α -> 命题} (f : (a : α) -> p a -> β) (v : Vector α n)
  证明: by
  simp only [getElem_def, toList_pmap, List.getElem_pmap]

Depends on / 依赖: List.getElem_pmap, getElem_def, getElem_pmap, toList_pmap
-/
theorem getElem_pmap {p : α -> Prop} (f : (a : α) -> p a -> β) (v : Vector α n)
    (hp : forall x in v.toList, p x) {i : Nat} (hi : i < n) :
    (v.pmap f hp)[i] = f v[i] (hp _ (by simp [getElem_def, List.getElem_mem])) := by
  simp only [getElem_def, toList_pmap, List.getElem_pmap]

/--
theorem `get_eq_get_toList` / 定理 `get_eq_get_toList`

English:
theorem get_eq_get_toList
  given: (v : Vector α n) (i : Fin n)
  proof: rfl

@[simp]

中文:
定理 get_eq_get_toList
  条件: (v : Vector α n) (i : 有限集 n)
  证明: rfl

@[simp]
-/
theorem get_eq_get_toList (v : Vector α n) (i : Fin n) :
    v.get i = v.toList.get (Fin.cast v.toList_length.symm i) :=
  rfl

@[simp]
/--
theorem `get_replicate` / 定理 `get_replicate`

English:
theorem get_replicate
  given: (a : α) (i : Fin n)
  statement: (Vector.replicate n a).get i = a
  proof: by
  apply List.getElem_replicate

中文:
定理 get_replicate
  条件: (a : α) (i : 有限集 n)
  结论: (Vector.replicate n a).get i = a
  证明: by
  apply List.getElem_replicate

Depends on / 依赖: List.getElem_replicate, getElem_replicate
-/
theorem get_replicate (a : α) (i : Fin n) : (Vector.replicate n a).get i = a := by
  apply List.getElem_replicate

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `get_map` / 定理 `get_map`

English:
theorem get_map
  given: {β : Type*} (v : Vector α n) (f : α -> β) (i : Fin n)
  proof: by
  cases v; simp [Vector.map, get_eq_get_toList]

@[simp]

中文:
定理 get_map
  条件: {β : 类型} (v : Vector α n) (f : α -> β) (i : 有限集 n)
  证明: by
  cases v; simp [Vector.map, get_eq_get_toList]

@[simp]

Depends on / 依赖: Vector, Vector.map, get_eq_get_toList
-/
theorem get_map {β : Type*} (v : Vector α n) (f : α -> β) (i : Fin n) :
    (v.map f).get i = f (v.get i) := by
  cases v; simp [Vector.map, get_eq_get_toList]

@[simp]
/--
theorem `map₂_nil` / 定理 `map₂_nil`

English:
theorem map₂_nil
  given: (f : α -> β -> γ)
  statement: Vector.map₂ f nil nil = nil
  proof: rfl

@[simp]

中文:
定理 map₂_nil
  条件: (f : α -> β -> γ)
  结论: Vector.map₂ f nil nil = nil
  证明: rfl

@[simp]
-/
theorem map₂_nil (f : α -> β -> γ) : Vector.map₂ f nil nil = nil :=
  rfl

@[simp]
/--
theorem `map₂_cons` / 定理 `map₂_cons`

English:
theorem map₂_cons
  given: (hd₁ : α) (tl₁ : Vector α n) (hd₂ : β) (tl₂ : Vector β n) (f : α -> β -> γ)
  proof: rfl

@[simp]

中文:
定理 map₂_cons
  条件: (hd₁ : α) (tl₁ : Vector α n) (hd₂ : β) (tl₂ : Vector β n) (f : α -> β -> γ)
  证明: rfl

@[simp]
-/
theorem map₂_cons (hd₁ : α) (tl₁ : Vector α n) (hd₂ : β) (tl₂ : Vector β n) (f : α -> β -> γ) :
    Vector.map₂ f (hd₁ ::ᵥ tl₁) (hd₂ ::ᵥ tl₂) = f hd₁ hd₂ ::ᵥ (Vector.map₂ f tl₁ tl₂) :=
  rfl

@[simp]
/--
theorem `get_ofFn` / 定理 `get_ofFn`

English:
theorem get_ofFn
  given: {n} (f : Fin n -> α) (i)
  statement: get (ofFn f) i = f i
  proof: by
  simp [get_eq_get_toList]

@[simp]

中文:
定理 get_ofFn
  条件: {n} (f : 有限集 n -> α) (i)
  结论: get (ofFn f) i = f i
  证明: by
  simp [get_eq_get_toList]

@[simp]

Depends on / 依赖: get_eq_get_toList
-/
theorem get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i = f i := by
  simp [get_eq_get_toList]

@[simp]
/--
theorem `ofFn_get` / 定理 `ofFn_get`

English:
theorem ofFn_get
  given: (v : Vector α n)
  statement: ofFn (get v) = v
  proof: by
  ext
  apply List.Vector.get_ofFn

中文:
定理 ofFn_get
  条件: (v : Vector α n)
  结论: ofFn (get v) = v
  证明: by
  ext
  apply List.Vector.get_ofFn

Depends on / 依赖: List.Vector.get_ofFn, Vector, get_ofFn
-/
theorem ofFn_get (v : Vector α n) : ofFn (get v) = v := by
  ext
  apply List.Vector.get_ofFn

/--
Definition of `_root_.Equiv.vectorEquivFin` / `_root_.Equiv.vectorEquivFin` 的定义

English:
definition _root_.Equiv.vectorEquivFin
  signature: (α : Type*) (n : Nat)
  body: ⟨Vector.get, Vector.ofFn, Vector.ofFn_get, fun f => funext Vector.get_ofFn f⟩

中文:
定义 _root_.等价.vectorEquivFin
  签名: (α : 类型) (n : 自然数)
  定义体: ⟨Vector.get, Vector.ofFn, Vector.ofFn_get, fun f => funext Vector.get_ofFn f⟩

Depends on / 依赖: Vector, Vector.get, Vector.get_ofFn, Vector.ofFn, Vector.ofFn_get, get_ofFn, ofFn_get
-/
def _root_.Equiv.vectorEquivFin (α : Type*) (n : Nat) : Vector α n ≃ (Fin n -> α) :=
⟨Vector.get, Vector.ofFn, Vector.ofFn_get, fun f => funext Vector.get_ofFn f⟩

/--
theorem `get_tail` / 定理 `get_tail`

English:
theorem get_tail
  given: (x : Vector α n) (i)
  statement: x.tail.get i = x.get ⟨i.1 + 1, by lia⟩
  proof: by
  obtain ⟨i, ih⟩ := i; dsimp
  rcases x with ⟨_ | _, h⟩ <;> try rfl
  rw [List.length] at h
  rw [← h] at ih
  contradiction

@[simp]

中文:
定理 get_tail
  条件: (x : Vector α n) (i)
  结论: x.tail.get i = x.get ⟨i.1 + 1, by lia⟩
  证明: by
  obtain ⟨i, ih⟩ := i; dsimp
  rcases x with ⟨_ | _, h⟩ <;> try rfl
  rw [List.length] at h
  rw [← h] at ih
  contradiction

@[simp]

Depends on / 依赖: List.length, length
-/
theorem get_tail (x : Vector α n) (i) : x.tail.get i = x.get ⟨i.1 + 1, by lia⟩ := by
  obtain ⟨i, ih⟩ := i; dsimp
  rcases x with ⟨_ | _, h⟩ <;> try rfl
  rw [List.length] at h
  rw [← h] at ih
  contradiction

@[simp]
/--
theorem `get_tail_succ` / 定理 `get_tail_succ`

English:
theorem get_tail_succ
  statement: forall (v : Vector α n.succ) (i : Fin n), get (tail v) i = get v i.succ

中文:
定理 get_tail_succ
  结论: 对任意 (v : Vector α n.succ) (i : 有限集 n), get (tail v) i = get v i.succ
-/
theorem get_tail_succ : forall (v : Vector α n.succ) (i : Fin n), get (tail v) i = get v i.succ
  | ⟨a :: l, e⟩, ⟨i, h⟩ => by simp [get_eq_get_toList]; rfl

@[simp]
/--
theorem `tail_val` / 定理 `tail_val`

English:
theorem tail_val
  statement: forall v : Vector α n.succ, v.tail.val = v.val.tail

中文:
定理 tail_val
  结论: 对任意 v : Vector α n.succ, v.tail.val = v.val.tail
-/
theorem tail_val : forall v : Vector α n.succ, v.tail.val = v.val.tail
  | ⟨_ :: _, _⟩ => rfl

/-- The `tail` of a `nil` vector is `nil`. -/
@[simp]
/--
theorem `tail_nil` / 定理 `tail_nil`

English:
theorem tail_nil
  statement: (@nil α).tail = nil
  proof: rfl

中文:
定理 tail_nil
  结论: (@nil α).tail = nil
  证明: rfl
-/
theorem tail_nil : (@nil α).tail = nil :=
  rfl

/-- The `tail` of a vector made up of one element is `nil`. -/
@[simp]
/--
theorem `singleton_tail` / 定理 `singleton_tail`

English:
theorem singleton_tail
  statement: forall (v : Vector α 1), v.tail = Vector.nil

中文:
定理 singleton_tail
  结论: 对任意 (v : Vector α 1), v.tail = Vector.nil
-/
theorem singleton_tail : forall (v : Vector α 1), v.tail = Vector.nil
  | ⟨[_], _⟩ => rfl

@[simp]
/--
theorem `tail_ofFn` / 定理 `tail_ofFn`

English:
theorem tail_ofFn
  given: {n : Nat} (f : Fin n.succ -> α)
  statement: tail (ofFn f) = ofFn fun i => f i.succ
  proof: (ofFn_get _).symm.trans by
    congr
    funext i
    rw [get_tail]; rw [get_ofFn]
    rfl

中文:
定理 tail_ofFn
  条件: {n : 自然数} (f : 有限集 n.succ -> α)
  结论: tail (ofFn f) = ofFn fun i => f i.succ
  证明: (ofFn_get _).symm.trans by
    congr
    funext i
    rw [get_tail]; rw [get_ofFn]
    rfl

Depends on / 依赖: get_ofFn, get_tail, ofFn_get, symm.trans
-/
theorem tail_ofFn {n : Nat} (f : Fin n.succ -> α) : tail (ofFn f) = ofFn fun i => f i.succ :=
(ofFn_get _).symm.trans by
    congr
    funext i
    rw [get_tail]; rw [get_ofFn]
    rfl

/--
theorem `toList_tail` / 定理 `toList_tail`

English:
theorem toList_tail
  statement: forall (v : Vector α n), v.tail.toList = v.toList.tail

中文:
定理 toList_tail
  结论: 对任意 (v : Vector α n), v.tail.toList = v.toList.tail
-/
theorem toList_tail : forall (v : Vector α n), v.tail.toList = v.toList.tail
  | ⟨[], _⟩ => by rfl
  | ⟨_ :: _, _⟩ => by rfl

@[simp]
/--
theorem `toList_empty` / 定理 `toList_empty`

English:
theorem toList_empty
  given: (v : Vector α 0)
  statement: v.toList = []
  proof: List.length_eq_zero_iff.mp v.2

中文:
定理 toList_empty
  条件: (v : Vector α 0)
  结论: v.toList = []
  证明: List.length_eq_zero_iff.mp v.2

Depends on / 依赖: List.length_eq_zero_iff.mp, length_eq_zero_iff
-/
theorem toList_empty (v : Vector α 0) : v.toList = [] :=
  List.length_eq_zero_iff.mp v.2

/-- The list that makes up a `Vector` made up of a single element,
retrieved via `toList`, is equal to the list of that single element. -/
@[simp]
/--
theorem `toList_singleton` / 定理 `toList_singleton`

English:
theorem toList_singleton
  given: (v : Vector α 1)
  statement: v.toList = [v.head]
  proof: by
  rw [← v.cons_head_tail]
  simp only [toList_cons, toList_nil, head_cons, singleton_tail]

@[simp]

中文:
定理 toList_singleton
  条件: (v : Vector α 1)
  结论: v.toList = [v.head]
  证明: by
  rw [← v.cons_head_tail]
  simp only [toList_cons, toList_nil, head_cons, singleton_tail]

@[simp]

Depends on / 依赖: cons_head_tail, head_cons, singleton_tail, toList_cons, toList_nil, v.cons_head_tail
-/
theorem toList_singleton (v : Vector α 1) : v.toList = [v.head] := by
  rw [← v.cons_head_tail]
  simp only [toList_cons, toList_nil, head_cons, singleton_tail]

@[simp]
/--
theorem `empty_toList_eq_ff` / 定理 `empty_toList_eq_ff`

English:
theorem empty_toList_eq_ff
  given: (v : Vector α (n + 1))
  statement: v.toList.isEmpty = false
  proof: match v with
  | ⟨_ :: _, _⟩ => rfl

中文:
定理 empty_toList_eq_ff
  条件: (v : Vector α (n + 1))
  结论: v.toList.isEmpty = false
  证明: match v with
  | ⟨_ :: _, _⟩ => rfl
-/
theorem empty_toList_eq_ff (v : Vector α (n + 1)) : v.toList.isEmpty = false :=
  match v with
  | ⟨_ :: _, _⟩ => rfl

/--
theorem `not_empty_toList` / 定理 `not_empty_toList`

English:
theorem not_empty_toList
  given: (v : Vector α (n + 1))
  statement: ¬v.toList.isEmpty
  proof: by
  simp only [empty_toList_eq_ff, Bool.coe_sort_false, not_false_iff]

中文:
定理 not_empty_toList
  条件: (v : Vector α (n + 1))
  结论: ¬v.toList.isEmpty
  证明: by
  simp only [empty_toList_eq_ff, Bool.coe_sort_false, not_false_iff]

Depends on / 依赖: Bool.coe_sort_false, coe_sort_false, empty_toList_eq_ff, not_false_iff
-/
theorem not_empty_toList (v : Vector α (n + 1)) : ¬v.toList.isEmpty := by
  simp only [empty_toList_eq_ff, Bool.coe_sort_false, not_false_iff]

/-- Mapping under `id` does not change a vector. -/
@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: {n : Nat} (v : Vector α n)
  statement: Vector.map id v = v
  proof: Vector.eq _ _ (by simp only [List.map_id, Vector.toList_map])

中文:
定理 map_id
  条件: {n : 自然数} (v : Vector α n)
  结论: Vector.map id v = v
  证明: Vector.eq _ _ (by simp only [List.map_id, Vector.toList_map])

Depends on / 依赖: List.map_id, Vector, Vector.eq, Vector.toList_map, map_id, toList_map
-/
theorem map_id {n : Nat} (v : Vector α n) : Vector.map id v = v :=
  Vector.eq _ _ (by simp only [List.map_id, Vector.toList_map])

/--
theorem `nodup_iff_injective_get` / 定理 `nodup_iff_injective_get`

English:
theorem nodup_iff_injective_get
  given: {v : Vector α n}
  statement: v.toList.Nodup ↔ Function.Injective v.get
  proof: by
  obtain ⟨l, rfl⟩ := v
  exact List.nodup_iff_injective_get

中文:
定理 nodup_iff_injective_get
  条件: {v : Vector α n}
  结论: v.toList.Nodup ↔ 函数.单射 v.get
  证明: by
  obtain ⟨l, rfl⟩ := v
  exact List.nodup_iff_injective_get

Depends on / 依赖: List.nodup_iff_injective_get, nodup_iff_injective_get
-/
theorem nodup_iff_injective_get {v : Vector α n} : v.toList.Nodup ↔ Function.Injective v.get := by
  obtain ⟨l, rfl⟩ := v
  exact List.nodup_iff_injective_get

/--
theorem `head?_toList` / 定理 `head?_toList`

English:
theorem head?_toList
  statement: forall v : Vector α n.succ, (toList v).head? = some (head v)

中文:
定理 head?_toList
  结论: 对任意 v : Vector α n.succ, (toList v).head? = some (head v)
-/
theorem head?_toList : forall v : Vector α n.succ, (toList v).head? = some (head v)
  | ⟨_ :: _, _⟩ => rfl

/--
Definition of `reverse` / `reverse` 的定义

English:
definition reverse
  signature: (v : Vector α n)
  body: ⟨v.toList.reverse, by simp⟩

中文:
定义 reverse
  签名: (v : Vector α n)
  定义体: ⟨v.toList.reverse, by simp⟩

Depends on / 依赖: reverse, toList, v.toList.reverse
-/
def reverse (v : Vector α n) : Vector α n :=
  ⟨v.toList.reverse, by simp⟩

/--
theorem `toList_reverse` / 定理 `toList_reverse`

English:
theorem toList_reverse
  given: {v : Vector α n}
  statement: v.reverse.toList = v.toList.reverse
  proof: rfl

中文:
定理 toList_reverse
  条件: {v : Vector α n}
  结论: v.reverse.toList = v.toList.reverse
  证明: rfl
-/
theorem toList_reverse {v : Vector α n} : v.reverse.toList = v.toList.reverse :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `reverse_reverse` / 定理 `reverse_reverse`

English:
theorem reverse_reverse
  given: {v : Vector α n}
  statement: v.reverse.reverse = v
  proof: by
  cases v
  simp [Vector.reverse]

@[simp]

中文:
定理 reverse_reverse
  条件: {v : Vector α n}
  结论: v.reverse.reverse = v
  证明: by
  cases v
  simp [Vector.reverse]

@[simp]

Depends on / 依赖: Vector, Vector.reverse, reverse
-/
theorem reverse_reverse {v : Vector α n} : v.reverse.reverse = v := by
  cases v
  simp [Vector.reverse]

@[simp]
/--
theorem `get_zero` / 定理 `get_zero`

English:
theorem get_zero
  statement: forall v : Vector α n.succ, get v 0 = head v

中文:
定理 get_zero
  结论: 对任意 v : Vector α n.succ, get v 0 = head v
-/
theorem get_zero : forall v : Vector α n.succ, get v 0 = head v
  | ⟨_ :: _, _⟩ => rfl

@[simp]
/--
theorem `head_ofFn` / 定理 `head_ofFn`

English:
theorem head_ofFn
  given: {n : Nat} (f : Fin n.succ -> α)
  statement: head (ofFn f) = f 0
  proof: by
  rw [← get_zero]; rw [get_ofFn]

中文:
定理 head_ofFn
  条件: {n : 自然数} (f : 有限集 n.succ -> α)
  结论: head (ofFn f) = f 0
  证明: by
  rw [← get_zero]; rw [get_ofFn]

Depends on / 依赖: get_ofFn, get_zero
-/
theorem head_ofFn {n : Nat} (f : Fin n.succ -> α) : head (ofFn f) = f 0 := by
  rw [← get_zero]; rw [get_ofFn]

/--
theorem `get_cons_zero` / 定理 `get_cons_zero`

English:
theorem get_cons_zero
  given: (a : α) (v : Vector α n)
  statement: get (a ::ᵥ v) 0 = a
  proof: by simp [get_zero]

中文:
定理 get_cons_zero
  条件: (a : α) (v : Vector α n)
  结论: get (a ::ᵥ v) 0 = a
  证明: by simp [get_zero]

Depends on / 依赖: get_zero
-/
theorem get_cons_zero (a : α) (v : Vector α n) : get (a ::ᵥ v) 0 = a := by simp [get_zero]

/-- Accessing the nth element of a vector made up
of one element `x : α` is `x` itself. -/
@[simp]
/--
theorem `get_cons_nil` / 定理 `get_cons_nil`

English:
theorem get_cons_nil
  statement: forall {ix : Fin 1} (x : α), get (x ::ᵥ nil) ix = x

中文:
定理 get_cons_nil
  结论: 对任意 {ix : 有限集 1} (x : α), get (x ::ᵥ nil) ix = x
-/
theorem get_cons_nil : forall {ix : Fin 1} (x : α), get (x ::ᵥ nil) ix = x
  | ⟨0, _⟩, _ => rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `get_cons_succ` / 定理 `get_cons_succ`

English:
theorem get_cons_succ
  given: (a : α) (v : Vector α n) (i : Fin n)
  statement: get (a ::ᵥ v) i.succ = get v i
  proof: by
  rw [← get_tail_succ]; rw [tail_cons]

中文:
定理 get_cons_succ
  条件: (a : α) (v : Vector α n) (i : 有限集 n)
  结论: get (a ::ᵥ v) i.succ = get v i
  证明: by
  rw [← get_tail_succ]; rw [tail_cons]

Depends on / 依赖: get_tail_succ, tail_cons
-/
theorem get_cons_succ (a : α) (v : Vector α n) (i : Fin n) : get (a ::ᵥ v) i.succ = get v i := by
  rw [← get_tail_succ]; rw [tail_cons]

/--
Definition of `last` / `last` 的定义

English:
definition last
  signature: (v : Vector α (n + 1))
  body: v.get (Fin.last n)

中文:
定义 last
  签名: (v : Vector α (n + 1))
  定义体: v.get (Fin.last n)

Depends on / 依赖: Fin.last, v.get
-/
def last (v : Vector α (n + 1)) : α :=
  v.get (Fin.last n)

/--
theorem `last_def` / 定理 `last_def`

English:
theorem last_def
  given: {v : Vector α (n + 1)}
  statement: v.last = v.get (Fin.last n)
  proof: rfl

中文:
定理 last_def
  条件: {v : Vector α (n + 1)}
  结论: v.last = v.get (有限集.last n)
  证明: rfl
-/
theorem last_def {v : Vector α (n + 1)} : v.last = v.get (Fin.last n) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `reverse_get_zero` / 定理 `reverse_get_zero`

English:
theorem reverse_get_zero
  given: {v : Vector α (n + 1)}
  statement: v.reverse.head = v.last
  proof: by
  rw [← get_zero]; rw [last_def]; rw [get_eq_get_toList]; rw [get_eq_get_toList]
  simp_rw [toList_reverse]
  simp

中文:
定理 reverse_get_zero
  条件: {v : Vector α (n + 1)}
  结论: v.reverse.head = v.last
  证明: by
  rw [← get_zero]; rw [last_def]; rw [get_eq_get_toList]; rw [get_eq_get_toList]
  simp_rw [toList_reverse]
  simp

Depends on / 依赖: get_eq_get_toList, get_zero, last_def, simp_rw, toList_reverse
-/
theorem reverse_get_zero {v : Vector α (n + 1)} : v.reverse.head = v.last := by
  rw [← get_zero]; rw [last_def]; rw [get_eq_get_toList]; rw [get_eq_get_toList]
  simp_rw [toList_reverse]
  simp

section Scan

variable {β : Type*}
variable (f : β -> α -> β) (b : β)
variable (v : Vector α n)

/--
Definition of `scanl` / `scanl` 的定义

English:
definition scanl
  signature: : Vector β (n + 1)
  body: ⟨List.scanl f b v.toList, by rw [List.length_scanl, toList_length]⟩

中文:
定义 scanl
  签名: : Vector β (n + 1)
  定义体: ⟨List.scanl f b v.toList, by rw [List.length_scanl, toList_length]⟩

Depends on / 依赖: List.length_scanl, List.scanl, length_scanl, toList, toList_length, v.toList
-/
def scanl : Vector β (n + 1) :=
  ⟨List.scanl f b v.toList, by rw [List.length_scanl, toList_length]⟩

/-- Providing an empty vector to `scanl` gives the starting value `b : β`. -/
@[simp]
/--
theorem `scanl_nil` / 定理 `scanl_nil`

English:
theorem scanl_nil
  statement: scanl f b nil = b ::ᵥ nil
  proof: by
  ext; simp [scanl, get]

中文:
定理 scanl_nil
  结论: scanl f b nil = b ::ᵥ nil
  证明: by
  ext; simp [scanl, get]
-/
theorem scanl_nil : scanl f b nil = b ::ᵥ nil := by
  ext; simp [scanl, get]

set_option backward.isDefEq.respectTransparency false in
/-- The recursive step of `scanl` splits a vector `x ::ᵥ v : Vector α (n + 1)`
into the provided starting value `b : β` and the recursed `scanl`
`f b x : β` as the starting value.

This lemma is the `cons` version of `scanl_get`.
-/
@[simp]
/--
theorem `scanl_cons` / 定理 `scanl_cons`

English:
theorem scanl_cons
  given: (x : α)
  statement: scanl f b (x ::ᵥ v) = b ::ᵥ scanl f (f b x) v
  proof: by
  apply Vector.eq; simp [scanl]

中文:
定理 scanl_cons
  条件: (x : α)
  结论: scanl f b (x ::ᵥ v) = b ::ᵥ scanl f (f b x) v
  证明: by
  apply Vector.eq; simp [scanl]

Depends on / 依赖: Vector, Vector.eq
-/
theorem scanl_cons (x : α) : scanl f b (x ::ᵥ v) = b ::ᵥ scanl f (f b x) v := by
  apply Vector.eq; simp [scanl]

/-- The underlying `List` of a `Vector` after a `scanl` is the `List.scanl`
of the underlying `List` of the original `Vector`.
-/
@[simp]
/--
theorem `scanl_val` / 定理 `scanl_val`

English:
theorem scanl_val
  statement: forall {v : Vector α n}, (scanl f b v).val = List.scanl f b v.val

中文:
定理 scanl_val
  结论: 对任意 {v : Vector α n}, (scanl f b v).val = 列表.scanl f b v.val
-/
theorem scanl_val : forall {v : Vector α n}, (scanl f b v).val = List.scanl f b v.val
  | _ => rfl

/-- The `toList` of a `Vector` after a `scanl` is the `List.scanl`
of the `toList` of the original `Vector`.
-/
@[simp]
/--
theorem `toList_scanl` / 定理 `toList_scanl`

English:
theorem toList_scanl
  statement: (scanl f b v).toList = List.scanl f b v.toList
  proof: rfl

中文:
定理 toList_scanl
  结论: (scanl f b v).toList = 列表.scanl f b v.toList
  证明: rfl
-/
theorem toList_scanl : (scanl f b v).toList = List.scanl f b v.toList :=
  rfl

/-- The recursive step of `scanl` splits a vector made up of a single element
`x ::ᵥ nil : Vector α 1` into a `Vector` of the provided starting value `b : β`
and the mapped `f b x : β` as the last value.
-/
@[simp]
/--
theorem `scanl_singleton` / 定理 `scanl_singleton`

English:
theorem scanl_singleton
  given: (v : Vector α 1)
  statement: scanl f b v = b ::ᵥ f b v.head ::ᵥ nil
  proof: by
  rw [← cons_head_tail v]
  simp only [scanl_cons, scanl_nil, head_cons, singleton_tail]

中文:
定理 scanl_singleton
  条件: (v : Vector α 1)
  结论: scanl f b v = b ::ᵥ f b v.head ::ᵥ nil
  证明: by
  rw [← cons_head_tail v]
  simp only [scanl_cons, scanl_nil, head_cons, singleton_tail]

Depends on / 依赖: cons_head_tail, head_cons, scanl_cons, scanl_nil, singleton_tail
-/
theorem scanl_singleton (v : Vector α 1) : scanl f b v = b ::ᵥ f b v.head ::ᵥ nil := by
  rw [← cons_head_tail v]
  simp only [scanl_cons, scanl_nil, head_cons, singleton_tail]

/-- The first element of `scanl` of a vector `v : Vector α n`,
retrieved via `head`, is the starting value `b : β`.
-/
@[simp]
/--
theorem `scanl_head` / 定理 `scanl_head`

English:
theorem scanl_head
  statement: (scanl f b v).head = b
  proof: by
  cases n
  · have : v = nil := by simp only [eq_iff_true_of_subsingleton]
    simp only [this, scanl_nil, head_cons]
  · rw [← cons_head_tail v]
    simp [← get_zero, get_eq_get_toList]

中文:
定理 scanl_head
  结论: (scanl f b v).head = b
  证明: by
  cases n
  · have : v = nil := by simp only [eq_iff_true_of_subsingleton]
    simp only [this, scanl_nil, head_cons]
  · rw [← cons_head_tail v]
    simp [← get_zero, get_eq_get_toList]

Depends on / 依赖: cons_head_tail, eq_iff_true_of_subsingleton, get_eq_get_toList, get_zero, head_cons, scanl_nil
-/
theorem scanl_head : (scanl f b v).head = b := by
  cases n
  · have : v = nil := by simp only [eq_iff_true_of_subsingleton]
    simp only [this, scanl_nil, head_cons]
  · rw [← cons_head_tail v]
    simp [← get_zero, get_eq_get_toList]

set_option backward.isDefEq.respectTransparency false in
/-- For an index `i : Fin n`, the nth element of `scanl` of a
vector `v : Vector α n` at `i.succ`, is equal to the application
function `f : β → α → β` of the `castSucc i` element of
`scanl f b v` and `get v i`.

This lemma is the `get` version of `scanl_cons`.
-/
@[simp]
/--
theorem `scanl_get` / 定理 `scanl_get`

English:
theorem scanl_get
  given: (i : Fin n)
  proof: by
  rcases n with - | n
  · exact i.elim0
  induction n generalizing b with
  | zero =>
    have i0 : i = 0 := Fin.eq_zero _
    simp [scanl_singleton, i0, get_zero]; simp [get_eq_get_toList]
  | succ n hn =>
    rw [← cons_head_tail v]; rw [scanl_cons]; rw [get_cons_succ]
    refine Fin.cases ?_ ?

中文:
定理 scanl_get
  条件: (i : 有限集 n)
  证明: by
  rcases n with - | n
  · exact i.elim0
  induction n generalizing b with
  | zero =>
    have i0 : i = 0 := Fin.eq_zero _
    simp [scanl_singleton, i0, get_zero]; simp [get_eq_get_toList]
  | succ n hn =>
    rw [← cons_head_tail v]; rw [scanl_cons]; rw [get_cons_succ]
    refine Fin.cases ?_ ?

Depends on / 依赖: Fin.cases, Fin.castSucc_succ, Fin.eq_zero, castSucc_succ, cons_head_tail, eq_zero, generalizing, get_cons_succ, get_eq_get_toList, get_zero, i.elim0, scanl_cons, scanl_singleton
-/
theorem scanl_get (i : Fin n) :
    (scanl f b v).get i.succ = f ((scanl f b v).get (Fin.castSucc i)) (v.get i) := by
  rcases n with - | n
  · exact i.elim0
  induction n generalizing b with
  | zero =>
    have i0 : i = 0 := Fin.eq_zero _
    simp [scanl_singleton, i0, get_zero]; simp [get_eq_get_toList]
  | succ n hn =>
    rw [← cons_head_tail v]; rw [scanl_cons]; rw [get_cons_succ]
    refine Fin.cases ?_ ?_ i
    · simp
    · intro i'
      simp only [hn, Fin.castSucc_succ, get_cons_succ]

end Scan

/--
Definition of `mOfFn` / `mOfFn` 的定义

English:
definition mOfFn
  signature: {m} [Monad m] {α : Type u}

中文:
定义 mOfFn
  签名: {m} [单子 m] {α : 类型u}
-/
def mOfFn {m} [Monad m] {α : Type u} : forall {n}, (Fin n -> m α) -> m (Vector α n)
  | 0, _ => pure nil
  | _ + 1, f => do
    let a ← f 0
    let v ← mOfFn fun i => f i.succ
    pure (a ::ᵥ v)

/--
theorem `mOfFn_pure` / 定理 `mOfFn_pure`

English:
theorem mOfFn_pure
  given: {m} [Monad m] [LawfulMonad m] {α}

中文:
定理 mOfFn_pure
  条件: {m} [单子 m] [合法单子 m] {α}
-/
theorem mOfFn_pure {m} [Monad m] [LawfulMonad m] {α} :
    forall {n} (f : Fin n -> α), (@mOfFn m _ _ _ fun i => pure (f i)) = pure (ofFn f)
  | 0, _ => rfl
  | n + 1, f => by
    rw [mOfFn]; rw [@mOfFn_pure m _ _ _ n _]; rw [ofFn]
    simp

/--
Definition of `mmap` / `mmap` 的定义

English:
definition mmap
  signature: {m} [Monad m] {α} {β : Type u} (f : α -> m β)

中文:
定义 mmap
  签名: {m} [单子 m] {α} {β : 类型u} (f : α -> m β)
-/
def mmap {m} [Monad m] {α} {β : Type u} (f : α -> m β) : forall {n}, Vector α n -> m (Vector β n)
  | 0, _ => pure nil
  | _ + 1, xs => do
    let h' ← f xs.head
    let t' ← mmap f xs.tail
    pure (h' ::ᵥ t')

@[simp]
/--
theorem `mmap_nil` / 定理 `mmap_nil`

English:
theorem mmap_nil
  given: {m} [Monad m] {α β} (f : α -> m β)
  statement: mmap f nil = pure nil
  proof: rfl

@[simp]

中文:
定理 mmap_nil
  条件: {m} [单子 m] {α β} (f : α -> m β)
  结论: mmap f nil = pure nil
  证明: rfl

@[simp]
-/
theorem mmap_nil {m} [Monad m] {α β} (f : α -> m β) : mmap f nil = pure nil :=
  rfl

@[simp]
/--
theorem `mmap_cons` / 定理 `mmap_cons`

English:
theorem mmap_cons
  given: {m} [Monad m] {α β} (f : α -> m β) (a)

中文:
定理 mmap_cons
  条件: {m} [单子 m] {α β} (f : α -> m β) (a)
-/
theorem mmap_cons {m} [Monad m] {α β} (f : α -> m β) (a) :
    forall {n} (v : Vector α n),
      mmap f (a ::ᵥ v) = do
        let h' ← f a
        let t' ← mmap f v
        pure (h' ::ᵥ t')
  | _, ⟨_, rfl⟩ => rfl

/--
Define `C v` by induction on `v : Vector α n`.

This function has two arguments: `nil` handles the base case on `C nil`,
and `cons` defines the inductive step using `∀ x : α, C w → C (x ::ᵥ w)`.

It is used as the default induction principle for the `induction` tactic.
-/
@[elab_as_elim, induction_eliminator]
/--
Definition of `inductionOn` / `inductionOn` 的定义

English:
definition inductionOn
  signature: {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (v : Vector α n)
  body: by
  induction n with
  | zero =>
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  | succ n ih =>
    rcases v with ⟨_ | ⟨a, v⟩, v_property⟩
    cases v_property
    exact cons (ih ⟨v, (add_left_inj 1).mp v_property⟩)

@[simp]

中文:
定义 inductionOn
  签名: {C : 对任意 {n : 自然数}, Vector α n -> 类型层*} {n : 自然数} (v : Vector α n)
  定义体: by
  induction n with
  | zero =>
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  | succ n ih =>
    rcases v with ⟨_ | ⟨a, v⟩, v_property⟩
    cases v_property
    exact cons (ih ⟨v, (add_left_inj 1).mp v_property⟩)

@[simp]

Depends on / 依赖: add_left_inj, v_property
-/
def inductionOn {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (v : Vector α n)
    (nil : C nil) (cons : forall {n : Nat} {x : α} {w : Vector α n}, C w -> C (x ::ᵥ w)) : C v := by
  induction n with
  | zero =>
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  | succ n ih =>
    rcases v with ⟨_ | ⟨a, v⟩, v_property⟩
    cases v_property
    exact cons (ih ⟨v, (add_left_inj 1).mp v_property⟩)

@[simp]
/--
theorem `inductionOn_nil` / 定理 `inductionOn_nil`

English:
theorem inductionOn_nil
  statement: {C : forall {n : Nat}, Vector α n -> Sort*}
  proof: rfl

@[simp]

中文:
定理 inductionOn_nil
  结论: {C : 对任意 {n : 自然数}, Vector α n -> 类型层*}
  证明: rfl

@[simp]
-/
theorem inductionOn_nil {C : forall {n : Nat}, Vector α n -> Sort*}
    (nil : C nil) (cons : forall {n : Nat} {x : α} {w : Vector α n}, C w -> C (x ::ᵥ w)) :
    Vector.nil.inductionOn nil cons = nil :=
  rfl

@[simp]
/--
theorem `inductionOn_cons` / 定理 `inductionOn_cons`

English:
theorem inductionOn_cons
  statement: {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (x : α) (v : Vector α n)
  proof: rfl

中文:
定理 inductionOn_cons
  结论: {C : 对任意 {n : 自然数}, Vector α n -> 类型层*} {n : 自然数} (x : α) (v : Vector α n)
  证明: rfl
-/
theorem inductionOn_cons {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (x : α) (v : Vector α n)
    (nil : C nil) (cons : forall {n : Nat} {x : α} {w : Vector α n}, C w -> C (x ::ᵥ w)) :
    (x ::ᵥ v).inductionOn nil cons = cons (v.inductionOn nil cons : C v) :=
  rfl

variable {β γ : Type*}

/-- Define `C v w` by induction on a pair of vectors `v : Vector α n` and `w : Vector β n`. -/
@[elab_as_elim]
/--
Definition of `inductionOn₂` / `inductionOn₂` 的定义

English:
definition inductionOn₂
  signature: {C : forall {n}, Vector α n -> Vector β n -> Sort*}
  body: by
  induction n with
  | zero =>
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  | succ n ih =>
    rcases v with ⟨_ | ⟨a, v⟩, v_property⟩
    cases v_property
    rcases w with ⟨_ | ⟨b, w⟩, w_property⟩
    cases w_property
    apply @cons n _ _ ⟨v, (add_

中文:
定义 inductionOn₂
  签名: {C : 对任意 {n}, Vector α n -> Vector β n -> 类型层*}
  定义体: by
  induction n with
  | zero =>
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  | succ n ih =>
    rcases v with ⟨_ | ⟨a, v⟩, v_property⟩
    cases v_property
    rcases w with ⟨_ | ⟨b, w⟩, w_property⟩
    cases w_property
    apply @cons n _ _ ⟨v, (add_

Depends on / 依赖: add_left_inj, v_property, w_property
-/
def inductionOn₂ {C : forall {n}, Vector α n -> Vector β n -> Sort*}
    (v : Vector α n) (w : Vector β n)
    (nil : C nil nil) (cons : forall {n a b} {x : Vector α n} {y}, C x y -> C (a ::ᵥ x) (b ::ᵥ y)) :
    C v w := by
  induction n with
  | zero =>
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  | succ n ih =>
    rcases v with ⟨_ | ⟨a, v⟩, v_property⟩
    cases v_property
    rcases w with ⟨_ | ⟨b, w⟩, w_property⟩
    cases w_property
    apply @cons n _ _ ⟨v, (add_left_inj 1).mp v_property⟩ ⟨w, (add_left_inj 1).mp w_property⟩
    apply ih

/-- Define `C u v w` by induction on a triplet of vectors
`u : Vector α n`, `v : Vector β n`, and `w : Vector γ b`. -/
@[elab_as_elim]
/--
Definition of `inductionOn₃` / `inductionOn₃` 的定义

English:
definition inductionOn₃
  signature: {C : forall {n}, Vector α n -> Vector β n -> Vector γ n -> Sort*}
  body: by
  induction n with
  | zero =>
    rcases u with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  | succ n ih =>
    rcases u with ⟨_ | ⟨a, u⟩, u_property⟩
    cases u_property
    rcases v with ⟨_ | ⟨b, v⟩, v_property⟩
    cases v_pr

中文:
定义 inductionOn₃
  签名: {C : 对任意 {n}, Vector α n -> Vector β n -> Vector γ n -> 类型层*}
  定义体: by
  induction n with
  | zero =>
    rcases u with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  | succ n ih =>
    rcases u with ⟨_ | ⟨a, u⟩, u_property⟩
    cases u_property
    rcases v with ⟨_ | ⟨b, v⟩, v_property⟩
    cases v_pr

Depends on / 依赖: add_left_inj, u_property, v_property, w_property
-/
def inductionOn₃ {C : forall {n}, Vector α n -> Vector β n -> Vector γ n -> Sort*}
    (u : Vector α n) (v : Vector β n) (w : Vector γ n) (nil : C nil nil nil)
    (cons : forall {n a b c} {x : Vector α n} {y z}, C x y z -> C (a ::ᵥ x) (b ::ᵥ y) (c ::ᵥ z)) :
    C u v w := by
  induction n with
  | zero =>
    rcases u with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  | succ n ih =>
    rcases u with ⟨_ | ⟨a, u⟩, u_property⟩
    cases u_property
    rcases v with ⟨_ | ⟨b, v⟩, v_property⟩
    cases v_property
    rcases w with ⟨_ | ⟨c, w⟩, w_property⟩
    cases w_property
    apply
      @cons n _ _ _ ⟨u, (add_left_inj 1).mp u_property⟩ ⟨v, (add_left_inj 1).mp v_property⟩
        ⟨w, (add_left_inj 1).mp w_property⟩
    apply ih

/--
Definition of `casesOn` / `casesOn` 的定义

English:
definition casesOn
  signature: {motive : forall {n}, Vector α n -> Sort*} (v : Vector α m)
  body: inductionOn (C := motive) v nil @fun _ hd tl _ => cons hd tl

中文:
定义 casesOn
  签名: {motive : 对任意 {n}, Vector α n -> 类型层*} (v : Vector α m)
  定义体: inductionOn (C := motive) v nil @fun _ hd tl _ => cons hd tl

Depends on / 依赖: inductionOn, motive
-/
def casesOn {motive : forall {n}, Vector α n -> Sort*} (v : Vector α m)
    (nil : motive nil)
    (cons : forall {n}, (hd : α) -> (tl : Vector α n) -> motive (Vector.cons hd tl)) :
    motive v :=
  inductionOn (C := motive) v nil @fun _ hd tl _ => cons hd tl

/--
Definition of `casesOn₂` / `casesOn₂` 的定义

English:
definition casesOn₂
  signature: {motive : forall {n}, Vector α n -> Vector β n -> Sort*} (v₁ : Vector α m) (v₂ : Vector β m)
  body: inductionOn₂ (C := motive) v₁ v₂ nil @fun _ x y xs ys _ => cons x y xs ys

中文:
定义 casesOn₂
  签名: {motive : 对任意 {n}, Vector α n -> Vector β n -> 类型层*} (v₁ : Vector α m) (v₂ : Vector β m)
  定义体: inductionOn₂ (C := motive) v₁ v₂ nil @fun _ x y xs ys _ => cons x y xs ys

Depends on / 依赖: motive
-/
def casesOn₂ {motive : forall {n}, Vector α n -> Vector β n -> Sort*} (v₁ : Vector α m) (v₂ : Vector β m)
    (nil : motive nil nil)
    (cons : forall {n}, (x : α) -> (y : β) -> (xs : Vector α n) -> (ys : Vector β n)
      -> motive (x ::ᵥ xs) (y ::ᵥ ys)) :
    motive v₁ v₂ :=
  inductionOn₂ (C := motive) v₁ v₂ nil @fun _ x y xs ys _ => cons x y xs ys

/--
Definition of `casesOn₃` / `casesOn₃` 的定义

English:
definition casesOn₃
  signature: {motive : forall {n}, Vector α n -> Vector β n -> Vector γ n -> Sort*} (v₁ : Vector α m)
  body: inductionOn₃ (C := motive) v₁ v₂ v₃ nil @fun _ x y z xs ys zs _ => cons x y z xs ys zs

中文:
定义 casesOn₃
  签名: {motive : 对任意 {n}, Vector α n -> Vector β n -> Vector γ n -> 类型层*} (v₁ : Vector α m)
  定义体: inductionOn₃ (C := motive) v₁ v₂ v₃ nil @fun _ x y z xs ys zs _ => cons x y z xs ys zs

Depends on / 依赖: motive
-/
def casesOn₃ {motive : forall {n}, Vector α n -> Vector β n -> Vector γ n -> Sort*} (v₁ : Vector α m)
    (v₂ : Vector β m) (v₃ : Vector γ m) (nil : motive nil nil nil)
    (cons : forall {n}, (x : α) -> (y : β) -> (z : γ) -> (xs : Vector α n) -> (ys : Vector β n)
      -> (zs : Vector γ n) -> motive (x ::ᵥ xs) (y ::ᵥ ys) (z ::ᵥ zs)) :
    motive v₁ v₂ v₃ :=
  inductionOn₃ (C := motive) v₁ v₂ v₃ nil @fun _ x y z xs ys zs _ => cons x y z xs ys zs

/--
Definition of `toArray` / `toArray` 的定义

English:
definition toArray
  signature: : Vector α n -> Array α

中文:
定义 toArray
  签名: : Vector α n -> 数组 α
-/
def toArray : Vector α n -> Array α
  | ⟨xs, _⟩ => xs.toArray

section InsertIdx

variable {a : α}

/--
Definition of `insertIdx` / `insertIdx` 的定义

English:
definition insertIdx
  signature: (a : α) (i : Fin (n + 1)) (v : Vector α n)
  body: ⟨v.1.insertIdx i a, by
    rw [List.length_insertIdx]; rw [v.2]
    split <;> lia⟩

中文:
定义 insertIdx
  签名: (a : α) (i : 有限集 (n + 1)) (v : Vector α n)
  定义体: ⟨v.1.insertIdx i a, by
    rw [List.length_insertIdx]; rw [v.2]
    split <;> lia⟩

Depends on / 依赖: List.length_insertIdx, insertIdx, length_insertIdx
-/
def insertIdx (a : α) (i : Fin (n + 1)) (v : Vector α n) : Vector α (n + 1) :=
  ⟨v.1.insertIdx i a, by
    rw [List.length_insertIdx]; rw [v.2]
    split <;> lia⟩

/--
theorem `insertIdx_val` / 定理 `insertIdx_val`

English:
theorem insertIdx_val
  given: {i : Fin (n + 1)} {v : Vector α n}
  proof: rfl

@[simp]

中文:
定理 insertIdx_val
  条件: {i : 有限集 (n + 1)} {v : Vector α n}
  证明: rfl

@[simp]
-/
theorem insertIdx_val {i : Fin (n + 1)} {v : Vector α n} :
    (v.insertIdx a i).val = v.val.insertIdx i.1 a :=
  rfl

@[simp]
/--
theorem `eraseIdx_val` / 定理 `eraseIdx_val`

English:
theorem eraseIdx_val
  given: {i : Fin n}
  statement: forall {v : Vector α n}, (eraseIdx i v).val = v.val.eraseIdx i

中文:
定理 eraseIdx_val
  条件: {i : 有限集 n}
  结论: 对任意 {v : Vector α n}, (eraseIdx i v).val = v.val.eraseIdx i
-/
theorem eraseIdx_val {i : Fin n} : forall {v : Vector α n}, (eraseIdx i v).val = v.val.eraseIdx i
  | _ => rfl

/--
theorem `eraseIdx_insertIdx_self` / 定理 `eraseIdx_insertIdx_self`

English:
theorem eraseIdx_insertIdx_self
  given: {v : Vector α n} {i : Fin (n + 1)}
  proof: Subtype.ext (List.eraseIdx_insertIdx_self ..)

中文:
定理 eraseIdx_insertIdx_self
  条件: {v : Vector α n} {i : 有限集 (n + 1)}
  证明: Subtype.ext (List.eraseIdx_insertIdx_self ..)

Depends on / 依赖: List.eraseIdx_insertIdx_self, Subtype, Subtype.ext, eraseIdx_insertIdx_self
-/
theorem eraseIdx_insertIdx_self {v : Vector α n} {i : Fin (n + 1)} :
    eraseIdx i (insertIdx a i v) = v :=
  Subtype.ext (List.eraseIdx_insertIdx_self ..)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eraseIdx_insertIdx'` / 定理 `eraseIdx_insertIdx'`

English:
theorem eraseIdx_insertIdx'
  given: {v : Vector α (n + 1)}

中文:
定理 eraseIdx_insertIdx'
  条件: {v : Vector α (n + 1)}
-/
theorem eraseIdx_insertIdx' {v : Vector α (n + 1)} :
    forall {i : Fin (n + 1)} {j : Fin (n + 2)},
      eraseIdx (j.succAbove i) (insertIdx a j v) = insertIdx a (i.predAbove j) (eraseIdx i v)
  | ⟨i, hi⟩, ⟨j, hj⟩ => by
    dsimp [insertIdx, eraseIdx, Fin.succAbove, Fin.predAbove]
    rw [Subtype.mk_eq_mk]
    simp only [Fin.lt_def]
    split_ifs with hij
    · rcases Nat.exists_eq_succ_of_ne_zero
        (Nat.pos_iff_ne_zero.1 (lt_of_le_of_lt (Nat.zero_le _) hij)) with ⟨j, rfl⟩
      rw [← List.insertIdx_eraseIdx_of_ge]
      · simp; rfl
      · simpa
      · simpa [Nat.lt_succ_iff] using hij
    · dsimp
      rw [← List.insertIdx_eraseIdx_of_le]
      · rfl
      · simpa
      · simpa [not_lt] using hij

/--
theorem `insertIdx_comm` / 定理 `insertIdx_comm`

English:
theorem insertIdx_comm
  given: (a b : α) (i j : Fin (n + 1)) (h : i <= j)

中文:
定理 insertIdx_comm
  条件: (a b : α) (i j : 有限集 (n + 1)) (h : i <= j)
-/
theorem insertIdx_comm (a b : α) (i j : Fin (n + 1)) (h : i <= j) :
    forall v : Vector α n,
      (v.insertIdx a i).insertIdx b j.succ = (v.insertIdx b j).insertIdx a (Fin.castSucc i)
  | ⟨l, hl⟩ => by
    refine Subtype.ext ?_
    simp only [insertIdx_val, Fin.val_succ, Fin.castSucc, Fin.val_castAdd]
    apply List.insertIdx_comm
    · assumption
    · rw [hl]
      exact Nat.le_of_succ_le_succ j.2

end InsertIdx

section Set

/--
Definition of `set` / `set` 的定义

English:
definition set
  signature: (v : Vector α n) (i : Fin n) (a : α)
  body: ⟨v.1.set i.1 a, by simp⟩

@[simp]

中文:
定义 set
  签名: (v : Vector α n) (i : 有限集 n) (a : α)
  定义体: ⟨v.1.set i.1 a, by simp⟩

@[simp]
-/
def set (v : Vector α n) (i : Fin n) (a : α) : Vector α n :=
  ⟨v.1.set i.1 a, by simp⟩

@[simp]
/--
theorem `toList_set` / 定理 `toList_set`

English:
theorem toList_set
  given: (v : Vector α n) (i : Fin n) (a : α)
  proof: rfl

中文:
定理 toList_set
  条件: (v : Vector α n) (i : 有限集 n) (a : α)
  证明: rfl
-/
theorem toList_set (v : Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList = v.toList.set i a :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `get_set_same` / 定理 `get_set_same`

English:
theorem get_set_same
  given: (v : Vector α n) (i : Fin n) (a : α)
  statement: (v.set i a).get i = a
  proof: by
  cases v; cases i; simp [Vector.set, get_eq_get_toList]

中文:
定理 get_set_same
  条件: (v : Vector α n) (i : 有限集 n) (a : α)
  结论: (v.set i a).get i = a
  证明: by
  cases v; cases i; simp [Vector.set, get_eq_get_toList]

Depends on / 依赖: Vector, Vector.set, get_eq_get_toList
-/
theorem get_set_same (v : Vector α n) (i : Fin n) (a : α) : (v.set i a).get i = a := by
  cases v; cases i; simp [Vector.set, get_eq_get_toList]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `get_set_of_ne` / 定理 `get_set_of_ne`

English:
theorem get_set_of_ne
  given: {v : Vector α n} {i j : Fin n} (h : i != j) (a : α)
  proof: by
  cases v; cases i; cases j
  simp only [get_eq_get_toList, toList_set, toList_mk, Fin.cast_mk, List.get_eq_getElem]
  rw [List.getElem_set_of_ne]
  · simpa using h

中文:
定理 get_set_of_ne
  条件: {v : Vector α n} {i j : 有限集 n} (h : i != j) (a : α)
  证明: by
  cases v; cases i; cases j
  simp only [get_eq_get_toList, toList_set, toList_mk, Fin.cast_mk, List.get_eq_getElem]
  rw [List.getElem_set_of_ne]
  · simpa using h

Depends on / 依赖: Fin.cast_mk, List.getElem_set_of_ne, List.get_eq_getElem, cast_mk, getElem_set_of_ne, get_eq_getElem, get_eq_get_toList, toList_mk, toList_set
-/
theorem get_set_of_ne {v : Vector α n} {i j : Fin n} (h : i != j) (a : α) :
    (v.set i a).get j = v.get j := by
  cases v; cases i; cases j
  simp only [get_eq_get_toList, toList_set, toList_mk, Fin.cast_mk, List.get_eq_getElem]
  rw [List.getElem_set_of_ne]
  · simpa using h

/--
theorem `get_set_eq_if` / 定理 `get_set_eq_if`

English:
theorem get_set_eq_if
  given: {v : Vector α n} {i j : Fin n} (a : α)
  proof: by
  split_ifs <;> (try simp [*]); rwa [get_set_of_ne]

@[to_additive]

中文:
定理 get_set_eq_if
  条件: {v : Vector α n} {i j : 有限集 n} (a : α)
  证明: by
  split_ifs <;> (try simp [*]); rwa [get_set_of_ne]

@[to_additive]

Depends on / 依赖: get_set_of_ne, split_ifs
-/
theorem get_set_eq_if {v : Vector α n} {i j : Fin n} (a : α) :
    (v.set i a).get j = if i = j then a else v.get j := by
  split_ifs <;> (try simp [*]); rwa [get_set_of_ne]

@[to_additive]
/--
theorem `prod_set` / 定理 `prod_set`

English:
theorem prod_set
  given: [Monoid α] (v : Vector α n) (i : Fin n) (a : α)
  proof: by
  refine (List.prod_set v.toList i a).trans ?_
  simp_all

中文:
定理 prod_set
  条件: [幺半群 α] (v : Vector α n) (i : 有限集 n) (a : α)
  证明: by
  refine (List.prod_set v.toList i a).trans ?_
  simp_all

Depends on / 依赖: List.prod_set, prod_set, toList, v.toList
-/
theorem prod_set [Monoid α] (v : Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList.prod = (v.take i).toList.prod * a * (v.drop (i + 1)).toList.prod := by
  refine (List.prod_set v.toList i a).trans ?_
  simp_all

/-- Variant of `List.Vector.prod_set` that multiplies by the inverse of the replaced element -/
@[to_additive
  /-- Variant of `List.Vector.sum_set` that subtracts the inverse of the replaced element -/]
/--
theorem `prod_set'` / 定理 `prod_set'`

English:
theorem prod_set'
  given: [CommGroup α] (v : Vector α n) (i : Fin n) (a : α)
  proof: by
  refine (List.prod_set' v.toList i a).trans ?_
  simp [get_eq_get_toList, mul_assoc]

中文:
定理 prod_set'
  条件: [交换群 α] (v : Vector α n) (i : 有限集 n) (a : α)
  证明: by
  refine (List.prod_set' v.toList i a).trans ?_
  simp [get_eq_get_toList, mul_assoc]

Depends on / 依赖: List.prod_set, get_eq_get_toList, mul_assoc, prod_set, toList, v.toList
-/
theorem prod_set' [CommGroup α] (v : Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList.prod = v.toList.prod * (v.get i)⁻¹ * a := by
  refine (List.prod_set' v.toList i a).trans ?_
  simp [get_eq_get_toList, mul_assoc]

end Set

end Vector

namespace Vector

section Traverse

variable {F G : Type u -> Type u}
variable [Applicative F] [Applicative G]

open Applicative Functor

open List (cons)

open Nat

/--
Definition of `traverseAux` / `traverseAux` 的定义

English:
definition traverseAux
  signature: {α β : Type u} (f : α -> F β)

中文:
定义 traverseAux
  签名: {α β : 类型u} (f : α -> F β)
-/
private def traverseAux {α β : Type u} (f : α -> F β) : forall x : List α, F (Vector β x.length)
  | [] => pure Vector.nil
| x :: xs => Vector.cons < > f x <*> traverseAux f xs

/--
Definition of `traverse` / `traverse` 的定义

English:
definition traverse
  signature: {α β : Type u} (f : α -> F β)

中文:
定义 traverse
  签名: {α β : 类型u} (f : α -> F β)
-/
@[no_expose] protected def traverse {α β : Type u} (f : α -> F β) : Vector α n -> F (Vector β n)
| ⟨v, Hv⟩ => cast (by rw [Hv]) traverseAux f v

section

variable {α β : Type u}

@[simp]
/--
theorem `traverse_def` / 定理 `traverse_def`

English:
theorem traverse_def
  given: (f : α -> F β) (x : α)
  proof: by
  rintro ⟨xs, rfl⟩; rfl

中文:
定理 traverse_def
  条件: (f : α -> F β) (x : α)
  证明: by
  rintro ⟨xs, rfl⟩; rfl
-/
protected theorem traverse_def (f : α -> F β) (x : α) :
forall xs : Vector α n, (x ::ᵥ xs).traverse f = cons < > f x <*> xs.traverse f := by
  rintro ⟨xs, rfl⟩; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `id_traverse` / 定理 `id_traverse`

English:
theorem id_traverse
  statement: forall x : Vector α n, x.traverse (pure : _ -> Id _) = pure x
  proof: by
  rintro ⟨x, rfl⟩; dsimp [Vector.traverse, cast]
  induction x with | nil => rfl | cons x xs IH => simp! [IH]

中文:
定理 id_traverse
  结论: 对任意 x : Vector α n, x.traverse (pure : _ -> Id _) = pure x
  证明: by
  rintro ⟨x, rfl⟩; dsimp [Vector.traverse, cast]
  induction x with | nil => rfl | cons x xs IH => simp! [IH]
-/
protected theorem id_traverse : forall x : Vector α n, x.traverse (pure : _ -> Id _) = pure x := by
  rintro ⟨x, rfl⟩; dsimp [Vector.traverse, cast]
  induction x with | nil => rfl | cons x xs IH => simp! [IH]

end

open Function

variable [LawfulApplicative G]
variable {α β γ : Type u}

-- We need to turn off the linter here as
-- the `LawfulTraversable` instance below expects a particular signature.
@[nolint unusedArguments]
/--
theorem `comp_traverse` / 定理 `comp_traverse`

English:
theorem comp_traverse
  given: (f : β -> F γ) (g : α -> G β) (x : Vector α n)
  proof: by
  induction x with
  | nil =>
    simp! [cast, *, functor_norm]
    rfl
  | cons ih =>
    rw [Vector.traverse_def]; rw [ih]
    simp [functor_norm, Function.comp_def]

中文:
定理 comp_traverse
  条件: (f : β -> F γ) (g : α -> G β) (x : Vector α n)
  证明: by
  induction x with
  | nil =>
    simp! [cast, *, functor_norm]
    rfl
  | cons ih =>
    rw [Vector.traverse_def]; rw [ih]
    simp [functor_norm, Function.comp_def]
-/
protected theorem comp_traverse (f : β -> F γ) (g : α -> G β) (x : Vector α n) :
    Vector.traverse (Comp.mk ∘ Functor.map f ∘ g) x =
      Comp.mk (Vector.traverse f <$> Vector.traverse g x) := by
  induction x with
  | nil =>
    simp! [cast, *, functor_norm]
    rfl
  | cons ih =>
    rw [Vector.traverse_def]; rw [ih]
    simp [functor_norm, Function.comp_def]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `traverse_eq_map_id` / 定理 `traverse_eq_map_id`

English:
theorem traverse_eq_map_id
  given: {α β} (f : α -> β)
  proof: by
  rintro ⟨x, rfl⟩
  simp!
  induction x <;> simp! [*, functor_norm]
  rfl

中文:
定理 traverse_eq_map_id
  条件: {α β} (f : α -> β)
  证明: by
  rintro ⟨x, rfl⟩
  simp!
  induction x <;> simp! [*, functor_norm]
  rfl
-/
protected theorem traverse_eq_map_id {α β} (f : α -> β) :
    forall x : Vector α n, x.traverse ((pure : _ -> Id _) ∘ f) = pure (map f x) := by
  rintro ⟨x, rfl⟩
  simp!
  induction x <;> simp! [*, functor_norm]
  rfl

variable [LawfulApplicative F] (η : ApplicativeTransformation F G)

/--
theorem `naturality` / 定理 `naturality`

English:
theorem naturality
  given: {α β : Type u} (f : α -> F β) (x : Vector α n)
  proof: by
  induction x with
  | nil => simp! [functor_norm, cast, η.preserves_pure]
  | cons ih =>
    rw [Vector.traverse_def]; rw [Vector.traverse_def]; rw [← ih]; rw [η.preserves_seq]; rw [η.preserves_map]
    rfl

中文:
定理 naturality
  条件: {α β : 类型u} (f : α -> F β) (x : Vector α n)
  证明: by
  induction x with
  | nil => simp! [functor_norm, cast, η.preserves_pure]
  | cons ih =>
    rw [Vector.traverse_def]; rw [Vector.traverse_def]; rw [← ih]; rw [η.preserves_seq]; rw [η.preserves_map]
    rfl
-/
protected theorem naturality {α β : Type u} (f : α -> F β) (x : Vector α n) :
    η (x.traverse f) = x.traverse (@η _ ∘ f) := by
  induction x with
  | nil => simp! [functor_norm, cast, η.preserves_pure]
  | cons ih =>
    rw [Vector.traverse_def]; rw [Vector.traverse_def]; rw [← ih]; rw [η.preserves_seq]; rw [η.preserves_map]
    rfl

end Traverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Traversable.{u} (flip Vector n)
  body: @Vector.traverse n
  map {α β} := @Vector.map.{u, u} α β n

中文:
实例 :
  签名: 可遍历.{u} (flip Vector n)
  定义体: @Vector.traverse n
  map {α β} := @Vector.map.{u, u} α β n

Depends on / 依赖: Vector, Vector.traverse, traverse
-/
instance : Traversable.{u} (flip Vector n) where
  traverse := @Vector.traverse n
  map {α β} := @Vector.map.{u, u} α β n

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulTraversable.{u} (flip Vector n)
  body: @Vector.id_traverse n
  comp_traverse := Vector.comp_traverse
  traverse_eq_map_id := @Vector.traverse_eq_map_id n
  naturality := Vector.naturality
  id_map := by intro _ x; cases x; simp! [(· <$> ·)]
  comp_map := by intro _ _ _ _ _ x; cases x; simp! [(· <$> ·)]
  map_const := rfl

中文:
实例 :
  签名: 合法可遍历.{u} (flip Vector n)
  定义体: @Vector.id_traverse n
  comp_traverse := Vector.comp_traverse
  traverse_eq_map_id := @Vector.traverse_eq_map_id n
  naturality := Vector.naturality
  id_map := by intro _ x; cases x; simp! [(· <$> ·)]
  comp_map := by intro _ _ _ _ _ x; cases x; simp! [(· <$> ·)]
  map_const := rfl

Depends on / 依赖: Finite, Vector, Vector.id_traverse, finite, id_traverse
-/
instance : LawfulTraversable.{u} (flip Vector n) where
  id_traverse := @Vector.id_traverse n
  comp_traverse := Vector.comp_traverse
  traverse_eq_map_id := @Vector.traverse_eq_map_id n
  naturality := Vector.naturality
  id_map := by intro _ x; cases x; simp! [(· <$> ·)]
  comp_map := by intro _ _ _ _ _ x; cases x; simp! [(· <$> ·)]
  map_const := rfl

section Simp

variable {x : α} {y : β} {s : σ} (xs : Vector α n)

@[simp]
/--
theorem `replicate_succ` / 定理 `replicate_succ`

English:
theorem replicate_succ
  given: (val : α)
  proof: rfl

中文:
定理 replicate_succ
  条件: (val : α)
  证明: rfl
-/
theorem replicate_succ (val : α) :
    replicate (n + 1) val = val ::ᵥ (replicate n val) :=
  rfl

section Append
variable (ys : Vector α m)

/--
lemma `get_append_cons_zero` / 引理 `get_append_cons_zero`

English:
lemma get_append_cons_zero
  statement: get (x ::ᵥ xs ++ ys) 0 = x
  proof: rfl

@[simp]

中文:
引理 get_append_cons_zero
  结论: get (x ::ᵥ xs ++ ys) 0 = x
  证明: rfl

@[simp]
-/
@[simp] lemma get_append_cons_zero : get (x ::ᵥ xs ++ ys) 0 = x := rfl

@[simp]
/--
theorem `get_append_cons_succ` / 定理 `get_append_cons_succ`

English:
theorem get_append_cons_succ
  given: {i : Fin (n + m)} {h}
  proof: rfl

中文:
定理 get_append_cons_succ
  条件: {i : 有限集 (n + m)} {h}
  证明: rfl
-/
theorem get_append_cons_succ {i : Fin (n + m)} {h} :
    get (x ::ᵥ xs ++ ys) ⟨i+1, h⟩ = get (xs ++ ys) i :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `append_nil` / 定理 `append_nil`

English:
theorem append_nil
  statement: xs ++ (nil : Vector α 0) = xs
  proof: by
  cases xs; simp only [append_def, append_nil]

中文:
定理 append_nil
  结论: xs ++ (nil : Vector α 0) = xs
  证明: by
  cases xs; simp only [append_def, append_nil]

Depends on / 依赖: append_def, append_nil
-/
theorem append_nil : xs ++ (nil : Vector α 0) = xs := by
  cases xs; simp only [append_def, append_nil]

end Append

variable (ys : Vector β n)

@[simp]
/--
theorem `get_map₂` / 定理 `get_map₂`

English:
theorem get_map₂
  given: (v₁ : Vector α n) (v₂ : Vector β n) (f : α -> β -> γ) (i : Fin n)
  proof: by
  induction v₁, v₂ using inductionOn₂ with
  | nil =>
    exact Fin.elim0 i
  | cons ih =>
    rw [map₂_cons]
    cases i using Fin.cases
    · simp only [get_zero, head_cons]
    · simp only [get_cons_succ, ih]

@[simp]

中文:
定理 get_map₂
  条件: (v₁ : Vector α n) (v₂ : Vector β n) (f : α -> β -> γ) (i : 有限集 n)
  证明: by
  induction v₁, v₂ using inductionOn₂ with
  | nil =>
    exact Fin.elim0 i
  | cons ih =>
    rw [map₂_cons]
    cases i using Fin.cases
    · simp only [get_zero, head_cons]
    · simp only [get_cons_succ, ih]

@[simp]

Depends on / 依赖: Fin.cases, Fin.elim0, get_cons_succ, get_zero, head_cons
-/
theorem get_map₂ (v₁ : Vector α n) (v₂ : Vector β n) (f : α -> β -> γ) (i : Fin n) :
    get (map₂ f v₁ v₂) i = f (get v₁ i) (get v₂ i) := by
  induction v₁, v₂ using inductionOn₂ with
  | nil =>
    exact Fin.elim0 i
  | cons ih =>
    rw [map₂_cons]
    cases i using Fin.cases
    · simp only [get_zero, head_cons]
    · simp only [get_cons_succ, ih]

@[simp]
/--
theorem `mapAccumr_cons` / 定理 `mapAccumr_cons`

English:
theorem mapAccumr_cons
  given: {f : α -> σ -> σ × β}
  proof: mapAccumr f xs s
      let q := f x r.1
      (q.1, q.2 ::ᵥ r.2) :=
  rfl

@[simp]

中文:
定理 mapAccumr_cons
  条件: {f : α -> σ -> σ × β}
  证明: mapAccumr f xs s
      let q := f x r.1
      (q.1, q.2 ::ᵥ r.2) :=
  rfl

@[simp]

Depends on / 依赖: mapAccumr
-/
theorem mapAccumr_cons {f : α -> σ -> σ × β} :
    mapAccumr f (x ::ᵥ xs) s
    = let r := mapAccumr f xs s
      let q := f x r.1
      (q.1, q.2 ::ᵥ r.2) :=
  rfl

@[simp]
/--
theorem `mapAccumr₂_cons` / 定理 `mapAccumr₂_cons`

English:
theorem mapAccumr₂_cons
  given: {f : α -> β -> σ -> σ × φ}
  proof: mapAccumr₂ f xs ys s
      let q := f x y r.1
      (q.1, q.2 ::ᵥ r.2) :=
  rfl

中文:
定理 mapAccumr₂_cons
  条件: {f : α -> β -> σ -> σ × φ}
  证明: mapAccumr₂ f xs ys s
      let q := f x y r.1
      (q.1, q.2 ::ᵥ r.2) :=
  rfl
-/
theorem mapAccumr₂_cons {f : α -> β -> σ -> σ × φ} :
    mapAccumr₂ f (x ::ᵥ xs) (y ::ᵥ ys) s
    = let r := mapAccumr₂ f xs ys s
      let q := f x y r.1
      (q.1, q.2 ::ᵥ r.2) :=
  rfl

end Simp

end List.Vector
