/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Multiset.Pi

/-!
# The Cartesian product of lists

## Main definitions

* `List.pi`: Cartesian product of lists indexed by a list.
-/

@[expose] public section

namespace List

namespace Pi
variable {ι : Type*} [DecidableEq ι] {α : ι -> Sort*}

/--
Definition of `nil` / `nil` 的定义

English:
definition nil
  signature: (α : ι -> Sort*)
  body: nofun

中文:
定义 nil
  签名: (α : ι -> Sort*)
  定义体: nofun
-/
def nil (α : ι -> Sort*) : (forall i in ([] : List ι), α i) :=
  nofun

variable {i : ι} {l : List ι}

/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: (f : forall j in i :: l, α j)
  body: f i mem_cons_self

中文:
定义 head
  签名: (f : 对任意 j in i :: l, α j)
  定义体: f i mem_cons_self

Depends on / 依赖: mem_cons_self
-/
def head (f : forall j in i :: l, α j) : α i :=
  f i mem_cons_self

/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: (f : forall j in i :: l, α j)
  body: fun j hj => f j (mem_cons_of_mem _ hj)

中文:
定义 tail
  签名: (f : 对任意 j in i :: l, α j)
  定义体: fun j hj => f j (mem_cons_of_mem _ hj)

Depends on / 依赖: mem_cons_of_mem
-/
def tail (f : forall j in i :: l, α j) : forall j in l, α j :=
  fun j hj => f j (mem_cons_of_mem _ hj)

variable (i l)

/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: (a : α i) (f : forall j in l, α j)
  body: Multiset.Pi.cons (α := ι) l _ a f

中文:
定义 cons
  签名: (a : α i) (f : 对任意 j in l, α j)
  定义体: Multiset.Pi.cons (α := ι) l _ a f

Depends on / 依赖: Multiset, Multiset.Pi.cons
-/
def cons (a : α i) (f : forall j in l, α j) : forall j in i :: l, α j :=
  Multiset.Pi.cons (α := ι) l _ a f

variable {i l}

/--
lemma `cons_def` / 引理 `cons_def`

English:
lemma cons_def
  given: (a : α i) (f : forall j in l, α j)
  statement: cons _ _ a f =
  proof: rfl

中文:
引理 cons_def
  条件: (a : α i) (f : 对任意 j in l, α j)
  结论: cons _ _ a f =
  证明: rfl
-/
lemma cons_def (a : α i) (f : forall j in l, α j) : cons _ _ a f =
fun j hj => if h : j = i then h.symm.rec a else f j (mem_cons.1 hj).resolve_left h :=
  rfl

/--
lemma `_root_.Multiset.Pi.cons_coe` / 引理 `_root_.Multiset.Pi.cons_coe`

English:
lemma _root_.Multiset.Pi.cons_coe
  given: {l : List ι} (a : α i) (f : forall j in l, α j)
  proof: rfl

中文:
引理 _root_.Multiset.Pi.cons_coe
  条件: {l : List ι} (a : α i) (f : 对任意 j in l, α j)
  证明: rfl
-/
@[simp] lemma _root_.Multiset.Pi.cons_coe {l : List ι} (a : α i) (f : forall j in l, α j) :
    Multiset.Pi.cons l _ a f = cons _ _ a f :=
  rfl

/--
lemma `cons_eta` / 引理 `cons_eta`

English:
lemma cons_eta
  given: (f : forall j in i :: l, α j)
  proof: Multiset.Pi.cons_eta (α := ι) (m := l) f

中文:
引理 cons_eta
  条件: (f : 对任意 j in i :: l, α j)
  证明: Multiset.Pi.cons_eta (α := ι) (m := l) f
-/
@[simp] lemma cons_eta (f : forall j in i :: l, α j) :
    cons _ _ (head f) (tail f) = f :=
  Multiset.Pi.cons_eta (α := ι) (m := l) f

/--
lemma `cons_map` / 引理 `cons_map`

English:
lemma cons_map
  statement: (a : α i) (f : forall j in l, α j)
  proof: Multiset.Pi.cons_map _ _ _

中文:
引理 cons_map
  结论: (a : α i) (f : 对任意 j in l, α j)
  证明: Multiset.Pi.cons_map _ _ _

Depends on / 依赖: Multiset, Multiset.Pi.cons_map, cons_map
-/
lemma cons_map (a : α i) (f : forall j in l, α j)
    {α' : ι -> Sort*} (φ : forall ⦃j⦄, α j -> α' j) :
    cons _ _ (φ a) (fun j hj => φ (f j hj)) = (fun j hj => φ ((cons _ _ a f) j hj)) :=
  Multiset.Pi.cons_map _ _ _

/--
lemma `forall_rel_cons_ext` / 引理 `forall_rel_cons_ext`

English:
lemma forall_rel_cons_ext
  statement: {r : forall ⦃i⦄, α i -> α i -> Prop} {a₁ a₂ : α i} {f₁ f₂ : forall j in l, α j}
  proof: Multiset.Pi.forall_rel_cons_ext (α := ι) (m := l) ha hf

中文:
引理 forall_rel_cons_ext
  结论: {r : 对任意 ⦃i⦄, α i -> α i -> 命题} {a₁ a₂ : α i} {f₁ f₂ : 对任意 j in l, α j}
  证明: Multiset.Pi.forall_rel_cons_ext (α := ι) (m := l) ha hf

Depends on / 依赖: Multiset, Multiset.Pi.forall_rel_cons_ext, forall_rel_cons_ext
-/
lemma forall_rel_cons_ext {r : forall ⦃i⦄, α i -> α i -> Prop} {a₁ a₂ : α i} {f₁ f₂ : forall j in l, α j}
    (ha : r a₁ a₂) (hf : forall (i : ι) (hi : i in l), r (f₁ i hi) (f₂ i hi)) :
    forall j hj, r (cons _ _ a₁ f₁ j hj) (cons _ _ a₂ f₂ j hj) :=
  Multiset.Pi.forall_rel_cons_ext (α := ι) (m := l) ha hf

end Pi

variable {ι : Type*} [DecidableEq ι] {α : ι -> Type*}

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: : forall l : List ι, (forall i, List (α i)) -> List (forall i, i in l -> α i)

中文:
定义 pi
  签名: : 对任意 l : List ι, (对任意 i, List (α i)) -> List (对任意 i, i in l -> α i)
-/
def pi : forall l : List ι, (forall i, List (α i)) -> List (forall i, i in l -> α i)
  | [], _ => [List.Pi.nil α]
  | i :: l, fs => (fs i).flatMap (fun b => (pi l fs).map (List.Pi.cons _ _ b))

/--
lemma `pi_nil` / 引理 `pi_nil`

English:
lemma pi_nil
  given: (t : forall i, List (α i))
  proof: rfl

中文:
引理 pi_nil
  条件: (t : 对任意 i, List (α i))
  证明: rfl
-/
@[simp] lemma pi_nil (t : forall i, List (α i)) :
    pi [] t = [Pi.nil α] :=
  rfl

/--
lemma `pi_cons` / 引理 `pi_cons`

English:
lemma pi_cons
  given: (i : ι) (l : List ι) (t : forall j, List (α j))
  proof: rfl

中文:
引理 pi_cons
  条件: (i : ι) (l : List ι) (t : 对任意 j, List (α j))
  证明: rfl
-/
@[simp] lemma pi_cons (i : ι) (l : List ι) (t : forall j, List (α j)) :
    pi (i :: l) t = ((t i).flatMap fun b => (pi l t).map <| Pi.cons _ _ b) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `_root_.Multiset.pi_coe` / 引理 `_root_.Multiset.pi_coe`

English:
lemma _root_.Multiset.pi_coe
  given: (l : List ι) (fs : forall i, List (α i))
  proof: by
  induction l with
  | nil =>
    simp only [Multiset.coe_nil, Multiset.pi_zero, pi_nil, Multiset.coe_singleton,
      Multiset.singleton_inj]
    ext i hi
    simp at hi
  | cons i l ih =>
    simp [ih, Multiset.coe_bind, ← Multiset.cons_coe]

中文:
引理 _root_.Multiset.pi_coe
  条件: (l : List ι) (fs : 对任意 i, List (α i))
  证明: by
  induction l with
  | nil =>
    simp only [Multiset.coe_nil, Multiset.pi_zero, pi_nil, Multiset.coe_singleton,
      Multiset.singleton_inj]
    ext i hi
    simp at hi
  | cons i l ih =>
    simp [ih, Multiset.coe_bind, ← Multiset.cons_coe]

Depends on / 依赖: Multiset, Multiset.coe_bind, Multiset.coe_nil, Multiset.coe_singleton, Multiset.cons_coe, Multiset.pi_zero, Multiset.singleton_inj, coe_bind, coe_nil, coe_singleton, cons_coe, pi_nil, pi_zero, singleton_inj
-/
lemma _root_.Multiset.pi_coe (l : List ι) (fs : forall i, List (α i)) :
    (l : Multiset ι).pi (fs ·) = (↑(pi l fs) : Multiset (forall i in l, α i)) := by
  induction l with
  | nil =>
    simp only [Multiset.coe_nil, Multiset.pi_zero, pi_nil, Multiset.coe_singleton,
      Multiset.singleton_inj]
    ext i hi
    simp at hi
  | cons i l ih =>
    simp [ih, Multiset.coe_bind, ← Multiset.cons_coe]

/--
lemma `mem_pi` / 引理 `mem_pi`

English:
lemma mem_pi
  given: {l : List ι} (fs : forall i, List (α i)) (f : forall i in l, α i)
  proof: by
  simpa [Multiset.pi_coe] using! Multiset.mem_pi ↑l (fs ·) f

中文:
引理 mem_pi
  条件: {l : List ι} (fs : 对任意 i, List (α i)) (f : 对任意 i in l, α i)
  证明: by
  simpa [Multiset.pi_coe] using! Multiset.mem_pi ↑l (fs ·) f

Depends on / 依赖: Multiset, Multiset.mem_pi, Multiset.pi_coe, mem_pi, pi_coe
-/
lemma mem_pi {l : List ι} (fs : forall i, List (α i)) (f : forall i in l, α i) :
    (f in pi l fs) ↔ (forall i (hi : i in l), f i hi in fs i) := by
  simpa [Multiset.pi_coe] using! Multiset.mem_pi ↑l (fs ·) f

end List
