/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yuyang Zhao
-/
module

public import Mathlib.Data.List.Pi
public import Mathlib.Data.Fintype.Defs

/-!
# Quotients of families indexed by a finite type

This file proves some basic facts and defines lifting and recursion principle for quotients indexed
by a finite type.

## Main definitions

* `Quotient.finChoice`: Given a function `f : Π i, Quotient (S i)` on a fintype `ι`, returns the
  class of functions `Π i, α i` sending each `i` to an element of the class `f i`.
* `Quotient.finChoiceEquiv`: A finite family of quotients is equivalent to a quotient of
  finite families.
* `Quotient.finLiftOn`: Given a fintype `ι`. A function on `Π i, α i` which respects
  setoid `S i` for each `i` can be lifted to a function on `Π i, Quotient (S i)`.
* `Quotient.finRecOn`: Recursion principle for quotients indexed by a finite type. It is the
  dependent version of `Quotient.finLiftOn`.

-/

@[expose] public section

-- We want the theorems in this file to be constructive.
set_option linter.unusedDecidableInType false

namespace Quotient

section List
variable {ι : Type*} [DecidableEq ι] {α : ι -> Sort*} {S : forall i, Setoid (α i)} {β : Sort*}

/--
Definition of `listChoice` / `listChoice` 的定义

English:
definition listChoice
  signature: {l : List ι} (q : forall i in l, Quotient (S i))
  body: match l with
  | [] => ⟦nofun⟧
  | i :: _ => Quotient.liftOn₂ (List.Pi.head (i := i) q)
    (listChoice (List.Pi.tail q))
    (⟦List.Pi.cons _ _ · ·⟧)
    (fun _ _ _ _ ha hl => Quotient.sound (List.Pi.forall_rel_cons_ext ha hl))

中文:
定义 listChoice
  签名: {l : 列表 ι} (q : 对任意 i in l, 商 (S i))
  定义体: match l with
  | [] => ⟦nofun⟧
  | i :: _ => Quotient.liftOn₂ (List.Pi.head (i := i) q)
    (listChoice (List.Pi.tail q))
    (⟦List.Pi.cons _ _ · ·⟧)
    (fun _ _ _ _ ha hl => Quotient.sound (List.Pi.forall_rel_cons_ext ha hl))

Depends on / 依赖: List.Pi.cons, List.Pi.forall_rel_cons_ext, List.Pi.head, List.Pi.tail, Quotient, Quotient.liftOn, Quotient.sound, forall_rel_cons_ext, listChoice
-/
def listChoice {l : List ι} (q : forall i in l, Quotient (S i)) : @Quotient (forall i in l, α i) piSetoid :=
  match l with
  | [] => ⟦nofun⟧
  | i :: _ => Quotient.liftOn₂ (List.Pi.head (i := i) q)
    (listChoice (List.Pi.tail q))
    (⟦List.Pi.cons _ _ · ·⟧)
    (fun _ _ _ _ ha hl => Quotient.sound (List.Pi.forall_rel_cons_ext ha hl))

/--
theorem `listChoice_mk` / 定理 `listChoice_mk`

English:
theorem listChoice_mk
  given: {l : List ι} (a : forall i in l, α i)
  statement: listChoice (S := S) (⟦a · ·⟧) = ⟦a⟧
  proof: match l with
  | [] => Quotient.sound nofun
  | i :: l => by
    unfold listChoice List.Pi.tail
    rw [listChoice_mk]
    exact congrArg (⟦·⟧) (List.Pi.cons_eta a)

中文:
定理 listChoice_mk
  条件: {l : 列表 ι} (a : 对任意 i in l, α i)
  结论: listChoice (S := S) (⟦a · ·⟧) = ⟦a⟧
  证明: match l with
  | [] => Quotient.sound nofun
  | i :: l => by
    unfold listChoice List.Pi.tail
    rw [listChoice_mk]
    exact congrArg (⟦·⟧) (List.Pi.cons_eta a)
-/
theorem listChoice_mk {l : List ι} (a : forall i in l, α i) : listChoice (S := S) (⟦a · ·⟧) = ⟦a⟧ :=
  match l with
  | [] => Quotient.sound nofun
  | i :: l => by
    unfold listChoice List.Pi.tail
    rw [listChoice_mk]
    exact congrArg (⟦·⟧) (List.Pi.cons_eta a)

/-- Choice-free induction principle for quotients indexed by a `List`. -/
@[elab_as_elim]
/--
lemma `list_ind` / 引理 `list_ind`

English:
lemma list_ind
  statement: {l : List ι} {C : (forall i in l, Quotient (S i)) -> Prop}
  proof: match l with
  | [] => cast (congr_arg _ (funext₂ nofun)) (f nofun)
  | i :: l => by
    rw [← List.Pi.cons_eta q]
    induction List.Pi.head q using Quotient.ind with | _ a
    refine @list_ind _ (fun q => C (List.Pi.cons _ _ ⟦a⟧ q)) ?_ (List.Pi.tail q)
    intro as
    rw [List.Pi.cons_map a as (f

中文:
引理 list_ind
  结论: {l : 列表 ι} {C : (对任意 i in l, 商 (S i)) -> 命题}
  证明: match l with
  | [] => cast (congr_arg _ (funext₂ nofun)) (f nofun)
  | i :: l => by
    rw [← List.Pi.cons_eta q]
    induction List.Pi.head q using Quotient.ind with | _ a
    refine @list_ind _ (fun q => C (List.Pi.cons _ _ ⟦a⟧ q)) ?_ (List.Pi.tail q)
    intro as
    rw [List.Pi.cons_map a as (f

Depends on / 依赖: List.Pi.cons, List.Pi.cons_eta, List.Pi.cons_map, List.Pi.head, List.Pi.tail, Quotient, Quotient.ind, Quotient.mk, congr_arg, cons_eta, cons_map, list_ind
-/
lemma list_ind {l : List ι} {C : (forall i in l, Quotient (S i)) -> Prop}
    (f : forall a : forall i in l, α i, C (⟦a · ·⟧)) (q : forall i in l, Quotient (S i)) : C q :=
  match l with
  | [] => cast (congr_arg _ (funext₂ nofun)) (f nofun)
  | i :: l => by
    rw [← List.Pi.cons_eta q]
    induction List.Pi.head q using Quotient.ind with | _ a
    refine @list_ind _ (fun q => C (List.Pi.cons _ _ ⟦a⟧ q)) ?_ (List.Pi.tail q)
    intro as
    rw [List.Pi.cons_map a as (fun i => Quotient.mk (S i))]
    exact f _

end List

section Fintype

-- `Fintype.ofFinite` depends on this file, so the `unusedFintypeInType` linter
-- makes no sense yet.
set_option linter.unusedFintypeInType false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι -> Sort*} {S : forall i, Setoid (α i)} {β : Sort*}

/-- Choice-free induction principle for quotients indexed by a finite type.
  See `Quotient.induction_on_pi` for the general version assuming `Classical.choice`. -/
@[elab_as_elim]
/--
lemma `ind_fintype_pi` / 引理 `ind_fintype_pi`

English:
lemma ind_fintype_pi
  statement: {C : (forall i, Quotient (S i)) -> Prop}
  proof: by
  have {m : Multiset ι} (C : (forall i in m, Quotient (S i)) -> Prop) :
      forall (_ : forall a : forall i in m, α i, C (⟦a · ·⟧)) (q : forall i in m, Quotient (S i)), C q := by
    induction m using Quotient.ind
    exact list_ind
  exact this (fun q => C (q · (Finset.mem_univ _))) (fun _ => 

中文:
引理 ind_fintype_pi
  结论: {C : (对任意 i, 商 (S i)) -> 命题}
  证明: by
  have {m : Multiset ι} (C : (forall i in m, Quotient (S i)) -> Prop) :
      forall (_ : forall a : forall i in m, α i, C (⟦a · ·⟧)) (q : forall i in m, Quotient (S i)), C q := by
    induction m using Quotient.ind
    exact list_ind
  exact this (fun q => C (q · (Finset.mem_univ _))) (fun _ => 

Depends on / 依赖: Finset, Finset.mem_univ, Multiset, Quotient, Quotient.ind, list_ind, mem_univ
-/
lemma ind_fintype_pi {C : (forall i, Quotient (S i)) -> Prop}
    (f : forall a : forall i, α i, C (⟦a ·⟧)) (q : forall i, Quotient (S i)) : C q := by
  have {m : Multiset ι} (C : (forall i in m, Quotient (S i)) -> Prop) :
      forall (_ : forall a : forall i in m, α i, C (⟦a · ·⟧)) (q : forall i in m, Quotient (S i)), C q := by
    induction m using Quotient.ind
    exact list_ind
  exact this (fun q => C (q · (Finset.mem_univ _))) (fun _ => f _) (fun i _ => q i)

/-- Choice-free induction principle for quotients indexed by a finite type.
  See `Quotient.induction_on_pi` for the general version assuming `Classical.choice`. -/
@[elab_as_elim]
/--
lemma `induction_on_fintype_pi` / 引理 `induction_on_fintype_pi`

English:
lemma induction_on_fintype_pi
  statement: {C : (forall i, Quotient (S i)) -> Prop}
  proof: ind_fintype_pi f q

中文:
引理 induction_on_fintype_pi
  结论: {C : (对任意 i, 商 (S i)) -> 命题}
  证明: ind_fintype_pi f q

Depends on / 依赖: ind_fintype_pi
-/
lemma induction_on_fintype_pi {C : (forall i, Quotient (S i)) -> Prop}
    (q : forall i, Quotient (S i)) (f : forall a : forall i, α i, C (⟦a ·⟧)) : C q :=
  ind_fintype_pi f q

/--
Definition of `finChoice` / `finChoice` 的定义

English:
definition finChoice
  signature: (q : forall i, Quotient (S i))
  body: by
  let e := Equiv.subtypeQuotientEquivQuotientSubtype (fun l : List ι => forall i, i in l)
    (fun s : Multiset ι => forall i, i in s) (fun i => Iff.rfl) (fun _ _ => Iff.rfl) ⟨_, Finset.mem_univ⟩
  refine e.liftOn
    (fun l => (listChoice fun i _ => q i).map (fun a i => a i (l.2 i)) ?_) ?_
  · e

中文:
定义 finChoice
  签名: (q : 对任意 i, 商 (S i))
  定义体: by
  let e := Equiv.subtypeQuotientEquivQuotientSubtype (fun l : List ι => forall i, i in l)
    (fun s : Multiset ι => forall i, i in s) (fun i => Iff.rfl) (fun _ _ => Iff.rfl) ⟨_, Finset.mem_univ⟩
  refine e.liftOn
    (fun l => (listChoice fun i _ => q i).map (fun a i => a i (l.2 i)) ?_) ?_
  · e

Depends on / 依赖: Equiv.subtypeQuotientEquivQuotientSubtype, Finset, Finset.mem_univ, Iff.rfl, Multiset, Quotient, Quotient.map_mk, e.liftOn, ind_fintype_pi, liftOn, listChoice, listChoice_mk, map_mk, mem_univ, simp_rw, subtypeQuotientEquivQuotientSubtype
-/
def finChoice (q : forall i, Quotient (S i)) :
    @Quotient (forall i, α i) piSetoid := by
  let e := Equiv.subtypeQuotientEquivQuotientSubtype (fun l : List ι => forall i, i in l)
    (fun s : Multiset ι => forall i, i in s) (fun i => Iff.rfl) (fun _ _ => Iff.rfl) ⟨_, Finset.mem_univ⟩
  refine e.liftOn
    (fun l => (listChoice fun i _ => q i).map (fun a i => a i (l.2 i)) ?_) ?_
  · exact fun _ _ h i => h i _
  intro _ _ _
  refine ind_fintype_pi (fun a => ?_) q
  simp_rw [listChoice_mk, Quotient.map_mk]

/--
theorem `finChoice_eq` / 定理 `finChoice_eq`

English:
theorem finChoice_eq
  given: (a : forall i, α i)
  proof: by
  dsimp [finChoice]
  obtain ⟨l, hl⟩ := (Finset.univ.val : Multiset ι).exists_rep
  simp_rw [← hl, Equiv.subtypeQuotientEquivQuotientSubtype, listChoice_mk]
  rfl

中文:
定理 finChoice_eq
  条件: (a : 对任意 i, α i)
  证明: by
  dsimp [finChoice]
  obtain ⟨l, hl⟩ := (Finset.univ.val : Multiset ι).exists_rep
  simp_rw [← hl, Equiv.subtypeQuotientEquivQuotientSubtype, listChoice_mk]
  rfl

Depends on / 依赖: Equiv.subtypeQuotientEquivQuotientSubtype, Finset, Finset.univ.val, Multiset, exists_rep, finChoice, listChoice_mk, simp_rw, subtypeQuotientEquivQuotientSubtype
-/
theorem finChoice_eq (a : forall i, α i) :
    finChoice (S := S) (⟦a ·⟧) = ⟦a⟧ := by
  dsimp [finChoice]
  obtain ⟨l, hl⟩ := (Finset.univ.val : Multiset ι).exists_rep
  simp_rw [← hl, Equiv.subtypeQuotientEquivQuotientSubtype, listChoice_mk]
  rfl

/--
lemma `eval_finChoice` / 引理 `eval_finChoice`

English:
lemma eval_finChoice
  given: (f : forall i, Quotient (S i))
  proof: induction_on_fintype_pi f (fun a => by rw [finChoice_eq]; rfl)

中文:
引理 eval_finChoice
  条件: (f : 对任意 i, 商 (S i))
  证明: induction_on_fintype_pi f (fun a => by rw [finChoice_eq]; rfl)

Depends on / 依赖: finChoice_eq, induction_on_fintype_pi
-/
lemma eval_finChoice (f : forall i, Quotient (S i)) :
    eval (finChoice f) = f :=
  induction_on_fintype_pi f (fun a => by rw [finChoice_eq]; rfl)

/--
Definition of `finLiftOn` / `finLiftOn` 的定义

English:
definition finLiftOn
  signature: (q : forall i, Quotient (S i)) (f : (forall i, α i) -> β)
  body: (finChoice q).liftOn f h

@[simp]

中文:
定义 finLiftOn
  签名: (q : 对任意 i, 商 (S i)) (f : (对任意 i, α i) -> β)
  定义体: (finChoice q).liftOn f h

@[simp]

Depends on / 依赖: finChoice, liftOn
-/
def finLiftOn (q : forall i, Quotient (S i)) (f : (forall i, α i) -> β)
    (h : forall (a b : forall i, α i), (forall i, a i ≈ b i) -> f a = f b) : β :=
  (finChoice q).liftOn f h

@[simp]
/--
lemma `finLiftOn_empty` / 引理 `finLiftOn_empty`

English:
lemma finLiftOn_empty
  given: [e : IsEmpty ι] (q : forall i, Quotient (S i))
  proof: by
  ext f h
  dsimp [finLiftOn]
  induction finChoice q using Quotient.ind
  exact h _ _ e.elim

@[simp]

中文:
引理 finLiftOn_empty
  条件: [e : 是空 ι] (q : 对任意 i, 商 (S i))
  证明: by
  ext f h
  dsimp [finLiftOn]
  induction finChoice q using Quotient.ind
  exact h _ _ e.elim

@[simp]

Depends on / 依赖: Quotient, Quotient.ind, e.elim, finChoice, finLiftOn
-/
lemma finLiftOn_empty [e : IsEmpty ι] (q : forall i, Quotient (S i)) :
    finLiftOn (β := β) q = fun f _ => f e.elim := by
  ext f h
  dsimp [finLiftOn]
  induction finChoice q using Quotient.ind
  exact h _ _ e.elim

@[simp]
/--
lemma `finLiftOn_mk` / 引理 `finLiftOn_mk`

English:
lemma finLiftOn_mk
  given: (a : forall i, α i)
  proof: by
  ext f h
  dsimp [finLiftOn]
  rw [finChoice_eq]
  rfl

中文:
引理 finLiftOn_mk
  条件: (a : 对任意 i, α i)
  证明: by
  ext f h
  dsimp [finLiftOn]
  rw [finChoice_eq]
  rfl

Depends on / 依赖: finChoice_eq, finLiftOn
-/
lemma finLiftOn_mk (a : forall i, α i) :
    finLiftOn (S := S) (β := β) (⟦a ·⟧) = fun f _ => f a := by
  ext f h
  dsimp [finLiftOn]
  rw [finChoice_eq]
  rfl

/-- `Quotient.finChoice` as an equivalence. -/
@[simps]
/--
Definition of `finChoiceEquiv` / `finChoiceEquiv` 的定义

English:
definition finChoiceEquiv
  signature: :
  body: finChoice
  invFun := eval
  left_inv q := by
    refine induction_on_fintype_pi q (fun a => ?_)
    rw [finChoice_eq]
    rfl
  right_inv q := by
    induction q using Quotient.ind
    exact finChoice_eq _

中文:
定义 finChoiceEquiv
  签名: :
  定义体: finChoice
  invFun := eval
  left_inv q := by
    refine induction_on_fintype_pi q (fun a => ?_)
    rw [finChoice_eq]
    rfl
  right_inv q := by
    induction q using Quotient.ind
    exact finChoice_eq _

Depends on / 依赖: finChoice
-/
def finChoiceEquiv :
    (forall i, Quotient (S i)) ≃ @Quotient (forall i, α i) piSetoid where
  toFun := finChoice
  invFun := eval
  left_inv q := by
    refine induction_on_fintype_pi q (fun a => ?_)
    rw [finChoice_eq]
    rfl
  right_inv q := by
    induction q using Quotient.ind
    exact finChoice_eq _

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_elim]
/--
Definition of `finHRecOn` / `finHRecOn` 的定义

English:
definition finHRecOn
  signature: {C : (forall i, Quotient (S i)) -> Sort*}
  body: eval_finChoice q ▸ (finChoice q).hrecOn f h

中文:
定义 finHRecOn
  签名: {C : (对任意 i, 商 (S i)) -> 类型层*}
  定义体: eval_finChoice q ▸ (finChoice q).hrecOn f h

Depends on / 依赖: eval_finChoice, finChoice, hrecOn
-/
def finHRecOn {C : (forall i, Quotient (S i)) -> Sort*}
    (q : forall i, Quotient (S i))
    (f : forall a : forall i, α i, C (⟦a ·⟧))
    (h : forall (a b : forall i, α i), (forall i, a i ≈ b i) -> f a ≍ f b) :
    C q :=
  eval_finChoice q ▸ (finChoice q).hrecOn f h

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_elim]
/--
Definition of `finRecOn` / `finRecOn` 的定义

English:
definition finRecOn
  signature: {C : (forall i, Quotient (S i)) -> Sort*}
  body: finHRecOn q f (eqRec_heq_iff.mp <| heq_of_eq <| h · · ·)

@[simp]

中文:
定义 finRecOn
  签名: {C : (对任意 i, 商 (S i)) -> 类型层*}
  定义体: finHRecOn q f (eqRec_heq_iff.mp <| heq_of_eq <| h · · ·)

@[simp]

Depends on / 依赖: eqRec_heq_iff, eqRec_heq_iff.mp, finHRecOn, heq_of_eq
-/
def finRecOn {C : (forall i, Quotient (S i)) -> Sort*}
    (q : forall i, Quotient (S i))
    (f : forall a : forall i, α i, C (⟦a ·⟧))
    (h : forall (a b : forall i, α i) (h : forall i, a i ≈ b i),
      Eq.ndrec (f a) (funext fun i => Quotient.sound (h i)) = f b) :
    C q :=
  finHRecOn q f (eqRec_heq_iff.mp <| heq_of_eq <| h · · ·)

@[simp]
/--
lemma `finHRecOn_mk` / 引理 `finHRecOn_mk`

English:
lemma finHRecOn_mk
  statement: {C : (forall i, Quotient (S i)) -> Sort*}
  proof: by
  ext f h
  refine eq_of_heq ((eqRec_heq _ _).trans ?_)
  rw [finChoice_eq]
  rfl

@[simp]

中文:
引理 finHRecOn_mk
  结论: {C : (对任意 i, 商 (S i)) -> 类型层*}
  证明: by
  ext f h
  refine eq_of_heq ((eqRec_heq _ _).trans ?_)
  rw [finChoice_eq]
  rfl

@[simp]

Depends on / 依赖: eqRec_heq, eq_of_heq, finChoice_eq
-/
lemma finHRecOn_mk {C : (forall i, Quotient (S i)) -> Sort*}
    (a : forall i, α i) :
    finHRecOn (C := C) (⟦a ·⟧) = fun f _ => f a := by
  ext f h
  refine eq_of_heq ((eqRec_heq _ _).trans ?_)
  rw [finChoice_eq]
  rfl

@[simp]
/--
lemma `finRecOn_mk` / 引理 `finRecOn_mk`

English:
lemma finRecOn_mk
  statement: {C : (forall i, Quotient (S i)) -> Sort*}
  proof: by
  unfold finRecOn
  simp

中文:
引理 finRecOn_mk
  结论: {C : (对任意 i, 商 (S i)) -> 类型层*}
  证明: by
  unfold finRecOn
  simp

Depends on / 依赖: finRecOn
-/
lemma finRecOn_mk {C : (forall i, Quotient (S i)) -> Sort*}
    (a : forall i, α i) :
    finRecOn (C := C) (⟦a ·⟧) = fun f _ => f a := by
  unfold finRecOn
  simp

end Fintype

end Quotient

namespace Trunc
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {α : ι -> Sort*} {β : Sort*}

/--
Definition of `finChoice` / `finChoice` 的定义

English:
definition finChoice
  signature: (q : forall i, Trunc (α i))
  body: Quotient.map' id (fun _ _ _ => trivial) (Quotient.finChoice q)

中文:
定义 finChoice
  签名: (q : 对任意 i, Trunc (α i))
  定义体: Quotient.map' id (fun _ _ _ => trivial) (Quotient.finChoice q)

Depends on / 依赖: Quotient, Quotient.finChoice, Quotient.map, finChoice
-/
def finChoice (q : forall i, Trunc (α i)) : Trunc (forall i, α i) :=
  Quotient.map' id (fun _ _ _ => trivial) (Quotient.finChoice q)

/--
theorem `finChoice_eq` / 定理 `finChoice_eq`

English:
theorem finChoice_eq
  given: (f : forall i, α i)
  statement: (Trunc.finChoice fun i => Trunc.mk (f i)) = Trunc.mk f
  proof: Subsingleton.elim _ _

中文:
定理 finChoice_eq
  条件: (f : 对任意 i, α i)
  结论: (Trunc.finChoice fun i => Trunc.mk (f i)) = Trunc.mk f
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem finChoice_eq (f : forall i, α i) : (Trunc.finChoice fun i => Trunc.mk (f i)) = Trunc.mk f :=
  Subsingleton.elim _ _

/--
Definition of `finLiftOn` / `finLiftOn` 的定义

English:
definition finLiftOn
  signature: (q : forall i, Trunc (α i)) (f : (forall i, α i) -> β) (h : forall (a b : forall i, α i), f a = f b)
  body: Quotient.finLiftOn q f (fun _ _ _ => h _ _)

@[simp]

中文:
定义 finLiftOn
  签名: (q : 对任意 i, Trunc (α i)) (f : (对任意 i, α i) -> β) (h : 对任意 (a b : 对任意 i, α i), f a = f b)
  定义体: Quotient.finLiftOn q f (fun _ _ _ => h _ _)

@[simp]

Depends on / 依赖: Quotient, Quotient.finLiftOn, finLiftOn
-/
def finLiftOn (q : forall i, Trunc (α i)) (f : (forall i, α i) -> β) (h : forall (a b : forall i, α i), f a = f b) : β :=
  Quotient.finLiftOn q f (fun _ _ _ => h _ _)

@[simp]
/--
lemma `finLiftOn_empty` / 引理 `finLiftOn_empty`

English:
lemma finLiftOn_empty
  given: [e : IsEmpty ι] (q : forall i, Trunc (α i))
  proof: funext₂ fun _ _ => congrFun₂ (Quotient.finLiftOn_empty q) _ _

@[simp]

中文:
引理 finLiftOn_empty
  条件: [e : 是空 ι] (q : 对任意 i, Trunc (α i))
  证明: funext₂ fun _ _ => congrFun₂ (Quotient.finLiftOn_empty q) _ _

@[simp]

Depends on / 依赖: e.elim
-/
lemma finLiftOn_empty [e : IsEmpty ι] (q : forall i, Trunc (α i)) :
    finLiftOn (β := β) q = fun f _ => f e.elim :=
  funext₂ fun _ _ => congrFun₂ (Quotient.finLiftOn_empty q) _ _

@[simp]
/--
lemma `finLiftOn_mk` / 引理 `finLiftOn_mk`

English:
lemma finLiftOn_mk
  given: (a : forall i, α i)
  proof: funext₂ fun _ _ => congrFun₂ (Quotient.finLiftOn_mk a) _ _

中文:
引理 finLiftOn_mk
  条件: (a : 对任意 i, α i)
  证明: funext₂ fun _ _ => congrFun₂ (Quotient.finLiftOn_mk a) _ _
-/
lemma finLiftOn_mk (a : forall i, α i) :
    finLiftOn (β := β) (⟦a ·⟧) = fun f _ => f a :=
  funext₂ fun _ _ => congrFun₂ (Quotient.finLiftOn_mk a) _ _

/-- `Trunc.finChoice` as an equivalence. -/
@[simps]
/--
Definition of `finChoiceEquiv` / `finChoiceEquiv` 的定义

English:
definition finChoiceEquiv
  signature: : (forall i, Trunc (α i)) ≃ Trunc (forall i, α i) where
  body: finChoice
  invFun q i := q.map (· i)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 finChoiceEquiv
  签名: : (对任意 i, Trunc (α i)) ≃ Trunc (对任意 i, α i) where
  定义体: finChoice
  invFun q i := q.map (· i)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

Depends on / 依赖: finChoice
-/
def finChoiceEquiv : (forall i, Trunc (α i)) ≃ Trunc (forall i, α i) where
  toFun := finChoice
  invFun q i := q.map (· i)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Recursion principle for `Trunc`s indexed by a finite type. -/
@[elab_as_elim]
/--
Definition of `finRecOn` / `finRecOn` 的定义

English:
definition finRecOn
  signature: {C : (forall i, Trunc (α i)) -> Sort*}
  body: Quotient.finRecOn q (f ·) (fun _ _ _ => h _ _)

中文:
定义 finRecOn
  签名: {C : (对任意 i, Trunc (α i)) -> 类型层*}
  定义体: Quotient.finRecOn q (f ·) (fun _ _ _ => h _ _)

Depends on / 依赖: Quotient, Quotient.finRecOn, finRecOn
-/
def finRecOn {C : (forall i, Trunc (α i)) -> Sort*}
    (q : forall i, Trunc (α i))
    (f : forall a : forall i, α i, C (mk <| a ·))
    (h : forall (a b : forall i, α i), (Eq.ndrec (f a) (funext fun _ => Trunc.eq _ _)) = f b) :
    C q :=
  Quotient.finRecOn q (f ·) (fun _ _ _ => h _ _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `finRecOn_mk` / 引理 `finRecOn_mk`

English:
lemma finRecOn_mk
  statement: {C : (forall i, Trunc (α i)) -> Sort*}
  proof: by
  unfold finRecOn
  simp

中文:
引理 finRecOn_mk
  结论: {C : (对任意 i, Trunc (α i)) -> 类型层*}
  证明: by
  unfold finRecOn
  simp

Depends on / 依赖: finRecOn
-/
lemma finRecOn_mk {C : (forall i, Trunc (α i)) -> Sort*}
    (a : forall i, α i) :
    finRecOn (C := C) (⟦a ·⟧) = fun f _ => f a := by
  unfold finRecOn
  simp

end Trunc
