/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Nat.Notation

/-!
# Relations holding pairwise

This file defines pairwise relations.

## Main declarations

* `Pairwise`: `Pairwise r` states that `r i j` for all `i ≠ j`.
* `Set.Pairwise`: `s.Pairwise r` states that `r i j` for all `i ≠ j` with `i, j ∈ s`.
-/

@[expose] public section

open Function

variable {α β ι : Type*} {r p : α -> α -> Prop}

section Pairwise

variable {f : ι -> α} {s : Set α} {a b : α}

/--
Definition of `Pairwise` / `Pairwise` 的定义

English:
definition Pairwise
  signature: (r : α -> α -> Prop)
  body: forall ⦃i j⦄, i != j -> r i j

中文:
定义 Pairwise
  签名: (r : α -> α -> 命题)
  定义体: forall ⦃i j⦄, i != j -> r i j
-/
def Pairwise (r : α -> α -> Prop) :=
  forall ⦃i j⦄, i != j -> r i j

/--
theorem `Pairwise.mono` / 定理 `Pairwise.mono`

English:
theorem Pairwise.mono
  given: (hr : Pairwise r) (h : forall ⦃i j⦄, r i j -> p i j)
  statement: Pairwise p
  proof: fun _i _j hij => h hr hij

中文:
定理 Pairwise.mono
  条件: (hr : Pairwise r) (h : 对任意 ⦃i j⦄, r i j -> p i j)
  结论: Pairwise p
  证明: fun _i _j hij => h hr hij
-/
theorem Pairwise.mono (hr : Pairwise r) (h : forall ⦃i j⦄, r i j -> p i j) : Pairwise p :=
fun _i _j hij => h hr hij

/--
theorem `Pairwise.eq` / 定理 `Pairwise.eq`

English:
theorem Pairwise.eq
  given: (h : Pairwise r)
  statement: ¬r a b -> a = b
  proof: not_imp_comm.1 @h _ _

@[simp]

中文:
定理 Pairwise.eq
  条件: (h : Pairwise r)
  结论: ¬r a b -> a = b
  证明: not_imp_comm.1 @h _ _

@[simp]
-/
protected theorem Pairwise.eq (h : Pairwise r) : ¬r a b -> a = b :=
not_imp_comm.1 @h _ _

@[simp]
/--
lemma `Subsingleton.pairwise` / 引理 `Subsingleton.pairwise`

English:
lemma Subsingleton.pairwise
  given: [Subsingleton α]
  statement: Pairwise r
  proof: fun _ _ h => False.elim h.elim Subsingleton.elim _ _

中文:
引理 Subsingleton.pairwise
  条件: [Subsingleton α]
  结论: Pairwise r
  证明: fun _ _ h => False.elim h.elim Subsingleton.elim _ _
-/
protected lemma Subsingleton.pairwise [Subsingleton α] : Pairwise r :=
fun _ _ h => False.elim h.elim Subsingleton.elim _ _

/--
theorem `Function.injective_iff_pairwise_ne` / 定理 `Function.injective_iff_pairwise_ne`

English:
theorem Function.injective_iff_pairwise_ne
  statement: Injective f ↔ Pairwise ((· != ·) on f)
  proof: forall₂_congr fun _i _j => not_imp_not.symm

alias ⟨Function.Injective.pairwise_ne, _⟩ := Function.injective_iff_pairwise_ne

中文:
定理 Function.injective_iff_pairwise_ne
  结论: Injective f ↔ Pairwise ((· != ·) on f)
  证明: forall₂_congr fun _i _j => not_imp_not.symm

alias ⟨Function.Injective.pairwise_ne, _⟩ := Function.injective_iff_pairwise_ne

Depends on / 依赖: not_imp_not, not_imp_not.symm
-/
theorem Function.injective_iff_pairwise_ne : Injective f ↔ Pairwise ((· != ·) on f) :=
  forall₂_congr fun _i _j => not_imp_not.symm

alias ⟨Function.Injective.pairwise_ne, _⟩ := Function.injective_iff_pairwise_ne

/--
lemma `Pairwise.comp_of_injective` / 引理 `Pairwise.comp_of_injective`

English:
lemma Pairwise.comp_of_injective
  given: (hr : Pairwise r) {f : β -> α} (hf : Injective f)
  proof: fun _ _ h => hr hf.ne h

中文:
引理 Pairwise.comp_of_injective
  条件: (hr : Pairwise r) {f : β -> α} (hf : Injective f)
  证明: fun _ _ h => hr hf.ne h

Depends on / 依赖: hf.ne
-/
lemma Pairwise.comp_of_injective (hr : Pairwise r) {f : β -> α} (hf : Injective f) :
    Pairwise (r on f) :=
fun _ _ h => hr hf.ne h

/--
lemma `Pairwise.of_comp_of_surjective` / 引理 `Pairwise.of_comp_of_surjective`

English:
lemma Pairwise.of_comp_of_surjective
  given: {f : β -> α} (hr : Pairwise (r on f)) (hf : Surjective f)
  proof: hf.forall₂.2 fun _ _ h => hr ne_of_apply_ne f h

中文:
引理 Pairwise.of_comp_of_surjective
  条件: {f : β -> α} (hr : Pairwise (r on f)) (hf : Surjective f)
  证明: hf.forall₂.2 fun _ _ h => hr ne_of_apply_ne f h

Depends on / 依赖: hf.forall, ne_of_apply_ne
-/
lemma Pairwise.of_comp_of_surjective {f : β -> α} (hr : Pairwise (r on f)) (hf : Surjective f) :
Pairwise r := hf.forall₂.2 fun _ _ h => hr ne_of_apply_ne f h

/--
lemma `Function.Bijective.pairwise_comp_iff` / 引理 `Function.Bijective.pairwise_comp_iff`

English:
lemma Function.Bijective.pairwise_comp_iff
  given: {f : β -> α} (hf : Bijective f)
  proof: ⟨fun hr => hr.of_comp_of_surjective hf.surjective, fun hr => hr.comp_of_injective hf.injective⟩

中文:
引理 Function.Bijective.pairwise_comp_iff
  条件: {f : β -> α} (hf : Bijective f)
  证明: ⟨fun hr => hr.of_comp_of_surjective hf.surjective, fun hr => hr.comp_of_injective hf.injective⟩

Depends on / 依赖: comp_of_injective, hf.injective, hf.surjective, hr.comp_of_injective, hr.of_comp_of_surjective, injective, of_comp_of_surjective, surjective
-/
lemma Function.Bijective.pairwise_comp_iff {f : β -> α} (hf : Bijective f) :
    Pairwise (r on f) ↔ Pairwise r :=
  ⟨fun hr => hr.of_comp_of_surjective hf.surjective, fun hr => hr.comp_of_injective hf.injective⟩

/--
theorem `pairwise_fin_succ_iff` / 定理 `pairwise_fin_succ_iff`

English:
theorem pairwise_fin_succ_iff
  given: {n : Nat} {R : Fin n.succ -> Fin n.succ -> Prop}
  proof: ⟨
    fun _ => h (Fin.succ_ne_zero _), fun _ => h (Fin.succ_ne_zero _).symm,
fun _i _j hij => h Fin.succ_inj.not.2 hij⟩
  mpr
  | ⟨hi, hj, h⟩ =>
    Fin.cases
      (Fin.cases nofun fun j _ => hj j)
      (fun i => Fin.cases (fun _ => hi i) fun _j hij => h (ne_of_apply_ne _ hij))

中文:
定理 pairwise_fin_succ_iff
  条件: {n : 自然数} {R : Fin n.succ -> Fin n.succ -> 命题}
  证明: ⟨
    fun _ => h (Fin.succ_ne_zero _), fun _ => h (Fin.succ_ne_zero _).symm,
fun _i _j hij => h Fin.succ_inj.not.2 hij⟩
  mpr
  | ⟨hi, hj, h⟩ =>
    Fin.cases
      (Fin.cases nofun fun j _ => hj j)
      (fun i => Fin.cases (fun _ => hi i) fun _j hij => h (ne_of_apply_ne _ hij))
-/
theorem pairwise_fin_succ_iff {n : Nat} {R : Fin n.succ -> Fin n.succ -> Prop} :
    Pairwise R ↔
      (forall i, R (Fin.succ i) 0) ∧ (forall j, R 0 (Fin.succ j)) ∧
      Pairwise fun i j => R (Fin.succ i) (Fin.succ j) where
  mp h := ⟨
    fun _ => h (Fin.succ_ne_zero _), fun _ => h (Fin.succ_ne_zero _).symm,
fun _i _j hij => h Fin.succ_inj.not.2 hij⟩
  mpr
  | ⟨hi, hj, h⟩ =>
    Fin.cases
      (Fin.cases nofun fun j _ => hj j)
      (fun i => Fin.cases (fun _ => hi i) fun _j hij => h (ne_of_apply_ne _ hij))

/--
theorem `pairwise_fin_succ_iff_of_isSymm` / 定理 `pairwise_fin_succ_iff_of_isSymm`

English:
theorem pairwise_fin_succ_iff_of_isSymm
  given: {n : Nat} {R : Fin n.succ -> Fin n.succ -> Prop} [Std.Symm R]
  proof: by
  simp only [pairwise_fin_succ_iff, comm (b := 0) (r := R), and_self_left]

中文:
定理 pairwise_fin_succ_iff_of_isSymm
  条件: {n : 自然数} {R : Fin n.succ -> Fin n.succ -> 命题} [Std.Symm R]
  证明: by
  simp only [pairwise_fin_succ_iff, comm (b := 0) (r := R), and_self_left]

Depends on / 依赖: and_self_left, pairwise_fin_succ_iff
-/
theorem pairwise_fin_succ_iff_of_isSymm {n : Nat} {R : Fin n.succ -> Fin n.succ -> Prop} [Std.Symm R] :
    Pairwise R ↔ (forall j, R 0 (Fin.succ j)) ∧ Pairwise fun i j => R (Fin.succ i) (Fin.succ j) := by
  simp only [pairwise_fin_succ_iff, comm (b := 0) (r := R), and_self_left]

namespace Set

/--
Definition of `Pairwise` / `Pairwise` 的定义

English:
definition Pairwise
  signature: (s : Set α) (r : α -> α -> Prop)
  body: forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x != y -> r x y

中文:
定义 Pairwise
  签名: (s : Set α) (r : α -> α -> 命题)
  定义体: forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x != y -> r x y
-/
protected def Pairwise (s : Set α) (r : α -> α -> Prop) :=
  forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x != y -> r x y

/--
theorem `pairwise_of_forall` / 定理 `pairwise_of_forall`

English:
theorem pairwise_of_forall
  given: (s : Set α) (r : α -> α -> Prop) (h : forall a b, r a b)
  statement: s.Pairwise r
  proof: fun a _ b _ _ => h a b

中文:
定理 pairwise_of_forall
  条件: (s : Set α) (r : α -> α -> 命题) (h : 对任意 a b, r a b)
  结论: s.Pairwise r
  证明: fun a _ b _ _ => h a b
-/
theorem pairwise_of_forall (s : Set α) (r : α -> α -> Prop) (h : forall a b, r a b) : s.Pairwise r :=
  fun a _ b _ _ => h a b

/--
theorem `Pairwise.imp_on` / 定理 `Pairwise.imp_on`

English:
theorem Pairwise.imp_on
  given: (h : s.Pairwise r) (hrp : s.Pairwise fun ⦃a b : α⦄ => r a b -> p a b)
  proof: fun _a ha _b hb hab => hrp ha hb hab h ha hb hab

中文:
定理 Pairwise.imp_on
  条件: (h : s.Pairwise r) (hrp : s.Pairwise fun ⦃a b : α⦄ => r a b -> p a b)
  证明: fun _a ha _b hb hab => hrp ha hb hab h ha hb hab
-/
theorem Pairwise.imp_on (h : s.Pairwise r) (hrp : s.Pairwise fun ⦃a b : α⦄ => r a b -> p a b) :
    s.Pairwise p :=
fun _a ha _b hb hab => hrp ha hb hab h ha hb hab

/--
theorem `Pairwise.imp` / 定理 `Pairwise.imp`

English:
theorem Pairwise.imp
  given: (h : s.Pairwise r) (hpq : forall ⦃a b : α⦄, r a b -> p a b)
  statement: s.Pairwise p
  proof: h.imp_on pairwise_of_forall s _ hpq

中文:
定理 Pairwise.imp
  条件: (h : s.Pairwise r) (hpq : 对任意 ⦃a b : α⦄, r a b -> p a b)
  结论: s.Pairwise p
  证明: h.imp_on pairwise_of_forall s _ hpq

Depends on / 依赖: h.imp_on, imp_on, pairwise_of_forall
-/
theorem Pairwise.imp (h : s.Pairwise r) (hpq : forall ⦃a b : α⦄, r a b -> p a b) : s.Pairwise p :=
h.imp_on pairwise_of_forall s _ hpq

/--
theorem `Pairwise.eq` / 定理 `Pairwise.eq`

English:
theorem Pairwise.eq
  given: (hs : s.Pairwise r) (ha : a in s) (hb : b in s) (h : ¬r a b)
  statement: a = b
  proof: of_not_not fun hab => h hs ha hb hab

中文:
定理 Pairwise.eq
  条件: (hs : s.Pairwise r) (ha : a in s) (hb : b in s) (h : ¬r a b)
  结论: a = b
  证明: of_not_not fun hab => h hs ha hb hab
-/
protected theorem Pairwise.eq (hs : s.Pairwise r) (ha : a in s) (hb : b in s) (h : ¬r a b) : a = b :=
of_not_not fun hab => h hs ha hb hab

/--
theorem `_root_.Std.Refl.set_pairwise_iff` / 定理 `_root_.Std.Refl.set_pairwise_iff`

English:
theorem _root_.Std.Refl.set_pairwise_iff
  given: [Std.Refl r]
  proof: forall₄_congr fun a _ _ _ => or_iff_not_imp_left.symm.trans or_iff_right_of_imp Eq.ndrec
    refl a

@[deprecated (since := "2026-03-27")]
alias _root_.Reflexive.set_pairwise_iff := Std.Refl.set_pairwise_iff

中文:
定理 _root_.Std.Refl.set_pairwise_iff
  条件: [Std.Refl r]
  证明: forall₄_congr fun a _ _ _ => or_iff_not_imp_left.symm.trans or_iff_right_of_imp Eq.ndrec
    refl a

@[deprecated (since := "2026-03-27")]
alias _root_.Reflexive.set_pairwise_iff := Std.Refl.set_pairwise_iff

Depends on / 依赖: Eq.ndrec, or_iff_not_imp_left, or_iff_not_imp_left.symm.trans, or_iff_right_of_imp
-/
theorem _root_.Std.Refl.set_pairwise_iff [Std.Refl r] :
    s.Pairwise r ↔ forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> r a b :=
forall₄_congr fun a _ _ _ => or_iff_not_imp_left.symm.trans or_iff_right_of_imp Eq.ndrec
    refl a

@[deprecated (since := "2026-03-27")]
alias _root_.Reflexive.set_pairwise_iff := Std.Refl.set_pairwise_iff

/--
theorem `Pairwise.on_injective` / 定理 `Pairwise.on_injective`

English:
theorem Pairwise.on_injective
  given: (hs : s.Pairwise r) (hf : Function.Injective f) (hfs : forall x, f x in s)
  proof: fun i j hij => hs (hfs i) (hfs j) (hf.ne hij)

中文:
定理 Pairwise.on_injective
  条件: (hs : s.Pairwise r) (hf : Function.Injective f) (hfs : 对任意 x, f x in s)
  证明: fun i j hij => hs (hfs i) (hfs j) (hf.ne hij)

Depends on / 依赖: hf.ne
-/
theorem Pairwise.on_injective (hs : s.Pairwise r) (hf : Function.Injective f) (hfs : forall x, f x in s) :
    Pairwise (r on f) := fun i j hij => hs (hfs i) (hfs j) (hf.ne hij)

end Set

/--
theorem `Pairwise.set_pairwise` / 定理 `Pairwise.set_pairwise`

English:
theorem Pairwise.set_pairwise
  given: (h : Pairwise r) (s : Set α)
  statement: s.Pairwise r
  proof: fun _ _ _ _ w => h w

中文:
定理 Pairwise.set_pairwise
  条件: (h : Pairwise r) (s : Set α)
  结论: s.Pairwise r
  证明: fun _ _ _ _ w => h w
-/
theorem Pairwise.set_pairwise (h : Pairwise r) (s : Set α) : s.Pairwise r := fun _ _ _ _ w => h w

end Pairwise
