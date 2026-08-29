/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
module

public import Mathlib.Computability.RecursiveIn
public import Mathlib.Order.Antisymmetrization

/-!
# Turing degrees

This file defines Turing reducibility and equivalence, proves that Turing equivalence is an
equivalence relation, and defines Turing degrees as the quotient under this relation.

## Main definitions

- `TuringReducible`: A relation defining Turing reducibility between partial functions.
- `TuringEquivalent`: An equivalence relation defining Turing equivalence between partial functions.
- `TuringDegree`: The type of Turing degrees, defined as the quotient of partial functions under
  `TuringEquivalent`.

## Notation

- `f ≤ᵀ g` : `f` is Turing reducible to `g`.
- `f ≡ᵀ g` : `f` is Turing equivalent to `g`.

## References

* [Odifreddi1989] Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers,
  Vol. I*. Springer-Verlag, 1989.

## Tags

Computability, Oracle, Turing Degrees, Reducibility, Equivalence Relation
-/

public section

open Primrec

variable {f g h : Nat ->. Nat}

/--
Definition of `TuringReducible` / `TuringReducible` 的定义

English:
abbreviation TuringReducible
  signature: (f g : Nat ->. Nat)
  body: RecursiveIn {g} f

中文:
缩写 TuringReducible
  签名: (f g : 自然数 ->. 自然数)
  定义体: RecursiveIn {g} f

Depends on / 依赖: RecursiveIn
-/
abbrev TuringReducible (f g : Nat ->. Nat) : Prop :=
  RecursiveIn {g} f

/--
Definition of `TuringEquivalent` / `TuringEquivalent` 的定义

English:
abbreviation TuringEquivalent
  signature: (f g : Nat ->. Nat)
  body: AntisymmRel TuringReducible f g

@[inherit_doc] scoped[Computability] infix:50 " <=ᵀ " => TuringReducible
@[inherit_doc] scoped[Computability] infix:50 " ≡ᵀ " => TuringEquivalent

中文:
缩写 TuringEquivalent
  签名: (f g : 自然数 ->. 自然数)
  定义体: AntisymmRel TuringReducible f g

@[inherit_doc] scoped[Computability] infix:50 " <=ᵀ " => TuringReducible
@[inherit_doc] scoped[Computability] infix:50 " ≡ᵀ " => TuringEquivalent

Depends on / 依赖: AntisymmRel, TuringReducible
-/
abbrev TuringEquivalent (f g : Nat ->. Nat) : Prop :=
  AntisymmRel TuringReducible f g

@[inherit_doc] scoped[Computability] infix:50 " <=ᵀ " => TuringReducible
@[inherit_doc] scoped[Computability] infix:50 " ≡ᵀ " => TuringEquivalent

open scoped Computability

/--
lemma `Partrec.turingReducible` / 引理 `Partrec.turingReducible`

English:
lemma Partrec.turingReducible
  given: (pF : Partrec f)
  statement: f <=ᵀ g
  proof: pF.recursiveIn

中文:
引理 Partrec.turingReducible
  条件: (pF : Partrec f)
  结论: f <=ᵀ g
  证明: pF.recursiveIn

Depends on / 依赖: pF.recursiveIn, recursiveIn
-/
lemma Partrec.turingReducible (pF : Partrec f) : f <=ᵀ g :=
  pF.recursiveIn

/--
lemma `TuringReducible.partrec_of_const` / 引理 `TuringReducible.partrec_of_const`

English:
lemma TuringReducible.partrec_of_const
  given: {s} (hf : f <=ᵀ fun _ => s)
  statement: Partrec f
  proof: RecursiveIn.partrec_of_const hf

中文:
引理 TuringReducible.partrec_of_const
  条件: {s} (hf : f <=ᵀ fun _ => s)
  结论: Partrec f
  证明: RecursiveIn.partrec_of_const hf

Depends on / 依赖: RecursiveIn, RecursiveIn.partrec_of_const, partrec_of_const
-/
lemma TuringReducible.partrec_of_const {s} (hf : f <=ᵀ fun _ => s) : Partrec f :=
  RecursiveIn.partrec_of_const hf

/--
theorem `partrec_iff_forall_turingReducible` / 定理 `partrec_iff_forall_turingReducible`

English:
theorem partrec_iff_forall_turingReducible
  statement: Partrec f ↔ forall g, f <=ᵀ g
  proof: .partrec_of_const⟩ ⟨fun hf _ => hf.turingReducible, fun hf => hf (fun _ => .none)

中文:
定理 partrec_iff_forall_turingReducible
  结论: Partrec f ↔ 对任意 g, f <=ᵀ g
  证明: .partrec_of_const⟩ ⟨fun hf _ => hf.turingReducible, fun hf => hf (fun _ => .none)

Depends on / 依赖: hf.turingReducible, partrec_of_const, turingReducible
-/
theorem partrec_iff_forall_turingReducible : Partrec f ↔ forall g, f <=ᵀ g :=
.partrec_of_const⟩ ⟨fun hf _ => hf.turingReducible, fun hf => hf (fun _ => .none)

/--
theorem `TuringReducible.refl` / 定理 `TuringReducible.refl`

English:
theorem TuringReducible.refl
  given: (f : Nat ->. Nat)
  statement: f <=ᵀ f
  proof: .oracle _ by simp

中文:
定理 TuringReducible.refl
  条件: (f : 自然数 ->. 自然数)
  结论: f <=ᵀ f
  证明: .oracle _ by simp
-/
protected theorem TuringReducible.refl (f : Nat ->. Nat) : f <=ᵀ f := .oracle _ by simp
/--
theorem `TuringReducible.rfl` / 定理 `TuringReducible.rfl`

English:
theorem TuringReducible.rfl
  statement: f <=ᵀ f
  proof: .refl _

中文:
定理 TuringReducible.rfl
  结论: f <=ᵀ f
  证明: .refl _
-/
protected theorem TuringReducible.rfl : f <=ᵀ f := .refl _

/--
theorem `TuringReducible.trans` / 定理 `TuringReducible.trans`

English:
theorem TuringReducible.trans
  given: (hg : f <=ᵀ g) (hh : g <=ᵀ h)
  statement: f <=ᵀ h
  proof: hg.subst (by simpa using hh)

中文:
定理 TuringReducible.trans
  条件: (hg : f <=ᵀ g) (hh : g <=ᵀ h)
  结论: f <=ᵀ h
  证明: hg.subst (by simpa using hh)

Depends on / 依赖: hg.subst
-/
theorem TuringReducible.trans (hg : f <=ᵀ g) (hh : g <=ᵀ h) : f <=ᵀ h :=
  hg.subst (by simpa using hh)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPreorder (Nat ->. Nat) TuringReducible
  body: .rfl
  trans := @TuringReducible.trans

中文:
实例 :
  签名: IsPreorder (自然数 ->. 自然数) TuringReducible
  定义体: .rfl
  trans := @TuringReducible.trans
-/
instance : IsPreorder (Nat ->. Nat) TuringReducible where
  refl _ := .rfl
  trans := @TuringReducible.trans

/--
theorem `TuringEquivalent.equivalence` / 定理 `TuringEquivalent.equivalence`

English:
theorem TuringEquivalent.equivalence
  statement: Equivalence TuringEquivalent
  proof: (AntisymmRel.setoid _ _).iseqv

@[refl]

中文:
定理 TuringEquivalent.equivalence
  结论: Equivalence TuringEquivalent
  证明: (AntisymmRel.setoid _ _).iseqv

@[refl]

Depends on / 依赖: AntisymmRel, AntisymmRel.setoid, setoid
-/
theorem TuringEquivalent.equivalence : Equivalence TuringEquivalent :=
  (AntisymmRel.setoid _ _).iseqv

@[refl]
/--
theorem `TuringEquivalent.refl` / 定理 `TuringEquivalent.refl`

English:
theorem TuringEquivalent.refl
  given: (f : Nat ->. Nat)
  statement: f ≡ᵀ f
  proof: Equivalence.refl equivalence f

@[symm]

中文:
定理 TuringEquivalent.refl
  条件: (f : 自然数 ->. 自然数)
  结论: f ≡ᵀ f
  证明: Equivalence.refl equivalence f

@[symm]
-/
protected theorem TuringEquivalent.refl (f : Nat ->. Nat) : f ≡ᵀ f :=
  Equivalence.refl equivalence f

@[symm]
/--
theorem `TuringEquivalent.symm` / 定理 `TuringEquivalent.symm`

English:
theorem TuringEquivalent.symm
  given: {f g : Nat ->. Nat} (h : f ≡ᵀ g)
  statement: g ≡ᵀ f
  proof: Equivalence.symm equivalence h

@[trans]

中文:
定理 TuringEquivalent.symm
  条件: {f g : 自然数 ->. 自然数} (h : f ≡ᵀ g)
  结论: g ≡ᵀ f
  证明: Equivalence.symm equivalence h

@[trans]

Depends on / 依赖: Equivalence, Equivalence.symm, equivalence
-/
theorem TuringEquivalent.symm {f g : Nat ->. Nat} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  Equivalence.symm equivalence h

@[trans]
/--
theorem `TuringEquivalent.trans` / 定理 `TuringEquivalent.trans`

English:
theorem TuringEquivalent.trans
  given: (f g h : Nat ->. Nat) (h₁ : f ≡ᵀ g) (h₂ : g ≡ᵀ h)
  statement: f ≡ᵀ h
  proof: Equivalence.trans equivalence h₁ h₂

中文:
定理 TuringEquivalent.trans
  条件: (f g h : 自然数 ->. 自然数) (h₁ : f ≡ᵀ g) (h₂ : g ≡ᵀ h)
  结论: f ≡ᵀ h
  证明: Equivalence.trans equivalence h₁ h₂

Depends on / 依赖: Equivalence, Equivalence.trans, equivalence
-/
theorem TuringEquivalent.trans (f g h : Nat ->. Nat) (h₁ : f ≡ᵀ g) (h₂ : g ≡ᵀ h) : f ≡ᵀ h :=
  Equivalence.trans equivalence h₁ h₂

/--
Definition of `TuringDegree` / `TuringDegree` 的定义

English:
abbreviation TuringDegree
  body: Antisymmetrization _ TuringReducible

中文:
缩写 TuringDegree
  定义体: Antisymmetrization _ TuringReducible

Depends on / 依赖: Antisymmetrization, TuringReducible
-/
abbrev TuringDegree :=
  Antisymmetrization _ TuringReducible

set_option backward.privateInPublic true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (Nat ->. Nat)
  body: TuringReducible
  le_refl := .refl
  le_trans _ _ _ := TuringReducible.trans

中文:
实例 :
  签名: Preorder (自然数 ->. 自然数)
  定义体: TuringReducible
  le_refl := .refl
  le_trans _ _ _ := TuringReducible.trans
-/
private instance : Preorder (Nat ->. Nat) where
  le := TuringReducible
  le_refl := .refl
  le_trans _ _ _ := TuringReducible.trans

/--
Instance `TuringDegree.instPartialOrder` / 实例 `TuringDegree.instPartialOrder`

English:
instance TuringDegree.instPartialOrder
  signature: : PartialOrder TuringDegree
  body: instPartialOrderAntisymmetrization

中文:
实例 TuringDegree.instPartialOrder
  签名: : PartialOrder TuringDegree
  定义体: instPartialOrderAntisymmetrization

Depends on / 依赖: instPartialOrderAntisymmetrization
-/
instance TuringDegree.instPartialOrder : PartialOrder TuringDegree :=
  instPartialOrderAntisymmetrization
