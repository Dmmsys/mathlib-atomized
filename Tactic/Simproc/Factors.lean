/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Eric Wieser
-/
module

import all Mathlib.Tactic.NormNum.Prime -- for accessing `evalMinFac.core`
public import Mathlib.Data.Nat.Factors
public import Mathlib.Tactic.NormNum.Prime

/-!
# `simproc` for `Nat.primeFactorsList`

Note that since `norm_num` can only produce numerals,
we can't register this as a `norm_num` extension.
-/

public meta section

open Nat

namespace Mathlib.Meta.Simproc
open Mathlib.Meta.NormNum

/--
Definition of `FactorsHelper` / `FactorsHelper` 的定义

English:
definition FactorsHelper
  signature: (n p : Nat) (l : List Nat)
  body: p.Prime -> (p :: l).IsChain (· <= ·) ∧ (forall a in l, Nat.Prime a) ∧ l.prod = n

中文:
定义 FactorsHelper
  签名: (n p : 自然数) (l : List 自然数)
  定义体: p.Prime -> (p :: l).IsChain (· <= ·) ∧ (forall a in l, Nat.Prime a) ∧ l.prod = n

Depends on / 依赖: IsChain, Nat.Prime, l.prod, p.Prime
-/
def FactorsHelper (n p : Nat) (l : List Nat) : Prop :=
  p.Prime -> (p :: l).IsChain (· <= ·) ∧ (forall a in l, Nat.Prime a) ∧ l.prod = n


/--
theorem `FactorsHelper.nil` / 定理 `FactorsHelper.nil`

English:
theorem FactorsHelper.nil
  given: {a : Nat}
  statement: FactorsHelper 1 a []
  proof: fun _ =>
  ⟨.singleton _, List.forall_mem_nil _, List.prod_nil⟩

中文:
定理 FactorsHelper.nil
  条件: {a : 自然数}
  结论: FactorsHelper 1 a []
  证明: fun _ =>
  ⟨.singleton _, List.forall_mem_nil _, List.prod_nil⟩
-/
theorem FactorsHelper.nil {a : Nat} : FactorsHelper 1 a [] := fun _ =>
  ⟨.singleton _, List.forall_mem_nil _, List.prod_nil⟩

/--
theorem `FactorsHelper.cons_of_le` / 定理 `FactorsHelper.cons_of_le`

English:
theorem FactorsHelper.cons_of_le
  proof: fun pa =>
  have pb : b.Prime := Nat.prime_def_minFac.2 ⟨le_trans pa.two_le h₂, h₃⟩
  let ⟨f₁, f₂, f₃⟩ := H pb
  ⟨List.IsChain.cons_cons h₂ f₁,
    fun _ h => (List.eq_or_mem_of_mem_cons h).elim (fun e => e.symm ▸ pb) (f₂ _),
    by rw [List.prod_cons, f₃, h₁.out, cast_id]⟩

中文:
定理 FactorsHelper.cons_of_le
  证明: fun pa =>
  have pb : b.Prime := Nat.prime_def_minFac.2 ⟨le_trans pa.two_le h₂, h₃⟩
  let ⟨f₁, f₂, f₃⟩ := H pb
  ⟨List.IsChain.cons_cons h₂ f₁,
    fun _ h => (List.eq_or_mem_of_mem_cons h).elim (fun e => e.symm ▸ pb) (f₂ _),
    by rw [List.prod_cons, f₃, h₁.out, cast_id]⟩
-/
theorem FactorsHelper.cons_of_le
    {n m : Nat} (a : Nat) {b : Nat} {l : List Nat} (h₁ : IsNat (b * m) n) (h₂ : a <= b)
    (h₃ : minFac b = b) (H : FactorsHelper m b l) : FactorsHelper n a (b :: l) := fun pa =>
  have pb : b.Prime := Nat.prime_def_minFac.2 ⟨le_trans pa.two_le h₂, h₃⟩
  let ⟨f₁, f₂, f₃⟩ := H pb
  ⟨List.IsChain.cons_cons h₂ f₁,
    fun _ h => (List.eq_or_mem_of_mem_cons h).elim (fun e => e.symm ▸ pb) (f₂ _),
    by rw [List.prod_cons, f₃, h₁.out, cast_id]⟩

/--
theorem `FactorsHelper.cons` / 定理 `FactorsHelper.cons`

English:
theorem FactorsHelper.cons
  proof: H.cons_of_le _ h₁ (Nat.blt_eq.mp h₂).le h₃.out

中文:
定理 FactorsHelper.cons
  证明: H.cons_of_le _ h₁ (Nat.blt_eq.mp h₂).le h₃.out

Depends on / 依赖: H.cons_of_le, Nat.blt_eq.mp, blt_eq, cons_of_le
-/
theorem FactorsHelper.cons
    {n m : Nat} {a : Nat} (b : Nat) {l : List Nat} (h₁ : IsNat (b * m) n) (h₂ : Nat.blt a b)
    (h₃ : IsNat (minFac b) b) (H : FactorsHelper m b l) : FactorsHelper n a (b :: l) :=
  H.cons_of_le _ h₁ (Nat.blt_eq.mp h₂).le h₃.out

/--
theorem `FactorsHelper.singleton` / 定理 `FactorsHelper.singleton`

English:
theorem FactorsHelper.singleton
  given: (n : Nat) {a : Nat} (h₁ : Nat.blt a n) (h₂ : IsNat (minFac n) n)
  proof: FactorsHelper.nil.cons _ ⟨mul_one _⟩ h₁ h₂

中文:
定理 FactorsHelper.singleton
  条件: (n : 自然数) {a : 自然数} (h₁ : 自然数.blt a n) (h₂ : Is自然数 (minFac n) n)
  证明: FactorsHelper.nil.cons _ ⟨mul_one _⟩ h₁ h₂

Depends on / 依赖: FactorsHelper, FactorsHelper.nil.cons, mul_one
-/
theorem FactorsHelper.singleton (n : Nat) {a : Nat} (h₁ : Nat.blt a n) (h₂ : IsNat (minFac n) n) :
    FactorsHelper n a [n] :=
  FactorsHelper.nil.cons _ ⟨mul_one _⟩ h₁ h₂

/--
theorem `FactorsHelper.cons_self` / 定理 `FactorsHelper.cons_self`

English:
theorem FactorsHelper.cons_self
  statement: {n m : Nat} (a : Nat) {l : List Nat}
  proof: fun pa =>
  H.cons_of_le _ h le_rfl (Nat.prime_def_minFac.1 pa).2 pa

中文:
定理 FactorsHelper.cons_self
  结论: {n m : 自然数} (a : 自然数) {l : List 自然数}
  证明: fun pa =>
  H.cons_of_le _ h le_rfl (Nat.prime_def_minFac.1 pa).2 pa
-/
theorem FactorsHelper.cons_self {n m : Nat} (a : Nat) {l : List Nat}
    (h : IsNat (a * m) n) (H : FactorsHelper m a l) :
    FactorsHelper n a (a :: l) := fun pa =>
  H.cons_of_le _ h le_rfl (Nat.prime_def_minFac.1 pa).2 pa

/--
theorem `FactorsHelper.singleton_self` / 定理 `FactorsHelper.singleton_self`

English:
theorem FactorsHelper.singleton_self
  given: (a : Nat)
  statement: FactorsHelper a a [a]
  proof: FactorsHelper.nil.cons_self _ ⟨mul_one _⟩

中文:
定理 FactorsHelper.singleton_self
  条件: (a : 自然数)
  结论: FactorsHelper a a [a]
  证明: FactorsHelper.nil.cons_self _ ⟨mul_one _⟩

Depends on / 依赖: FactorsHelper, FactorsHelper.nil.cons_self, cons_self, mul_one
-/
theorem FactorsHelper.singleton_self (a : Nat) : FactorsHelper a a [a] :=
  FactorsHelper.nil.cons_self _ ⟨mul_one _⟩

/--
theorem `FactorsHelper.primeFactorsList_eq` / 定理 `FactorsHelper.primeFactorsList_eq`

English:
theorem FactorsHelper.primeFactorsList_eq
  given: {n : Nat} {l : List Nat} (H : FactorsHelper n 2 l)
  proof: let ⟨h₁, h₂, h₃⟩ := H Nat.prime_two
  have := List.isChain_iff_pairwise.1 (@List.IsChain.tail _ _ (_ :: _) h₁)
  ((Nat.primeFactorsList_unique h₃ h₂).eq_of_pairwise'
     this (Nat.primeFactorsList_sorted _).pairwise).symm

中文:
定理 FactorsHelper.primeFactorsList_eq
  条件: {n : 自然数} {l : List 自然数} (H : FactorsHelper n 2 l)
  证明: let ⟨h₁, h₂, h₃⟩ := H Nat.prime_two
  have := List.isChain_iff_pairwise.1 (@List.IsChain.tail _ _ (_ :: _) h₁)
  ((Nat.primeFactorsList_unique h₃ h₂).eq_of_pairwise'
     this (Nat.primeFactorsList_sorted _).pairwise).symm

Depends on / 依赖: IsChain, List.IsChain.tail, List.isChain_iff_pairwise, Nat.primeFactorsList_sorted, Nat.primeFactorsList_unique, Nat.prime_two, eq_of_pairwise, isChain_iff_pairwise, pairwise, primeFactorsList_sorted, primeFactorsList_unique, prime_two
-/
theorem FactorsHelper.primeFactorsList_eq {n : Nat} {l : List Nat} (H : FactorsHelper n 2 l) :
    Nat.primeFactorsList n = l :=
  let ⟨h₁, h₂, h₃⟩ := H Nat.prime_two
  have := List.isChain_iff_pairwise.1 (@List.IsChain.tail _ _ (_ :: _) h₁)
  ((Nat.primeFactorsList_unique h₃ h₂).eq_of_pairwise'
     this (Nat.primeFactorsList_sorted _).pairwise).symm

open Lean Elab Tactic Qq

/--
Definition of `evalPrimeFactorsListAux` / `evalPrimeFactorsListAux` 的定义

English:
definition evalPrimeFactorsListAux
  body: do
  /-
  In this function we will use the convention that all `e` prefixed variables (proofs or otherwise)
  contain `Expr`s. The variables starting with `h` are proofs about the _meta_ code;
  these will not actually be used in the construction of the proof, and are simply used to help the
  reade

中文:
定义 evalPrimeFactorsListAux
  定义体: do
  /-
  In this function we will use the convention that all `e` prefixed variables (proofs or otherwise)
  contain `Expr`s. The variables starting with `h` are proofs about the _meta_ code;
  these will not actually be used in the construction of the proof, and are simply used to help the
  reade
-/
private partial def evalPrimeFactorsListAux
    {en enl : Q(Nat)} {ea eal : Q(Nat)} (ehn : Q(IsNat $en $enl)) (eha : Q(IsNat $ea $eal)) :
    MetaM ((l : Q(List Nat)) × Q(FactorsHelper $en $ea $l)) := do
  /-
  In this function we will use the convention that all `e` prefixed variables (proofs or otherwise)
  contain `Expr`s. The variables starting with `h` are proofs about the _meta_ code;
  these will not actually be used in the construction of the proof, and are simply used to help the
  reader reason about why the proof construction is correct.
  -/
  let n := enl.natLit!
let ⟨hn0⟩ ← if h : 0 < n then pure PLift.up h else
    throwError m!"{enl} must be positive"
  let a := eal.natLit!
  let b := n.minFac
let ⟨hab⟩ ← if h : a <= b then pure PLift.up h else
    throwError m!"{q($eal < $(enl).minFac)} does not hold"
  if h_bn : b < n then
    -- the factor is less than `n`, so we are not done; remove it to get `m`
    let m := n / b
    have em : Q(Nat) := mkRawNatLit m
    have ehm : Q(IsNat (OfNat.ofNat $em) $em) := q(⟨rfl⟩)
    if h_ba_eq : b = a then
      -- if the factor is our minimum `a`, then recurse without changing the minimum
      have eh : Q($eal * $em = $en) :=
        have : a * m = n := by simp [m, b, ← h_ba_eq, Nat.mul_div_cancel' (minFac_dvd _)]
        (q(Eq.refl $en) : Expr)
      let ehp₁ := q(isNat_mul rfl $eha $ehm $eh)
      let ⟨el, ehp₂⟩ ← evalPrimeFactorsListAux ehm eha
      pure ⟨q($ea :: $el), q(($ehp₂).cons_self _ $ehp₁)⟩
    else
      -- Otherwise when we recurse, we should use `b` as the new minimum factor. Note that
      -- we must use `evalMinFac.core` to get a proof that `b` is what we computed it as.
      have eb : Q(Nat) := mkRawNatLit b
      have ehb : Q(IsNat (OfNat.ofNat $eb) $eb) := q(⟨rfl⟩)
      have ehbm : Q($eb * $em = $en) :=
        have : b * m = n := Nat.mul_div_cancel' (minFac_dvd _)
        (q(Eq.refl $en) : Expr)
      have ehp₁ := q(isNat_mul rfl $ehb $ehm $ehbm)
      have ehp₂ : Q(Nat.blt $ea $eb = true) :=
        have : a < b := lt_of_le_of_ne' hab h_ba_eq
        (q(Eq.refl (true)) : Expr)
      let .isNat _ lit ehp₃ ← evalMinFac.core q($eb) q(inferInstance) q($eb) ehb b | failure
      assertInstancesCommute
have : lit =Q eb := ⟨⟩
      let ⟨l, p₄⟩ ← evalPrimeFactorsListAux ehm ehb
      pure ⟨q($eb :: $l), q(($p₄).cons _ $ehp₁ $ehp₂ $ehp₃ )⟩
  else
    -- the factor is our number itself, so we are done
    have hbn_eq : b = n := (minFac_le hn0).eq_or_lt.resolve_right h_bn
    if hba : b = a then
      have eh : Q($en = $ea) :=
        have : n = a := hbn_eq.symm.trans hba
        (q(Eq.refl $en) : Expr)
      pure ⟨q([$ea]), q($eh ▸ FactorsHelper.singleton_self $ea)⟩
    else do
      let eh_a_lt_n : Q(Nat.blt $ea $en = true) :=
        have : a < n := by lia
        (q(Eq.refl true) : Expr)
      let .isNat _ lit ehn_minFac ← evalMinFac.core q($en) q(inferInstance) q($enl) ehn n | failure
have : lit =Q en := ⟨⟩
      assertInstancesCommute
      pure ⟨q([$en]), q(FactorsHelper.singleton $en $eh_a_lt_n $ehn_minFac)⟩

/--
Definition of `evalPrimeFactorsList` / `evalPrimeFactorsList` 的定义

English:
definition evalPrimeFactorsList
  body: do
  match enl.natLit! with
  | 0 =>
have _ : enl =Q nat_lit 0 := ⟨⟩
    have hen : Q($en = 0) := q($(hn).out)
    return ⟨_, q($hen ▸ Nat.primeFactorsList_zero)⟩
  | 1 =>
let _ : enl =Q nat_lit 1 := ⟨⟩
    have hen : Q($en = 1) := q($(hn).out)
    return ⟨_, q($hen ▸ Nat.primeFactorsList_one)⟩
  | 

中文:
定义 evalPrimeFactorsList
  定义体: do
  match enl.natLit! with
  | 0 =>
have _ : enl =Q nat_lit 0 := ⟨⟩
    have hen : Q($en = 0) := q($(hn).out)
    return ⟨_, q($hen ▸ Nat.primeFactorsList_zero)⟩
  | 1 =>
let _ : enl =Q nat_lit 1 := ⟨⟩
    have hen : Q($en = 1) := q($(hn).out)
    return ⟨_, q($hen ▸ Nat.primeFactorsList_one)⟩
  | 
-/
def evalPrimeFactorsList
    {en enl : Q(Nat)} (hn : Q(IsNat $en $enl)) :
    MetaM ((l : Q(List Nat)) × Q(Nat.primeFactorsList $en = $l)) := do
  match enl.natLit! with
  | 0 =>
have _ : enl =Q nat_lit 0 := ⟨⟩
    have hen : Q($en = 0) := q($(hn).out)
    return ⟨_, q($hen ▸ Nat.primeFactorsList_zero)⟩
  | 1 =>
let _ : enl =Q nat_lit 1 := ⟨⟩
    have hen : Q($en = 1) := q($(hn).out)
    return ⟨_, q($hen ▸ Nat.primeFactorsList_one)⟩
  | _ => do
    have h2 : Q(IsNat 2 (nat_lit 2)) := q(⟨Eq.refl (nat_lit 2)⟩)
    let ⟨l, p⟩ ← evalPrimeFactorsListAux hn h2
    return ⟨l, q(($p).primeFactorsList_eq)⟩

end Mathlib.Meta.Simproc

open Qq Mathlib.Meta.Simproc Mathlib.Meta.NormNum

/-- A simproc for terms of the form `Nat.primeFactorsList (OfNat.ofNat n)`. -/
simproc Nat.primeFactorsList_ofNat (Nat.primeFactorsList _) := .ofQ fun u α e => do
  match u, α, e with
  | 1, ~q(List Nat), ~q(Nat.primeFactorsList (OfNat.ofNat $n)) =>
    let hn : Q(IsNat (OfNat.ofNat $n) $n) := q(⟨rfl⟩)
    let ⟨l, p⟩ ← evalPrimeFactorsList hn
return .done .mk q($l) some q($p)
  | _ =>
    return .continue
