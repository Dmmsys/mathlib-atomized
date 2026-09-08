/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Eric Wieser
-/
module

import all Mathlib.Tactic.NormNum.Prime  -- for accessing `evalMinFac.core`
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

/-- A proof of the partial computation of `primeFactorsList`.
Asserts that `l` is a sorted list of primes multiplying to `n` and lower bounded by a prime `p`. -/
/-
**Mathlib.Meta.Simproc.FactorsHelper** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Sim
proc`。
形式化陈述：FactorsHelper (n p : Nat) (l : List Nat) : Prop
参数：n p : Nat；l : List Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A proof of the partial computation of `primeFactorsList`.
Asserts that `l` is a sorted list of primes multiplying to `n` and lower bounded
 by a prime `p`.
-/
def FactorsHelper (n p : ℕ) (l : List ℕ) : Prop :=
  p.Prime → (p :: l).IsChain (· ≤ ·) ∧ (∀ a ∈ l, Nat.Prime a) ∧ l.prod = n

/-! The argument explicitness in this section is chosen to make only the numerals in the factors
list appear in the proof term. -/

/-
**Mathlib.Meta.Simproc.FactorsHelper.nil** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta
.Simproc.FactorsHelper`。
形式化陈述：∀ {a : ℕ}, Mathlib.Meta.Simproc.FactorsHelper 1 a []
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.forall_mem_nil`：∀ {α : Type u_1} (p : α → Prop), ∀ x ∈ [], p x
· 使用定理 `List.prod_nil`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α], [].prod =
 1

--- 原说明 ---
The argument explicitness in this section is chosen to make only the numerals in
 the factors
list appear in the proof term.
-/
theorem FactorsHelper.nil {a : ℕ} : FactorsHelper 1 a [] := fun _ =>
  ⟨.singleton _, List.forall_mem_nil _, List.prod_nil⟩
/-
**Mathlib.Meta.Simproc.FactorsHelper.cons_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Meta.Simproc.FactorsHelper`。
形式化陈述：∀ {n m : ℕ} (a : ℕ) {b : ℕ} {l : List ℕ},   Mathlib.Meta.NormNum.IsNat (b 
* m) n →     a ≤ b → b.minFac = b → Mathlib.Meta.Simproc.FactorsHelper m b l → M
athlib.Meta.Simproc.FactorsHelper n a (b :: l)
参数：a : ℕ；b * m；b :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.prime_def_minFac`：prime_def_minFac {p : Nat} : Prime p ↔ 2 <= p ∧ mi
nFac p = p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `List.eq_or_mem_of_mem_cons`：∀ {α : Type u_1} {a b : α} {l : List α}, a ∈
 b :: l → a = b ∨ a ∈ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Nat.cast_id`：Nat.cast_id (n : Nat) : n.cast = n
-/
theorem FactorsHelper.cons_of_le
    {n m : ℕ} (a : ℕ) {b : ℕ} {l : List ℕ} (h₁ : IsNat (b * m) n) (h₂ : a ≤ b)
    (h₃ : minFac b = b) (H : FactorsHelper m b l) : FactorsHelper n a (b :: l) := fun pa =>
  have pb : b.Prime := Nat.prime_def_minFac.2 ⟨le_trans pa.two_le h₂, h₃⟩
  let ⟨f₁, f₂, f₃⟩ := H pb
  ⟨List.IsChain.cons_cons h₂ f₁,
    fun _ h => (List.eq_or_mem_of_mem_cons h).elim (fun e => e.symm ▸ pb) (f₂ _),
    by rw [List.prod_cons, f₃, h₁.out, cast_id]⟩
/-
**Mathlib.Meta.Simproc.FactorsHelper.cons** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Met
a.Simproc.FactorsHelper`。
形式化陈述：∀ {n m a : ℕ} (b : ℕ) {l : List ℕ},   Mathlib.Meta.NormNum.IsNat (b * m) n
 →     a.blt b = true →       Mathlib.Meta.NormNum.IsNat b.minFac b →         Ma
thlib.Meta.Simproc.FactorsHelper m b l → Mathlib.Meta.Simproc.FactorsHelper n a 
(b :: l)
参数：b : ℕ；b * m；b :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.Simproc.FactorsHelper.cons_of_le`：∀ {n m : ℕ} (a : ℕ) {b : 
ℕ} {l : List ℕ},   Mathlib.Meta.NormNum.IsNat (b * m) n →     a ≤ b → b.minFac =
 b → Mathlib.Meta.Simproc.FactorsHe…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.blt_eq`：∀ {x y : ℕ}, (x.blt y = true) = (x < y)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
-/
theorem FactorsHelper.cons
    {n m : ℕ} {a : ℕ} (b : ℕ) {l : List ℕ} (h₁ : IsNat (b * m) n) (h₂ : Nat.blt a b)
    (h₃ : IsNat (minFac b) b) (H : FactorsHelper m b l) : FactorsHelper n a (b :: l) :=
  H.cons_of_le _ h₁ (Nat.blt_eq.mp h₂).le h₃.out
/-
**Mathlib.Meta.Simproc.FactorsHelper.singleton** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Meta.Simproc.FactorsHelper`。
形式化陈述：∀ (n : ℕ) {a : ℕ}, a.blt n = true → Mathlib.Meta.NormNum.IsNat n.minFac n 
→ Mathlib.Meta.Simproc.FactorsHelper n a [n]
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.Simproc.FactorsHelper.cons`：∀ {n m a : ℕ} (b : ℕ) {l : List
 ℕ},   Mathlib.Meta.NormNum.IsNat (b * m) n →     a.blt b = true →       Mathlib
.Meta.NormNum.IsNat b.minFac …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Meta.Simproc.FactorsHelper.nil`：∀ {a : ℕ}, Mathlib.Meta.Simproc.
FactorsHelper 1 a []
-/
theorem FactorsHelper.singleton (n : ℕ) {a : ℕ} (h₁ : Nat.blt a n) (h₂ : IsNat (minFac n) n) :
    FactorsHelper n a [n] :=
  FactorsHelper.nil.cons _ ⟨mul_one _⟩ h₁ h₂
/-
**Mathlib.Meta.Simproc.FactorsHelper.cons_self** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Meta.Simproc.FactorsHelper`。
形式化陈述：∀ {n m : ℕ} (a : ℕ) {l : List ℕ},   Mathlib.Meta.NormNum.IsNat (a * m) n →
     Mathlib.Meta.Simproc.FactorsHelper m a l → Mathlib.Meta.Simproc.FactorsHelp
er n a (a :: l)
参数：a : ℕ；a * m；a :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.Simproc.FactorsHelper.cons_of_le`：∀ {n m : ℕ} (a : ℕ) {b : 
ℕ} {l : List ℕ},   Mathlib.Meta.NormNum.IsNat (b * m) n →     a ≤ b → b.minFac =
 b → Mathlib.Meta.Simproc.FactorsHe…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_def_minFac`：prime_def_minFac {p : Nat} : Prime p ↔ 2 <= p ∧ mi
nFac p = p
-/
theorem FactorsHelper.cons_self {n m : ℕ} (a : ℕ) {l : List ℕ}
    (h : IsNat (a * m) n) (H : FactorsHelper m a l) :
    FactorsHelper n a (a :: l) := fun pa =>
  H.cons_of_le _ h le_rfl (Nat.prime_def_minFac.1 pa).2 pa
/-
**Mathlib.Meta.Simproc.FactorsHelper.singleton_self** 是 Mathlib 中的一个定理，位于命名空间 `M
athlib.Meta.Simproc.FactorsHelper`。
形式化陈述：∀ (a : ℕ), Mathlib.Meta.Simproc.FactorsHelper a a [a]
参数：a : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.Simproc.FactorsHelper.cons_self`：∀ {n m : ℕ} (a : ℕ) {l : L
ist ℕ},   Mathlib.Meta.NormNum.IsNat (a * m) n →     Mathlib.Meta.Simproc.Factor
sHelper m a l → Mathlib.Meta.Simpr…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Meta.Simproc.FactorsHelper.nil`：∀ {a : ℕ}, Mathlib.Meta.Simproc.
FactorsHelper 1 a []
-/
theorem FactorsHelper.singleton_self (a : ℕ) : FactorsHelper a a [a] :=
  FactorsHelper.nil.cons_self _ ⟨mul_one _⟩
/-
**Mathlib.Meta.Simproc.FactorsHelper.primeFactorsList_eq** 是 Mathlib 中的一个定理，位于命名
空间 `Mathlib.Meta.Simproc.FactorsHelper`。
形式化陈述：∀ {n : ℕ} {l : List ℕ}, Mathlib.Meta.Simproc.FactorsHelper n 2 l → n.prime
FactorsList = l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.isChain_iff_pairwise`：∀ {α : Type u_1} {R : α → α → Prop} {l : List
 α} [Trans R R R], List.IsChain R l ↔ List.Pairwise R l
· 使用定理 `List.IsChain.tail`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α}, Lis
t.IsChain R l → List.IsChain R l.tail
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Perm.eq_of_pairwise'`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Anti
symm r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pairwise r l₂ → l₁.Perm l₂
 → l₁ = l₂
· 使用定理 `Nat.instAntisymmLe`：Std.Antisymm fun x1 x2 => x1 ≤ x2
· 使用定理 `List.SortedLE.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLE → List.Pairwise (fun x1 x2 => x1 ≤ x2) l
· 使用定理 `Nat.primeFactorsList_sorted`：primeFactorsList_sorted (n : Nat) : List.So
rtedLE (primeFactorsList n)
· 使用定理 `Nat.primeFactorsList_unique`：primeFactorsList_unique {n : Nat} {l : List
 Nat} (h₁ : prod l = n) (h₂ : forall p in l, Prime p) : l ~ primeFactorsList n
-/
theorem FactorsHelper.primeFactorsList_eq {n : ℕ} {l : List ℕ} (H : FactorsHelper n 2 l) :
    Nat.primeFactorsList n = l :=
  let ⟨h₁, h₂, h₃⟩ := H Nat.prime_two
  have := List.isChain_iff_pairwise.1 (@List.IsChain.tail _ _ (_ :: _) h₁)
  ((Nat.primeFactorsList_unique h₃ h₂).eq_of_pairwise'
     this (Nat.primeFactorsList_sorted _).pairwise).symm

open Lean Elab Tactic Qq

/-- Given `n` and `a` (in expressions `en` and `ea`) corresponding to literal numerals
(in `enl` and `eal`), returns `(l, ⊢ factorsHelper n a l)`. -/
/-
**Mathlib.Meta.Simproc.evalPrimeFactorsListAux** 是 Mathlib 中的一个定义，位于命名空间 `Mathli
b.Meta.Simproc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `n` and `a` (in expressions `en` and `ea`) corresponding to literal numera
ls
(in `enl` and `eal`), returns `(l, ⊢ factorsHelper n a l)`.
-/
private partial def evalPrimeFactorsListAux
    {en enl : Q(ℕ)} {ea eal : Q(ℕ)} (ehn : Q(IsNat $en $enl)) (eha : Q(IsNat $ea $eal)) :
    MetaM ((l : Q(List ℕ)) × Q(FactorsHelper $en $ea $l)) := do
  /-
  In this function we will use the convention that all `e` prefixed variables (proofs or otherwise)
  contain `Expr`s. The variables starting with `h` are proofs about the _meta_ code;
  these will not actually be used in the construction of the proof, and are simply used to help the
  reader reason about why the proof construction is correct.
  -/
  let n := enl.natLit!
  let ⟨hn0⟩ ← if h : 0 < n then pure <| PLift.up h else
    throwError m!"{enl} must be positive"
  let a := eal.natLit!
  let b := n.minFac
  let ⟨hab⟩ ← if h : a ≤ b then pure <| PLift.up h else
    throwError m!"{q($eal < $(enl).minFac)} does not hold"
  if h_bn : b < n then
    -- the factor is less than `n`, so we are not done; remove it to get `m`
    let m := n / b
    have em : Q(ℕ) := mkRawNatLit m
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
      have eb : Q(ℕ) := mkRawNatLit b
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
      have : $lit =Q $eb := ⟨⟩
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
      have : $lit =Q $en := ⟨⟩
      assertInstancesCommute
      pure ⟨q([$en]), q(FactorsHelper.singleton $en $eh_a_lt_n $ehn_minFac)⟩

/-- Given a natural number `n`, returns `(l, ⊢ Nat.primeFactorsList n = l)`. -/
/-
**Mathlib.Meta.Simproc.evalPrimeFactorsList** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.M
eta.Simproc`。
形式化陈述：evalPrimeFactorsList {en enl : Q(Nat)} (hn : Q(IsNat $en $enl)) : MetaM ((
l : Q(List Nat)) × Q(Nat.primeFactorsList $en = $l))
参数：Nat；hn : Q(IsNat $en $enl)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural number `n`, returns `(l, ⊢ Nat.primeFactorsList n = l)`.
-/
def evalPrimeFactorsList
    {en enl : Q(ℕ)} (hn : Q(IsNat $en $enl)) :
    MetaM ((l : Q(List ℕ)) × Q(Nat.primeFactorsList $en = $l)) := do
  match enl.natLit! with
  | 0 =>
    have _ : $enl =Q nat_lit 0 := ⟨⟩
    have hen : Q($en = 0) := q($(hn).out)
    return ⟨_, q($hen ▸ Nat.primeFactorsList_zero)⟩
  | 1 =>
    let _ : $enl =Q nat_lit 1 := ⟨⟩
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
  | 1, ~q(List ℕ), ~q(Nat.primeFactorsList (OfNat.ofNat $n)) =>
    let hn : Q(IsNat (OfNat.ofNat $n) $n) := q(⟨rfl⟩)
    let ⟨l, p⟩ ← evalPrimeFactorsList hn
    return .done <| .mk q($l) <| some q($p)
  | _ =>
    return .continue

