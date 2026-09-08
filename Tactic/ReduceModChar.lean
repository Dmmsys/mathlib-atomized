/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public meta import Mathlib.Util.AtLocation
public import Mathlib.Data.ZMod.Basic  -- shake: keep (Qq dependency)
public import Mathlib.RingTheory.Polynomial.Basic  -- shake: keep (Qq dependency)
import all Mathlib.Tactic.NormNum.DivMod  -- for accessing `evalIntMod.go`
public import Mathlib.Tactic.NormNum.PowMod
public import Mathlib.Tactic.ReduceModChar.Ext

/-!
# `reduce_mod_char` tactic

Define the `reduce_mod_char` tactic, which traverses expressions looking for numerals `n`,
such that the type of `n` is a ring of (positive) characteristic `p`, and reduces these
numerals modulo `p`, to lie between `0` and `p`.

## Implementation

The main entry point is `ReduceModChar.derive`, which uses `simp` to traverse expressions and
calls `matchAndNorm` on each subexpression.
The type of each subexpression is matched syntactically to determine if it is a ring with positive
characteristic in `typeToCharP`. Using syntactic matching should be faster than trying to infer
a `CharP` instance on each subexpression.
The actual reduction happens in `normIntNumeral`. This is written to be compatible with `norm_num`
so it can serve as a drop-in replacement for some `norm_num`-based routines (specifically, the
intended use is as an option for the `ring` tactic).

In addition to the main functionality, we call `normNeg` and `normNegCoeffMul` to replace negation
with multiplication by `p - 1`, and simp lemmas tagged `@[reduce_mod_char]` to clean up the
resulting expression: e.g. `1 * X + 0` becomes `X`.
-/

public meta section

open Lean Meta Simp
open Lean.Elab
open Tactic
open Qq

namespace Tactic

namespace ReduceModChar

open Mathlib.Meta.NormNum

variable {u : Level}

/-
**Tactic.ReduceModChar.CharP.isInt_of_mod** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.Redu
ceModChar.CharP`。
形式化陈述：∀ {e' r : ℤ} {α : Type u_1} [inst : Ring α] {n n' : ℕ},   CharP α n →     
∀ {e : α},       Mathlib.Meta.NormNum.IsInt e e' →         Mathlib.Meta.NormNum.
IsNat n n' → Mathlib.Meta.NormNum.IsInt (e' % ↑n') r → Mathlib.Meta.NormNum.IsIn
t e r
参数：e' % ↑n'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.out`：∀ {α : Type u} [inst : Ring α] {a : α} {
n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → a = ↑n
· 使用引理 `CharP.intCast_eq_intCast_mod`：intCast_eq_intCast_mod : (a : R) = a % (p 
: Int)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Int.cast_id`：∀ {n : ℤ}, ↑n = n
-/
lemma CharP.isInt_of_mod {e' r : ℤ} {α : Type*} [Ring α] {n n' : ℕ} (inst : CharP α n) {e : α}
    (he : IsInt e e') (hn : IsNat n n') (h₂ : IsInt (e' % n') r) : IsInt e r :=
  ⟨by rw [he.out, CharP.intCast_eq_intCast_mod α n, show n = n' from hn.out, h₂.out, Int.cast_id]⟩
/-
**Tactic.ReduceModChar.CharP.isNat_pow** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ReduceM
odChar.CharP`。
形式化陈述：∀ {α : Type u_1} [inst : Semiring α] {f : α → ℕ → α} {a : α} {a' b b' c n 
n' : ℕ},   CharP α n →     f = HPow.hPow →       Mathlib.Meta.NormNum.IsNat a a'
 →         Mathlib.Meta.NormNum.IsNat b b' →           Mathlib.Meta.NormNum.IsNa
t n n' → (a'.pow b').mod n' = c → Mathlib.Meta.NormNum.IsNat (f a b) c
参数：a'.pow b'；f a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_id`：Nat.cast_id (n : Nat) : n.cast = n
· 使用定理 `Nat.pow_eq`：∀ {m n : ℕ}, m.pow n = m ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用引理 `CharP.natCast_eq_natCast_mod`：natCast_eq_natCast_mod (a : Nat) : (a : R)
 = a % p
-/
lemma CharP.isNat_pow {α} [Semiring α] : ∀ {f : α → ℕ → α} {a : α} {a' b b' c n n' : ℕ},
    CharP α n → f = HPow.hPow → IsNat a a' → IsNat b b' → IsNat n n' →
    Nat.mod (Nat.pow a' b') n' = c → IsNat (f a b) c
  | _, _, a, _, b, _, _, n, _, rfl, ⟨h⟩, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by
    rw [h, Nat.cast_id, Nat.pow_eq, ← Nat.cast_pow, CharP.natCast_eq_natCast_mod α n]
    rfl⟩

attribute [local instance] Mathlib.Meta.monadLiftOptionMetaM in
/-- Evaluates `e` to an integer using `norm_num` and reduces the result modulo `n`. -/
/-
**Tactic.ReduceModChar.normBareNumeral** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.ReduceM
odChar`。
形式化陈述：normBareNumeral {α : Q(Type u)} (n n' : Q(Nat)) (pn : Q(IsNat «$n» «$n'»))
 (e : Q($α)) (_ : Q(Ring $α)) (instCharP : Q(CharP $α $n)) : MetaM (Result e)
参数：Type u；n n' : Q(Nat)；pn : Q(IsNat «$n» «$n'»)；e : Q($α)；_ : Q(Ring $α)；instCh
arP : Q(CharP $α $n)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates `e` to an integer using `norm_num` and reduces the result modulo `n`.
-/
def normBareNumeral {α : Q(Type u)} (n n' : Q(ℕ)) (pn : Q(IsNat «$n» «$n'»))
    (e : Q($α)) (_ : Q(Ring $α)) (instCharP : Q(CharP $α $n)) : MetaM (Result e) := do
  let ⟨ze, ne, pe⟩ ← Result.toInt _ (← Mathlib.Meta.NormNum.derive e)
  let rr ← evalIntMod.go _ _ ze q(IsInt.raw_refl $ne) _ <|
    .isNat q(instAddMonoidWithOne) _ q(isNat_natCast _ _ (IsNat.raw_refl $n'))
  let ⟨zr, nr, pr⟩ ← rr.toInt _
  return .isInt _ nr zr q(CharP.isInt_of_mod $instCharP $pe $pn $pr)

mutual

  /-- Given an expression of the form `a ^ b` in a ring of characteristic `n`, reduces `a`
  modulo `n` recursively and then calculates `a ^ b` using fast modular exponentiation. -/
  partial def normPow {α : Q(Type u)} (n n' : Q(ℕ)) (pn : Q(IsNat «$n» «$n'»)) (e : Q($α))
      (_ : Q(Ring $α)) (instCharP : Q(CharP $α $n)) : MetaM (Result e) := do
    let .app (.app (f : Q($α → ℕ → $α)) (a : Q($α))) (b : Q(ℕ)) ← whnfR e | failure
    let .isNat sα na pa ← normIntNumeral' n n' pn a _ instCharP | failure
    let ⟨nb, pb⟩ ← Mathlib.Meta.NormNum.deriveNat b q(Nat.instAddMonoidWithOne)
    guard <|← withNewMCtxDepth <| isDefEq f q(HPow.hPow (α := $α))
    haveI' : $e =Q $a ^ $b := ⟨⟩
    haveI' : $f =Q HPow.hPow := ⟨⟩
    have ⟨c, r⟩ := evalNatPowMod na nb n'
    assumeInstancesCommute
    return .isNat sα c q(CharP.isNat_pow (f := $f) $instCharP (.refl $f) $pa $pb $pn $r)

  /-- If `e` is of the form `a ^ b`, reduce it using fast modular exponentiation, otherwise
  reduce it using `norm_num`. -/
  partial def normIntNumeral' {α : Q(Type u)} (n n' : Q(ℕ)) (pn : Q(IsNat «$n» «$n'»))
      (e : Q($α)) (_ : Q(Ring $α)) (instCharP : Q(CharP $α $n)) : MetaM (Result e) :=
    normPow n n' pn e _ instCharP <|> normBareNumeral n n' pn e _ instCharP

end

/-
**Tactic.ReduceModChar.CharP.intCast_eq_mod** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.Re
duceModChar.CharP`。
形式化陈述：∀ (R : Type u_1) [inst : Ring R] (p : ℕ) [CharP R p] (k : ℤ), ↑k = ↑(k % ↑
p)
参数：R : Type u_1；p : ℕ；k : ℤ；k % ↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.intCast_eq_intCast_mod`：intCast_eq_intCast_mod : (a : R) = a % (p 
: Int)
-/
lemma CharP.intCast_eq_mod (R : Type _) [Ring R] (p : ℕ) [CharP R p] (k : ℤ) :
    (k : R) = (k % p : ℤ) :=
  CharP.intCast_eq_intCast_mod R p

/-- Given an integral expression `e : t` such that `t` is a ring of characteristic `n`,
reduce `e` modulo `n`. -/
/-
**Tactic.ReduceModChar.normIntNumeral** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.ReduceMo
dChar`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (n : Q(ℕ)) → (e : Q(«$α»)) → (x : Q(
Ring «$α»)) → Q(CharP «$α» «$n») → MetaM (Mathlib.Meta.NormNum.Result e)
参数：Type u；n : Q(ℕ)；e : Q(«$α»)；x : Q(Ring «$α»)；CharP «$α» «$n»；Mathlib.Meta.Nor
mNum.Result e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an integral expression `e : t` such that `t` is a ring of characteristic `
n`,
reduce `e` modulo `n`.
-/
partial def normIntNumeral {α : Q(Type u)} (n : Q(ℕ)) (e : Q($α)) (_ : Q(Ring $α))
    (instCharP : Q(CharP $α $n)) : MetaM (Result e) := do
  let ⟨n', pn⟩ ← deriveNat n q(Nat.instAddMonoidWithOne)
  normIntNumeral' n n' pn e _ instCharP
/-
**Tactic.ReduceModChar.CharP.neg_eq_sub_one_mul** 是 Mathlib 中的一个定理，位于命名空间 `Tacti
c.ReduceModChar.CharP`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] (n : ℕ),   CharP α n → ∀ (b : α) (a : ℕ) 
(a' : α), Mathlib.Meta.NormNum.IsNat (↑n - 1) a → ↑a = a' → -b = a' * b
参数：n : ℕ；b : α；a : ℕ；a' : α；↑n - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma CharP.neg_eq_sub_one_mul {α : Type _} [Ring α] (n : ℕ) (inst : CharP α n) (b : α)
    (a : ℕ) (a' : α) (p : IsNat (n - 1 : α) a) (pa : a = a') :
    -b = a' * b := by
  rw [← pa, ← p.out, ← neg_one_mul]
  simp

/-- Given an expression `(-e) : t` such that `t` is a ring of characteristic `n`,
simplify this to `(n - 1) * e`.

This should be called only when `normIntNumeral` fails, because `normIntNumeral` would otherwise
be more useful by evaluating `-e` mod `n` to an actual numeral.
-/
@[nolint unusedHavesSuffices] -- the `=Q` is necessary for type checking
/-
**Tactic.ReduceModChar.normNeg** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.ReduceModChar`。
形式化陈述：{u : Level} →   {α : Q(Type u)} → (n : Q(ℕ)) → Q(«$α») → (_instRing : Q(Ri
ng «$α»)) → Q(CharP «$α» «$n») → MetaM Meta.Simp.Result
参数：Type u；n : Q(ℕ)；«$α»；_instRing : Q(Ring «$α»)；CharP «$α» «$n»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an expression `(-e) : t` such that `t` is a ring of characteristic `n`,
simplify this to `(n - 1) * e`.

This should be called only when `normIntNumeral` fails, because `normIntNumeral`
 would otherwise
be more useful by evaluating `-e` mod `n` to an actual numeral.
-/
partial def normNeg {α : Q(Type u)} (n : Q(ℕ)) (e : Q($α)) (_instRing : Q(Ring $α))
    (instCharP : Q(CharP $α $n)) :
    MetaM Simp.Result := do
  let .app f (b : Q($α)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq f q(Neg.neg (α := $α))
  let r ← (derive (α := α) q($n - 1))
  match r with
  | .isNat sα a p => do
    have : instAddMonoidWithOne =Q $sα := ⟨⟩
    let ⟨a', pa'⟩ ← mkOfNat α sα a
    let pf : Q(-$b = $a' * $b) := q(CharP.neg_eq_sub_one_mul $n $instCharP $b $a $a' $p $pa')
    return { expr := q($a' * $b), proof? := pf }
  | .isNegNat _ _ _ =>
    throwError "normNeg: nothing useful to do in negative characteristic"
  | _ => throwError "normNeg: evaluating `{n} - 1` should give an integer result"
/-
**Tactic.ReduceModChar.CharP.neg_mul_eq_sub_one_mul** 是 Mathlib 中的一个定理，位于命名空间 `T
actic.ReduceModChar.CharP`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] (n : ℕ),   CharP α n →     ∀ (a b : α) (n
a : ℕ) (na' : α), Mathlib.Meta.NormNum.IsNat ((↑n - 1) * a) na → ↑na = na' → -(a
 * b) = na' * b
参数：n : ℕ；a b : α；na : ℕ；na' : α；(↑n - 1) * a；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma CharP.neg_mul_eq_sub_one_mul {α : Type _} [Ring α] (n : ℕ) (inst : CharP α n) (a b : α)
    (na : ℕ) (na' : α) (p : IsNat ((n - 1) * a : α) na) (pa : na = na') :
    -(a * b) = na' * b := by
  rw [← pa, ← p.out, ← neg_one_mul]
  simp

/-- Given an expression `-(a * b) : t` such that `t` is a ring of characteristic `n`,
and `a` is a numeral, simplify this to `((n - 1) * a) * b`. -/
@[nolint unusedHavesSuffices] -- the `=Q` is necessary for type checking
/-
**Tactic.ReduceModChar.normNegCoeffMul** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.ReduceM
odChar`。
形式化陈述：{u : Level} →   {α : Q(Type u)} → (n : Q(ℕ)) → Q(«$α») → (_instRing : Q(Ri
ng «$α»)) → Q(CharP «$α» «$n») → MetaM Meta.Simp.Result
参数：Type u；n : Q(ℕ)；«$α»；_instRing : Q(Ring «$α»)；CharP «$α» «$n»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an expression `-(a * b) : t` such that `t` is a ring of characteristic `n`
,
and `a` is a numeral, simplify this to `((n - 1) * a) * b`.
-/
partial def normNegCoeffMul {α : Q(Type u)} (n : Q(ℕ)) (e : Q($α)) (_instRing : Q(Ring $α))
    (instCharP : Q(CharP $α $n)) :
    MetaM Simp.Result := do
  let .app neg (.app (.app mul (a : Q($α))) (b : Q($α))) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq neg q(Neg.neg (α := $α))
  guard <|← withNewMCtxDepth <| isDefEq mul q(HMul.hMul (α := $α))
  let r ← (derive (α := α) q(($n - 1) * $a))
  match r with
  | .isNat sα na np => do
    have : AddGroupWithOne.toAddMonoidWithOne =Q $sα := ⟨⟩
    let ⟨na', npa'⟩ ← mkOfNat α sα na
    let pf : Q(-($a * $b) = $na' * $b) :=
      q(CharP.neg_mul_eq_sub_one_mul $n $instCharP $a $b $na $na' $np $npa')
    return { expr := q($na' * $b), proof? := pf }
  | .isNegNat _ _ _ =>
    throwError "normNegCoeffMul: nothing useful to do in negative characteristic"
  | _ => throwError "normNegCoeffMul: evaluating `{n} - 1` should give an integer result"

/-- A `TypeToCharPResult α` indicates if `α` can be determined to be a ring of characteristic `p`.
-/
/-
**Tactic.ReduceModChar.TypeToCharPResult** 是 Mathlib 中的一个归纳类型，位于命名空间 `Tactic.Red
uceModChar`。
形式化陈述：{u : Level} → Q(Type u) → Type
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `TypeToCharPResult α` indicates if `α` can be determined to be a ring of chara
cteristic `p`.
-/
inductive TypeToCharPResult (α : Q(Type u))
  | intLike (n : Q(ℕ)) (instRing : Q(Ring $α)) (instCharP : Q(CharP $α $n))
  | failure
/-
**Tactic.ReduceModChar.** 是 Mathlib 中的一个实例，位于命名空间 `Tactic.ReduceModChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Q(Type u)} : Inhabited (TypeToCharPResult α) := ⟨.failure⟩

/-- Determine the characteristic of a ring from the type.
This should be fast, so this pattern-matches on the type, rather than searching for a
`CharP` instance.
Use `typeToCharP (expensive := true)` to do more work in finding the characteristic,
in particular it will search for a `CharP` instance in the context. -/
/-
**Tactic.ReduceModChar.typeToCharP** 是 Mathlib 中的一个不透明定义，位于命名空间 `Tactic.ReduceMo
dChar`。
形式化陈述：{u : Level} → optParam Bool false → (t : Q(Type u)) → MetaM (Tactic.Reduce
ModChar.TypeToCharPResult t)
参数：t : Q(Type u)；Tactic.ReduceModChar.TypeToCharPResult t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Determine the characteristic of a ring from the type.
This should be fast, so this pattern-matches on the type, rather than searching 
for a
`CharP` instance.
Use `typeToCharP (expensive := true)` to do more work in finding the characteris
tic,
in particular it will search for a `CharP` instance in the context.
-/
partial def typeToCharP (expensive := false) (t : Q(Type u)) : MetaM (TypeToCharPResult t) :=
match Expr.getAppFnArgs t with
| (``ZMod, #[(n : Q(ℕ))]) =>
  return .intLike n
    (q((ZMod.commRing _).toRing) : Q(Ring (ZMod $n)))
    (q(ZMod.charP _) : Q(CharP (ZMod $n) $n))
| (``Polynomial, #[(R : Q(Type u)), _]) => do match ← typeToCharP (expensive := expensive) R with
  | (.intLike n _ _) =>
    return .intLike n
      (q(Polynomial.ring) : Q(Ring (Polynomial $R)))
      (q(Polynomial.instCharP _) : Q(CharP (Polynomial $R) $n))
  | .failure => return .failure
| _ => if ! expensive then return .failure else do
  -- Fallback: run an expensive procedures to determine a characteristic,
  -- by looking for a `CharP` instance.
  withNewMCtxDepth do
    /- If we want to support semirings, here we could implement the `natLike` fallback. -/
    let .some instRing ← trySynthInstanceQ q(Ring $t) | return .failure

    let n ← mkFreshExprMVarQ q(ℕ)
    let some instCharP ← findLocalDeclWithTypeQ? q(CharP $t $n) | return .failure

    return .intLike (← instantiateMVarsQ n) instRing instCharP

/-- Given an expression `e`, determine whether it is a numeric expression in characteristic `n`,
and if so, reduce `e` modulo `n`.

This is not a `norm_num` plugin because it does not match on the syntax of `e`,
rather it matches on the type of `e`.

Use `matchAndNorm (expensive := true)` to do more work in finding the characteristic of
the type of `e`.
-/
/-
**Tactic.ReduceModChar.matchAndNorm** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.ReduceModC
har`。
形式化陈述：optParam Bool false → Expr → MetaM Meta.Simp.Result
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an expression `e`, determine whether it is a numeric expression in charact
eristic `n`,
and if so, reduce `e` modulo `n`.

This is not a `norm_num` plugin because it does not match on the syntax of `e`,
rather it matches on the type of `e`.

Use `matchAndNorm (expensive := true)` to do more work in finding the characteri
stic of
the type of `e`.
-/
partial def matchAndNorm (expensive := false) (e : Expr) : MetaM Simp.Result := do
  let α ← inferType e
  let u_succ : Level ← getLevel α
  let (.succ u) := u_succ | throwError "expected {α} to be a `Type _`, not `Sort {u_succ}`"
  have α : Q(Type u) := α
  match ← typeToCharP (expensive := expensive) α with
    | (.intLike n instRing instCharP) =>
      -- Handle the numeric expressions first, e.g. `-5` (which shouldn't become `-1 * 5`)
      normIntNumeral n e instRing instCharP >>= Result.toSimpResult <|>
      normNegCoeffMul n e instRing instCharP <|> -- `-(3 * X) → ((n - 1) * 3) * X`
      normNeg n e instRing instCharP -- `-X → (n - 1) * X`

    /- Here we could add a `natLike` result using only a `Semiring` instance.
    This would activate only the less-powerful procedures
    that cannot handle subtraction.
    -/

    | .failure =>
      throwError "inferred type `{α}` does not have a known characteristic"

-- We use a few `simp` lemmas to preprocess the expression and clean up subterms like `0 * X`.
attribute [reduce_mod_char] sub_eq_add_neg
attribute [reduce_mod_char] zero_add add_zero zero_mul mul_zero one_mul mul_one
attribute [reduce_mod_char] eq_self_iff_true -- For closing non-numeric goals, e.g. `X = X`

/-- Reduce all numeric subexpressions of `e` modulo their characteristic.

Use `derive (expensive := true)` to do more work in finding the characteristic of
the type of `e`.
-/
/-
**Tactic.ReduceModChar.derive** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.ReduceModChar`。
形式化陈述：optParam Bool false → Expr → MetaM Meta.Simp.Result
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reduce all numeric subexpressions of `e` modulo their characteristic.

Use `derive (expensive := true)` to do more work in finding the characteristic o
f
the type of `e`.
-/
partial def derive (expensive := false) (e : Expr) : MetaM Simp.Result := do
  withTraceNode `Tactic.reduce_mod_char (fun _ => return m!"{e}") do
  let e ← instantiateMVars e

  let config : Simp.Config := {
    zeta := false
    beta := false
    eta  := false
    proj := false
    iota := false
  }
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ext? ← getSimpExtension? `reduce_mod_char
  let ext ← match ext? with
  | some ext => pure ext
  | none => throwError "internal error: reduce_mod_char not registered as simp extension"
  let ctx ← Simp.mkContext config (congrTheorems := congrTheorems)
    (simpTheorems := #[← ext.getTheorems])
  let discharge := Mathlib.Meta.NormNum.discharge
  let r : Simp.Result := {expr := e}
  let matchAndNorm : Simproc := fun e =>
      try return (Simp.Step.done (← matchAndNorm (expensive := expensive) e))
      catch _ => pure .continue
  let pre := Simp.preDefault #[] >> matchAndNorm
  let post := Simp.postDefault #[]
  let r ← r.mkEqTrans (← Simp.main r.expr ctx (methods := { pre, post, discharge? := discharge })).1

  return r

open Parser.Tactic

/--
The tactic `reduce_mod_char` looks for numeric expressions in characteristic `p`
and reduces these to lie between `0` and `p`.

For example:
```
example : (5 : ZMod 4) = 1 := by reduce_mod_char
example : (X ^ 2 - 3 * X + 4 : (ZMod 4)[X]) = X ^ 2 + X := by reduce_mod_char
```

It also handles negation, turning it into multiplication by `p - 1`,
and similarly subtraction.

This tactic uses the type of the subexpression to figure out if it is indeed of positive
characteristic, for improved performance compared to trying to synthesise a `CharP` instance.
The variant `reduce_mod_char!` also tries to use `CharP R n` hypotheses in the context.
(Limitations of the typeclass system mean the tactic can't search for a `CharP R n` instance if
`n` is not yet known; use `have : CharP R n := inferInstance; reduce_mod_char!` as a workaround.)
-/
syntax (name := reduce_mod_char) "reduce_mod_char" (location)? : tactic
@[tactic_alt reduce_mod_char]
syntax (name := reduce_mod_char!) "reduce_mod_char!" (location)? : tactic

open Mathlib.Tactic in
elab_rules : tactic
| `(tactic| reduce_mod_char $[$loc]?) => unsafe do
  let loc := expandOptLocation (Lean.mkOptionalNode loc)
  transformAtNondepPropLocation (derive (expensive := false) ·) "reduce_mod_char" loc
    (ifUnchanged := .silent)
| `(tactic| reduce_mod_char! $[$loc]?) => unsafe do
  let loc := expandOptLocation (Lean.mkOptionalNode loc)
  transformAtNondepPropLocation (derive (expensive := true) ·) "reduce_mod_char"
    loc (ifUnchanged := .silent)

end ReduceModChar

end Tactic

