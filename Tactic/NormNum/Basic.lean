/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Thomas Murrills
-/
module

public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Commute
public import Mathlib.Tactic.HaveI
public import Mathlib.Tactic.NormNum.Core

/-!
# `norm_num` basic plugins

This file adds `norm_num` plugins for
* constructors and constants
* `Nat.cast`, `Int.cast`, and `mkRat`
* `+`, `-`, `*`, and `/`
* `Nat.succ`, `Nat.sub`, `Nat.mod`, and `Nat.div`.

See other files in this directory for many more plugins.
-/

public section

universe u

namespace Mathlib.Meta.NormNum

/-- If `b` divides `a` and `a` is invertible, then `b` is invertible. -/
@[instance_reducible]
/-
**Mathlib.Meta.NormNum.invertibleOfMul** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：{α : Type u_1} → [inst : Semiring α] → (k : ℕ) → (b a : α) → [Invertible a
] → a = ↑k * b → Invertible b
参数：k : ℕ；b a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `b` divides `a` and `a` is invertible, then `b` is invertible.
-/
def invertibleOfMul {α} [Semiring α] (k : ℕ) (b : α) :
    ∀ (a : α) [Invertible a], a = k * b → Invertible b
  | _, ⟨c, hc1, hc2⟩, rfl => by
    rw [← mul_assoc] at hc1
    rw [Nat.cast_commute k, mul_assoc, Nat.cast_commute k] at hc2
    exact ⟨_, hc1, hc2⟩

/-- If `b` divides `a` and `a` is invertible, then `b` is invertible. -/
@[instance_reducible]
/-
**Mathlib.Meta.NormNum.invertibleOfMul'** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：invertibleOfMul' {α} [Semiring α] {a k b : Nat} [Invertible (a : α)] (h : 
a = k * b) : Invertible (b : α)
参数：a : α；h : a = k * b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `b` divides `a` and `a` is invertible, then `b` is invertible.
-/
def invertibleOfMul' {α} [Semiring α] {a k b : ℕ} [Invertible (a : α)]
    (h : a = k * b) : Invertible (b : α) := invertibleOfMul k (b:α) ↑a (by simp [h])
/-
**Mathlib.Meta.NormNum.IsInt.raw_refl** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum.IsInt`。
形式化陈述：∀ (n : ℤ), Mathlib.Meta.NormNum.IsInt n n
参数：n : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsInt.raw_refl (n : ℤ) : IsInt n n := ⟨rfl⟩

meta section

open Lean Meta Qq

/-! ### Constructors and constants -/

/-
**Mathlib.Meta.NormNum.isNat_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：isNat_zero (α) [AddMonoidWithOne α] : IsNat (Zero.zero : α) (nat_lit 0)
参数：α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0

--- 原说明 ---
### Constructors and constants
-/
theorem isNat_zero (α) [AddMonoidWithOne α] : IsNat (Zero.zero : α) (nat_lit 0) :=
  ⟨Nat.cast_zero.symm⟩

/-- The `norm_num` extension which identifies the expression `Zero.zero`, returning `0`. -/
/-
**Mathlib.Meta.NormNum.evalZero** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`
。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies the expression `Zero.zero`, returning 
`0`.
-/
@[norm_num Zero.zero] def evalZero : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(Zero.zero) => return .isNat sα q(nat_lit 0) q(isNat_zero $α)
/-
**Mathlib.Meta.NormNum.isNat_one** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：isNat_one (α) [AddMonoidWithOne α] : IsNat (One.one : α) (nat_lit 1)
参数：α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem isNat_one (α) [AddMonoidWithOne α] : IsNat (One.one : α) (nat_lit 1) := ⟨Nat.cast_one.symm⟩

/-- The `norm_num` extension which identifies the expression `One.one`, returning `1`. -/
/-
**Mathlib.Meta.NormNum.evalOne** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies the expression `One.one`, returning `1
`.
-/
@[norm_num One.one] def evalOne : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(One.one) => return .isNat sα q(nat_lit 1) q(isNat_one $α)
/-
**Mathlib.Meta.NormNum.isNat_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：isNat_ofNat (α : Type u) [AddMonoidWithOne α] {a : α} {n : Nat} (h : n = a
) : IsNat a n
参数：α : Type u；h : n = a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isNat_ofNat (α : Type u) [AddMonoidWithOne α] {a : α} {n : ℕ}
    (h : n = a) : IsNat a n := ⟨h.symm⟩

/-- The `norm_num` extension which identifies an expression `OfNat.ofNat n`, returning `n`. -/
/-
**Mathlib.Meta.NormNum.evalOfNat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies an expression `OfNat.ofNat n`, returni
ng `n`.
-/
@[norm_num OfNat.ofNat _] def evalOfNat : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(@OfNat.ofNat _ $n $oα) =>
    let n : Q(ℕ) ← whnf n
    guard n.isRawNatLit
    let ⟨a, (pa : Q($n = $e))⟩ ← mkOfNat α sα n
    guard <|← isDefEq a e
    return .isNat sα n q(isNat_ofNat $α $pa)
/-
**Mathlib.Meta.NormNum.isNat_intOfNat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：∀ {n n' : ℕ}, Mathlib.Meta.NormNum.IsNat n n' → Mathlib.Meta.NormNum.IsNat
 (Int.ofNat n) n'
参数：Int.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNat_intOfNat : {n n' : ℕ} → IsNat n n' → IsNat (Int.ofNat n) n'
  | _, _, ⟨rfl⟩ => ⟨rfl⟩

/-- The `norm_num` extension which identifies the constructor application `Int.ofNat n` such that
`norm_num` successfully recognizes `n`, returning `n`. -/
/-
**Mathlib.Meta.NormNum.evalIntOfNat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies the constructor application `Int.ofNat
 n` such that
`norm_num` successfully recognizes `n`, returning `n`.
-/
@[norm_num Int.ofNat _] def evalIntOfNat : NormNumExt where eval {u α} e := do
  let .app (.const ``Int.ofNat _) (n : Q(ℕ)) ← whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q Int := ⟨⟩
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let sℤ : Q(AddMonoidWithOne ℤ) := q(instAddMonoidWithOne)
  let ⟨n', p⟩ ← deriveNat n sℕ
  haveI' x : $e =Q Int.ofNat $n := ⟨⟩
  return .isNat sℤ n' q(isNat_intOfNat $p)
/-
**Mathlib.Meta.NormNum.isInt_negOfNat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isInt_negOfNat (m n : Nat) (h : IsNat m n) : IsInt (Int.negOfNat m) (.negO
fNat n)
参数：m n : Nat；h : IsNat m n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
-/
theorem isInt_negOfNat (m n : ℕ) (h : IsNat m n) : IsInt (Int.negOfNat m) (.negOfNat n) :=
  ⟨congr_arg Int.negOfNat h.1⟩

/-- `norm_num` extension for `Int.negOfNat`.

It's useful for calling `derive` with the numerator of an `.isNegNNRat` branch. -/
@[norm_num Int.negOfNat _]
/-
**Mathlib.Meta.NormNum.evalNegOfNat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：evalNegOfNat : NormNumExt where eval {u αZ} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`norm_num` extension for `Int.negOfNat`.

It's useful for calling `derive` with the numerator of an `.isNegNNRat` branch.
-/
def evalNegOfNat : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(ℤ), ~q(Int.negOfNat $a) =>
    let ⟨n, pn⟩ ← deriveNat (u := 0) a q(inferInstance)
    return .isNegNat q(inferInstance) n q(isInt_negOfNat $a $n $pn)
  | _ => failure
/-
**Mathlib.Meta.NormNum.isNat_natAbs_pos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：∀ {n : ℤ} {a : ℕ}, Mathlib.Meta.NormNum.IsNat n a → Mathlib.Meta.NormNum.I
sNat n.natAbs a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNat_natAbs_pos : {n : ℤ} → {a : ℕ} → IsNat n a → IsNat n.natAbs a
  | _, _, ⟨rfl⟩ => ⟨rfl⟩
/-
**Mathlib.Meta.NormNum.isNat_natAbs_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：∀ {n : ℤ} {a : ℕ}, Mathlib.Meta.NormNum.IsInt n (Int.negOfNat a) → Mathlib
.Meta.NormNum.IsNat n.natAbs a
参数：Int.negOfNat a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNat_natAbs_neg : {n : ℤ} → {a : ℕ} → IsInt n (.negOfNat a) → IsNat n.natAbs a
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

/-- The `norm_num` extension which identifies the expression `Int.natAbs n` such that
`norm_num` successfully recognizes `n`. -/
/-
**Mathlib.Meta.NormNum.evalIntNatAbs** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies the expression `Int.natAbs n` such tha
t
`norm_num` successfully recognizes `n`.
-/
@[norm_num Int.natAbs (_ : ℤ)] def evalIntNatAbs : NormNumExt where eval {u α} e := do
  let .app (.const ``Int.natAbs _) (x : Q(ℤ)) ← whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q Int.natAbs $x := ⟨⟩
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  match ← derive (u := .zero) x with
  | .isNat    _ a p => assumeInstancesCommute; return .isNat sℕ a q(isNat_natAbs_pos $p)
  | .isNegNat _ a p => assumeInstancesCommute; return .isNat sℕ a q(isNat_natAbs_neg $p)
  | _ => failure

/-! ### Casts -/

/-
**Mathlib.Meta.NormNum.isNat_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：isNat_natCast {R} [AddMonoidWithOne R] (n m : Nat) : IsNat n m -> IsNat (n
 : R) m
参数：n m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Casts
-/
theorem isNat_natCast {R} [AddMonoidWithOne R] (n m : ℕ) :
    IsNat n m → IsNat (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

/-- The `norm_num` extension which identifies an expression `Nat.cast n`, returning `n`. -/
/-
**Mathlib.Meta.NormNum.evalNatCast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies an expression `Nat.cast n`, returning 
`n`.
-/
@[norm_num Nat.cast _, NatCast.natCast _] def evalNatCast : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  let .app n (a : Q(ℕ)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq n q(Nat.cast (R := $α))
  let ⟨na, pa⟩ ← deriveNat a q(Nat.instAddMonoidWithOne)
  haveI' : $e =Q $a := ⟨⟩
  return .isNat sα na q(isNat_natCast $a $na $pa)
/-
**Mathlib.Meta.NormNum.isNat_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：isNat_intCast {R} [Ring R] (n : Int) (m : Nat) : IsNat n m -> IsNat (n : R
) m
参数：n : Int；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNat_intCast {R} [Ring R] (n : ℤ) (m : ℕ) :
    IsNat n m → IsNat (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
/-
**Mathlib.Meta.NormNum.isintCast** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：isintCast {R} [Ring R] (n m : Int) : IsInt n m -> IsInt (n : R) m
参数：n m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isintCast {R} [Ring R] (n m : ℤ) :
    IsInt n m → IsInt (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

/-- The `norm_num` extension which identifies an expression `Int.cast n`, returning `n`. -/
/-
**Mathlib.Meta.NormNum.evalIntCast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies an expression `Int.cast n`, returning 
`n`.
-/
@[norm_num Int.cast _, IntCast.intCast _] def evalIntCast : NormNumExt where eval {u α} e := do
  let rα ← inferRing α
  let .app i (a : Q(ℤ)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq i q(Int.cast (R := $α))
  match ← derive (α := q(ℤ)) a with
  | .isNat _ na pa =>
    assumeInstancesCommute
    haveI' : $e =Q Int.cast $a := ⟨⟩
    return .isNat _ na q(isNat_intCast $a $na $pa)
  | .isNegNat _ na pa =>
    assumeInstancesCommute
    haveI' : $e =Q Int.cast $a := ⟨⟩
    return .isNegNat _ na q(isintCast $a (.negOfNat $na) $pa)
  | _ => failure

/-! ### Arithmetic -/

library_note «norm_num lemma function equality» /--
Note: Many of the lemmas in this file use a function equality hypothesis like `f = HAdd.hAdd`
below. The reason for this is that when this is applied, to prove e.g. `100 + 200 = 300`, the
`+` here is `HAdd.hAdd` with an instance that may not be syntactically equal to the one supplied
by the `AddMonoidWithOne` instance, and rather than attempting to prove the instances equal lean
will sometimes decide to evaluate `100 + 200` directly (into whatever `+` is defined to do in this
ring), which is definitely not what we want; if the subterms are expensive to kernel-reduce then
this could cause a `(kernel) deep recursion detected` error (see https://github.com/leanprover/lean4/issues/2171, https://github.com/leanprover-community/mathlib4/pull/4048).

By using an equality for the unapplied `+` function and proving it by `rfl` we take away the
opportunity for lean to unfold the numerals (and the instance defeq problem is usually comparatively
easy).
-/

-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isNat_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {α : Type u_1} [inst : AddMonoidWithOne α] {f : α → α → α} {a b : α} {a'
 b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsNat a a' →       Mathli
b.Meta.NormNum.IsNat b b' → a'.add b' = c → Mathlib.Meta.NormNum.IsNat (f a b) c
参数：f a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
-/
theorem isNat_add {α} [AddMonoidWithOne α] : ∀ {f : α → α → α} {a b : α} {a' b' c : ℕ},
    f = HAdd.hAdd → IsNat a a' → IsNat b b' → Nat.add a' b' = c → IsNat (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Nat.cast_add _ _).symm⟩

-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isInt_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] {f : α → α → α} {a b : α} {a' b' c : ℤ}, 
  f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsInt a a' →       Mathlib.Meta.NormN
um.IsInt b b' → a'.add b' = c → Mathlib.Meta.NormNum.IsInt (f a b) c
参数：f a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
-/
theorem isInt_add {α} [Ring α] : ∀ {f : α → α → α} {a b : α} {a' b' c : ℤ},
    f = HAdd.hAdd → IsInt a a' → IsInt b b' → Int.add a' b' = c → IsInt (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_add ..).symm⟩

-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isNNRat_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：isNNRat_add {α} [Semiring α] {f : α -> α -> α} {a b : α} {na nb nc : Nat} 
{da db dc k : Nat} : f = HAdd.hAdd -> IsNNRat a na da -> IsNNRat b nb db -> Nat.
add (Nat.mul na db) (Nat.mul nb da) = Nat.mul k nc -> Nat.mul da db = Nat.mul k 
dc -> IsNNRat (f a b) nc dc
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Commute.right_comm`：∀ {S : Type u_3} [inst : Semigroup S] {b c : S}, Com
mute b c → ∀ (a : S), a * b * c = a * c * b
· 使用定理 `Commute.invOf_right`：Commute.invOf_right [Monoid α] {a b : α} [Invertibl
e b] (h : Commute a b) : Commute a (⅟b)
· 使用定理 `Commute.invOf_left`：Commute.invOf_left [Monoid α] {a b : α} [Invertible 
b] (h : Commute b a) : Commute (⅟b) a
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_invOf_cancel_right'`：mul_invOf_cancel_right' {_ : Invertible b} : a 
* b * ⅟b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_invOf_cancel_right`：mul_invOf_cancel_right [Invertible b] : a * b * 
⅟b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isNNRat_add {α} [Semiring α] {f : α → α → α} {a b : α} {na nb nc : ℕ} {da db dc k : ℕ} :
    f = HAdd.hAdd → IsNNRat a na da → IsNNRat b nb db →
    Nat.add (Nat.mul na db) (Nat.mul nb da) = Nat.mul k nc →
    Nat.mul da db = Nat.mul k dc →
    IsNNRat (f a b) nc dc := by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * db + nb * da = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  use this
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm
  have h₁ := congr_arg (↑· * (⅟↑da * ⅟↑db : α)) h₁
  simp only [Nat.cast_add, Nat.cast_mul, ← mul_assoc,
    add_mul, mul_invOf_cancel_right] at h₁
  have h₂ := congr_arg (↑nc * ↑· * (⅟↑da * ⅟↑db * ⅟↑dc : α)) h₂
  simp only [H, mul_invOf_cancel_right', Nat.cast_mul, ← mul_assoc] at h₁ h₂
  rw [h₁, h₂, Nat.cast_commute]
  simp only [mul_invOf_cancel_right,
    (Nat.cast_commute (α := α) da dc).invOf_left.invOf_right.right_comm,
    (Nat.cast_commute (α := α) db dc).invOf_left.invOf_right.right_comm]

-- TODO: clean up and move it somewhere in mathlib? It's a bit much for this file
-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isRat_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：isRat_add {α} [Ring α] {f : α -> α -> α} {a b : α} {na nb nc : Int} {da db
 dc k : Nat} : f = HAdd.hAdd -> IsRat a na da -> IsRat b nb db -> Int.add (Int.m
ul na db) (Int.mul nb da) = Int.mul k nc -> Nat.mul da db = Nat.mul k dc -> IsRa
t (f a b) nc dc
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Commute.right_comm`：∀ {S : Type u_3} [inst : Semigroup S] {b c : S}, Com
mute b c → ∀ (a : S), a * b * c = a * c * b
· 使用定理 `Commute.invOf_right`：Commute.invOf_right [Monoid α] {a b : α} [Invertibl
e b] (h : Commute a b) : Commute a (⅟b)
· 使用定理 `Commute.invOf_left`：Commute.invOf_left [Monoid α] {a b : α} [Invertible 
b] (h : Commute b a) : Commute (⅟b) a
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_invOf_cancel_right'`：mul_invOf_cancel_right' {_ : Invertible b} : a 
* b * ⅟b = a
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_invOf_cancel_right`：mul_invOf_cancel_right [Invertible b] : a * b * 
⅟b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isRat_add {α} [Ring α] {f : α → α → α} {a b : α} {na nb nc : ℤ} {da db dc k : ℕ} :
    f = HAdd.hAdd → IsRat a na da → IsRat b nb db →
    Int.add (Int.mul na db) (Int.mul nb da) = Int.mul k nc →
    Nat.mul da db = Nat.mul k dc →
    IsRat (f a b) nc dc := by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * db + nb * da = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  use this
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm
  have h₁ := congr_arg (↑· * (⅟↑da * ⅟↑db : α)) h₁
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ← mul_assoc,
    add_mul, mul_invOf_cancel_right] at h₁
  have h₂ := congr_arg (↑nc * ↑· * (⅟↑da * ⅟↑db * ⅟↑dc : α)) h₂
  simp only [H, mul_invOf_cancel_right', Nat.cast_mul, ← mul_assoc] at h₁ h₂
  rw [h₁, h₂, Nat.cast_commute]
  simp only [mul_invOf_cancel_right,
    (Nat.cast_commute (α := α) da dc).invOf_left.invOf_right.right_comm,
    (Nat.cast_commute (α := α) db dc).invOf_left.invOf_right.right_comm]

/-- Consider an `Option` as an object in the `MetaM` monad, by throwing an error on `none`. -/
@[expose, instance_reducible]
/-
**Mathlib.Meta.NormNum._root_.Mathlib.Meta.monadLiftOptionMetaM** 是 Mathlib 中的一个
定义，位于命名空间 `Mathlib.Meta.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider an `Option` as an object in the `MetaM` monad, by throwing an error on 
`none`.
-/
def _root_.Mathlib.Meta.monadLiftOptionMetaM : MonadLift Option MetaM where
  monadLift
  | none => failure
  | some e => pure e

attribute [local instance] monadLiftOptionMetaM in
/-- The result of adding two `norm_num` results. -/
/-
**Mathlib.Meta.NormNum.Result.add** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {a b : Q(«$α»)} →       Mathlib.Meta
.NormNum.Result q(«$a») →         Mathlib.Meta.NormNum.Result q(«$b») →         
  (inst : autoParam Q(Add «$α») Mathlib.Meta.NormNum.Result.add._auto_1) →      
       MetaM (Mathlib.Meta.NormNum.Result q(«$a» + «$b»))
参数：Type u；«$α»；«$a»；«$b»；inst : autoParam Q(Add «$α») Mathlib.Meta.NormNum.Resul
t.add._auto_1；Mathlib.Meta.NormNum.Result q(«$a» + «$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result of adding two `norm_num` results.
-/
def Result.add {u : Level} {α : Q(Type u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
    (inst : Q(Add $α) := by exact q(delta% inferInstance)) :
    MetaM (Result q($a + $b)) := do
  let rec intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt _; let ⟨zb, nb, pb⟩ ← rb.toInt _
    let zc := za + zb
    have c := mkRawIntLit zc
    haveI' : Int.add $na $nb =Q $c := ⟨⟩
    return .isInt rα c zc q(isInt_add (.refl _) $pa $pb (.refl $c))
  let rec nnratArm (dsα : Q(DivisionSemiring $α)) : MetaM (Result _) := do
    assumeInstancesCommute
    let ⟨qa, na, da, pa⟩ ← ra.toNNRat' dsα; let ⟨qb, nb, db, pb⟩ ← rb.toNNRat' dsα
    let qc := qa + qb
    let dd := qa.den * qb.den
    let k := dd / qc.den
    have t1 : Q(ℕ) := mkRawNatLit (k * qc.num.toNat)
    have t2 : Q(ℕ) := mkRawNatLit dd
    have nc : Q(ℕ) := mkRawNatLit qc.num.toNat
    have dc : Q(ℕ) := mkRawNatLit qc.den
    have k : Q(ℕ) := mkRawNatLit k
    let r1 : Q(Nat.add (Nat.mul $na $db) (Nat.mul $nb $da) = Nat.mul $k $nc) :=
      (q(Eq.refl $t1) : Expr)
    let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
    return .isNNRat' dsα qc nc dc q(isNNRat_add (.refl _) $pa $pb $r1 $r2)
  let rec ratArm (dα : Q(DivisionRing $α)) : MetaM (Result _) := do
    assumeInstancesCommute
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα; let ⟨qb, nb, db, pb⟩ ← rb.toRat' dα
    let qc := qa + qb
    let dd := qa.den * qb.den
    let k := dd / qc.den
    have t1 : Q(ℤ) := mkRawIntLit (k * qc.num)
    have t2 : Q(ℕ) := mkRawNatLit dd
    have nc : Q(ℤ) := mkRawIntLit qc.num
    have dc : Q(ℕ) := mkRawNatLit qc.den
    have k : Q(ℕ) := mkRawNatLit k
    let r1 : Q(Int.add (Int.mul $na $db) (Int.mul $nb $da) = Int.mul $k $nc) :=
      (q(Eq.refl $t1) : Expr)
    let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
    return .isRat dα qc nc dc q(isRat_add (.refl _) $pa $pb $r1 $r2)
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isNegNNRat dα .., _ | _, .isNegNNRat dα .. => ratArm dα
  -- mixing positive rationals and negative naturals means we need to use the full rat handler
  | .isNNRat _dsα .., .isNegNat _rα .. | .isNegNat _rα .., .isNNRat _dsα .. =>
    -- could alternatively try to combine `rα` and `dsα` here, but we'd have to do a defeq check
    -- so would still need to be in `MetaM`.
    let dα ← synthInstanceQ q(DivisionRing $α)
    assumeInstancesCommute
    ratArm q($dα)
  | .isNNRat dsα .., _ | _, .isNNRat dsα .. => nnratArm dsα
  | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
  | .isNat _ na pa, .isNat sα nb pb =>
    assumeInstancesCommute
    have c : Q(ℕ) := mkRawNatLit (na.natLit! + nb.natLit!)
    haveI' : Nat.add $na $nb =Q $c := ⟨⟩
    return .isNat sα c q(isNat_add (.refl _) $pa $pb (.refl $c))

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `a + b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.NormNum.evalAdd** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `a + b`,
such that `norm_num` successfully recognises both `a` and `b`.
-/
@[norm_num _ + _] def evalAdd : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let ra ← derive a; let rb ← derive b
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isNat _ .., .isNat _ .. | .isNat _ .., .isNegNat _ .. | .isNat _ .., .isNNRat _ ..
    | .isNat _ .., .isNegNNRat _ ..
  | .isNegNat _ .., .isNat _ .. | .isNegNat _ .., .isNegNat _ .. | .isNegNat _ .., .isNNRat _ ..
    | .isNegNat _ .., .isNegNNRat _ ..
  | .isNNRat _ .., .isNat _ .. | .isNNRat _ .., .isNegNat _ .. | .isNNRat _ .., .isNNRat _ ..
    | .isNNRat _ .., .isNegNNRat _ ..
  | .isNegNNRat _ .., .isNat _ .. | .isNegNNRat _ .., .isNegNat _ ..
    | .isNegNNRat _ .., .isNNRat _ .. | .isNegNNRat _ .., .isNegNNRat _ .. =>
    guard <|← withNewMCtxDepth <| isDefEq f q(HAdd.hAdd (α := $α))
    ra.add rb

-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isInt_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] {f : α → α} {a : α} {a' b : ℤ},   f = Neg
.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.neg = b → Mathlib.Meta.NormNum.IsInt
 (-a) b
参数：-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
-/
theorem isInt_neg {α} [Ring α] : ∀ {f : α → α} {a : α} {a' b : ℤ},
    f = Neg.neg → IsInt a a' → Int.neg a' = b → IsInt (-a) b
  | _, _, _, _, rfl, ⟨rfl⟩, rfl => ⟨(Int.cast_neg ..).symm⟩

-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isRat_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] {f : α → α} {a : α} {n n' : ℤ} {d : ℕ},  
 f = Neg.neg → Mathlib.Meta.NormNum.IsRat a n d → n.neg = n' → Mathlib.Meta.Norm
Num.IsRat (-a) n' d
参数：-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
-/
theorem isRat_neg {α} [Ring α] : ∀ {f : α → α} {a : α} {n n' : ℤ} {d : ℕ},
    f = Neg.neg → IsRat a n d → Int.neg n = n' → IsRat (-a) n' d
  | _, _, _, _, _, rfl, ⟨h, rfl⟩, rfl => ⟨h, by rw [← neg_mul, ← Int.cast_neg]; rfl⟩

attribute [local instance] monadLiftOptionMetaM in
/-- The result of negating a `norm_num` result. -/
/-
**Mathlib.Meta.NormNum.Result.neg** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {a : Q(«$α»)} →       Mathlib.Meta.N
ormNum.Result q(«$a») →         (rα : autoParam Q(Ring «$α») Mathlib.Meta.NormNu
m.Result.neg._auto_1) →           MetaM (Mathlib.Meta.NormNum.Result q(-«$a»))
参数：Type u；«$α»；«$a»；rα : autoParam Q(Ring «$α») Mathlib.Meta.NormNum.Result.neg.
_auto_1；Mathlib.Meta.NormNum.Result q(-«$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result of negating a `norm_num` result.
-/
def Result.neg {u : Level} {α : Q(Type u)} {a : Q($α)} (ra : Result q($a))
    (rα : Q(Ring $α) := by exact q(delta% inferInstance)) :
    MetaM (Result q(-$a)) := do
  let intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt rα
    let zb := -za
    have b := mkRawIntLit zb
    haveI' : Int.neg $na =Q $b := ⟨⟩
    return .isInt rα b zb q(isInt_neg (.refl _) $pa (.refl $b))
  let ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
    assumeInstancesCommute
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα
    let qb := -qa
    have nb := mkRawIntLit qb.num
    haveI' : Int.neg $na =Q $nb := ⟨⟩
    return .isRat dα qb nb da q(isRat_neg (.refl _) $pa (.refl $nb))
  match ra with
  | .isBool _ .. => failure
  | .isNat _ .. => intArm rα
  | .isNegNat rα .. => intArm rα
  | .isNNRat _dsα .. => ratArm (← synthInstanceQ q(DivisionRing $α))
  | .isNegNNRat dα .. => ratArm dα

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `-a`,
such that `norm_num` successfully recognises `a`. -/
/-
**Mathlib.Meta.NormNum.evalNeg** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `-a`,
such that `norm_num` successfully recognises `a`.
-/
@[norm_num -_] def evalNeg : NormNumExt where eval {u α} e := do
  let .app (f : Q($α → $α)) (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let rα ← inferRing α
  let ⟨(_f_eq : $f =Q Neg.neg)⟩ ← withNewMCtxDepth <| assertDefEqQ _ _
  haveI' _e_eq : $e =Q -$a := ⟨⟩
  ra.neg

-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isInt_sub** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] {f : α → α → α} {a b : α} {a' b' c : ℤ}, 
  f = HSub.hSub →     Mathlib.Meta.NormNum.IsInt a a' →       Mathlib.Meta.NormN
um.IsInt b b' → a'.sub b' = c → Mathlib.Meta.NormNum.IsInt (f a b) c
参数：f a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
-/
theorem isInt_sub {α} [Ring α] : ∀ {f : α → α → α} {a b : α} {a' b' c : ℤ},
    f = HSub.hSub → IsInt a a' → IsInt b b' → Int.sub a' b' = c → IsInt (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_sub ..).symm⟩

-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isRat_sub** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：isRat_sub {α} [Ring α] {f : α -> α -> α} {a b : α} {na nb nc : Int} {da db
 dc k : Nat} (hf : f = HSub.hSub) (ra : IsRat a na da) (rb : IsRat b nb db) (h₁ 
: Int.sub (Int.mul na db) (Int.mul nb da) = Int.mul k nc) (h₂ : Nat.mul da db = 
Nat.mul k dc) : IsRat (f a b) nc dc
参数：hf : f = HSub.hSub；ra : IsRat a na da；rb : IsRat b nb db；h₁ : Int.sub (Int.mu
l na db) (Int.mul nb da) = Int.mul k nc；h₂ : Nat.mul da db = Nat.mul k dc。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Mathlib.Meta.NormNum.isRat_add`：isRat_add {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} : f = HAdd.hAdd -> IsRat a na da 
-> IsRat b nb db -> …
· 使用定理 `Mathlib.Meta.NormNum.isRat_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {n n' : ℤ} {d : ℕ},   f = Neg.neg → Mathlib.Meta.NormNum.IsRat a n 
d → n.neg = n' → Mat…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
theorem isRat_sub {α} [Ring α] {f : α → α → α} {a b : α} {na nb nc : ℤ} {da db dc k : ℕ}
    (hf : f = HSub.hSub) (ra : IsRat a na da) (rb : IsRat b nb db)
    (h₁ : Int.sub (Int.mul na db) (Int.mul nb da) = Int.mul k nc)
    (h₂ : Nat.mul da db = Nat.mul k dc) :
    IsRat (f a b) nc dc := by
  rw [hf, sub_eq_add_neg]
  refine isRat_add rfl ra (isRat_neg (n' := -nb) rfl rb rfl) (k := k) (nc := nc) ?_ h₂
  rw [show Int.mul (-nb) _ = _ from neg_mul ..]; exact h₁

attribute [local instance] monadLiftOptionMetaM in
/-- The result of subtracting two `norm_num` results. -/
/-
**Mathlib.Meta.NormNum.Result.sub** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {a b : Q(«$α»)} →       Mathlib.Meta
.NormNum.Result q(«$a») →         Mathlib.Meta.NormNum.Result q(«$b») →         
  (inst : autoParam Q(Ring «$α») Mathlib.Meta.NormNum.Result.sub._auto_1) →     
        MetaM (Mathlib.Meta.NormNum.Result q(«$a» - «$b»))
参数：Type u；«$α»；«$a»；«$b»；inst : autoParam Q(Ring «$α») Mathlib.Meta.NormNum.Resu
lt.sub._auto_1；Mathlib.Meta.NormNum.Result q(«$a» - «$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result of subtracting two `norm_num` results.
-/
def Result.sub {u : Level} {α : Q(Type u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
    (inst : Q(Ring $α) := by exact q(delta% inferInstance)) :
    MetaM (Result q($a - $b)) := do
  let intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt rα; let ⟨zb, nb, pb⟩ ← rb.toInt rα
    let zc := za - zb
    have c := mkRawIntLit zc
    haveI' : Int.sub $na $nb =Q $c := ⟨⟩
    return Result.isInt rα c zc q(isInt_sub (.refl _) $pa $pb (.refl $c))
  let ratArm (dα : Q(DivisionRing $α)) : MetaM (Result _) := do
    assumeInstancesCommute
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα; let ⟨qb, nb, db, pb⟩ ← rb.toRat' dα
    let qc := qa - qb
    let dd := qa.den * qb.den
    let k := dd / qc.den
    have t1 : Q(ℤ) := mkRawIntLit (k * qc.num)
    have t2 : Q(ℕ) := mkRawNatLit dd
    have nc : Q(ℤ) := mkRawIntLit qc.num
    have dc : Q(ℕ) := mkRawNatLit qc.den
    have k : Q(ℕ) := mkRawNatLit k
    let r1 : Q(Int.sub (Int.mul $na $db) (Int.mul $nb $da) = Int.mul $k $nc) :=
      (q(Eq.refl $t1) : Expr)
    let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
    return .isRat dα qc nc dc q(isRat_sub (.refl _) $pa $pb $r1 $r2)
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isNegNNRat dα .., _ | _, .isNegNNRat dα .. =>
    ratArm dα
  | _, .isNNRat _dsα .. | .isNNRat _dsα .., _ =>
    ratArm (← synthInstanceQ q(DivisionRing $α))
  | .isNegNat _rα .., _ | _, .isNegNat _rα ..
  | .isNat _ .., .isNat _ .. =>
    intArm inst

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `a - b` in a ring,
such that `norm_num` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.NormNum.evalSub** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `a - b` in a r
ing,
such that `norm_num` successfully recognises both `a` and `b`.
-/
@[norm_num _ - _] def evalSub : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let rα ← inferRing α
  let ⟨(_f_eq : $f =Q HSub.hSub)⟩ ← withNewMCtxDepth <| assertDefEqQ _ _
  let ra ← derive a; let rb ← derive b
  haveI' _e_eq : $e =Q $a - $b := ⟨⟩
  ra.sub rb

-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isNat_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {α : Type u_1} [inst : Semiring α] {f : α → α → α} {a b : α} {a' b' c : 
ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsNat a a' →       Mathlib.Meta.N
ormNum.IsNat b b' → a'.mul b' = c → Mathlib.Meta.NormNum.IsNat (a * b) c
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
-/
theorem isNat_mul {α} [Semiring α] : ∀ {f : α → α → α} {a b : α} {a' b' c : ℕ},
    f = HMul.hMul → IsNat a a' → IsNat b b' → Nat.mul a' b' = c → IsNat (a * b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Nat.cast_mul ..).symm⟩

-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isInt_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] {f : α → α → α} {a b : α} {a' b' c : ℤ}, 
  f = HMul.hMul →     Mathlib.Meta.NormNum.IsInt a a' →       Mathlib.Meta.NormN
um.IsInt b b' → a'.mul b' = c → Mathlib.Meta.NormNum.IsInt (a * b) c
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
-/
theorem isInt_mul {α} [Ring α] : ∀ {f : α → α → α} {a b : α} {a' b' c : ℤ},
    f = HMul.hMul → IsInt a a' → IsInt b b' → Int.mul a' b' = c → IsInt (a * b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_mul ..).symm⟩
/-
**Mathlib.Meta.NormNum.isNNRat_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：isNNRat_mul {α} [Semiring α] {f : α -> α -> α} {a b : α} {na nb nc : Nat} 
{da db dc k : Nat} : f = HMul.hMul -> IsNNRat a na da -> IsNNRat b nb db -> Nat.
mul na nb = Nat.mul k nc -> Nat.mul da db = Nat.mul k dc -> IsNNRat (f a b) nc d
c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Commute.right_comm`：∀ {S : Type u_3} [inst : Semigroup S] {b c : S}, Com
mute b c → ∀ (a : S), a * b * c = a * c * b
· 使用定理 `Commute.invOf_right`：Commute.invOf_right [Monoid α] {a b : α} [Invertibl
e b] (h : Commute a b) : Commute a (⅟b)
· 使用定理 `Commute.invOf_left`：Commute.invOf_left [Monoid α] {a b : α} [Invertible 
b] (h : Commute b a) : Commute (⅟b) a
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_invOf_cancel_right'`：mul_invOf_cancel_right' {_ : Invertible b} : a 
* b * ⅟b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isNNRat_mul {α} [Semiring α] {f : α → α → α} {a b : α} {na nb nc : ℕ} {da db dc k : ℕ} :
    f = HMul.hMul → IsNNRat a na da → IsNNRat b nb db →
    Nat.mul na nb = Nat.mul k nc →
    Nat.mul da db = Nat.mul k dc →
    IsNNRat (f a b) nc dc := by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * nb = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  refine ⟨this, ?_⟩
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm
  have h₁ := congr_arg (Nat.cast (R := α)) h₁
  simp only [Nat.cast_mul] at h₁
  simp only [← mul_assoc, (Nat.cast_commute (α := α) da nb).invOf_left.right_comm, h₁]
  have h₂ := congr_arg (↑nc * ↑· * (⅟↑da * ⅟↑db * ⅟↑dc : α)) h₂
  simp only [Nat.cast_mul, ← mul_assoc] at h₂; rw [H] at h₂
  simp only [mul_invOf_cancel_right'] at h₂; rw [h₂, Nat.cast_commute]
  simp only [mul_invOf_cancel_right',
    (Nat.cast_commute (α := α) da dc).invOf_left.invOf_right.right_comm,
    (Nat.cast_commute (α := α) db dc).invOf_left.invOf_right.right_comm]
/-
**Mathlib.Meta.NormNum.isRat_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：isRat_mul {α} [Ring α] {f : α -> α -> α} {a b : α} {na nb nc : Int} {da db
 dc k : Nat} : f = HMul.hMul -> IsRat a na da -> IsRat b nb db -> Int.mul na nb 
= Int.mul k nc -> Nat.mul da db = Nat.mul k dc -> IsRat (f a b) nc dc
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Commute.right_comm`：∀ {S : Type u_3} [inst : Semigroup S] {b c : S}, Com
mute b c → ∀ (a : S), a * b * c = a * c * b
· 使用定理 `Commute.invOf_right`：Commute.invOf_right [Monoid α] {a b : α} [Invertibl
e b] (h : Commute a b) : Commute a (⅟b)
· 使用定理 `Commute.invOf_left`：Commute.invOf_left [Monoid α] {a b : α} [Invertible 
b] (h : Commute b a) : Commute (⅟b) a
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `mul_invOf_cancel_right'`：mul_invOf_cancel_right' {_ : Invertible b} : a 
* b * ⅟b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_invOf_cancel_right`：mul_invOf_cancel_right [Invertible b] : a * b * 
⅟b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isRat_mul {α} [Ring α] {f : α → α → α} {a b : α} {na nb nc : ℤ} {da db dc k : ℕ} :
    f = HMul.hMul → IsRat a na da → IsRat b nb db →
    Int.mul na nb = Int.mul k nc →
    Nat.mul da db = Nat.mul k dc →
    IsRat (f a b) nc dc := by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * nb = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  refine ⟨this, ?_⟩
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm
  have h₁ := congr_arg (Int.cast (R := α)) h₁
  simp only [Int.cast_mul, Int.cast_natCast] at h₁
  simp only [← mul_assoc, (Nat.cast_commute (α := α) da nb).invOf_left.right_comm, h₁]
  have h₂ := congr_arg (↑nc * ↑· * (⅟↑da * ⅟↑db * ⅟↑dc : α)) h₂
  simp only [Nat.cast_mul, ← mul_assoc] at h₂; rw [H] at h₂
  simp only [mul_invOf_cancel_right'] at h₂; rw [h₂, Nat.cast_commute]
  simp only [mul_invOf_cancel_right,
    (Nat.cast_commute (α := α) da dc).invOf_left.invOf_right.right_comm,
    (Nat.cast_commute (α := α) db dc).invOf_left.invOf_right.right_comm]

attribute [local instance] monadLiftOptionMetaM in
/-- The result of multiplying two `norm_num` results. -/
/-
**Mathlib.Meta.NormNum.Result.mul** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {a b : Q(«$α»)} →       Mathlib.Meta
.NormNum.Result q(«$a») →         Mathlib.Meta.NormNum.Result q(«$b») →         
  (inst : autoParam Q(Semiring «$α») Mathlib.Meta.NormNum.Result.mul._auto_1) → 
            MetaM (Mathlib.Meta.NormNum.Result q(«$a» * «$b»))
参数：Type u；«$α»；«$a»；«$b»；inst : autoParam Q(Semiring «$α») Mathlib.Meta.NormNum.
Result.mul._auto_1；Mathlib.Meta.NormNum.Result q(«$a» * «$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result of multiplying two `norm_num` results.
-/
def Result.mul {u : Level} {α : Q(Type u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
    (inst : Q(Semiring $α) := by exact q(delta% inferInstance)) :
    MetaM (Result q($a * $b)) := do
  let intArm (rα : Q(Ring $α)) := do
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← ra.toInt rα; let ⟨zb, nb, pb⟩ ← rb.toInt rα
    let zc := za * zb
    have c := mkRawIntLit zc
    haveI' : Int.mul $na $nb =Q $c := ⟨⟩
    return .isInt rα c zc q(isInt_mul (.refl _) $pa $pb (.refl $c))
  let nnratArm (dsα : Q(DivisionSemiring $α)) : Option (Result _) := do
    assumeInstancesCommute
    let ⟨qa, na, da, pa⟩ ← ra.toNNRat' dsα; let ⟨qb, nb, db, pb⟩ ← rb.toNNRat' dsα
    let qc := qa * qb
    let dd := qa.den * qb.den
    let k := dd / qc.den
    have nc : Q(ℕ) := mkRawNatLit qc.num.toNat
    have dc : Q(ℕ) := mkRawNatLit qc.den
    have k : Q(ℕ) := mkRawNatLit k
    let r1 : Q(Nat.mul $na $nb = Nat.mul $k $nc) :=
      (q(Eq.refl (Nat.mul $na $nb)) : Expr)
    have t2 : Q(ℕ) := mkRawNatLit dd
    let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
    return .isNNRat' dsα qc nc dc q(isNNRat_mul (.refl _) $pa $pb $r1 $r2)
  let rec ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
    assumeInstancesCommute
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα; let ⟨qb, nb, db, pb⟩ ← rb.toRat' dα
    let qc := qa * qb
    let dd := qa.den * qb.den
    let k := dd / qc.den
    have nc : Q(ℤ) := mkRawIntLit qc.num
    have dc : Q(ℕ) := mkRawNatLit qc.den
    have k : Q(ℕ) := mkRawNatLit k
    let r1 : Q(Int.mul $na $nb = Int.mul $k $nc) :=
      (q(Eq.refl (Int.mul $na $nb)) : Expr)
    have t2 : Q(ℕ) := mkRawNatLit dd
    let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
    return .isRat dα qc nc dc q(isRat_mul (.refl _) $pa $pb $r1 $r2)
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isNegNNRat dα .., _ | _, .isNegNNRat dα .. =>
    ratArm dα
  -- mixing positive rationals and negative naturals means we need to use the full rat handler
  | .isNNRat dsα .., .isNegNat rα .. | .isNegNat rα .., .isNNRat dsα .. =>
    -- could alternatively try to combine `rα` and `dsα` here, but we'd have to do a defeq check
    -- so would still need to be in `MetaM`.
    ratArm (← synthInstanceQ q(DivisionRing $α))
  | .isNNRat dsα .., _ | _, .isNNRat dsα .. =>
    nnratArm dsα
  | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
  | .isNat mα' na pa, .isNat mα nb pb => do
    haveI' : $mα =Q by clear! $mα $mα'; apply AddCommMonoidWithOne.toAddMonoidWithOne := ⟨⟩
    assumeInstancesCommute
    have c : Q(ℕ) := mkRawNatLit (na.natLit! * nb.natLit!)
    haveI' : Nat.mul $na $nb =Q $c := ⟨⟩
    return .isNat mα c q(isNat_mul (.refl _) $pa $pb (.refl $c))

/-- The `norm_num` extension which identifies expressions of the form `a * b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.NormNum.evalMul** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `a * b`,
such that `norm_num` successfully recognises both `a` and `b`.
-/
@[norm_num _ * _] def evalMul : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let sα ← inferSemiring α
  let ra ← derive a; let rb ← derive b
  guard <|← withNewMCtxDepth <| isDefEq f q(HMul.hMul (α := $α))
  haveI' : $f =Q HMul.hMul := ⟨⟩
  haveI' : $e =Q $a * $b := ⟨⟩
  ra.mul rb
/-
**Mathlib.Meta.NormNum.isNNRat_div** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：∀ {α : Type u} [inst : DivisionSemiring α] {a b : α} {cn cd : ℕ},   Mathli
b.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mathlib.Meta.NormNum.IsNNRat (a / b) cn
 cd
参数：a * b⁻¹；a / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem isNNRat_div {α : Type u} [DivisionSemiring α] : {a b : α} → {cn : ℕ} → {cd : ℕ} →
    IsNNRat (a * b⁻¹) cn cd → IsNNRat (a / b) cn cd
  | _, _, _, _, h => by simpa [div_eq_mul_inv] using h
/-
**Mathlib.Meta.NormNum.isRat_div** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {α : Type u} [inst : DivisionRing α] {a b : α} {cn : ℤ} {cd : ℕ},   Math
lib.Meta.NormNum.IsRat (a * b⁻¹) cn cd → Mathlib.Meta.NormNum.IsRat (a / b) cn c
d
参数：a * b⁻¹；a / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem isRat_div {α : Type u} [DivisionRing α] : {a b : α} → {cn : ℤ} → {cd : ℕ} →
    IsRat (a * b⁻¹) cn cd → IsRat (a / b) cn cd
  | _, _, _, _, h => by simpa [div_eq_mul_inv] using h

/-- Helper function to synthesize a typed `DivisionSemiring α` expression. -/
/-
**Mathlib.Meta.NormNum.inferDivisionSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.
Meta.NormNum`。
形式化陈述：inferDivisionSemiring {u : Level} (α : Q(Type u)) : MetaM Q(DivisionSemiri
ng $α)
参数：α : Q(Type u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function to synthesize a typed `DivisionSemiring α` expression.
-/
def inferDivisionSemiring {u : Level} (α : Q(Type u)) : MetaM Q(DivisionSemiring $α) :=
  return ← synthInstanceQ q(DivisionSemiring $α) <|> throwError "not a division semiring"

/-- Helper function to synthesize a typed `DivisionRing α` expression. -/
/-
**Mathlib.Meta.NormNum.inferDivisionRing** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta
.NormNum`。
形式化陈述：inferDivisionRing {u : Level} (α : Q(Type u)) : MetaM Q(DivisionRing $α)
参数：α : Q(Type u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function to synthesize a typed `DivisionRing α` expression.
-/
def inferDivisionRing {u : Level} (α : Q(Type u)) : MetaM Q(DivisionRing $α) :=
  return ← synthInstanceQ q(DivisionRing $α) <|> throwError "not a division ring"

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `a / b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.NormNum.evalDiv** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `a / b`,
such that `norm_num` successfully recognises both `a` and `b`.
-/
@[norm_num _ / _] def evalDiv : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let dsα ← inferDivisionSemiring α
  haveI' : $e =Q $a / $b := ⟨⟩
  guard <| ← withNewMCtxDepth <| isDefEq f q(HDiv.hDiv (α := $α))
  let rab ← derive (q($a * $b⁻¹) : Q($α))
  if let some ⟨qa, na, da, pa⟩ := rab.toNNRat' dsα then
    assumeInstancesCommute
    return .isNNRat' dsα qa na da q(isNNRat_div $pa)
  else
    let dα ← inferDivisionRing α
    let ⟨qa, na, da, pa⟩ ← rab.toRat' dα
    assumeInstancesCommute
    return .isRat dα qa na da q(isRat_div $pa)

/-! ### Logic -/

/-- The `norm_num` extension which identifies `True`. -/
/-
**Mathlib.Meta.NormNum.evalTrue** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`
。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies `True`.
-/
@[norm_num True] def evalTrue : NormNumExt where eval {u α} e :=
  return (.isTrue q(True.intro) : Result q(True))

/-- The `norm_num` extension which identifies `False`. -/
/-
**Mathlib.Meta.NormNum.evalFalse** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies `False`.
-/
@[norm_num False] def evalFalse : NormNumExt where eval {u α} e :=
  return (.isFalse q(not_false) : Result q(False))

/-- The `norm_num` extension which identifies expressions of the form `¬a`,
such that `norm_num` successfully recognises `a`. -/
/-
**Mathlib.Meta.NormNum.evalNot** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `¬a`,
such that `norm_num` successfully recognises `a`.
-/
@[norm_num ¬_] def evalNot : NormNumExt where eval {u α} e := do
  let .app (.const ``Not _) (a : Q(Prop)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq α q(Prop)
  let ⟨b, p⟩ ← deriveBool q($a)
  match b with
  | true => return .isFalse q(not_not_intro $p)
  | false => return .isTrue q($p)

/-! ### (In)equalities -/

variable {α : Type u}

/-
**Mathlib.Meta.NormNum.isNat_eq_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] {a b : α} {c : ℕ},   Mathlib.Me
ta.NormNum.IsNat a c → Mathlib.Meta.NormNum.IsNat b c → a = b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNat_eq_true [AddMonoidWithOne α] : {a b : α} → {c : ℕ} →
    IsNat a c → IsNat b c → a = b
  | _, _, _, ⟨rfl⟩, ⟨rfl⟩ => rfl
/-
**Mathlib.Meta.NormNum.ble_eq_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：ble_eq_false {x y : Nat} : x.ble y = false ↔ y < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.not_le`：∀ {a b : ℕ}, ¬a ≤ b ↔ b < a
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `Nat.ble_eq`：∀ {x y : ℕ}, (x.ble y = true) = (x ≤ y)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ble_eq_false {x y : ℕ} : x.ble y = false ↔ y < x := by
  rw [← Nat.not_le, ← Bool.not_eq_true, Nat.ble_eq]
/-
**Mathlib.Meta.NormNum.isInt_eq_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {α : Type u} [inst : Ring α] {a b : α} {z : ℤ},   Mathlib.Meta.NormNum.I
sInt a z → Mathlib.Meta.NormNum.IsInt b z → a = b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isInt_eq_true [Ring α] : {a b : α} → {z : ℤ} → IsInt a z → IsInt b z → a = b
  | _, _, _, ⟨rfl⟩, ⟨rfl⟩ => rfl
/-
**Mathlib.Meta.NormNum.isNNRat_eq_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {a b : α} {n d : ℕ},   Mathlib.Meta.Nor
mNum.IsNNRat a n d → Mathlib.Meta.NormNum.IsNNRat b n d → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem isNNRat_eq_true [Semiring α] : {a b : α} → {n : ℕ} → {d : ℕ} →
    IsNNRat a n d → IsNNRat b n d → a = b
  | _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => by congr; apply Subsingleton.elim
/-
**Mathlib.Meta.NormNum.isRat_eq_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {α : Type u} [inst : Ring α] {a b : α} {n : ℤ} {d : ℕ},   Mathlib.Meta.N
ormNum.IsRat a n d → Mathlib.Meta.NormNum.IsRat b n d → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem isRat_eq_true [Ring α] : {a b : α} → {n : ℤ} → {d : ℕ} →
    IsRat a n d → IsRat b n d → a = b
  | _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => by congr; apply Subsingleton.elim
/-
**Mathlib.Meta.NormNum.eq_of_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：eq_of_true {a b : Prop} (ha : a) (hb : b) : a = b
参数：ha : a；hb : b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
-/
theorem eq_of_true {a b : Prop} (ha : a) (hb : b) : a = b := propext (iff_of_true ha hb)
/-
**Mathlib.Meta.NormNum.ne_of_false_of_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Me
ta.NormNum`。
形式化陈述：ne_of_false_of_true {a b : Prop} (ha : ¬a) (hb : b) : a != b
参数：ha : ¬a；hb : b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_of_false_of_true {a b : Prop} (ha : ¬a) (hb : b) : a ≠ b := mt (· ▸ hb) ha
/-
**Mathlib.Meta.NormNum.ne_of_true_of_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Me
ta.NormNum`。
形式化陈述：ne_of_true_of_false {a b : Prop} (ha : a) (hb : ¬b) : a != b
参数：ha : a；hb : ¬b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem ne_of_true_of_false {a b : Prop} (ha : a) (hb : ¬b) : a ≠ b := mt (· ▸ ha) hb
/-
**Mathlib.Meta.NormNum.eq_of_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：eq_of_false {a b : Prop} (ha : ¬a) (hb : ¬b) : a = b
参数：ha : ¬a；hb : ¬b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
-/
theorem eq_of_false {a b : Prop} (ha : ¬a) (hb : ¬b) : a = b := propext (iff_of_false ha hb)

/-! ### Nat operations -/

/-
**Mathlib.Meta.NormNum.isNat_natSucc** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {a a' c : ℕ}, Mathlib.Meta.NormNum.IsNat a a' → a'.succ = c → Mathlib.Me
ta.NormNum.IsNat a.succ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Nat operations
-/
theorem isNat_natSucc : {a : ℕ} → {a' c : ℕ} →
    IsNat a a' → Nat.succ a' = c → IsNat (a.succ) c
  | _, _,_, ⟨rfl⟩, rfl => ⟨by simp⟩

/-- The `norm_num` extension which identifies expressions of the form `Nat.succ a`,
such that `norm_num` successfully recognises `a`. -/
/-
**Mathlib.Meta.NormNum.evalNatSucc** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `Nat.succ a`,
such that `norm_num` successfully recognises `a`.
-/
@[norm_num Nat.succ _] def evalNatSucc : NormNumExt where eval {u α} e := do
  let .app f (a : Q(ℕ)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq f q(Nat.succ)
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q Nat.succ $a := ⟨⟩
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨na, pa⟩ ← deriveNat a sℕ
  have nc : Q(ℕ) := mkRawNatLit (na.natLit!.succ)
  haveI' : $nc =Q ($na).succ := ⟨⟩
  return .isNat sℕ nc q(isNat_natSucc $pa (.refl $nc))
/-
**Mathlib.Meta.NormNum.isNat_natSub** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：∀ {a b a' b' c : ℕ},   Mathlib.Meta.NormNum.IsNat a a' →     Mathlib.Meta.
NormNum.IsNat b b' → a'.sub b' = c → Mathlib.Meta.NormNum.IsNat (a - b) c
参数：a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNat_natSub : {a b : ℕ} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.sub a' b' = c → IsNat (a - b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

/-- The `norm_num` extension which identifies expressions of the form `Nat.sub a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.NormNum.evalNatSub** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `Nat.sub a b`,
such that `norm_num` successfully recognises both `a` and `b`.
-/
@[norm_num (_ : ℕ) - _] def evalNatSub :
    NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℕ))) (b : Q(ℕ)) ← whnfR e | failure
  -- We assert that the default instance for `HSub` is `Nat.sub` when the first parameter is `ℕ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(HSub.hSub (α := ℕ))
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q $a - $b := ⟨⟩
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨na, pa⟩ ← deriveNat a sℕ; let ⟨nb, pb⟩ ← deriveNat b sℕ
  have nc : Q(ℕ) := mkRawNatLit (na.natLit! - nb.natLit!)
  haveI' : Nat.sub $na $nb =Q $nc := ⟨⟩
  return .isNat sℕ nc q(isNat_natSub $pa $pb (.refl $nc))
/-
**Mathlib.Meta.NormNum.isNat_natMod** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：∀ {a b a' b' c : ℕ},   Mathlib.Meta.NormNum.IsNat a a' →     Mathlib.Meta.
NormNum.IsNat b b' → a'.mod b' = c → Mathlib.Meta.NormNum.IsNat (a % b) c
参数：a % b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNat_natMod : {a b : ℕ} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.mod a' b' = c → IsNat (a % b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by aesop⟩

/-- The `norm_num` extension which identifies expressions of the form `Nat.mod a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.NormNum.evalNatMod** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `Nat.mod a b`,
such that `norm_num` successfully recognises both `a` and `b`.
-/
@[norm_num (_ : ℕ) % _] def evalNatMod :
    NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℕ))) (b : Q(ℕ)) ← whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q $a % $b := ⟨⟩
  -- We assert that the default instance for `HMod` is `Nat.mod` when the first parameter is `ℕ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(HMod.hMod (α := ℕ))
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨na, pa⟩ ← deriveNat a sℕ; let ⟨nb, pb⟩ ← deriveNat b sℕ
  have nc : Q(ℕ) := mkRawNatLit (na.natLit! % nb.natLit!)
  haveI' : Nat.mod $na $nb =Q $nc := ⟨⟩
  return .isNat sℕ nc q(isNat_natMod $pa $pb (.refl $nc))
/-
**Mathlib.Meta.NormNum.isNat_natDiv** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：∀ {a b a' b' c : ℕ},   Mathlib.Meta.NormNum.IsNat a a' →     Mathlib.Meta.
NormNum.IsNat b b' → a'.div b' = c → Mathlib.Meta.NormNum.IsNat (a / b) c
参数：a / b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNat_natDiv : {a b : ℕ} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.div a' b' = c → IsNat (a / b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by aesop⟩

/-- The `norm_num` extension which identifies expressions of the form `Nat.div a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ : ℕ) / _]
/-
**Mathlib.Meta.NormNum.evalNatDiv** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：evalNatDiv : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `Nat.div a b`,
such that `norm_num` successfully recognises both `a` and `b`.
-/
def evalNatDiv : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℕ))) (b : Q(ℕ)) ← whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q $a / $b := ⟨⟩
  -- We assert that the default instance for `HDiv` is `Nat.div` when the first parameter is `ℕ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(HDiv.hDiv (α := ℕ))
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨na, pa⟩ ← deriveNat a sℕ; let ⟨nb, pb⟩ ← deriveNat b sℕ
  have nc : Q(ℕ) := mkRawNatLit (na.natLit! / nb.natLit!)
  haveI' : Nat.div $na $nb =Q $nc := ⟨⟩
  return .isNat sℕ nc q(isNat_natDiv $pa $pb (.refl $nc))
/-
**Mathlib.Meta.NormNum.isNat_dvd_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：∀ {a b a' b' : ℕ}, Mathlib.Meta.NormNum.IsNat a a' → Mathlib.Meta.NormNum.
IsNat b b' → b'.mod a' = 0 → a ∣ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_of_mod_eq_zero`：∀ {m n : ℕ}, n % m = 0 → m ∣ n
-/
theorem isNat_dvd_true : {a b : ℕ} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.mod b' a' = nat_lit 0 → a ∣ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, e => Nat.dvd_of_mod_eq_zero e
/-
**Mathlib.Meta.NormNum.isNat_dvd_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：∀ {a b a' b' c : ℕ}, Mathlib.Meta.NormNum.IsNat a a' → Mathlib.Meta.NormNu
m.IsNat b b' → b'.mod a' = c.succ → ¬a ∣ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Nat.mod_eq_zero_of_dvd`：∀ {m n : ℕ}, m ∣ n → n % m = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isNat_dvd_false : {a b : ℕ} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.mod b' a' = Nat.succ c → ¬a ∣ b
  | _, _, _, _, c, ⟨rfl⟩, ⟨rfl⟩, e => mt Nat.mod_eq_zero_of_dvd (e.symm ▸ Nat.succ_ne_zero c :)

/-- The `norm_num` extension which identifies expressions of the form `(a : ℕ) | b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.NormNum.evalNatDvd** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `(a : ℕ) | b`,
such that `norm_num` successfully recognises both `a` and `b`.
-/
@[norm_num (_ : ℕ) ∣ _] def evalNatDvd : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℕ))) (b : Q(ℕ)) ← whnfR e | failure
  -- We assert that the default instance for `Dvd` is `Nat.dvd` when the first parameter is `ℕ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(Dvd.dvd (α := ℕ))
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨na, pa⟩ ← deriveNat a sℕ; let ⟨nb, pb⟩ ← deriveNat b sℕ
  match nb.natLit! % na.natLit! with
  | 0 =>
    have : Q(Nat.mod $nb $na = nat_lit 0) := (q(Eq.refl (nat_lit 0)) : Expr)
    return .isTrue q(isNat_dvd_true $pa $pb $this)
  | c+1 =>
    have nc : Q(ℕ) := mkRawNatLit c
    have : Q(Nat.mod $nb $na = Nat.succ $nc) := (q(Eq.refl (Nat.succ $nc)) : Expr)
    return .isFalse q(isNat_dvd_false $pa $pb $this)

end

end Mathlib.Meta.NormNum

