/-
Copyright (c) 2023 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Tactic.NormNum.Pow

/-!
# `norm_num` handling for expressions of the form `a ^ b % m`.

These expressions can often be evaluated efficiently in cases where first evaluating `a ^ b` and
then reducing mod `m` is not feasible. We provide a function `evalNatPowMod` which is used by the
`reduce_mod_char` tactic to efficiently evaluate powers in rings with positive characteristic.

The approach taken here is identical to (and copied from) the development in
`Mathlib/Tactic/NormNum/Pow.lean`.

## TODO

* Adapt the `norm_num` extensions for `Nat.mod` and `Int.emod` to efficiently evaluate expressions
  of the form `a ^ b % m` using `evalNatPowMod`.

-/

public meta section

assert_not_exists RelIso

set_option autoImplicit true

namespace Mathlib
open Lean
open Meta

namespace Meta.NormNum
open Qq

/-- Represents and proves equalities of the form `a^b % m = c` for natural numbers. -/
/-
**Mathlib.Meta.NormNum.IsNatPowModT** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：Prop → ℕ → ℕ → ℕ → ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Represents and proves equalities of the form `a^b % m = c` for natural numbers.
-/
structure IsNatPowModT (p : Prop) (a b m c : Nat) : Prop where
  run' : p → Nat.mod (Nat.pow a b) m = c
/-
**Mathlib.Meta.NormNum.IsNatPowModT.run** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum.IsNatPowModT`。
形式化陈述：∀ {a m : ℕ} {b c : ℕ}, Mathlib.Meta.NormNum.IsNatPowModT ((a.pow 1).mod m 
= a.mod m) a b m c → (a.pow b).mod m = c
参数：(a.pow 1).mod m = a.mod m；a.pow b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowModT.run'`：∀ {p : Prop} {a b m c : ℕ}, Math
lib.Meta.NormNum.IsNatPowModT p a b m c → p → (a.pow b).mod m = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
-/
theorem IsNatPowModT.run
    (p : IsNatPowModT (Nat.mod (Nat.pow a (nat_lit 1)) m = Nat.mod a m) a b m c) :
    Nat.mod (Nat.pow a b) m = c := p.run' (congr_arg (fun x => x % m) (Nat.pow_one a))
/-
**Mathlib.Meta.NormNum.IsNatPowModT.trans** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Met
a.NormNum.IsNatPowModT`。
形式化陈述：∀ {p : Prop} {a b m c b' c' : ℕ},   Mathlib.Meta.NormNum.IsNatPowModT p a 
b m c →     Mathlib.Meta.NormNum.IsNatPowModT ((a.pow b).mod m = c) a b' m c' → 
Mathlib.Meta.NormNum.IsNatPowModT p a b' m c'
参数：(a.pow b).mod m = c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowModT.run'`：∀ {p : Prop} {a b m c : ℕ}, Math
lib.Meta.NormNum.IsNatPowModT p a b m c → p → (a.pow b).mod m = c
-/
theorem IsNatPowModT.trans (h1 : IsNatPowModT p a b m c)
    (h2 : IsNatPowModT (Nat.mod (Nat.pow a b) m = c) a b' m c') : IsNatPowModT p a b' m c' :=
  ⟨h2.run' ∘ h1.run'⟩
/-
**Mathlib.Meta.NormNum.IsNatPowModT.bit0** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta
.NormNum.IsNatPowModT`。
形式化陈述：∀ {a b m : ℕ} {c : ℕ}, Mathlib.Meta.NormNum.IsNatPowModT ((a.pow b).mod m 
= c) a (2 * b) m ((c.mul c).mod m)
参数：(a.pow b).mod m = c；2 * b；(c.mul c).mod m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_mod`：∀ (a b n : ℕ), a * b % n = a % n * (b % n) % n
-/
theorem IsNatPowModT.bit0 :
    IsNatPowModT (Nat.mod (Nat.pow a b) m = c) a (nat_lit 2 * b) m (Nat.mod (Nat.mul c c) m) :=
  ⟨fun h1 => by simp only [two_mul, Nat.pow_eq, pow_add, ← h1, Nat.mul_eq]; exact Nat.mul_mod ..⟩
/-
**Mathlib.Meta.NormNum.natPow_zero_natMod_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Meta.NormNum`。
形式化陈述：natPow_zero_natMod_zero : Nat.mod (Nat.pow a (nat_lit 0)) (nat_lit 0) = na
t_lit 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.modCore.eq_1`：∀ (x y : ℕ), x.modCore y = if hy : 0 < y then Nat.modC
ore.go y hy x.succ x ⋯ else x
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natPow_zero_natMod_zero : Nat.mod (Nat.pow a (nat_lit 0)) (nat_lit 0) = nat_lit 1 := by
  simp [Nat.mod, Nat.modCore]
/-
**Mathlib.Meta.NormNum.natPow_zero_natMod_one** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Meta.NormNum`。
形式化陈述：natPow_zero_natMod_one : Nat.mod (Nat.pow a (nat_lit 0)) (nat_lit 1) = nat
_lit 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `Nat.modCore_eq`：∀ (x y : ℕ), x.modCore y = if 0 < y ∧ y ≤ x then (x - y)
.modCore y else x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natPow_zero_natMod_one : Nat.mod (Nat.pow a (nat_lit 0)) (nat_lit 1) = nat_lit 0 := by
  simp [Nat.mod, Nat.modCore_eq]
/-
**Mathlib.Meta.NormNum.natPow_zero_natMod_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `M
athlib.Meta.NormNum`。
形式化陈述：natPow_zero_natMod_succ_succ : Nat.mod (Nat.pow a (nat_lit 0)) (Nat.succ (
Nat.succ m)) = nat_lit 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natPow_zero_natMod_succ_succ :
    Nat.mod (Nat.pow a (nat_lit 0)) (Nat.succ (Nat.succ m)) = nat_lit 1 := by
  rfl
/-
**Mathlib.Meta.NormNum.natPow_one_natMod** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta
.NormNum`。
形式化陈述：natPow_one_natMod : Nat.mod (Nat.pow a (nat_lit 1)) m = Nat.mod a m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.natPow_one`：natPow_one : Nat.pow a (nat_lit 1) = a
-/
theorem natPow_one_natMod : Nat.mod (Nat.pow a (nat_lit 1)) m = Nat.mod a m := by rw [natPow_one]
/-
**Mathlib.Meta.NormNum.IsNatPowModT.bit1** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta
.NormNum.IsNatPowModT`。
形式化陈述：∀ {a b m : ℕ} {c : ℕ},   Mathlib.Meta.NormNum.IsNatPowModT ((a.pow b).mod 
m = c) a (2 * b + 1) m ((c.mul ((c.mul a).mod m)).mod m)
参数：(a.pow b).mod m = c；2 * b + 1；(c.mul ((c.mul a).mod m)).mod m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.mul_mod`：∀ (a b n : ℕ), a * b % n = a % n * (b % n) % n
· 使用定理 `Nat.mod_mod`：∀ (a n : ℕ), a % n % n = a % n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem IsNatPowModT.bit1 :
    IsNatPowModT (Nat.mod (Nat.pow a b) m = c) a (nat_lit 2 * b + 1) m
      (Nat.mod (Nat.mul c (Nat.mod (Nat.mul c a) m)) m) :=
  ⟨by
    rintro rfl
    change a ^ (2 * b + 1) % m = (a ^ b % m) * ((a ^ b % m * a) % m) % m
    rw [pow_add, two_mul, pow_add, pow_one, Nat.mul_mod (a ^ b % m) a, Nat.mod_mod,
      ← Nat.mul_mod (a ^ b) a, ← Nat.mul_mod, mul_assoc]⟩

/-- Evaluates and proves `a^b % m` for natural numbers using fast modular exponentiation. -/
/-
**Mathlib.Meta.NormNum.evalNatPowMod** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：(a b m : Q(ℕ)) → (c : Q(ℕ)) × Q((«$a».pow «$b»).mod «$m» = «$c»)
参数：ℕ；ℕ；«$a».pow «$b»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates and proves `a^b % m` for natural numbers using fast modular exponentia
tion.
-/
partial def evalNatPowMod (a b m : Q(ℕ)) : (c : Q(ℕ)) × Q(Nat.mod (Nat.pow $a $b) $m = $c) :=
  if b.natLit! = 0 then
    haveI : $b =Q 0 := ⟨⟩
    if m.natLit! = 0 then -- a ^ 0 % 0 = 1
      haveI : $m =Q 0 := ⟨⟩
      ⟨q(nat_lit 1), q(natPow_zero_natMod_zero)⟩
    else
      have m' : Q(ℕ) := mkRawNatLit (m.natLit! - 1)
      if m'.natLit! = 0 then -- a ^ 0 % 1 = 0
        haveI : $m =Q 1 := ⟨⟩
        ⟨q(nat_lit 0), q(natPow_zero_natMod_one)⟩
      else -- a ^ 0 % m = 1
        have m'' : Q(ℕ) := mkRawNatLit (m'.natLit! - 1)
        haveI : $m =Q Nat.succ (Nat.succ $m'') := ⟨⟩
        ⟨q(nat_lit 1), q(natPow_zero_natMod_succ_succ)⟩
  else if b.natLit! = 1 then -- a ^ 1 % m = a % m
    have c : Q(ℕ) := mkRawNatLit (a.natLit! % m.natLit!)
    haveI : $b =Q 1 := ⟨⟩
    haveI : $c =Q Nat.mod $a $m := ⟨⟩
    ⟨c, q(natPow_one_natMod)⟩
  else
    have c₀ : Q(ℕ) := mkRawNatLit (a.natLit! % m.natLit!)
    haveI : $c₀ =Q Nat.mod $a $m := ⟨⟩
    let ⟨c, p⟩ := go b.natLit!.log2 a m q(nat_lit 1) c₀ b _ .rfl
    ⟨c, q(($p).run)⟩
where
  /-- Invariants: `a ^ b₀ % m = c₀`, `depth > 0`, `b >>> depth = b₀` -/
  go (depth : Nat) (a m b₀ c₀ b : Q(ℕ))
      (p : Q(Prop)) (hp : $p =Q (Nat.mod (Nat.pow $a $b₀) $m = $c₀)) :
      (c : Q(ℕ)) × Q(IsNatPowModT $p $a $b $m $c) :=
    let b' := b.natLit!
    let m' := m.natLit!
    if depth ≤ 1 then
      let a' := a.natLit!
      let c₀' := c₀.natLit!
      if b' &&& 1 == 0 then
        have c : Q(ℕ) := mkRawNatLit ((c₀' * c₀') % m')
        haveI : $c =Q Nat.mod (Nat.mul $c₀ $c₀) $m := ⟨⟩
        haveI : $b =Q 2 * $b₀ := ⟨⟩
        ⟨c, q(IsNatPowModT.bit0)⟩
      else
        have c : Q(ℕ) := mkRawNatLit ((c₀' * ((c₀' * a') % m')) % m')
        haveI : $c =Q Nat.mod (Nat.mul $c₀ (Nat.mod (Nat.mul $c₀ $a) $m)) $m := ⟨⟩
        haveI : $b =Q 2 * $b₀ + 1 := ⟨⟩
        ⟨c, q(IsNatPowModT.bit1)⟩
    else
      let d := depth >>> 1
      have hi : Q(ℕ) := mkRawNatLit (b' >>> d)
      let ⟨c1, p1⟩ := go (depth - d) a m b₀ c₀ hi p (by exact hp)
      let ⟨c2, p2⟩ := go d a m hi c1 b q(Nat.mod (Nat.pow $a $hi) $m = $c1) ⟨⟩
      ⟨c2, q(($p1).trans $p2)⟩
end NormNum
end Meta
end Mathlib

