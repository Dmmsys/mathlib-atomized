/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Mario Carneiro
-/
module

public import Mathlib.Tactic.NormNum.Ineq

/-!
# `norm_num` extension for integer div/mod and divides

This file adds support for the `%`, `/`, and `∣` (divisibility) operators on `ℤ`
to the `norm_num` tactic.
-/

public meta section

namespace Mathlib
open Lean
open Meta

namespace Meta.NormNum
open Qq

/-
**Mathlib.Meta.NormNum.isInt_ediv_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：∀ {a b r : ℤ}, Mathlib.Meta.NormNum.IsInt a r → Mathlib.Meta.NormNum.IsNat
 b 0 → Mathlib.Meta.NormNum.IsNat (a / b) 0
参数：a / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.ediv_zero`：∀ (a : ℤ), a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isInt_ediv_zero : ∀ {a b r : ℤ}, IsInt a r → IsNat b (nat_lit 0) → IsNat (a / b) (nat_lit 0)
  | _, _, _, ⟨rfl⟩, ⟨rfl⟩ => ⟨by simp [Int.ediv_zero]⟩
/-
**Mathlib.Meta.NormNum.isInt_ediv** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：isInt_ediv {a b q m a' : Int} {b' r : Nat} (ha : IsInt a a') (hb : IsNat b
 b') (hm : q * b' = m) (h : r + m = a') (h₂ : Nat.blt r b' = true) : IsInt (a / 
b) q
参数：ha : IsInt a a'；hb : IsNat b b'；hm : q * b' = m；h : r + m = a'；h₂ : Nat.blt r
 b' = true。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.add_mul_ediv_right`：∀ (a b : ℤ) {c : ℤ}, c ≠ 0 → (a + b * c) / c = a
 / c + b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.blt_eq`：∀ {x y : ℕ}, (x.blt y = true) = (x < y)
· 使用定理 `Int.ediv_eq_zero_of_lt`：∀ {a b : ℤ}, 0 ≤ a → a < b → a / b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma isInt_ediv {a b q m a' : ℤ} {b' r : ℕ}
    (ha : IsInt a a') (hb : IsNat b b')
    (hm : q * b' = m) (h : r + m = a') (h₂ : Nat.blt r b' = true) :
    IsInt (a / b) q := ⟨by
  obtain ⟨⟨rfl⟩, ⟨rfl⟩⟩ := ha, hb
  simp only [Nat.blt_eq] at h₂; simp only [← h, ← hm, Int.cast_id]
  rw [Int.add_mul_ediv_right _ _ (Int.ofNat_ne_zero.2 ((Nat.zero_le ..).trans_lt h₂).ne')]
  rw [Int.ediv_eq_zero_of_lt, zero_add] <;> [simp; simpa using h₂]⟩
/-
**Mathlib.Meta.NormNum.isInt_ediv_neg** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isInt_ediv_neg {a b q q' : Int} (h : IsInt (a / -b) q) (hq : -q = q') : Is
Int (a / b) q'
参数：h : IsInt (a / -b) q；hq : -q = q'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_id`：∀ {n : ℤ}, ↑n = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Meta.NormNum.IsInt.out`：∀ {α : Type u} [inst : Ring α] {a : α} {
n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → a = ↑n
· 使用定理 `Int.ediv_neg`：∀ (a b : ℤ), a / -b = -(a / b)
· 使用定理 `Int.neg_neg`：∀ (a : ℤ), - -a = a
-/
lemma isInt_ediv_neg {a b q q' : ℤ} (h : IsInt (a / -b) q) (hq : -q = q') : IsInt (a / b) q' :=
  ⟨by rw [Int.cast_id, ← hq, ← @Int.cast_id q, ← h.out, ← Int.ediv_neg, Int.neg_neg]⟩
/-
**Mathlib.Meta.NormNum.isNat_neg_of_isNegNat** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.
Meta.NormNum`。
形式化陈述：isNat_neg_of_isNegNat {a : Int} {b : Nat} (h : IsInt a (.negOfNat b)) : Is
Nat (-a) b
参数：h : IsInt a (.negOfNat b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.out`：∀ {α : Type u} [inst : Ring α] {a : α} {
n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → a = ↑n
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isNat_neg_of_isNegNat {a : ℤ} {b : ℕ} (h : IsInt a (.negOfNat b)) : IsNat (-a) b :=
  ⟨by simp [h.out]⟩

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `Int.ediv a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ : ℤ) / _, Int.ediv _ _]
/-
**Mathlib.Meta.NormNum.evalIntDiv** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `Int.ediv a b`
,
such that `norm_num` successfully recognises both `a` and `b`.
-/
partial def evalIntDiv : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℤ))) (b : Q(ℤ)) ← whnfR e | failure
  -- We assert that the default instance for `HDiv` is `Int.div` when the first parameter is `ℤ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(HDiv.hDiv (α := ℤ))
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℤ := ⟨⟩
  haveI' : $e =Q ($a / $b) := ⟨⟩
  let rℤ : Q(Ring ℤ) := q(Int.instRing)
  let ⟨za, na, pa⟩ ← (← derive a).toInt rℤ
  match ← derive (u := .zero) b with
  | .isNat inst nb pb =>
    assumeInstancesCommute
    if nb.natLit! == 0 then
      have _ : $nb =Q nat_lit 0 := ⟨⟩
      return .isNat q(instAddMonoidWithOne) q(nat_lit 0) q(isInt_ediv_zero $pa $pb)
    else
      let ⟨zq, q, p⟩ := core a na za pa b nb pb
      return .isInt rℤ q zq p
  | .isNegNat _ nb pb =>
    assumeInstancesCommute
    let ⟨zq, q, p⟩ := core a na za pa q(-$b) nb q(isNat_neg_of_isNegNat $pb)
    have q' := mkRawIntLit (-zq)
    have : Q(-$q = $q') := (q(Eq.refl $q') :)
    return .isInt rℤ q' (-zq) q(isInt_ediv_neg $p $this)
  | _ => failure
where
  /-- Given a result for evaluating `a b` in `ℤ` where `b > 0`, evaluate `a / b`. -/
  core (a na : Q(ℤ)) (za : ℤ) (pa : Q(IsInt $a $na))
      (b : Q(ℤ)) (nb : Q(ℕ)) (pb : Q(IsNat $b $nb)) :
      ℤ × (q : Q(ℤ)) × Q(IsInt ($a / $b) $q) :=
    let b := nb.natLit!
    let q := za / b
    have nq := mkRawIntLit q
    let r := za.natMod b
    have nr : Q(ℕ) := mkRawNatLit r
    let m := q * b
    have nm := mkRawIntLit m
    have pf₁ : Q($nq * $nb = $nm) := (q(Eq.refl $nm) :)
    have pf₂ : Q($nr + $nm = $na) := (q(Eq.refl $na) :)
    have pf₃ : Q(Nat.blt $nr $nb = true) := (q(Eq.refl true) :)
    ⟨q, nq, q(isInt_ediv $pa $pb $pf₁ $pf₂ $pf₃)⟩
/-
**Mathlib.Meta.NormNum.isInt_emod_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：∀ {a b r : ℤ}, Mathlib.Meta.NormNum.IsInt a r → Mathlib.Meta.NormNum.IsNat
 b 0 → Mathlib.Meta.NormNum.IsInt (a % b) r
参数：a % b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.emod_zero`：∀ (a : ℤ), a % 0 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma isInt_emod_zero : ∀ {a b r : ℤ}, IsInt a r → IsNat b (nat_lit 0) → IsInt (a % b) r
  | _, _, _, e, ⟨rfl⟩ => by simp [e]
/-
**Mathlib.Meta.NormNum.isInt_emod** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：isInt_emod {a b q m a' : Int} {b' r : Nat} (ha : IsInt a a') (hb : IsNat b
 b') (hm : q * b' = m) (h : r + m = a') (h₂ : Nat.blt r b' = true) : IsNat (a % 
b) r
参数：ha : IsInt a a'；hb : IsNat b b'；hm : q * b' = m；h : r + m = a'；h₂ : Nat.blt r
 b' = true。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.add_mul_emod_self_right`：∀ (a b c : ℤ), (a + b * c) % c = a % c
· 使用定理 `Int.emod_eq_of_lt`：∀ {a b : ℤ}, 0 ≤ a → a < b → a % b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.blt_eq`：∀ {x y : ℕ}, (x.blt y = true) = (x < y)
-/
lemma isInt_emod {a b q m a' : ℤ} {b' r : ℕ}
    (ha : IsInt a a') (hb : IsNat b b')
    (hm : q * b' = m) (h : r + m = a') (h₂ : Nat.blt r b' = true) :
    IsNat (a % b) r := ⟨by
  obtain ⟨⟨rfl⟩, ⟨rfl⟩⟩ := ha, hb
  simp only [← h, ← hm, Int.add_mul_emod_self_right]
  rw [Int.emod_eq_of_lt] <;> [simp; simpa using h₂]⟩
/-
**Mathlib.Meta.NormNum.isInt_emod_neg** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isInt_emod_neg {a b : Int} {r : Nat} (h : IsNat (a % -b) r) : IsNat (a % b
) r
参数：h : IsNat (a % -b) r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.emod_neg`：∀ (a b : ℤ), a % -b = a % b
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
-/
lemma isInt_emod_neg {a b : ℤ} {r : ℕ} (h : IsNat (a % -b) r) : IsNat (a % b) r :=
  ⟨by rw [← Int.emod_neg, h.out]⟩

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `Int.emod a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ : ℤ) % _, Int.emod _ _]
/-
**Mathlib.Meta.NormNum.evalIntMod** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `Int.emod a b`
,
such that `norm_num` successfully recognises both `a` and `b`.
-/
partial def evalIntMod : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℤ))) (b : Q(ℤ)) ← whnfR e | failure
  -- We assert that the default instance for `HMod` is `Int.mod` when the first parameter is `ℤ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(HMod.hMod (α := ℤ))
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℤ := ⟨⟩
  haveI' : $e =Q ($a % $b) := ⟨⟩
  let rℤ : Q(Ring ℤ) := q(Int.instRing)
  let some ⟨za, na, pa⟩ := (← derive a).toInt rℤ | failure
  go a na za pa b (← derive (u := .zero) b)
where
  /-- Given a result for evaluating `a b` in `ℤ`, evaluate `a % b`. -/
  go (a na : Q(ℤ)) (za : ℤ) (pa : Q(IsInt $a $na))
      (b : Q(ℤ)) : Result b → Option (Result q($a % $b))
    | .isNat inst nb pb => do
      assumeInstancesCommute
      if nb.natLit! == 0 then
        have _ : $nb =Q nat_lit 0 := ⟨⟩
        return .isInt q(Int.instRing) na za q(isInt_emod_zero $pa $pb)
      else
        let ⟨r, p⟩ := core a na za pa b nb pb
        return .isNat q(instAddMonoidWithOne) r p
    | .isNegNat _ nb pb => do
      assumeInstancesCommute
      let ⟨r, p⟩ := core a na za pa q(-$b) nb q(isNat_neg_of_isNegNat $pb)
      return .isNat q(instAddMonoidWithOne) r q(isInt_emod_neg $p)
    | _ => none

  /-- Given a result for evaluating `a b` in `ℤ` where `b > 0`, evaluate `a % b`. -/
  core (a na : Q(ℤ)) (za : ℤ) (pa : Q(IsInt $a $na))
      (b : Q(ℤ)) (nb : Q(ℕ)) (pb : Q(IsNat $b $nb)) :
      (r : Q(ℕ)) × Q(IsNat ($a % $b) $r) :=
    let b := nb.natLit!
    let q := za / b
    have nq := mkRawIntLit q
    let r := za.natMod b
    have nr : Q(ℕ) := mkRawNatLit r
    let m := q * b
    have nm := mkRawIntLit m
    have pf₁ : Q($nq * $nb = $nm) := (q(Eq.refl $nm) :)
    have pf₂ : Q($nr + $nm = $na) := (q(Eq.refl $na) :)
    have pf₃ : Q(Nat.blt $nr $nb = true) := (q(Eq.refl true) :)
    ⟨nr, q(isInt_emod $pa $pb $pf₁ $pf₂ $pf₃)⟩
/-
**Mathlib.Meta.NormNum.isInt_dvd_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：∀ {a b a' b' c : ℤ}, Mathlib.Meta.NormNum.IsInt a a' → Mathlib.Meta.NormNu
m.IsInt b b' → a'.mul c = b' → a ∣ b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isInt_dvd_true : {a b : ℤ} → {a' b' c : ℤ} →
    IsInt a a' → IsInt b b' → Int.mul a' c = b' → a ∣ b
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨_, rfl⟩
/-
**Mathlib.Meta.NormNum.isInt_dvd_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：∀ {a b a' b' : ℤ}, Mathlib.Meta.NormNum.IsInt a a' → Mathlib.Meta.NormNum.
IsInt b b' → (b'.emod a' != 0) = true → ¬a ∣ b
参数：b'.emod a' != 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Int.emod_eq_zero_of_dvd`：∀ {a b : ℤ}, a ∣ b → b % a = 0
· 使用定理 `Int.instLawfulBEq`：LawfulBEq ℤ
-/
theorem isInt_dvd_false : {a b : ℤ} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → Int.emod b' a' != 0 → ¬a ∣ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, e => mt Int.emod_eq_zero_of_dvd (by simpa using! e)

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `(a : ℤ) ∣ b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.NormNum.evalIntDvd** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `(a : ℤ) ∣ b`,
such that `norm_num` successfully recognises both `a` and `b`.
-/
@[norm_num (_ : ℤ) ∣ _] def evalIntDvd : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℤ))) (b : Q(ℤ)) ← whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q Prop := ⟨⟩
  haveI' : $e =Q ($a ∣ $b) := ⟨⟩
  -- We assert that the default instance for `Dvd` is `Int.dvd` when the first parameter is `ℕ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(Dvd.dvd (α := ℤ))
  let rℤ : Q(Ring ℤ) := q(Int.instRing)
  let ⟨za, na, pa⟩ ← (← derive a).toInt rℤ
  let ⟨zb, nb, pb⟩ ← (← derive b).toInt rℤ
  if zb % za == 0 then
    let zc := zb / za
    have c := mkRawIntLit zc
    haveI' : Int.mul $na $c =Q $nb := ⟨⟩
    return .isTrue q(isInt_dvd_true $pa $pb (.refl $nb))
  else
    have : Q(Int.emod $nb $na != 0) := (q(Eq.refl true) : Expr)
    return .isFalse q(isInt_dvd_false $pa $pb $this)

end Mathlib.Meta.NormNum

