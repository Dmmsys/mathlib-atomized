/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.Partrec
public import Mathlib.Data.Option.Basic

/-!
# Gödel Numbering for Partial Recursive Functions.

This file defines `Nat.Partrec.Code`, an inductive datatype describing code for partial
recursive functions on ℕ. It defines an encoding for these codes, and proves that the constructors
are primitive recursive with respect to the encoding.

It also defines the evaluation of these codes as partial functions using `PFun`, and proves that a
function is partially recursive (as defined by `Nat.Partrec`) if and only if it is the evaluation
of some code.

## Main Definitions

* `Nat.Partrec.Code`: Inductive datatype for partial recursive codes.
* `Nat.Partrec.Code.encodeCode`: A (computable) encoding of codes as natural numbers.
* `Nat.Partrec.Code.ofNatCode`: The inverse of this encoding.
* `Nat.Partrec.Code.eval`: The interpretation of a `Nat.Partrec.Code` as a partial function.

## Main Results

* `Nat.Partrec.Code.primrec_recOn`: Recursion on `Nat.Partrec.Code` is primitive recursive.
* `Nat.Partrec.Code.computable_recOn`: Recursion on `Nat.Partrec.Code` is computable.
* `Nat.Partrec.Code.smn`: The $S_n^m$ theorem.
* `Nat.Partrec.Code.exists_code`: Partial recursiveness is equivalent to being the eval of a code.
* `Nat.Partrec.Code.primrec_evaln`: `evaln` is primitive recursive.
* `Nat.Partrec.Code.fixed_point`: Roger's fixed point theorem.
* `Nat.Partrec.Code.fixed_point₂`: Kleene's second recursion theorem.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]

-/

@[expose] public section

open Encodable Denumerable

namespace Nat.Partrec

/-
**Nat.Partrec.rfind'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec`。
形式化陈述：rfind' {f} (hf : Nat.Partrec f) : Nat.Partrec (Nat.unpaired fun a m => (Na
t.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + m))).map (· + m))
参数：hf : Nat.Partrec f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Partrec₂.unpaired'`：unpaired' {f : Nat -> Nat ->. Nat} : Nat.Partrec (Na
t.unpaired f) ↔ Partrec₂ f
· 使用定理 `Partrec.map`：map {f : α ->. β} {g : α -> β -> σ} (hf : Partrec f) (hg : 
Computable₂ g) : Partrec fun a => (f a).map (g a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Partrec.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β →. σ} {g 
: …
· 使用定理 `Partrec.nat_iff`：nat_iff {f : Nat ->. Nat} : Partrec f ↔ Nat.Partrec f
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec₂.pair`：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α] [i
nst_1 : Primcodable β], Primrec₂ Prod.mk
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.unpair`：unpair : Primrec Nat.unpair
· 使用定理 `Primrec.nat_add`：nat_add : Primrec₂ ((· + ·) : Nat -> Nat -> Nat)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Computable.to₂`：to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ f
un a b => f (a, b)
-/
theorem rfind' {f} (hf : Nat.Partrec f) :
    Nat.Partrec
      (Nat.unpaired fun a m =>
        (Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + m))).map (· + m)) :=
  Partrec₂.unpaired'.2 <| by
    refine
      Partrec.map
        ((@Partrec₂.unpaired' fun a b : ℕ =>
              Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + b))).1
          ?_)
        (Primrec.nat_add.comp Primrec.snd <| Primrec.snd.comp Primrec.fst).to_comp.to₂
    have : Nat.Partrec (fun a => Nat.rfind (fun n => (fun m => decide (m = 0)) <$>
      Nat.unpaired (fun a b => f (Nat.pair (Nat.unpair a).1 (b + (Nat.unpair a).2)))
        (Nat.pair a n))) :=
      rfind
        (Partrec₂.unpaired'.2
          ((Partrec.nat_iff.2 hf).comp
              (Primrec₂.pair.comp (Primrec.fst.comp <| Primrec.unpair.comp Primrec.fst)
                  (Primrec.nat_add.comp Primrec.snd
                    (Primrec.snd.comp <| Primrec.unpair.comp Primrec.fst))).to_comp))
    simpa

/-- Code for partial recursive functions from ℕ to ℕ.
See `Nat.Partrec.Code.eval` for the interpretation of these constructors.
-/
/-
**Nat.Partrec.Code** 是 Mathlib 中的一个归纳类型，位于命名空间 `Nat.Partrec`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Code for partial recursive functions from ℕ to ℕ.
See `Nat.Partrec.Code.eval` for the interpretation of these constructors.
-/
inductive Code : Type
  | zero : Code
  | succ : Code
  | left : Code
  | right : Code
  | pair : Code → Code → Code
  | comp : Code → Code → Code
  | prec : Code → Code → Code
  | rfind' : Code → Code

compile_inductive% Code

end Nat.Partrec

namespace Nat.Partrec.Code

/-
**Nat.Partrec.Code.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：instInhabited : Inhabited Code
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited Code :=
  ⟨zero⟩

/-- Returns a code for the constant function outputting a particular natural. -/
/-
**Nat.Partrec.Code.const** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：ℕ → Nat.Partrec.Code
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns a code for the constant function outputting a particular natural.
-/
protected def const : ℕ → Code
  | 0 => zero
  | n + 1 => comp succ (Code.const n)
/-
**Nat.Partrec.Code.const_inj** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：const_inj : forall {n₁ n₂}, Nat.Partrec.Code.const n₁ = Nat.Partrec.Code.c
onst n₂ -> n₁ = n₂ | 0, 0, _ => by simp | n₁ + 1, n₂ + 1, h => by dsimp [Nat.Par
trec.Code.const] at h injection h with h₁ h₂ simp only [const_inj h₂]  /-- A cod
e for the identity function. -/ protected def id : Code
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_inj : ∀ {n₁ n₂}, Nat.Partrec.Code.const n₁ = Nat.Partrec.Code.const n₂ → n₁ = n₂
  | 0, 0, _ => by simp
  | n₁ + 1, n₂ + 1, h => by
    dsimp [Nat.Partrec.Code.const] at h
    injection h with h₁ h₂
    simp only [const_inj h₂]

/-- A code for the identity function. -/
/-
**Nat.Partrec.Code.id** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：Nat.Partrec.Code
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A code for the identity function.
-/
protected def id : Code :=
  pair left right

/-- Given a code `c` taking a pair as input, returns a code using `n` as the first argument to `c`.
-/
/-
**Nat.Partrec.Code.curry** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：curry (c : Code) (n : Nat) : Code
参数：c : Code；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a code `c` taking a pair as input, returns a code using `n` as the first a
rgument to `c`.
-/
def curry (c : Code) (n : ℕ) : Code :=
  comp c (pair (Code.const n) Code.id)

/-- An encoding of a `Nat.Partrec.Code` as a ℕ. -/
/-
**Nat.Partrec.Code.encodeCode** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：Nat.Partrec.Code → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An encoding of a `Nat.Partrec.Code` as a ℕ.
-/
def encodeCode : Code → ℕ
  | zero => 0
  | succ => 1
  | left => 2
  | right => 3
  | pair cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 4
  | comp cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) + 4
  | prec cf cg => (2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 1) + 4
  | rfind' cf => (2 * (2 * encodeCode cf + 1) + 1) + 4

/--
A decoder for `Nat.Partrec.Code.encodeCode`, taking any ℕ to the `Nat.Partrec.Code` it represents.
-/
/-
**Nat.Partrec.Code.ofNatCode** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：ofNatCode : Nat -> Code | 0 => zero | 1 => succ | 2 => left | 3 => right |
 n + 4 => let m
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A decoder for `Nat.Partrec.Code.encodeCode`, taking any ℕ to the `Nat.Partrec.Co
de` it represents.
-/
def ofNatCode : ℕ → Code
  | 0 => zero
  | 1 => succ
  | 2 => left
  | 3 => right
  | n + 4 =>
    let m := n.div2.div2
    have hm : m < n + 4 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
    match n.bodd, n.div2.bodd with
    | false, false => pair (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | false, true => comp (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true, false => prec (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true, true => rfind' (ofNatCode m)

set_option backward.privateInPublic true in
/-- Proof that `Nat.Partrec.Code.ofNatCode` is the inverse of `Nat.Partrec.Code.encodeCode` -/
/-
**Nat.Partrec.Code.encode_ofNatCode** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Proof that `Nat.Partrec.Code.ofNatCode` is the inverse of `Nat.Partrec.Code.enco
deCode`
-/
private theorem encode_ofNatCode : ∀ n, encodeCode (ofNatCode n) = n
  | 0 => by simp [ofNatCode, encodeCode]
  | 1 => by simp [ofNatCode, encodeCode]
  | 2 => by simp [ofNatCode, encodeCode]
  | 3 => by simp [ofNatCode, encodeCode]
  | n + 4 => by
    let m := n.div2.div2
    have hm : m < n + 4 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := encode_ofNatCode m
    have IH1 := encode_ofNatCode m.unpair.1
    have IH2 := encode_ofNatCode m.unpair.2
    conv_rhs => rw [← Nat.bit_bodd_div2 n, ← Nat.bit_bodd_div2 n.div2]
    simp only [ofNatCode.eq_5]
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [m, encodeCode, IH, IH1, IH2, Nat.bit_val]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Nat.Partrec.Code.instDenumerable** 是 Mathlib 中的一个实例，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：instDenumerable : Denumerable Code
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Computability.PartrecCode.0.Nat.Partrec.Code.encode_ofN
atCode`：∀ (n : ℕ), (Nat.Partrec.Code.ofNatCode n).encodeCode = n
-/
instance instDenumerable : Denumerable Code :=
  mk'
    ⟨encodeCode, ofNatCode, fun c => by
        induction c <;> simp [encodeCode, ofNatCode, Nat.div2_val, *],
      encode_ofNatCode⟩
/-
**Nat.Partrec.Code.encodeCode_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：encodeCode_eq : encode = encodeCode
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encodeCode_eq : encode = encodeCode :=
  rfl
/-
**Nat.Partrec.Code.ofNatCode_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：ofNatCode_eq : ofNat Code = ofNatCode
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofNatCode_eq : ofNat Code = ofNatCode :=
  rfl
/-
**Nat.Partrec.Code.encode_lt_pair** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：encode_lt_pair (cf cg) : encode cf < encode (pair cf cg) ∧ encode cg < enc
ode (pair cf cg)
参数：cf cg。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.left_le_pair`：left_le_pair (a b : Nat) : a <= pair a b
· 使用定理 `Nat.right_le_pair`：right_le_pair (a b : Nat) : b <= pair a b
-/
theorem encode_lt_pair (cf cg) :
    encode cf < encode (pair cf cg) ∧ encode cg < encode (pair cf cg) := by
  simp only [encodeCode_eq, encodeCode]
  have := Nat.mul_le_mul_right (Nat.pair cf.encodeCode cg.encodeCode) (by decide : 1 ≤ 2 * 2)
  rw [one_mul, mul_assoc] at this
  have := lt_of_le_of_lt this (lt_add_of_pos_right _ (by decide : 0 < 4))
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair _ _) this, lt_of_le_of_lt (Nat.right_le_pair _ _) this⟩
/-
**Nat.Partrec.Code.encode_lt_comp** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：encode_lt_comp (cf cg) : encode cf < encode (comp cf cg) ∧ encode cg < enc
ode (comp cf cg)
参数：cf cg。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Nat.Partrec.Code.encode_lt_pair`：encode_lt_pair (cf cg) : encode cf < en
code (pair cf cg) ∧ encode cg < encode (pair cf cg)
-/
theorem encode_lt_comp (cf cg) :
    encode cf < encode (comp cf cg) ∧ encode cg < encode (comp cf cg) := by
  have : encode (pair cf cg) < encode (comp cf cg) := by simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this
/-
**Nat.Partrec.Code.encode_lt_prec** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：encode_lt_prec (cf cg) : encode cf < encode (prec cf cg) ∧ encode cg < enc
ode (prec cf cg)
参数：cf cg。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Nat.Partrec.Code.encode_lt_pair`：encode_lt_pair (cf cg) : encode cf < en
code (pair cf cg) ∧ encode cg < encode (pair cf cg)
-/
theorem encode_lt_prec (cf cg) :
    encode cf < encode (prec cf cg) ∧ encode cg < encode (prec cf cg) := by
  have : encode (pair cf cg) < encode (prec cf cg) := by simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this
/-
**Nat.Partrec.Code.encode_lt_rfind'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`
。
形式化陈述：encode_lt_rfind' (cf) : encode cf < encode (rfind' cf)
参数：cf。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem encode_lt_rfind' (cf) : encode cf < encode (rfind' cf) := by
  simp only [encodeCode_eq, encodeCode]
  lia

end Nat.Partrec.Code

section
open Primrec
namespace Nat.Partrec.Code

/-
**Nat.Partrec.Code.primrec** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem primrec₂_pair : Primrec₂ pair :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)
/-
**Nat.Partrec.Code.primrec** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem primrec₂_comp : Primrec₂ comp :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double_succ.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)
/-
**Nat.Partrec.Code.primrec** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem primrec₂_prec : Primrec₂ prec :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)
/-
**Nat.Partrec.Code.primrec_rfind'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：primrec_rfind' : Primrec rfind'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.ofNat_iff`：ofNat_iff {α β} [Denumerable α] [Primcodable β] {f : 
α -> β} : Primrec f ↔ Primrec fun n => f (ofNat α n)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.encode_iff`：encode_iff {f : α -> σ} : (Primrec fun a => encode (
f a)) ↔ Primrec f
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.nat_add`：nat_add : Primrec₂ ((· + ·) : Nat -> Nat -> Nat)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.nat_double_succ`：nat_double_succ : Primrec (fun n : Nat => 2 * n
 + 1)
· 使用定理 `Primrec.ofNat`：∀ (α : Type u_4) [inst : Denumerable α], Primrec (Denumer
able.ofNat α)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
-/
theorem primrec_rfind' : Primrec rfind' :=
  ofNat_iff.2 <|
    encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <| nat_double_succ.comp <|
          encode_iff.2 <| Primrec.ofNat Code)
        (const 4)

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/-
**Nat.Partrec.Code.primrec_recOn'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：primrec_recOn' {α σ} [Primcodable α] [Primcodable σ] {c : α -> Code} (hc :
 Primrec c) {z : α -> σ} (hz : Primrec z) {s : α -> σ} (hs : Primrec s) {l : α -
> σ} (hl : Primrec l) {r : α -> σ} (hr : Primrec r) {pr : α -> Code × Code × σ ×
 σ -> σ} (hpr : Primrec₂ pr) {co : α -> Code × Code × σ × σ -> σ} (hco : Primrec
₂ co) {pc : α -> Code × Code × σ × σ -> σ} (hpc : Primrec₂ pc) {rf : α -> Code ×
 σ -> σ} (hrf : Primrec₂ rf) : let PR (a) cf cg hf hg
参数：hc : Primrec c；hz : Primrec z；hs : Primrec s；hl : Primrec l；hr : Primrec r；hp
r : Primrec₂ pr；hco : Primrec₂ co；hpc : Primrec₂ pc；hrf : Primrec₂ rf。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.option_bind`：option_bind {f : α -> Option β} {g : α -> β -> Opti
on σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).bind (g a)
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_getElem?`：∀ {α : Type u_1} [inst : Primcodable α], Primrec₂
 fun x1 x2 => x1[x2]?
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec₂.mk`：mk {f : α -> β -> σ} (hf : Primrec fun p : α × β => f p.1 p
.2) : Primrec₂ f
· 使用定理 `Primrec.unpair`：unpair : Primrec Nat.unpair
· 使用定理 `Primrec.option_map`：option_map {f : α -> Option β} {g : α -> β -> σ} (hf
 : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).map (g a)
· 使用定理 `Primrec.cond`：cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Primr
ec c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) 
el…
· 使用定理 `Primrec.nat_bodd`：nat_bodd : Primrec Nat.bodd
· 使用定理 `Primrec.nat_div2`：nat_div2 : Primrec Nat.div2
· 使用定理 `Primrec.pair`：pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable 
γ] {f : α -> β} {g : α -> γ} (hf : Primrec f) (hg : Primrec g) : Primrec fun a =
> …
· 使用定理 `Primrec.ofNat`：∀ (α : Type u_4) [inst : Denumerable α], Primrec (Denumer
able.ofNat α)
· 使用定理 `Primrec.nat_casesOn`：nat_casesOn {f : α -> Nat} {g : α -> β} {h : α -> N
at -> β} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => 
((f a).ca…
· 使用定理 `Primrec.list_length`：list_length : Primrec (@List.length α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.option_some_iff`：option_some_iff {f : α -> σ} : (Primrec fun a =
> some (f a)) ↔ Primrec f
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.nat_strong_rec`：nat_strong_rec (f : α -> Nat -> σ) {g : α -> Lis
t σ -> Option σ} (hg : Primrec₂ g) (H : forall a n, g a ((List.range n).map (f a
)) = some (f…
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `Nat.Partrec.Code.ofNatCode.eq_1`：Nat.Partrec.Code.ofNatCode 0 = Nat.Part
rec.Code.zero
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Nat.Partrec.Code.ofNatCode.eq_2`：Nat.Partrec.Code.ofNatCode 1 = Nat.Part
rec.Code.succ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 55 条，此处仅展示前 30 条）
-/
theorem primrec_recOn' {α σ}
    [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Primrec c) {z : α → σ}
    (hz : Primrec z) {s : α → σ} (hs : Primrec s) {l : α → σ} (hl : Primrec l) {r : α → σ}
    (hr : Primrec r) {pr : α → Code × Code × σ × σ → σ} (hpr : Primrec₂ pr)
    {co : α → Code × Code × σ × σ → σ} (hco : Primrec₂ co) {pc : α → Code × Code × σ × σ → σ}
    (hpc : Primrec₂ pc) {rf : α → Code × σ → σ} (hrf : Primrec₂ rf) :
    let PR (a) cf cg hf hg := pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : Code) : σ :=
      Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a)
    Primrec (fun a => F a (c a) : α → σ) := by
  intro _ _ _ _ F
  let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
    letI a := p.1.1; letI IH := p.1.2; letI n := p.2.1; letI m := p.2.2
    IH[m]?.bind fun s =>
    IH[m.unpair.1]?.bind fun s₁ =>
    IH[m.unpair.2]?.map fun s₂ =>
    cond n.bodd
      (cond n.div2.bodd (rf a (ofNat Code m, s))
        (pc a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
      (cond n.div2.bodd (co a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂))
        (pr a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
  have : Primrec G₁ :=
    option_bind (list_getElem?.comp (snd.comp fst) (snd.comp snd)) <| .mk <|
    option_bind ((list_getElem?.comp (snd.comp fst)
      (fst.comp <| Primrec.unpair.comp (snd.comp snd))).comp fst) <| .mk <|
    option_map ((list_getElem?.comp (snd.comp fst)
      (snd.comp <| Primrec.unpair.comp (snd.comp snd))).comp <| fst.comp fst) <| .mk <|
    have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
    have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m₁ := fst.comp (Primrec.unpair.comp m)
    have m₂ := snd.comp (Primrec.unpair.comp m)
    have s := snd.comp (fst.comp fst)
    have s₁ := snd.comp fst
    have s₂ := snd
    (nat_bodd.comp n).cond
      ((nat_bodd.comp <| nat_div2.comp n).cond
        (hrf.comp a (((Primrec.ofNat Code).comp m).pair s))
        (hpc.comp a (((Primrec.ofNat Code).comp m₁).pair <|
          ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
      (Primrec.cond (nat_bodd.comp <| nat_div2.comp n)
        (hco.comp a (((Primrec.ofNat Code).comp m₁).pair <|
          ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂))
        (hpr.comp a (((Primrec.ofNat Code).comp m₁).pair <|
          ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
  let G : α → List σ → Option σ := fun a IH =>
    IH.length.casesOn (some (z a)) fun n =>
    n.casesOn (some (s a)) fun n =>
    n.casesOn (some (l a)) fun n =>
    n.casesOn (some (r a)) fun n =>
    G₁ ((a, IH), n, n.div2.div2)
  have : Primrec₂ G := .mk <|
    nat_casesOn (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hs.comp (fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst))) <| .mk <|
    this.comp <|
      ((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst).pair <|
      snd.pair <| nat_div2.comp <| nat_div2.comp snd
  refine (nat_strong_rec (fun a n => F a (ofNat Code n)) this.to₂ fun a n => ?_)
    |>.comp .id (encode_iff.2 hc) |>.of_eq fun a => by simp
  iterate 4 rcases n with - | n; · simp [ofNatCode_eq, ofNatCode]; rfl
  simp only [G]; rw [List.length_map, List.length_range]
  let m := n.div2.div2
  change G₁ ((a, (List.range (n + 4)).map fun n => F a (ofNat Code n)), n, m)
    = some (F a (ofNat Code (n + 4)))
  have hm : m < n + 4 := by
    simp only [m, div2_val]
    exact lt_of_le_of_lt
      (le_trans (Nat.div_le_self ..) (Nat.div_le_self ..))
      (Nat.succ_le_succ (Nat.le_add_right ..))
  have m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
  have m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
  simp [G₁, m, hm, m1, m2]
  rw [show ofNat Code (n + 4) = ofNatCode (n + 4) from rfl]
  simp [ofNatCode]
  cases n.bodd <;> cases n.div2.bodd <;> rfl

/-- Recursion on `Nat.Partrec.Code` is primitive recursive. -/
/-
**Nat.Partrec.Code.primrec_recOn** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：primrec_recOn {α σ} [Primcodable α] [Primcodable σ] {c : α -> Code} (hc : 
Primrec c) {z : α -> σ} (hz : Primrec z) {s : α -> σ} (hs : Primrec s) {l : α ->
 σ} (hl : Primrec l) {r : α -> σ} (hr : Primrec r) {pr : α -> Code -> Code -> σ 
-> σ -> σ} (hpr : Primrec fun a : α × Code × Code × σ × σ => pr a.1 a.2.1 a.2.2.
1 a.2.2.2.1 a.2.2.2.2) {co : α -> Code -> Code -> σ -> σ -> σ} (hco : Primrec fu
n a : α × Code × Code × σ × σ => co a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) {pc :
 α -> Code -> Code -> σ ->
参数：hc : Primrec c；hz : Primrec z；hs : Primrec s；hl : Primrec l；hr : Primrec r；hp
r : Primrec fun a : α × Code × Code × σ × σ => pr a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.
2.2.2.2；hco : Primrec fun a : α × Code × Code × σ × σ => co a.1 a.2.1 a.2.2.1 a.
2.2.2.1 a.2.2.2.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.Code.primrec_recOn'`：primrec_recOn' {α σ} [Primcodable α] [P
rimcodable σ] {c : α -> Code} (hc : Primrec c) {z : α -> σ} (hz : Primrec z) {s 
: α -> σ} (hs : Primr…
· 使用定理 `Primrec₂.mk`：mk {f : α -> β -> σ} (hf : Primrec fun p : α × β => f p.1 p
.2) : Primrec₂ f

--- 原说明 ---
Recursion on `Nat.Partrec.Code` is primitive recursive.
-/
theorem primrec_recOn {α σ}
    [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Primrec c) {z : α → σ}
    (hz : Primrec z) {s : α → σ} (hs : Primrec s) {l : α → σ} (hl : Primrec l) {r : α → σ}
    (hr : Primrec r) {pr : α → Code → Code → σ → σ → σ}
    (hpr : Primrec fun a : α × Code × Code × σ × σ => pr a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {co : α → Code → Code → σ → σ → σ}
    (hco : Primrec fun a : α × Code × Code × σ × σ => co a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {pc : α → Code → Code → σ → σ → σ}
    (hpc : Primrec fun a : α × Code × Code × σ × σ => pc a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {rf : α → Code → σ → σ} (hrf : Primrec fun a : α × Code × σ => rf a.1 a.2.1 a.2.2) :
    let F (a : α) (c : Code) : σ :=
      Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (pr a) (co a) (pc a) (rf a)
    Primrec fun a => F a (c a) :=
  primrec_recOn' hc hz hs hl hr
    (pr := fun a b => pr a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpr)
    (co := fun a b => co a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hco)
    (pc := fun a b => pc a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpc)
    (rf := fun a b => rf a b.1 b.2) (.mk hrf)

end Nat.Partrec.Code
end

namespace Nat.Partrec.Code
section

open Computable

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/-- Recursion on `Nat.Partrec.Code` is computable. -/
/-
**Nat.Partrec.Code.computable_recOn** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`
。
形式化陈述：computable_recOn {α σ} [Primcodable α] [Primcodable σ] {c : α -> Code} (hc
 : Computable c) {z : α -> σ} (hz : Computable z) {s : α -> σ} (hs : Computable 
s) {l : α -> σ} (hl : Computable l) {r : α -> σ} (hr : Computable r) {pr : α -> 
Code × Code × σ × σ -> σ} (hpr : Computable₂ pr) {co : α -> Code × Code × σ × σ 
-> σ} (hco : Computable₂ co) {pc : α -> Code × Code × σ × σ -> σ} (hpc : Computa
ble₂ pc) {rf : α -> Code × σ -> σ} (hrf : Computable₂ rf) : let PR (a) cf cg hf 
hg
参数：hc : Computable c；hz : Computable z；hs : Computable s；hl : Computable l；hr : 
Computable r；hpr : Computable₂ pr；hco : Computable₂ co；hpc : Computable₂ pc；hrf 
: Computable₂ rf。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.option_bind`：option_bind {f : α -> Option β} {g : α -> β -> O
ption σ} (hf : Computable f) (hg : Computable₂ g) : Computable fun a => (f a).bi
nd (g a)
· 使用定理 `Computable₂.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Ty
pe u_5} [inst : Primcodable α] [inst_1 : Primcodable β]   [inst_2 : Primcodable 
γ] [in…
· 使用定理 `Computable.list_getElem?`：∀ {α : Type u_1} [inst : Primcodable α], Compu
table₂ fun x1 x2 => x1[x2]?
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `Computable.fst`：fst : Computable (@Prod.fst α β)
· 使用定理 `Computable₂.mk`：mk {f : α -> β -> σ} (hf : Computable fun p : α × β => f
 p.1 p.2) : Computable₂ f
· 使用定理 `Computable.unpair`：unpair : Computable Nat.unpair
· 使用定理 `Computable.option_map`：option_map {f : α -> Option β} {g : α -> β -> σ} 
(hf : Computable f) (hg : Computable₂ g) : Computable fun a => (f a).map (g a)
· 使用定理 `Computable.cond`：cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Co
mputable c) (hf : Computable f) (hg : Computable g) : Computable fun a => cond (
c a) …
· 使用定理 `Computable.nat_bodd`：nat_bodd : Computable Nat.bodd
· 使用定理 `Computable.nat_div2`：nat_div2 : Computable Nat.div2
· 使用定理 `Computable.pair`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {f : α → β} {
g : α…
· 使用定理 `Computable.ofNat`：∀ (α : Type u_5) [inst : Denumerable α], Computable (D
enumerable.ofNat α)
· 使用定理 `Computable.nat_casesOn`：nat_casesOn {f : α -> Nat} {g : α -> σ} {h : α -
> Nat -> σ} (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) : Compu
table fun a …
· 使用定理 `Computable.list_length`：list_length : Computable (@List.length α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Computable.option_some_iff`：option_some_iff {f : α -> σ} : (Computable f
un a => Option.some (f a)) ↔ Computable f
· 使用定理 `Computable.of_eq`：of_eq {f g : α -> σ} (hf : Computable f) (H : forall n
, f n = g n) : Computable g
· 使用定理 `Computable.nat_strong_rec`：nat_strong_rec (f : α -> Nat -> σ) {g : α -> 
List σ -> Option σ} (hg : Computable₂ g) (H : forall a n, g a ((List.range n).ma
p (f a)) = Opti…
· 使用定理 `Computable.to₂`：to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ f
un a b => f (a, b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `Nat.Partrec.Code.ofNatCode.eq_1`：Nat.Partrec.Code.ofNatCode 0 = Nat.Part
rec.Code.zero
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Nat.Partrec.Code.ofNatCode.eq_2`：Nat.Partrec.Code.ofNatCode 1 = Nat.Part
rec.Code.succ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
Recursion on `Nat.Partrec.Code` is computable.
-/
theorem computable_recOn {α σ} [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Computable c)
    {z : α → σ} (hz : Computable z) {s : α → σ} (hs : Computable s) {l : α → σ} (hl : Computable l)
    {r : α → σ} (hr : Computable r) {pr : α → Code × Code × σ × σ → σ} (hpr : Computable₂ pr)
    {co : α → Code × Code × σ × σ → σ} (hco : Computable₂ co) {pc : α → Code × Code × σ × σ → σ}
    (hpc : Computable₂ pc) {rf : α → Code × σ → σ} (hrf : Computable₂ rf) :
    let PR (a) cf cg hf hg := pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : Code) : σ :=
      Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a)
    Computable fun a => F a (c a) := by
  -- TODO(Mario): less copy-paste from previous proof
  intro _ _ _ _ F
  let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
    letI a := p.1.1; letI IH := p.1.2; letI n := p.2.1; letI m := p.2.2
    IH[m]?.bind fun s =>
    IH[m.unpair.1]?.bind fun s₁ =>
    IH[m.unpair.2]?.map fun s₂ =>
    cond n.bodd
      (cond n.div2.bodd (rf a (ofNat Code m, s))
        (pc a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
      (cond n.div2.bodd (co a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂))
        (pr a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
  have : Computable G₁ := by
    refine option_bind (list_getElem?.comp (snd.comp fst) (snd.comp snd)) <| .mk ?_
    refine option_bind ((list_getElem?.comp (snd.comp fst)
      (fst.comp <| Computable.unpair.comp (snd.comp snd))).comp fst) <| .mk ?_
    refine option_map ((list_getElem?.comp (snd.comp fst)
      (snd.comp <| Computable.unpair.comp (snd.comp snd))).comp <| fst.comp fst) <| .mk ?_
    exact
      have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
      have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
      have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
      have m₁ := fst.comp (Computable.unpair.comp m)
      have m₂ := snd.comp (Computable.unpair.comp m)
      have s := snd.comp (fst.comp fst)
      have s₁ := snd.comp fst
      have s₂ := snd
      (nat_bodd.comp n).cond
        ((nat_bodd.comp <| nat_div2.comp n).cond
          (hrf.comp a (((Computable.ofNat Code).comp m).pair s))
          (hpc.comp a (((Computable.ofNat Code).comp m₁).pair <|
            ((Computable.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
        (Computable.cond (nat_bodd.comp <| nat_div2.comp n)
          (hco.comp a (((Computable.ofNat Code).comp m₁).pair <|
            ((Computable.ofNat Code).comp m₂).pair <| s₁.pair s₂))
          (hpr.comp a (((Computable.ofNat Code).comp m₁).pair <|
            ((Computable.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
  let G : α → List σ → Option σ := fun a IH =>
    IH.length.casesOn (some (z a)) fun n =>
    n.casesOn (some (s a)) fun n =>
    n.casesOn (some (l a)) fun n =>
    n.casesOn (some (r a)) fun n =>
    G₁ ((a, IH), n, n.div2.div2)
  have : Computable₂ G := .mk <|
    nat_casesOn (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hs.comp (fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst))) <| .mk <|
    this.comp <|
      ((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst).pair <|
      snd.pair <| nat_div2.comp <| nat_div2.comp snd
  refine (nat_strong_rec (fun a n => F a (ofNat Code n)) this.to₂ fun a n => ?_)
    |>.comp .id (encode_iff.2 hc) |>.of_eq fun a => by simp
  iterate 4 rcases n with - | n; · simp [ofNatCode_eq, ofNatCode]; rfl
  simp only [G]; rw [List.length_map, List.length_range]
  let m := n.div2.div2
  change G₁ ((a, (List.range (n + 4)).map fun n => F a (ofNat Code n)), n, m)
    = some (F a (ofNat Code (n + 4)))
  have hm : m < n + 4 := by
    simp only [m, div2_val]
    exact lt_of_le_of_lt
      (le_trans (Nat.div_le_self ..) (Nat.div_le_self ..))
      (Nat.succ_le_succ (Nat.le_add_right ..))
  have m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
  have m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
  simp [G₁, m, hm, m1, m2]
  rw [show ofNat Code (n + 4) = ofNatCode (n + 4) from rfl]
  simp [ofNatCode]
  cases n.bodd <;> cases n.div2.bodd <;> rfl

end

/-- The interpretation of a `Nat.Partrec.Code` as a partial function.
* `Nat.Partrec.Code.zero`: The constant zero function.
* `Nat.Partrec.Code.succ`: The successor function.
* `Nat.Partrec.Code.left`: Left unpairing of a pair of ℕ (encoded by `Nat.pair`)
* `Nat.Partrec.Code.right`: Right unpairing of a pair of ℕ (encoded by `Nat.pair`)
* `Nat.Partrec.Code.pair`: Pairs the outputs of argument codes using `Nat.pair`.
* `Nat.Partrec.Code.comp`: Composition of two argument codes.
* `Nat.Partrec.Code.prec`: Primitive recursion. Given an argument of the form `Nat.pair a n`:
  * If `n = 0`, returns `eval cf a`.
  * If `n = succ k`, returns `eval cg (pair a (pair k (eval (prec cf cg) (pair a k))))`
* `Nat.Partrec.Code.rfind'`: Minimization starting at a provided value. Given an argument of the
  form `Nat.pair a m`, returns the least `n ≥ m` such that `eval cf (pair a n) = 0`, if such an `n`
  exists and if `eval cf (pair a k)` terminates for all `m ≤ k ≤ n`.
-/
/-
**Nat.Partrec.Code.eval** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：Nat.Partrec.Code → ℕ →. ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The interpretation of a `Nat.Partrec.Code` as a partial function.
* `Nat.Partrec.Code.zero`: The constant zero function.
* `Nat.Partrec.Code.succ`: The successor function.
* `Nat.Partrec.Code.left`: Left unpairing of a pair of ℕ (encoded by `Nat.pair`)
* `Nat.Partrec.Code.right`: Right unpairing of a pair of ℕ (encoded by `Nat.pair
`)
* `Nat.Partrec.Code.pair`: Pairs the outputs of argument codes using `Nat.pair`.
* `Nat.Partrec.Code.comp`: Composition of two argument codes.
* `Nat.Partrec.Code.prec`: Primitive recursion. Given an argument of the form `N
at.pair a n`:
  * If `n = 0`, returns `eval cf a`.
  * If `n = succ k`, returns `eval cg (pair a (pair k (eval (prec cf cg) (pair a
 k))))`
* `Nat.Partrec.Code.rfind'`: Minimization starting at a provided value. Given an
 argument of the
  form `Nat.pair a m`, returns the least `n ≥ m` such that `eval cf (pair a n) =
 0`, if such an `n`
  exists and if `eval cf (pair a k)` terminates for all `m ≤ k ≤ n`.
-/
def eval : Code → ℕ →. ℕ
  | zero => pure 0
  | succ => Nat.succ
  | left => ↑fun n : ℕ => n.unpair.1
  | right => ↑fun n : ℕ => n.unpair.2
  | pair cf cg => fun n => Nat.pair <$> eval cf n <*> eval cg n
  | comp cf cg => fun n => eval cg n >>= eval cf
  | prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (eval cf a) fun y IH => do
        let i ← IH
        eval cg (Nat.pair a (Nat.pair y i))
  | rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun m => m = 0) <$> eval cf (Nat.pair a (n + m))).map (· + m)

/-- Helper lemma for the evaluation of `prec` in the base case. -/
@[simp]
/-
**Nat.Partrec.Code.eval_prec_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：eval_prec_zero (cf cg : Code) (a : Nat) : eval (prec cf cg) (Nat.pair a 0)
 = eval cf a
参数：cf cg : Code；a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Partrec.Code.eval.eq_7`：∀ (cf cg : Nat.Partrec.Code),   (cf.prec cg)
.eval =     Nat.unpaired fun a n =>       Nat.rec (cf.eval a)         (fun y IH 
=> do           …
· 使用定理 `Nat.unpaired.eq_1`：∀ {α : Sort u_1} (f : ℕ → ℕ → α) (n : ℕ), Nat.unpaire
d f n = f (Nat.unpair n).1 (Nat.unpair n).2
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用引理 `Nat.rec_zero`：rec_zero {C : Nat -> Sort*} (h0 : C 0) (h : forall n, C n 
-> C (n + 1)) : Nat.rec h0 h 0 = h0

--- 原说明 ---
Helper lemma for the evaluation of `prec` in the base case.
-/
theorem eval_prec_zero (cf cg : Code) (a : ℕ) : eval (prec cf cg) (Nat.pair a 0) = eval cf a := by
  rw [eval, Nat.unpaired, Nat.unpair_pair]
  rw [Nat.rec_zero]

/-- Helper lemma for the evaluation of `prec` in the recursive case. -/
/-
**Nat.Partrec.Code.eval_prec_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：eval_prec_succ (cf cg : Code) (a k : Nat) : eval (prec cf cg) (Nat.pair a 
(Nat.succ k)) = do {let ih ← eval (prec cf cg) (Nat.pair a k); eval cg (Nat.pair
 a (Nat.pair k ih))}
参数：cf cg : Code；a k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Partrec.Code.eval.eq_7`：∀ (cf cg : Nat.Partrec.Code),   (cf.prec cg)
.eval =     Nat.unpaired fun a n =>       Nat.rec (cf.eval a)         (fun y IH 
=> do           …
· 使用定理 `Nat.unpaired.eq_1`：∀ {α : Sort u_1} (f : ℕ → ℕ → α) (n : ℕ), Nat.unpaire
d f n = f (Nat.unpair n).1 (Nat.unpair n).2
· 使用定理 `Part.bind_eq_bind`：bind_eq_bind {α β} (f : Part α) (g : α -> Part β) : f
 >>= g = f.bind g
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Helper lemma for the evaluation of `prec` in the recursive case.
-/
theorem eval_prec_succ (cf cg : Code) (a k : ℕ) :
    eval (prec cf cg) (Nat.pair a (Nat.succ k)) =
      do {let ih ← eval (prec cf cg) (Nat.pair a k); eval cg (Nat.pair a (Nat.pair k ih))} := by
  rw [eval, Nat.unpaired, Part.bind_eq_bind, Nat.unpair_pair]
  simp
/-
**Nat.Partrec.Code.** 是 Mathlib 中的一个实例，位于命名空间 `Nat.Partrec.Code`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership (ℕ →. ℕ) Code :=
  ⟨fun c f => eval c = f⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Nat.Partrec.Code.eval_const** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：∀ (n m : ℕ), (Nat.Partrec.Code.const n).eval m = Part.some n
参数：n m : ℕ；Nat.Partrec.Code.const n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval_const : ∀ n m, eval (Code.const n) m = Part.some n
  | 0, _ => rfl
  | n + 1, m => by simp! [eval_const n m]

@[simp]
/-
**Nat.Partrec.Code.eval_id** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：eval_id (n) : eval Code.id n = Part.some n
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Partrec.Code.id.eq_1`：Nat.Partrec.Code.id = Nat.Partrec.Code.left.pa
ir Nat.Partrec.Code.right
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `Nat.pair_unpair`：pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 
= n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_id (n) : eval Code.id n = Part.some n := by simp! [Seq.seq, Code.id]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Nat.Partrec.Code.eval_curry** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：eval_curry (c n x) : eval (curry c n) x = eval c (Nat.pair n x)
参数：c n x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Partrec.Code.curry.eq_1`：∀ (c : Nat.Partrec.Code) (n : ℕ), c.curry n
 = c.comp ((Nat.Partrec.Code.const n).pair Nat.Partrec.Code.id)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.Partrec.Code.eval_const`：∀ (n m : ℕ), (Nat.Partrec.Code.const n).eva
l m = Part.some n
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.Partrec.Code.eval_id`：eval_id (n) : eval Code.id n = Part.some n
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_curry (c n x) : eval (curry c n) x = eval c (Nat.pair n x) := by simp! [Seq.seq, curry]
/-
**Nat.Partrec.Code.primrec_const** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：primrec_const : Primrec Code.const
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.nat_iterate`：nat_iterate {f : α -> Nat} {g : α -> β} {h : α -> β
 -> β} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => (h
 a)^[f a]…
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Nat.Partrec.Code.primrec₂_comp`：primrec₂_comp : Primrec₂ comp
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
-/
theorem primrec_const : Primrec Code.const :=
  (_root_.Primrec.id.nat_iterate (_root_.Primrec.const zero)
    (primrec₂_comp.comp (_root_.Primrec.const succ) Primrec.snd).to₂).of_eq
    fun n => by simp; induction n <;>
      simp [*, Code.const, Function.iterate_succ', -Function.iterate_succ]
/-
**Nat.Partrec.Code.primrec** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem primrec₂_curry : Primrec₂ curry :=
  primrec₂_comp.comp Primrec.fst <| primrec₂_pair.comp (primrec_const.comp Primrec.snd)
    (_root_.Primrec.const Code.id)
/-
**Nat.Partrec.Code.curry_inj** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：curry_inj {c₁ c₂ n₁ n₂} (h : curry c₁ n₁ = curry c₂ n₂) : c₁ = c₂ ∧ n₁ = n
₂
参数：h : curry c₁ n₁ = curry c₂ n₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.Code.const_inj`：const_inj : forall {n₁ n₂}, Nat.Partrec.Code
.const n₁ = Nat.Partrec.Code.const n₂ -> n₁ = n₂ | 0, 0, _ => by simp | n₁ + 1, 
n₂ + 1, h => by …
-/
theorem curry_inj {c₁ c₂ n₁ n₂} (h : curry c₁ n₁ = curry c₂ n₂) : c₁ = c₂ ∧ n₁ = n₂ :=
  ⟨by injection h, by
    injection h with h₁ h₂
    injection h₂ with h₃ h₄
    exact const_inj h₃⟩

/--
The $S_n^m$ theorem: There is a computable function, namely `Nat.Partrec.Code.curry`, that takes a
program and a ℕ `n`, and returns a new program using `n` as the first argument.
-/
/-
**Nat.Partrec.Code.smn** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：smn : exists f : Code -> Nat -> Code, Computable₂ f ∧ forall c n x, eval (
f c n) x = eval c (Nat.pair n x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.to_comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst :
 Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α → β →
 σ}, P…
· 使用定理 `Nat.Partrec.Code.primrec₂_curry`：primrec₂_curry : Primrec₂ curry
· 使用定理 `Nat.Partrec.Code.eval_curry`：eval_curry (c n x) : eval (curry c n) x = e
val c (Nat.pair n x)

--- 原说明 ---
The $S_n^m$ theorem: There is a computable function, namely `Nat.Partrec.Code.cu
rry`, that takes a
program and a ℕ `n`, and returns a new program using `n` as the first argument.
-/
theorem smn :
    ∃ f : Code → ℕ → Code, Computable₂ f ∧ ∀ c n x, eval (f c n) x = eval c (Nat.pair n x) :=
  ⟨curry, Primrec₂.to_comp primrec₂_curry, eval_curry⟩

set_option backward.isDefEq.respectTransparency false in
/-- A function is partial recursive if and only if there is a code implementing it. Therefore,
`eval` is a **universal partial recursive function**. -/
/-
**Nat.Partrec.Code.exists_code** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：exists_code {f : Nat ->. Nat} : Nat.Partrec f ↔ exists c : Code, eval c = 
f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.Partrec.Code.eval_id`：eval_id (n) : eval Code.id n = Part.some n
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Part.map_id'`：map_id' {f : α -> α} (H : forall x : α, f x = x) (o) : map
 f o = o
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.Partrec.rfind'`：rfind' {f} (hf : Nat.Partrec f) : Nat.Partrec (Nat.u
npaired fun a m => (Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + m
))).map …

--- 原说明 ---
A function is partial recursive if and only if there is a code implementing it. 
Therefore,
`eval` is a **universal partial recursive function**.
-/
theorem exists_code {f : ℕ →. ℕ} : Nat.Partrec f ↔ ∃ c : Code, eval c = f := by
  refine ⟨fun h => ?_, ?_⟩
  · induction h with
    | zero => exact ⟨zero, rfl⟩
    | succ => exact ⟨succ, rfl⟩
    | left => exact ⟨left, rfl⟩
    | right => exact ⟨right, rfl⟩
    | pair pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨pair cf cg, rfl⟩
    | comp pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨comp cf cg, rfl⟩
    | prec pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨prec cf cg, rfl⟩
    | rfind pf hf =>
      rcases hf with ⟨cf, rfl⟩
      refine ⟨comp (rfind' cf) (pair Code.id zero), ?_⟩
      simp [eval, Seq.seq, pure, PFun.pure, Part.map_id']
  · rintro ⟨c, rfl⟩
    induction c with
    | zero => exact Nat.Partrec.zero
    | succ => exact Nat.Partrec.succ
    | left => exact Nat.Partrec.left
    | right => exact Nat.Partrec.right
    | pair cf cg pf pg => exact pf.pair pg
    | comp cf cg pf pg => exact pf.comp pg
    | prec cf cg pf pg => exact pf.prec pg
    | rfind' cf pf => exact pf.rfind'

/-- A modified evaluation for the code which returns an `Option ℕ` instead of a `Part ℕ`. To avoid
undecidability, `evaln` takes a parameter `k` and fails if it encounters a number ≥ k in the course
of its execution. Other than this, the semantics are the same as in `Nat.Partrec.Code.eval`.
-/
/-
**Nat.Partrec.Code.evaln** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：ℕ → Nat.Partrec.Code → ℕ → Option ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A modified evaluation for the code which returns an `Option ℕ` instead of a `Par
t ℕ`. To avoid
undecidability, `evaln` takes a parameter `k` and fails if it encounters a numbe
r ≥ k in the course
of its execution. Other than this, the semantics are the same as in `Nat.Partrec
.Code.eval`.
-/
def evaln : ℕ → Code → ℕ → Option ℕ
  | 0, _ => fun _ => Option.none
  | k + 1, zero => fun n => do
    guard (n ≤ k)
    return 0
  | k + 1, succ => fun n => do
    guard (n ≤ k)
    return (Nat.succ n)
  | k + 1, left => fun n => do
    guard (n ≤ k)
    return n.unpair.1
  | k + 1, right => fun n => do
    guard (n ≤ k)
    pure n.unpair.2
  | k + 1, pair cf cg => fun n => do
    guard (n ≤ k)
    Nat.pair <$> evaln (k + 1) cf n <*> evaln (k + 1) cg n
  | k + 1, comp cf cg => fun n => do
    guard (n ≤ k)
    let x ← evaln (k + 1) cg n
    evaln (k + 1) cf x
  | k + 1, prec cf cg => fun n => do
    guard (n ≤ k)
    n.unpaired fun a n =>
      n.casesOn (evaln (k + 1) cf a) fun y => do
        let i ← evaln k (prec cf cg) (Nat.pair a y)
        evaln (k + 1) cg (Nat.pair a (Nat.pair y i))
  | k + 1, rfind' cf => fun n => do
    guard (n ≤ k)
    n.unpaired fun a m => do
      let x ← evaln (k + 1) cf (Nat.pair a m)
      if x = 0 then
        pure m
      else
        evaln k (rfind' cf) (Nat.pair a (m + 1))
/-
**Nat.Partrec.Code.evaln_bound** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：∀ {k : ℕ} {c : Nat.Partrec.Code} {n x : ℕ}, x ∈ Nat.Partrec.Code.evaln k c
 n → n < k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Nat.Partrec.Code.evaln.eq_1`：∀ (x : Nat.Partrec.Code), Nat.Partrec.Code.
evaln 0 x = fun x => none
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Nat.Partrec.Code.evaln.eq_2`：∀ (k : ℕ),   Nat.Partrec.Code.evaln k.succ 
Nat.Partrec.Code.zero = fun n => do     guard (n ≤ k)     pure 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Partrec.Code.evaln.eq_3`：∀ (k : ℕ),   Nat.Partrec.Code.evaln k.succ 
Nat.Partrec.Code.succ = fun n => do     guard (n ≤ k)     pure n.succ
· 使用定理 `Nat.Partrec.Code.evaln.eq_4`：∀ (k : ℕ),   Nat.Partrec.Code.evaln k.succ 
Nat.Partrec.Code.left = fun n => do     guard (n ≤ k)     pure (Nat.unpair n).1
· 使用定理 `Nat.Partrec.Code.evaln.eq_5`：∀ (k : ℕ),   Nat.Partrec.Code.evaln k.succ 
Nat.Partrec.Code.right = fun n => do     guard (n ≤ k)     pure (Nat.unpair n).2
· 使用定理 `Nat.Partrec.Code.evaln.eq_6`：∀ (k : ℕ) (cf cg : Nat.Partrec.Code),   Nat
.Partrec.Code.evaln k.succ (cf.pair cg) = fun n => do     guard (n ≤ k)     Nat.
pair <$> Nat.Part…
· 使用定理 `Nat.Partrec.Code.evaln.eq_7`：∀ (k : ℕ) (cf cg : Nat.Partrec.Code),   Nat
.Partrec.Code.evaln k.succ (cf.comp cg) = fun n => do     guard (n ≤ k)     let 
x ← Nat.Partrec.C…
· 使用定理 `Nat.Partrec.Code.evaln.eq_8`：∀ (k : ℕ) (cf cg : Nat.Partrec.Code),   Nat
.Partrec.Code.evaln k.succ (cf.prec cg) = fun n => do     guard (n ≤ k)     Nat.
unpaired         …
· 使用定理 `Nat.Partrec.Code.evaln.eq_9`：∀ (k : ℕ) (cf : Nat.Partrec.Code),   Nat.Pa
rtrec.Code.evaln k.succ cf.rfind' = fun n => do     guard (n ≤ k)     Nat.unpair
ed         (fun a…
-/
theorem evaln_bound : ∀ {k c n x}, x ∈ evaln k c n → n < k
  | 0, c, n, x, h => by simp [evaln] at h
  | k + 1, c, n, x, h => by
    suffices ∀ {o : Option ℕ}, x ∈ do { guard (n ≤ k); o } → n < k + 1 by
      cases c <;> rw [evaln] at h <;> exact this h
    simpa [Option.bind_eq_some_iff] using Nat.lt_succ_of_le

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/-
**Nat.Partrec.Code.evaln_mono** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：evaln_mono : forall {k₁ k₂ c n x}, k₁ <= k₂ -> x in evaln k₁ c n -> x in e
valn k₂ c n | 0, k₂, c, n, x, _, h => by simp [evaln] at h | k + 1, k₂ + 1, c, n
, x, hl, h => by have hl'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evaln_mono : ∀ {k₁ k₂ c n x}, k₁ ≤ k₂ → x ∈ evaln k₁ c n → x ∈ evaln k₂ c n
  | 0, k₂, c, n, x, _, h => by simp [evaln] at h
  | k + 1, k₂ + 1, c, n, x, hl, h => by
    have hl' := Nat.le_of_succ_le_succ hl
    have :
      ∀ {k k₂ n x : ℕ} {o₁ o₂ : Option ℕ},
        k ≤ k₂ → (x ∈ o₁ → x ∈ o₂) →
          x ∈ do { guard (n ≤ k); o₁ } → x ∈ do { guard (n ≤ k₂); o₂ } := by
      simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some',
        exists_and_left, exists_const, and_imp]
      introv h h₁ h₂ h₃
      exact ⟨le_trans h₂ h, h₁ h₃⟩
    simp? at h ⊢ says simp only [Option.mem_def] at h ⊢
    induction c generalizing x n <;> rw [evaln] at h ⊢ <;> refine this hl' (fun h => ?_) h
    iterate 4 exact h
    case pair cf cg hf hg _ =>
      simp? [Seq.seq, Option.bind_eq_some_iff] at h ⊢ says
        simp only [Seq.seq, Option.map_eq_map, Option.mem_def, Option.bind_eq_some_iff,
          Option.map_eq_some_iff, exists_exists_and_eq_and] at h ⊢
      exact h.imp fun a => And.imp (hf _ _) <| Exists.imp fun b => And.imp_left (hg _ _)
    case comp cf cg hf hg _ =>
      simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
        simp only [bind, Option.mem_def, Option.bind_eq_some_iff] at h ⊢
      exact h.imp fun a => And.imp (hg _ _) (hf _ _)
    case prec cf cg hf hg _ =>
      revert h
      simp only [unpaired, bind, Option.mem_def]
      induction n.unpair.2 <;> simp [Option.bind_eq_some_iff]
      · apply hf
      · exact fun y h₁ h₂ => ⟨y, evaln_mono hl' h₁, hg _ _ h₂⟩
    case rfind' cf hf _ =>
      simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
        simp only [unpaired, bind, pair_unpair, Option.pure_def, Option.mem_def,
          Option.bind_eq_some_iff] at h ⊢
      refine h.imp fun x => And.imp (hf _ _) ?_
      by_cases x0 : x = 0 <;> simp [x0]
      exact evaln_mono hl'

set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/-
**Nat.Partrec.Code.evaln_sound** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：evaln_sound : forall {k c n x}, x in evaln k c n -> x in eval c n | 0, _, 
n, x, h => by simp [evaln] at h | k + 1, c, n, x, h => by induction c generalizi
ng x n <;> simp [eval, evaln, Option.bind_eq_some_iff, Seq.seq] at h ⊢ <;> obtai
n ⟨_, h⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evaln_sound : ∀ {k c n x}, x ∈ evaln k c n → x ∈ eval c n
  | 0, _, n, x, h => by simp [evaln] at h
  | k + 1, c, n, x, h => by
    induction c generalizing x n <;> simp [eval, evaln, Option.bind_eq_some_iff, Seq.seq] at h ⊢ <;>
      obtain ⟨_, h⟩ := h
    iterate 4 simpa [pure, PFun.pure, eq_comm] using h
    case pair cf cg hf hg _ =>
      rcases h with ⟨y, ef, z, eg, rfl⟩
      exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩
    case comp cf cg hf hg _ =>
      rcases h with ⟨y, eg, ef⟩
      exact ⟨_, hg _ _ eg, hf _ _ ef⟩
    case prec cf cg hf hg _ =>
      revert h
      induction n.unpair.2 generalizing x with simp [Option.bind_eq_some_iff]
      | zero => apply hf
      | succ m IH =>
        refine fun y h₁ h₂ => ⟨y, IH _ ?_, ?_⟩
        · have := evaln_mono k.le_succ h₁
          simp [evaln, Option.bind_eq_some_iff] at this
          exact this.2
        · exact hg _ _ h₂
    case rfind' cf hf _ =>
      rcases h with ⟨m, h₁, h₂⟩
      by_cases m0 : m = 0 <;> simp [m0] at h₂
      · exact
          ⟨0, ⟨by simpa [m0] using hf _ _ h₁, fun {m} => (Nat.not_lt_zero _).elim⟩, by simp [h₂]⟩
      · have := evaln_sound h₂
        simp [eval] at this
        rcases this with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
        refine
          ⟨y + 1, ⟨by simpa [add_comm, add_left_comm] using hy₁, fun {i} im => ?_⟩, by
            simp [add_comm, add_left_comm]⟩
        rcases i with - | i
        · exact ⟨m, by simpa using hf _ _ h₁, m0⟩
        · rcases hy₂ (Nat.lt_of_succ_lt_succ im) with ⟨z, hz, z0⟩
          exact ⟨z, by simpa [add_comm, add_left_comm] using hz, z0⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/-
**Nat.Partrec.Code.evaln_complete** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：evaln_complete {c n x} : x in eval c n ↔ exists k, x in evaln k c n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Nat.Partrec.Code.evaln.eq_2`：∀ (k : ℕ),   Nat.Partrec.Code.evaln k.succ 
Nat.Partrec.Code.zero = fun n => do     guard (n ≤ k)     pure 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Partrec.Code.evaln.eq_3`：∀ (k : ℕ),   Nat.Partrec.Code.evaln k.succ 
Nat.Partrec.Code.succ = fun n => do     guard (n ≤ k)     pure n.succ
· 使用定理 `Nat.Partrec.Code.evaln.eq_4`：∀ (k : ℕ),   Nat.Partrec.Code.evaln k.succ 
Nat.Partrec.Code.left = fun n => do     guard (n ≤ k)     pure (Nat.unpair n).1
· 使用定理 `Nat.Partrec.Code.evaln.eq_5`：∀ (k : ℕ),   Nat.Partrec.Code.evaln k.succ 
Nat.Partrec.Code.right = fun n => do     guard (n ≤ k)     pure (Nat.unpair n).2
· 使用定理 `Nat.Partrec.Code.evaln.eq_6`：∀ (k : ℕ) (cf cg : Nat.Partrec.Code),   Nat
.Partrec.Code.evaln k.succ (cf.pair cg) = fun n => do     guard (n ≤ k)     Nat.
pair <$> Nat.Part…
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `Part.bind_map`：bind_map {γ} (f : α -> β) (x) (g : β -> Part γ) : (map f 
x).bind g = x.bind fun y => g (f y)
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Nat.Partrec.Code.evaln_bound`：∀ {k : ℕ} {c : Nat.Partrec.Code} {n x : ℕ}
, x ∈ Nat.Partrec.Code.evaln k c n → n < k
· 使用定理 `Nat.Partrec.Code.evaln_mono`：evaln_mono : forall {k₁ k₂ c n x}, k₁ <= k₂
 -> x in evaln k₁ c n -> x in evaln k₂ c n | 0, k₂, c, n, x, _, h => by simp [ev
aln] at h | k + 1…
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Nat.Partrec.Code.evaln.eq_7`：∀ (k : ℕ) (cf cg : Nat.Partrec.Code),   Nat
.Partrec.Code.evaln k.succ (cf.comp cg) = fun n => do     guard (n ≤ k)     let 
x ← Nat.Partrec.C…
· 使用定理 `Nat.Partrec.Code.evaln.eq_8`：∀ (k : ℕ) (cf cg : Nat.Partrec.Code),   Nat
.Partrec.Code.evaln k.succ (cf.prec cg) = fun n => do     guard (n ≤ k)     Nat.
unpaired         …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
（共 47 条，此处仅展示前 30 条）
-/
theorem evaln_complete {c n x} : x ∈ eval c n ↔ ∃ k, x ∈ evaln k c n := by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => evaln_sound h⟩
  rsuffices ⟨k, h⟩ : ∃ k, x ∈ evaln (k + 1) c n
  · exact ⟨k + 1, h⟩
  induction c generalizing n x with
      simp [eval, evaln, pure, PFun.pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
  | pair cf cg hf hg =>
    rcases h with ⟨x, hx, y, hy, rfl⟩
    rcases hf hx with ⟨k₁, hk₁⟩; rcases hg hy with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    refine
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂, rfl⟩
  | comp cf cg hf hg =>
    rcases h with ⟨y, hy, hx⟩
    rcases hg hy with ⟨k₁, hk₁⟩; rcases hf hx with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    exact
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁,
        evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂⟩
  | prec cf cg hf hg =>
    revert h
    generalize n.unpair.1 = n₁; generalize n.unpair.2 = n₂
    induction n₂ generalizing x n with simp [Option.bind_eq_some_iff]
    | zero =>
      intro h
      rcases hf h with ⟨k, hk⟩
      exact ⟨_, le_max_left _ _, evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk⟩
    | succ m IH =>
      intro y hy hx
      rcases IH hy with ⟨k₁, nk₁, hk₁⟩
      rcases hg hx with ⟨k₂, hk₂⟩
      refine
        ⟨(max k₁ k₂).succ,
          Nat.le_succ_of_le <| le_max_of_le_left <|
            le_trans (le_max_left _ (Nat.pair n₁ m)) nk₁, y,
          evaln_mono (Nat.succ_le_succ <| le_max_left _ _) ?_,
          evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_right _ _) hk₂⟩
      simp only [evaln.eq_8, bind, unpaired, unpair_pair, Option.mem_def, Option.bind_eq_some_iff,
        Option.guard_eq_some', exists_and_left, exists_const]
      exact ⟨le_trans (le_max_right _ _) nk₁, hk₁⟩
  | rfind' cf hf =>
    rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    suffices ∃ k, y + n.unpair.2 ∈ evaln (k + 1) (rfind' cf) (Nat.pair n.unpair.1 n.unpair.2) by
      simpa [evaln, Option.bind_eq_some_iff]
    revert hy₁ hy₂
    generalize n.unpair.2 = m
    intro hy₁ hy₂
    induction y generalizing m with simp [evaln, Option.bind_eq_some_iff]
    | zero =>
      simp at hy₁
      rcases hf hy₁ with ⟨k, hk⟩
      exact ⟨_, Nat.le_of_lt_succ <| evaln_bound hk, _, hk, by simp⟩
    | succ y IH =>
      rcases hy₂ (Nat.succ_pos _) with ⟨a, ha, a0⟩
      rcases hf ha with ⟨k₁, hk₁⟩
      rcases IH m.succ (by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hy₁)
          fun {i} hi => by
          simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using
            hy₂ (Nat.succ_lt_succ hi) with
        ⟨k₂, hk₂⟩
      use (max k₁ k₂).succ
      rw [zero_add] at hk₁
      use Nat.le_succ_of_le <| le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁
      use a
      use evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_left _ _) hk₁
      simpa [a0, add_comm, add_left_comm] using
        evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂
  | _ => exact ⟨⟨_, le_rfl⟩, h.symm⟩

section

/-
**Nat.Partrec.Code.lup** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partrec.Code`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def lup (L : List (List (Option ℕ))) (p : ℕ × Code) (n : ℕ) := do
  let l ← L[encode p]?
  let o ← l[n]?
  o
/-
**Nat.Partrec.Code.hlup** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem hlup : Primrec fun p : _ × (_ × _) × _ => lup p.1 p.2.1 p.2.2 :=
  Primrec.option_bind
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.encode.comp <| Primrec.fst.comp Primrec.snd))
    (Primrec.option_bind (Primrec.list_getElem?.comp Primrec.snd <| Primrec.snd.comp <|
      Primrec.snd.comp Primrec.fst) Primrec.snd)
/-
**Nat.Partrec.Code.G** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partrec.Code`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def G (L : List (List (Option ℕ))) : Option (List (Option ℕ)) :=
  Option.some <|
    let a := ofNat (ℕ × Code) L.length
    let k := a.1
    let c := a.2
    (List.range k).map fun n =>
      k.casesOn Option.none fun k' =>
        Nat.Partrec.Code.recOn c
          (some 0) -- zero
          (some (Nat.succ n))
          (some n.unpair.1)
          (some n.unpair.2)
          (fun cf cg _ _ => do
            let x ← lup L (k, cf) n
            let y ← lup L (k, cg) n
            some (Nat.pair x y))
          (fun cf cg _ _ => do
            let x ← lup L (k, cg) n
            lup L (k, cf) x)
          (fun cf cg _ _ =>
            let z := n.unpair.1
            n.unpair.2.casesOn (lup L (k, cf) z) fun y => do
              let i ← lup L (k', c) (Nat.pair z y)
              lup L (k, cg) (Nat.pair z (Nat.pair y i)))
          (fun cf _ =>
            let z := n.unpair.1
            let m := n.unpair.2
            do
              let x ← lup L (k, cf) (Nat.pair z m)
              x.casesOn (some m) fun _ => lup L (k', c) (Nat.pair z (m + 1)))
/-
**Nat.Partrec.Code.hG** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem hG : Primrec G := by
  have a := (Primrec.ofNat (ℕ × Code)).comp (Primrec.list_length (α := List (Option ℕ)))
  have k := Primrec.fst.comp a
  refine Primrec.option_some.comp (Primrec.list_map (Primrec.list_range.comp k) (?_ : Primrec _))
  replace k := k.comp (Primrec.fst (β := ℕ))
  have n := Primrec.snd (α := List (List (Option ℕ))) (β := ℕ)
  refine Primrec.nat_casesOn k (_root_.Primrec.const Option.none) (?_ : Primrec _)
  have k := k.comp (Primrec.fst (β := ℕ))
  have n := n.comp (Primrec.fst (β := ℕ))
  have k' := Primrec.snd (α := List (List (Option ℕ)) × ℕ) (β := ℕ)
  have c := Primrec.snd.comp (a.comp <| (Primrec.fst (β := ℕ)).comp (Primrec.fst (β := ℕ)))
  apply
    Nat.Partrec.Code.primrec_recOn c
      (_root_.Primrec.const (some 0))
      (Primrec.option_some.comp (_root_.Primrec.succ.comp n))
      (Primrec.option_some.comp (Primrec.fst.comp <| Primrec.unpair.comp n))
      (Primrec.option_some.comp (Primrec.snd.comp <| Primrec.unpair.comp n))
  · have L := (Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    have k := k.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have n := n.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    refine Primrec.option_bind (hlup.comp <| L.pair <| (k.pair cf).pair n) ?_
    unfold Primrec₂
    conv =>
      congr
      · ext p
        dsimp only
        erw [Option.bind_eq_bind, ← Option.map_eq_bind]
    refine Primrec.option_map ((hlup.comp <| L.pair <| (k.pair cg).pair n).comp Primrec.fst) ?_
    unfold Primrec₂
    exact Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  · have L := (Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    have k := k.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have n := n.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    refine Primrec.option_bind (hlup.comp <| L.pair <| (k.pair cg).pair n) ?_
    unfold Primrec₂
    have h :=
      hlup.comp ((L.comp Primrec.fst).pair <| ((k.pair cf).comp Primrec.fst).pair Primrec.snd)
    exact h
  · have L := (Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    have k := k.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have n := n.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    have z := Primrec.fst.comp (Primrec.unpair.comp n)
    refine
      Primrec.nat_casesOn (Primrec.snd.comp (Primrec.unpair.comp n))
        (hlup.comp <| L.pair <| (k.pair cf).pair z)
        (?_ : Primrec _)
    have L := L.comp (Primrec.fst (β := ℕ))
    have z := z.comp (Primrec.fst (β := ℕ))
    have y := Primrec.snd
      (α := ((List (List (Option ℕ)) × ℕ) × ℕ) × Code × Code × Option ℕ × Option ℕ) (β := ℕ)
    have h₁ := hlup.comp <| L.pair <| (((k'.pair c).comp Primrec.fst).comp Primrec.fst).pair
      (Primrec₂.natPair.comp z y)
    refine Primrec.option_bind h₁ (?_ : Primrec _)
    have z := z.comp (Primrec.fst (β := ℕ))
    have y := y.comp (Primrec.fst (β := ℕ))
    have i := Primrec.snd
      (α := (((List (List (Option ℕ)) × ℕ) × ℕ) × Code × Code × Option ℕ × Option ℕ) × ℕ)
      (β := ℕ)
    have h₂ := hlup.comp ((L.comp Primrec.fst).pair <|
      ((k.pair cg).comp <| Primrec.fst.comp Primrec.fst).pair <|
        Primrec₂.natPair.comp z <| Primrec₂.natPair.comp y i)
    exact h₂
  · have L := (Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Option ℕ))
    have k := k.comp (Primrec.fst (β := Code × Option ℕ))
    have n := n.comp (Primrec.fst (β := Code × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Option ℕ))
    have z := Primrec.fst.comp (Primrec.unpair.comp n)
    have m := Primrec.snd.comp (Primrec.unpair.comp n)
    have h₁ := hlup.comp <| L.pair <| (k.pair cf).pair (Primrec₂.natPair.comp z m)
    refine Primrec.option_bind h₁ (?_ : Primrec _)
    have m := m.comp (Primrec.fst (β := ℕ))
    refine Primrec.nat_casesOn Primrec.snd (Primrec.option_some.comp m) ?_
    unfold Primrec₂
    exact (hlup.comp ((L.comp Primrec.fst).pair <|
      ((k'.pair c).comp <| Primrec.fst.comp Primrec.fst).pair
        (Primrec₂.natPair.comp (z.comp Primrec.fst) (_root_.Primrec.succ.comp m)))).comp
      Primrec.fst
/-
**Nat.Partrec.Code.evaln_map** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem evaln_map (k c n) :
    ((List.range k)[n]?.bind fun a ↦ evaln k c a) = evaln k c n := by
  by_cases kn : n < k
  · simp [List.getElem?_range kn]
  · rw [List.getElem?_eq_none]
    · cases e : evaln k c n
      · rfl
      exact kn.elim (evaln_bound e)
    simpa using kn

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/-- The `Nat.Partrec.Code.evaln` function is primitive recursive. -/
/-
**Nat.Partrec.Code.primrec_evaln** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：primrec_evaln : Primrec fun a : (Nat × Code) × Nat => evaln a.1.1 a.1.2 a.
2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.nat_strong_rec`：nat_strong_rec (f : α -> Nat -> σ) {g : α -> Lis
t σ -> Option σ} (hg : Primrec₂ g) (H : forall a n, g a ((List.range n).map (f a
)) = some (f…
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `_private.Mathlib.Computability.PartrecCode.0.Nat.Partrec.Code.hG`：Primre
c Nat.Partrec.Code.G✝
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Denumerable.prod_ofNat_val`：prod_ofNat_val (n : Nat) : ofNat (α × β) n =
 (ofNat α (unpair n).1, ofNat β (unpair n).2)
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
· 使用定理 `Nat.pair_unpair`：pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 
= n
· 使用定理 `List.map_congr_left`：∀ {α : Type u_1} {l : List α} {α_1 : Type u_2} {f g
 : α → α_1}, (∀ a ∈ l, f a = g a) → List.map f l = List.map g l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Denumerable.encode_ofNat`：encode_ofNat (n) : encode (ofNat α n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Nat.Partrec.Code.evaln.eq_1`：∀ (x : Nat.Partrec.Code), Nat.Partrec.Code.
evaln 0 x = fun x => none
· 使用定理 `List.getElem?_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List
 α} {i : ℕ}, (List.map f l)[i]? = Option.map f l[i]?
· 使用定理 `List.getElem?_range`：∀ {i n : ℕ}, i < n → (List.range n)[i]? = some i
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Denumerable.ofNat_encode`：ofNat_encode (a) : ofNat α (encode a) = a
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `Option.bind_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α →
 β} {g : β → Option γ} {x : Option α},   (Option.map f x).bind g = x.bind (g ∘ f
)
· 使用定理 `_private.Mathlib.Computability.PartrecCode.0.Nat.Partrec.Code.evaln_map`
：∀ (k : ℕ) (c : Nat.Partrec.Code) (n : ℕ),   ((List.range k)[n]?.bind fun a => N
at.Partrec.Code.evaln k c a) = Nat.Partrec.Code.evaln k c n
· 使用定理 `Nat.Partrec.Code.evaln.eq_2`：∀ (k : ℕ),   Nat.Partrec.Code.evaln k.succ 
Nat.Partrec.Code.zero = fun n => do     guard (n ≤ k)     pure 0
· 使用定理 `guard.congr_simp`：∀ {f : Type → Type v} [inst : Alternative f] (p p_1 : 
Prop),   p = p_1 → ∀ {inst_1 : Decidable p} [inst_2 : Decidable p_1], guard p = 
guard …
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
The `Nat.Partrec.Code.evaln` function is primitive recursive.
-/
theorem primrec_evaln : Primrec fun a : (ℕ × Code) × ℕ => evaln a.1.1 a.1.2 a.2 :=
  have :
    Primrec₂ fun (_ : Unit) (n : ℕ) =>
      let a := ofNat (ℕ × Code) n
      (List.range a.1).map (evaln a.1 a.2) :=
    Primrec.nat_strong_rec _ (hG.comp Primrec.snd).to₂ fun _ p => by
      simp only [G, prod_ofNat_val, ofNat_nat, List.length_map, List.length_range,
        Nat.pair_unpair, Option.some_inj]
      refine List.map_congr_left fun n => ?_
      have : List.range p = List.range (Nat.pair p.unpair.1 (encode (ofNat Code p.unpair.2))) := by
        simp
      rw [this]
      generalize p.unpair.1 = k
      generalize ofNat Code p.unpair.2 = c
      intro nk
      rcases k with - | k'
      · simp [evaln]
      let k := k' + 1
      simp only
      simp only [List.mem_range, Nat.lt_succ_iff] at nk
      have hg :
        ∀ {k' c' n},
          Nat.pair k' (encode c') < Nat.pair k (encode c) →
            lup ((List.range (Nat.pair k (encode c))).map fun n =>
              (List.range n.unpair.1).map (evaln n.unpair.1 (ofNat Code n.unpair.2))) (k', c') n =
            evaln k' c' n := by
        intro k₁ c₁ n₁ hl
        simp [lup, List.getElem?_range hl, evaln_map, Bind.bind, Option.bind_map]
      obtain - | - | - | - | ⟨cf, cg⟩ | ⟨cf, cg⟩ | ⟨cf, cg⟩ | cf := c <;>
        simp [evaln, nk, Bind.bind, Functor.map, Seq.seq, pure]
      · obtain ⟨lf, lg⟩ := encode_lt_pair cf cg
        rw [hg (Nat.pair_lt_pair_right _ lf), hg (Nat.pair_lt_pair_right _ lg)]
        cases evaln k cf n
        · rfl
        cases evaln k cg n <;> rfl
      · obtain ⟨lf, lg⟩ := encode_lt_comp cf cg
        rw [hg (Nat.pair_lt_pair_right _ lg)]
        cases evaln k cg n
        · rfl
        simp [k, hg (Nat.pair_lt_pair_right _ lf)]
      · obtain ⟨lf, lg⟩ := encode_lt_prec cf cg
        rw [hg (Nat.pair_lt_pair_right _ lf)]
        cases n.unpair.2
        · rfl
        simp only
        rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
        cases evaln k' _ _
        · rfl
        simp [k, hg (Nat.pair_lt_pair_right _ lg)]
      · have lf := encode_lt_rfind' cf
        rw [hg (Nat.pair_lt_pair_right _ lf)]
        rcases evaln k cf n with - | x
        · rfl
        simp only [Option.bind_some]
        cases x <;> simp
        rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
  (Primrec.option_bind
    (Primrec.list_getElem?.comp (this.comp (_root_.Primrec.const ())
      (Primrec.encode_iff.2 Primrec.fst)) Primrec.snd) Primrec.snd.to₂).of_eq
    fun ⟨⟨k, c⟩, n⟩ => by simp [evaln_map, Option.bind_map]

end

section

open Computable

/-
**Nat.Partrec.Code.eval_eq_rfindOpt** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`
。
形式化陈述：eval_eq_rfindOpt (c n) : eval c n = Nat.rfindOpt fun k => evaln k c n
参数：c n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.Partrec.Code.evaln_complete`：evaln_complete {c n x} : x in eval c n 
↔ exists k, x in evaln k c n
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Nat.rfindOpt_mono`：rfindOpt_mono {α} {f : Nat -> Option α} (H : forall {
a m n}, m <= n -> a in f m -> a in f n) {a} : a in rfindOpt f ↔ exists n, a in f
 n
· 使用定理 `Nat.Partrec.Code.evaln_mono`：evaln_mono : forall {k₁ k₂ c n x}, k₁ <= k₂
 -> x in evaln k₁ c n -> x in evaln k₂ c n | 0, k₂, c, n, x, _, h => by simp [ev
aln] at h | k + 1…
-/
theorem eval_eq_rfindOpt (c n) : eval c n = Nat.rfindOpt fun k => evaln k c n :=
  Part.ext fun x => by
    refine evaln_complete.trans (Nat.rfindOpt_mono ?_).symm
    intro a m n hl; apply evaln_mono hl
/-
**Nat.Partrec.Code.eval_part** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：eval_part : Partrec₂ eval
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.of_eq`：of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n
 = g n) : Partrec g
· 使用定理 `Partrec.rfindOpt`：rfindOpt {f : α -> Nat -> Option σ} (hf : Computable₂ 
f) : Partrec fun a => Nat.rfindOpt (f a)
· 使用定理 `Computable.to₂`：to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ f
un a b => f (a, b)
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Nat.Partrec.Code.primrec_evaln`：primrec_evaln : Primrec fun a : (Nat × C
ode) × Nat => evaln a.1.1 a.1.2 a.2
· 使用定理 `Computable.pair`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {f : α → β} {
g : α…
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `Computable.fst`：fst : Computable (@Prod.fst α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Partrec.Code.eval_eq_rfindOpt`：eval_eq_rfindOpt (c n) : eval c n = N
at.rfindOpt fun k => evaln k c n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_part : Partrec₂ eval :=
  (Partrec.rfindOpt
    (primrec_evaln.to_comp.comp
      ((Computable.snd.pair (fst.comp fst)).pair (snd.comp fst))).to₂).of_eq
    fun a => by simp [eval_eq_rfindOpt]

/-- **Roger's fixed-point theorem**: any total, computable `f` has a fixed point.
That is, under the interpretation given by `Nat.Partrec.Code.eval`, there is a code `c`
such that `c` and `f c` have the same evaluation.
-/
/-
**Nat.Partrec.Code.fixed_point** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：fixed_point {f : Code -> Code} (hf : Computable f) : exists c : Code, eval
 (f c) = eval c
参数：hf : Computable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.bind`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α →. β} {g 
: …
· 使用定理 `Partrec₂.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type 
u_5} [inst : Primcodable α] [inst_1 : Primcodable β]   [inst_2 : Primcodable γ] 
[in…
· 使用定理 `Nat.Partrec.Code.eval_part`：eval_part : Partrec₂ eval
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.ofNat`：∀ (α : Type u_5) [inst : Denumerable α], Computable (D
enumerable.ofNat α)
· 使用定理 `Computable.fst`：fst : Computable (@Prod.fst α β)
· 使用定理 `Partrec.to₂`：to₂ {f : α × β ->. σ} (hf : Partrec f) : Partrec₂ fun a b =
> f (a, b)
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Partrec.Code.exists_code`：exists_code {f : Nat ->. Nat} : Nat.Partre
c f ↔ exists c : Code, eval c = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Denumerable.decode_eq_ofNat`：decode_eq_ofNat (α) [Denumerable α] (n : Na
t) : decode (α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Denumerable.ofEquiv_ofNat`：ofEquiv_ofNat (α) {β} [Denumerable α] (e : β 
≃ α) (n) : @ofNat β (ofEquiv _ e) n = e.symm (ofNat α n)
· 使用定理 `Denumerable.sigma_ofNat_val`：sigma_ofNat_val (n : Nat) : ofNat (Sigma γ)
 n = ⟨ofNat α (unpair n).1, ofNat (γ _) (unpair n).2⟩
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Equiv.sigmaEquivProd_apply`：∀ (α : Type u_1) (β : Type u_2) (a : (_ : α)
 × β), (Equiv.sigmaEquivProd α β) a = (a.fst, a.snd)
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Nat.Partrec.Code.primrec₂_curry`：primrec₂_curry : Primrec₂ curry
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
**Roger's fixed-point theorem**: any total, computable `f` has a fixed point.
That is, under the interpretation given by `Nat.Partrec.Code.eval`, there is a c
ode `c`
such that `c` and `f c` have the same evaluation.
-/
theorem fixed_point {f : Code → Code} (hf : Computable f) : ∃ c : Code, eval (f c) = eval c :=
  let g (x y : ℕ) : Part ℕ := eval (ofNat Code x) x >>= fun b => eval (ofNat Code b) y
  have : Partrec₂ g :=
    (eval_part.comp ((Computable.ofNat _).comp fst) fst).bind
      (eval_part.comp ((Computable.ofNat _).comp snd) (snd.comp fst)).to₂
  let ⟨cg, eg⟩ := exists_code.1 this
  have eg' : ∀ a n, eval cg (Nat.pair a n) = Part.map encode (g a n) := by simp [eg]
  let F (x : ℕ) : Code := f (curry cg x)
  have : Computable F :=
    hf.comp (primrec₂_curry.comp (_root_.Primrec.const cg) _root_.Primrec.id).to_comp
  let ⟨cF, eF⟩ := exists_code.1 this
  have eF' : eval cF (encode cF) = Part.some (encode (F (encode cF))) := by simp [eF]
  ⟨curry cg (encode cF),
    funext fun n =>
      show eval (f (curry cg (encode cF))) n = eval (curry cg (encode cF)) n by
        simp [F, g, eg', eF', Part.map_id']⟩

/-- **Kleene's second recursion theorem** -/
/-
**Nat.Partrec.Code.fixed_point** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：fixed_point {f : Code -> Code} (hf : Computable f) : exists c : Code, eval
 (f c) = eval c
参数：hf : Computable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.bind`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α →. β} {g 
: …
· 使用定理 `Partrec₂.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type 
u_5} [inst : Primcodable α] [inst_1 : Primcodable β]   [inst_2 : Primcodable γ] 
[in…
· 使用定理 `Nat.Partrec.Code.eval_part`：eval_part : Partrec₂ eval
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.ofNat`：∀ (α : Type u_5) [inst : Denumerable α], Computable (D
enumerable.ofNat α)
· 使用定理 `Computable.fst`：fst : Computable (@Prod.fst α β)
· 使用定理 `Partrec.to₂`：to₂ {f : α × β ->. σ} (hf : Partrec f) : Partrec₂ fun a b =
> f (a, b)
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Partrec.Code.exists_code`：exists_code {f : Nat ->. Nat} : Nat.Partre
c f ↔ exists c : Code, eval c = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Denumerable.decode_eq_ofNat`：decode_eq_ofNat (α) [Denumerable α] (n : Na
t) : decode (α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Denumerable.ofEquiv_ofNat`：ofEquiv_ofNat (α) {β} [Denumerable α] (e : β 
≃ α) (n) : @ofNat β (ofEquiv _ e) n = e.symm (ofNat α n)
· 使用定理 `Denumerable.sigma_ofNat_val`：sigma_ofNat_val (n : Nat) : ofNat (Sigma γ)
 n = ⟨ofNat α (unpair n).1, ofNat (γ _) (unpair n).2⟩
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Equiv.sigmaEquivProd_apply`：∀ (α : Type u_1) (β : Type u_2) (a : (_ : α)
 × β), (Equiv.sigmaEquivProd α β) a = (a.fst, a.snd)
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Nat.Partrec.Code.primrec₂_curry`：primrec₂_curry : Primrec₂ curry
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
**Kleene's second recursion theorem**
-/
theorem fixed_point₂ {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) : ∃ c : Code, eval c = f c :=
  let ⟨cf, ef⟩ := exists_code.1 hf
  (fixed_point (primrec₂_curry.comp (_root_.Primrec.const cf) Primrec.encode).to_comp).imp
    fun c e => funext fun n => by simp [e.symm, ef, Part.map_id']

end

/-- There are only countably many partial recursive partial functions `ℕ →. ℕ`. -/
/-
**Nat.Partrec.Code.** 是 Mathlib 中的一个实例，位于命名空间 `Nat.Partrec.Code`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There are only countably many partial recursive partial functions `ℕ →. ℕ`.
-/
instance : Countable {f : ℕ →. ℕ // Partrec f} := by
  apply Function.Surjective.countable (f := fun c => ⟨eval c, eval_part.comp (.const c) .id⟩)
  intro ⟨f, hf⟩; simpa using! exists_code.1 hf

set_option backward.isDefEq.respectTransparency false in
/-- There are only countably many computable functions `ℕ → ℕ`. -/
/-
**Nat.Partrec.Code.** 是 Mathlib 中的一个实例，位于命名空间 `Nat.Partrec.Code`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There are only countably many computable functions `ℕ → ℕ`.
-/
instance : Countable {f : ℕ → ℕ // Computable f} :=
  @Function.Injective.countable {f : ℕ → ℕ // Computable f} {f : ℕ →. ℕ // Partrec f} _
    (fun f => ⟨f.val, f.2⟩)
    (fun _ _ h => Subtype.val_inj.1 (PFun.lift_injective (by simpa using h)))

end Nat.Partrec.Code

