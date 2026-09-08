/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.FieldTheory.Perfect

/-!

# The perfect closure of a characteristic `p` ring

## Main definitions

- `PerfectClosure`: the perfect closure of a characteristic `p` ring, which is the smallest
  extension that makes frobenius surjective.

- `PerfectClosure.mk K p (n, x)`: for `n : ℕ` and `x : K` this is `x ^ (p ^ -n)` viewed as
  an element of `PerfectClosure K p`. Every element of `PerfectClosure K p` is of this form
  (`PerfectClosure.mk_surjective`).

- `PerfectClosure.of`: the structure map from `K` to `PerfectClosure K p`.

- `PerfectClosure.lift`: given a ring `K` of characteristic `p` and a perfect ring `L` of the same
  characteristic, any homomorphism `K →+* L` can be lifted to `PerfectClosure K p`.

## Main results

- `PerfectClosure.induction_on`: to prove a result for all elements of the perfect closure, one only
  needs to prove it for all elements of the form `x ^ (p ^ -n)`.

- `PerfectClosure.mk_mul_mk`, `PerfectClosure.one_def`, `PerfectClosure.mk_add_mk`,
  `PerfectClosure.neg_mk`, `PerfectClosure.zero_def`, `PerfectClosure.mk_zero_zero`,
  `PerfectClosure.mk_zero`, `PerfectClosure.mk_inv`, `PerfectClosure.mk_pow`:
  how to do multiplication, addition, etc. on elements of form `x ^ (p ^ -n)`.

- `PerfectClosure.mk_eq_iff`: when does `x ^ (p ^ -n)` equal.

- `PerfectClosure.eq_iff`: same as `PerfectClosure.mk_eq_iff` but with additional assumption that
  `K` being reduced, hence gives a simpler criterion.

- `PerfectClosure.instPerfectRing`: `PerfectClosure K p` is a perfect ring.

## Tags

perfect ring, perfect closure

-/

@[expose] public section

universe u v

open Function

section

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- `PerfectClosure.R` is the relation `(n, x) ∼ (n + 1, x ^ p)` for `n : ℕ` and `x : K`.
`PerfectClosure K p` is the quotient by this relation. -/
@[mk_iff]
/-
**PerfectClosure.R** 是 Mathlib 中的一个归纳类型，位于命名空间 `PerfectClosure`。
形式化陈述：(K : Type u) → [inst : CommRing K] → (p : ℕ) → [Fact (Nat.Prime p)] → [Cha
rP K p] → ℕ × K → ℕ × K → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PerfectClosure.R` is the relation `(n, x) ∼ (n + 1, x ^ p)` for `n : ℕ` and `x 
: K`.
`PerfectClosure K p` is the quotient by this relation.
-/
inductive PerfectClosure.R : ℕ × K → ℕ × K → Prop
  | intro : ∀ n x, PerfectClosure.R (n, x) (n + 1, frobenius K p x)

/-- The perfect closure is the smallest extension that makes frobenius surjective. -/
/-
**PerfectClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PerfectClosure : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The perfect closure is the smallest extension that makes frobenius surjective.
-/
def PerfectClosure : Type u :=
  Quot (PerfectClosure.R K p)

end

namespace PerfectClosure

variable (K : Type u)

section Ring

variable [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- `PerfectClosure.mk K p (n, x)` for `n : ℕ` and `x : K` is an element of `PerfectClosure K p`,
viewed as `x ^ (p ^ -n)`. Every element of `PerfectClosure K p` is of this form
(`PerfectClosure.mk_surjective`). -/
/-
**PerfectClosure.mk** 是 Mathlib 中的一个定义，位于命名空间 `PerfectClosure`。
形式化陈述：mk (x : Nat × K) : PerfectClosure K p
参数：x : Nat × K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PerfectClosure.mk K p (n, x)` for `n : ℕ` and `x : K` is an element of `Perfect
Closure K p`,
viewed as `x ^ (p ^ -n)`. Every element of `PerfectClosure K p` is of this form
(`PerfectClosure.mk_surjective`).
-/
def mk (x : ℕ × K) : PerfectClosure K p :=
  Quot.mk (R K p) x
/-
**PerfectClosure.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：mk_surjective : Function.Surjective (mk K p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
theorem mk_surjective : Function.Surjective (mk K p) := Quot.mk_surjective
/-
**PerfectClosure.mk_succ_pow** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：∀ (K : Type u) [inst : CommRing K] (p : ℕ) [inst_1 : Fact (Nat.Prime p)] [
inst_2 : CharP K p] (m : ℕ) (x : K),   PerfectClosure.mk K p (m + 1, x ^ p) = Pe
rfectClosure.mk K p (m, x)
参数：K : Type u；p : ℕ；Nat.Prime p；m : ℕ；x : K；m + 1, x ^ p；m, x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] theorem mk_succ_pow (m : ℕ) (x : K) : mk K p ⟨m + 1, x ^ p⟩ = mk K p ⟨m, x⟩ :=
  Eq.symm <| Quot.sound (R.intro m x)

@[simp]
/-
**PerfectClosure.quot_mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：quot_mk_eq_mk (x : Nat × K) : (Quot.mk (R K p) x : PerfectClosure K p) = m
k K p x
参数：x : Nat × K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mk_eq_mk (x : ℕ × K) : (Quot.mk (R K p) x : PerfectClosure K p) = mk K p x :=
  rfl

variable {K p}

/-- Lift a function `ℕ × K → L` to a function on `PerfectClosure K p`. -/
/-
**PerfectClosure.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `PerfectClosure`。
形式化陈述：liftOn {L : Type*} (x : PerfectClosure K p) (f : Nat × K -> L) (hf : foral
l x y, R K p x y -> f x = f y) : L
参数：x : PerfectClosure K p；f : Nat × K -> L；hf : forall x y, R K p x y -> f x = f
 y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a function `ℕ × K → L` to a function on `PerfectClosure K p`.
-/
def liftOn {L : Type*} (x : PerfectClosure K p) (f : ℕ × K → L)
    (hf : ∀ x y, R K p x y → f x = f y) : L :=
  Quot.liftOn x f hf

@[simp]
/-
**PerfectClosure.liftOn_mk** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：liftOn_mk {L : Sort _} (f : Nat × K -> L) (hf : forall x y, R K p x y -> f
 x = f y) (x : Nat × K) : (mk K p x).liftOn f hf = f x
参数：f : Nat × K -> L；hf : forall x y, R K p x y -> f x = f y；x : Nat × K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftOn_mk {L : Sort _} (f : ℕ × K → L) (hf : ∀ x y, R K p x y → f x = f y) (x : ℕ × K) :
    (mk K p x).liftOn f hf = f x :=
  rfl

@[elab_as_elim]
/-
**PerfectClosure.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：induction_on (x : PerfectClosure K p) {q : PerfectClosure K p -> Prop} (h 
: forall x, q (mk K p x)) : q x
参数：x : PerfectClosure K p；h : forall x, q (mk K p x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
-/
theorem induction_on (x : PerfectClosure K p) {q : PerfectClosure K p → Prop}
    (h : ∀ x, q (mk K p x)) : q x :=
  Quot.inductionOn x h

variable (K p)

set_option backward.privateInPublic true in
/-
**PerfectClosure.mul_aux_left** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_aux_left (x1 x2 y : ℕ × K) (H : R K p x1 x2) :
    mk K p (x1.1 + y.1, (frobenius K p)^[y.1] x1.2 * (frobenius K p)^[x1.1] y.2) =
      mk K p (x2.1 + y.1, (frobenius K p)^[y.1] x2.2 * (frobenius K p)^[x2.1] y.2) :=
  match x1, x2, H with
  | _, _, R.intro n x =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ_apply', iterate_succ_apply', ← map_mul,
        Nat.succ_add]
      apply R.intro

set_option backward.privateInPublic true in
/-
**PerfectClosure.mul_aux_right** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_aux_right (x y1 y2 : ℕ × K) (H : R K p y1 y2) :
    mk K p (x.1 + y1.1, (frobenius K p)^[y1.1] x.2 * (frobenius K p)^[x.1] y1.2) =
      mk K p (x.1 + y2.1, (frobenius K p)^[y2.1] x.2 * (frobenius K p)^[x.1] y2.2) :=
  match y1, y2, H with
  | _, _, R.intro n y =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ_apply', iterate_succ_apply', ← map_mul]
      apply R.intro

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**PerfectClosure.instMul** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instMul : Mul (PerfectClosure K p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.FieldTheory.PerfectClosure.0.PerfectClosure.mul_aux_rig
ht`：∀ (K : Type u) [inst : CommRing K] (p : ℕ) [inst_1 : Fact (Nat.Prime p)] [in
st_2 : CharP K p] (x y1 y2 : ℕ × K),   PerfectClosure.R K p y1 y…
-/
instance instMul : Mul (PerfectClosure K p) :=
  ⟨Quot.lift
      (fun x : ℕ × K =>
        Quot.lift
          (fun y : ℕ × K =>
            mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 * (frobenius K p)^[x.1] y.2))
          (mul_aux_right K p x))
      fun x1 x2 (H : R K p x1 x2) =>
      funext fun e => Quot.inductionOn e fun y => mul_aux_left K p x1 x2 y H⟩

@[simp]
/-
**PerfectClosure.mk_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：mk_mul_mk (x y : Nat × K) : mk K p x * mk K p y = mk K p (x.1 + y.1, (frob
enius K p)^[y.1] x.2 * (frobenius K p)^[x.1] y.2)
参数：x y : Nat × K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mul_mk (x y : ℕ × K) :
    mk K p x * mk K p y =
      mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 * (frobenius K p)^[x.1] y.2) :=
  rfl
/-
**PerfectClosure.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instCommMonoid : CommMonoid (PerfectClosure K p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoid : CommMonoid (PerfectClosure K p) :=
  { (inferInstance : Mul (PerfectClosure K p)) with
    mul_assoc := fun e f g =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          Quot.inductionOn g fun ⟨s, z⟩ => by
            apply congr_arg (Quot.mk _)
            simp only [mul_assoc, iterate_map_mul, ← iterate_add_apply,
              add_comm, add_left_comm]
    one := mk K p (0, 1)
    one_mul := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [iterate_map_one, iterate_zero_apply, one_mul, zero_add]
    mul_one := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [iterate_map_one, iterate_zero_apply, mul_one, add_zero]
    mul_comm := fun e f =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          congr_arg (Quot.mk _) <| by simp only [add_comm, mul_comm] }
/-
**PerfectClosure.one_def** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：one_def : (1 : PerfectClosure K p) = mk K p (0, 1)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : PerfectClosure K p) = mk K p (0, 1) :=
  rfl
/-
**PerfectClosure.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instInhabited : Inhabited (PerfectClosure K p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (PerfectClosure K p) :=
  ⟨1⟩

set_option backward.privateInPublic true in
/-
**PerfectClosure.add_aux_left** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem add_aux_left (x1 x2 y : ℕ × K) (H : R K p x1 x2) :
    mk K p (x1.1 + y.1, (frobenius K p)^[y.1] x1.2 + (frobenius K p)^[x1.1] y.2) =
      mk K p (x2.1 + y.1, (frobenius K p)^[y.1] x2.2 + (frobenius K p)^[x2.1] y.2) :=
  match x1, x2, H with
  | _, _, R.intro n x =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ_apply', iterate_succ_apply', ← map_add,
        Nat.succ_add]
      apply R.intro

set_option backward.privateInPublic true in
/-
**PerfectClosure.add_aux_right** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem add_aux_right (x y1 y2 : ℕ × K) (H : R K p y1 y2) :
    mk K p (x.1 + y1.1, (frobenius K p)^[y1.1] x.2 + (frobenius K p)^[x.1] y1.2) =
      mk K p (x.1 + y2.1, (frobenius K p)^[y2.1] x.2 + (frobenius K p)^[x.1] y2.2) :=
  match y1, y2, H with
  | _, _, R.intro n y =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ_apply', iterate_succ_apply', ← map_add]
      apply R.intro

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**PerfectClosure.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instAdd : Add (PerfectClosure K p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.FieldTheory.PerfectClosure.0.PerfectClosure.add_aux_rig
ht`：∀ (K : Type u) [inst : CommRing K] (p : ℕ) [inst_1 : Fact (Nat.Prime p)] [in
st_2 : CharP K p] (x y1 y2 : ℕ × K),   PerfectClosure.R K p y1 y…
-/
instance instAdd : Add (PerfectClosure K p) :=
  ⟨Quot.lift
      (fun x : ℕ × K =>
        Quot.lift
          (fun y : ℕ × K =>
            mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 + (frobenius K p)^[x.1] y.2))
          (add_aux_right K p x))
      fun x1 x2 (H : R K p x1 x2) =>
      funext fun e => Quot.inductionOn e fun y => add_aux_left K p x1 x2 y H⟩

@[simp]
/-
**PerfectClosure.mk_add_mk** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：mk_add_mk (x y : Nat × K) : mk K p x + mk K p y = mk K p (x.1 + y.1, (frob
enius K p)^[y.1] x.2 + (frobenius K p)^[x.1] y.2)
参数：x y : Nat × K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_add_mk (x y : ℕ × K) :
    mk K p x + mk K p y =
      mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 + (frobenius K p)^[x.1] y.2) :=
  rfl
/-
**PerfectClosure.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instNeg : Neg (PerfectClosure K p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg : Neg (PerfectClosure K p) :=
  ⟨Quot.lift (fun x : ℕ × K => mk K p (x.1, -x.2)) fun x y (H : R K p x y) =>
      match x, y, H with
      | _, _, R.intro n x => Quot.sound <| by rw [← map_neg]; apply R.intro⟩

@[simp]
/-
**PerfectClosure.neg_mk** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：neg_mk (x : Nat × K) : -mk K p x = mk K p (x.1, -x.2)
参数：x : Nat × K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_mk (x : ℕ × K) : -mk K p x = mk K p (x.1, -x.2) :=
  rfl
/-
**PerfectClosure.instZero** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instZero : Zero (PerfectClosure K p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (PerfectClosure K p) :=
  ⟨mk K p (0, 0)⟩
/-
**PerfectClosure.zero_def** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：zero_def : (0 : PerfectClosure K p) = mk K p (0, 0)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_def : (0 : PerfectClosure K p) = mk K p (0, 0) :=
  rfl

/-- Prior to https://github.com/leanprover-community/mathlib4/pull/15862, this lemma was called `mk_zero_zero`.
See `mk_zero_right` for the lemma used to be called `mk_zero`. -/
@[simp]
/-
**PerfectClosure.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：mk_zero : mk K p 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prior to https://github.com/leanprover-community/mathlib4/pull/15862, this lemma
 was called `mk_zero_zero`.
See `mk_zero_right` for the lemma used to be called `mk_zero`.
-/
theorem mk_zero : mk K p 0 = 0 :=
  rfl

@[simp]
/-
**PerfectClosure.mk_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：mk_zero_right (n : Nat) : mk K p (n, 0) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem mk_zero_right (n : ℕ) : mk K p (n, 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    apply (Quot.sound _).symm
    have := R.intro (p := p) n (0 : K)
    rwa [map_zero] at this
/-
**PerfectClosure.R.sound** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure.R`。
形式化陈述：∀ (K : Type u) [inst : CommRing K] (p : ℕ) [inst_1 : Fact (Nat.Prime p)] [
inst_2 : CharP K p] (m n : ℕ) (x y : K),   (⇑(frobenius K p))^[m] x = y → Perfec
tClosure.mk K p (n, x) = PerfectClosure.mk K p (m + n, y)
参数：K : Type u；p : ℕ；Nat.Prime p；m n : ℕ；x y : K；⇑(frobenius K p)；n, x；m + n, y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
-/
theorem R.sound (m n : ℕ) (x y : K) (H : (frobenius K p)^[m] x = y) :
    mk K p (n, x) = mk K p (m + n, y) := by
  subst H
  induction m with
  | zero => simp only [zero_add, iterate_zero_apply]
  | succ m ih =>
    rw [ih, Nat.succ_add, iterate_succ']
    apply Quot.sound
    apply R.intro
/-
**PerfectClosure.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instAddCommGroup : AddCommGroup (PerfectClosure K p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.FieldTheory.PerfectClosure.0.PerfectClosure.add_aux_rig
ht`：∀ (K : Type u) [inst : CommRing K] (p : ℕ) [inst_1 : Fact (Nat.Prime p)] [in
st_2 : CharP K p] (x y1 y2 : ℕ × K),   PerfectClosure.R K p y1 y…
-/
instance instAddCommGroup : AddCommGroup (PerfectClosure K p) :=
  { (inferInstance : Add (PerfectClosure K p)),
    (inferInstance : Neg (PerfectClosure K p)) with
    add_assoc := fun e f g =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          Quot.inductionOn g fun ⟨s, z⟩ => by
            apply congr_arg (Quot.mk _)
            simp only [iterate_map_add, ← iterate_add_apply, add_assoc, add_comm s _]
    zero_add := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [iterate_map_zero, iterate_zero_apply, zero_add]
    add_zero := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [iterate_map_zero, iterate_zero_apply, add_zero]
    sub_eq_add_neg := fun _ _ => rfl
    neg_add_cancel := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ => by
        simp only [quot_mk_eq_mk, neg_mk, mk_add_mk, iterate_map_neg, neg_add_cancel, mk_zero_right]
    add_comm := fun e f =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ => congr_arg (Quot.mk _) <| by simp only [add_comm]
    nsmul := nsmulRec
    zsmul := zsmulRec }
/-
**PerfectClosure.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instCommRing : CommRing (PerfectClosure K p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommRing : CommRing (PerfectClosure K p) :=
  { instAddCommGroup K p, AddMonoidWithOne.unary,
    (inferInstance : CommMonoid (PerfectClosure K p)) with
    zero_mul := fun a => by
      refine Quot.inductionOn a fun ⟨m, x⟩ => ?_
      rw [zero_def, quot_mk_eq_mk, mk_mul_mk]
      simp only [zero_add, iterate_zero, id_eq, iterate_map_zero, zero_mul, mk_zero_right]
    mul_zero := fun a => by
      refine Quot.inductionOn a fun ⟨m, x⟩ => ?_
      rw [zero_def, quot_mk_eq_mk, mk_mul_mk]
      simp only [iterate_zero, id_eq, iterate_map_zero, mul_zero, mk_zero_right]
    left_distrib := fun e f g =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          Quot.inductionOn g fun ⟨s, z⟩ => by
            simp only [quot_mk_eq_mk, mk_add_mk, mk_mul_mk, add_comm, add_left_comm]
            apply R.sound
            simp only [iterate_map_mul, iterate_map_add, ← iterate_add_apply,
              mul_add, add_comm, add_left_comm]
    right_distrib := fun e f g =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          Quot.inductionOn g fun ⟨s, z⟩ => by
            simp only [quot_mk_eq_mk, mk_add_mk, mk_mul_mk, add_assoc, add_comm _ s,
              add_left_comm _ s]
            apply R.sound
            simp only [iterate_map_mul, iterate_map_add, ← iterate_add_apply,
              add_mul, add_comm, add_left_comm] }
/-
**PerfectClosure.mk_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：mk_eq_iff (x y : Nat × K) : mk K p x = mk K p y ↔ exists z, (frobenius K p
)^[y.1 + z] x.2 = (frobenius K p)^[x.1 + z] y.2
参数：x y : Nat × K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.eqvGen_exact`：Quot.eqvGen_exact (H : Quot.mk r a = Quot.mk r b) : E
qvGen r a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PerfectClosure.R.sound`：∀ (K : Type u) [inst : CommRing K] (p : ℕ) [inst
_1 : Fact (Nat.Prime p)] [inst_2 : CharP K p] (m n : ℕ) (x y : K),   (⇑(frobeniu
s K p))^[m] …
-/
theorem mk_eq_iff (x y : ℕ × K) :
    mk K p x = mk K p y ↔ ∃ z, (frobenius K p)^[y.1 + z] x.2 = (frobenius K p)^[x.1 + z] y.2 := by
  constructor
  · intro H
    replace H := Quot.eqvGen_exact H
    induction H with
    | rel x y H => obtain ⟨n, x⟩ := H; exact ⟨0, rfl⟩
    | refl H => exact ⟨0, rfl⟩
    | symm x y H ih => obtain ⟨w, ih⟩ := ih; exact ⟨w, ih.symm⟩
    | trans x y z H1 H2 ih1 ih2 =>
      obtain ⟨z1, ih1⟩ := ih1
      obtain ⟨z2, ih2⟩ := ih2
      exists z2 + (y.1 + z1)
      rw [← add_assoc, iterate_add_apply, ih1]
      rw [← iterate_add_apply, add_comm, iterate_add_apply, ih2]
      rw [← iterate_add_apply]
      simp only [add_comm, add_left_comm]
  intro H
  obtain ⟨m, x⟩ := x
  obtain ⟨n, y⟩ := y
  obtain ⟨z, H⟩ := H; dsimp only at H
  rw [R.sound K p (n + z) m x _ rfl, R.sound K p (m + z) n y _ rfl, H]
  rw [add_assoc, add_comm, add_comm z]

@[simp]
/-
**PerfectClosure.mk_pow** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：mk_pow (x : Nat × K) (n : Nat) : mk K p x ^ n = mk K p (x.1, x.2 ^ n)
参数：x : Nat × K；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `PerfectClosure.one_def`：one_def : (1 : PerfectClosure K p) = mk K p (0, 
1)
· 使用定理 `PerfectClosure.mk_eq_iff`：mk_eq_iff (x y : Nat × K) : mk K p x = mk K p 
y ↔ exists z, (frobenius K p)^[y.1 + z] x.2 = (frobenius K p)^[x.1 + z] y.2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `PerfectClosure.mk_mul_mk`：mk_mul_mk (x y : Nat × K) : mk K p x * mk K p 
y = mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 * (frobenius K p)^[x.1] y.2)
· 使用引理 `iterate_frobenius`：iterate_frobenius : (frobenius R p)^[n] x = x ^ p ^ n
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem mk_pow (x : ℕ × K) (n : ℕ) : mk K p x ^ n = mk K p (x.1, x.2 ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, one_def, mk_eq_iff]
    exact ⟨0, by simp_rw [← coe_iterateFrobenius, map_one]⟩
  | succ n ih =>
    rw [pow_succ, pow_succ, ih, mk_mul_mk, mk_eq_iff]
    exact ⟨0, by simp_rw [iterate_frobenius, add_zero, mul_pow, ← pow_mul,
      ← pow_add, mul_assoc, ← pow_add]⟩
/-
**PerfectClosure.natCast** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：natCast (n x : Nat) : (x : PerfectClosure K p) = mk K p (n, x)
参数：n x : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `PerfectClosure.mk_zero_right`：mk_zero_right (n : Nat) : mk K p (n, 0) = 
0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `iterate_map_one`：iterate_map_one {M F : Type*} [One M] [FunLike F M M] [
OneHomClass F M M] (f : F) (n : Nat) : f^[n] 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
-/
theorem natCast (n x : ℕ) : (x : PerfectClosure K p) = mk K p (n, x) := by
  induction n with
  | zero =>
    induction x with
    | zero => simp
    | succ x ih => simp [Nat.cast_succ, ih, one_def]
  | succ n ih =>
    rw [ih]; apply Quot.sound
    suffices R K p (n, (x : K)) (Nat.succ n, frobenius K p (x : K)) by
      rwa [map_natCast] at this
    apply R.intro
/-
**PerfectClosure.intCast** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：intCast (x : Int) : (x : PerfectClosure K p) = mk K p (0, x)
参数：x : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `PerfectClosure.natCast`：natCast (n x : Nat) : (x : PerfectClosure K p) =
 mk K p (n, x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
-/
theorem intCast (x : ℤ) : (x : PerfectClosure K p) = mk K p (0, x) := by
  cases x <;> simp [natCast K p 0]
/-
**PerfectClosure.natCast_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：natCast_eq_iff (x y : Nat) : (x : PerfectClosure K p) = y ↔ (x : K) = y
参数：x y : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PerfectClosure.mk_eq_iff`：mk_eq_iff (x y : Nat × K) : mk K p x = mk K p 
y ↔ exists z, (frobenius K p)^[y.1 + z] x.2 = (frobenius K p)^[x.1 + z] y.2
· 使用定理 `PerfectClosure.natCast`：natCast (n x : Nat) : (x : PerfectClosure K p) =
 mk K p (n, x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Function.iterate_fixed`：iterate_fixed {x} (h : f x = x) (n : Nat) : f^[n
] x = x
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
-/
theorem natCast_eq_iff (x y : ℕ) : (x : PerfectClosure K p) = y ↔ (x : K) = y := by
  constructor <;> intro H
  · rw [natCast K p 0, natCast K p 0, mk_eq_iff] at H
    obtain ⟨z, H⟩ := H
    simpa only [zero_add, iterate_fixed (map_natCast _ _)] using H
  rw [natCast K p 0, natCast K p 0, H]
/-
**PerfectClosure.instCharP** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instCharP : CharP (PerfectClosure K p) p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `PerfectClosure.natCast_eq_iff`：natCast_eq_iff (x y : Nat) : (x : Perfect
Closure K p) = y ↔ (x : K) = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
instance instCharP : CharP (PerfectClosure K p) p := by
  constructor; intro x; rw [← CharP.cast_eq_zero_iff K]
  rw [← Nat.cast_zero, natCast_eq_iff, Nat.cast_zero]
/-
**PerfectClosure.frobenius_mk** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：frobenius_mk (x : Nat × K) : (frobenius (PerfectClosure K p) p : PerfectCl
osure K p -> PerfectClosure K p) (mk K p x) = mk _ _ (x.1, x.2 ^ p)
参数：x : Nat × K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectClosure.mk_pow`：mk_pow (x : Nat × K) (n : Nat) : mk K p x ^ n = m
k K p (x.1, x.2 ^ n)
-/
theorem frobenius_mk (x : ℕ × K) :
    (frobenius (PerfectClosure K p) p : PerfectClosure K p → PerfectClosure K p) (mk K p x) =
      mk _ _ (x.1, x.2 ^ p) := by
  simp only [frobenius_def]
  exact mk_pow K p x p

/-- Embedding of `K` into `PerfectClosure K p` -/
/-
**PerfectClosure.of** 是 Mathlib 中的一个定义，位于命名空间 `PerfectClosure`。
形式化陈述：of : K ->+* PerfectClosure K p where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of `K` into `PerfectClosure K p`
-/
def of : K →+* PerfectClosure K p where
  toFun x := mk _ _ (0, x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
/-
**PerfectClosure.of_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：of_apply (x : K) : of K p x = mk _ _ (0, x)
参数：x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_apply (x : K) : of K p x = mk _ _ (0, x) :=
  rfl
/-
**PerfectClosure.instReduced** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instReduced : IsReduced (PerfectClosure K p) where eq_zero x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectClosure.induction_on`：induction_on (x : PerfectClosure K p) {q : 
PerfectClosure K p -> Prop} (h : forall x, q (mk K p x)) : q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_pow_self`：∀ {n a : ℕ}, 1 < a → n < a ^ n
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `PerfectClosure.mk_pow`：mk_pow (x : Nat × K) (n : Nat) : mk K p x ^ n = m
k K p (x.1, x.2 ^ n)
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
-/
instance instReduced : IsReduced (PerfectClosure K p) where
  eq_zero x := induction_on x fun x ⟨n, h⟩ ↦ by
    replace h : mk K p x ^ p ^ n = 0 := by
      rw [← Nat.sub_add_cancel ((n.lt_pow_self (Fact.out : p.Prime).one_lt).le),
        pow_add, h, mul_zero]
    simp only [zero_def, mk_pow, mk_eq_iff, zero_add, ← coe_iterateFrobenius, map_zero] at h ⊢
    obtain ⟨m, h⟩ := h
    exact ⟨n + m, by simpa only [iterateFrobenius_def, pow_add, pow_mul] using h⟩
/-
**PerfectClosure.instPerfectRing** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instPerfectRing : PerfectRing (PerfectClosure K p) p where bijective_frobe
nius
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `PerfectClosure.induction_on`：induction_on (x : PerfectClosure K p) {q : 
PerfectClosure K p -> Prop} (h : forall x, q (mk K p x)) : q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PerfectClosure.frobenius_mk`：frobenius_mk (x : Nat × K) : (frobenius (Pe
rfectClosure K p) p : PerfectClosure K p -> PerfectClosure K p) (mk K p x) = mk 
_ _ (x.1, x.2 ^ p…
· 使用定理 `PerfectClosure.mk_succ_pow`：∀ (K : Type u) [inst : CommRing K] (p : ℕ) [
inst_1 : Fact (Nat.Prime p)] [inst_2 : CharP K p] (m : ℕ) (x : K),   PerfectClos
ure.mk K p (m + …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instPerfectRing : PerfectRing (PerfectClosure K p) p where
  bijective_frobenius := by
    simp_rw [← frobenius_def]
    let f : PerfectClosure K p → PerfectClosure K p := fun e ↦
      liftOn e (fun x => mk K p (x.1 + 1, x.2)) fun x y H =>
      match x, y, H with
      | _, _, R.intro n x => Quot.sound (R.intro _ _)
    refine bijective_iff_has_inverse.mpr ⟨f, fun e ↦ induction_on e fun ⟨n, x⟩ ↦ ?_,
      fun e ↦ induction_on e fun ⟨n, x⟩ ↦ ?_⟩ <;>
      simp only [f, liftOn_mk, frobenius_mk, mk_succ_pow]

@[simp]
/-
**PerfectClosure.iterate_frobenius_mk** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`
。
形式化陈述：iterate_frobenius_mk (n : Nat) (x : K) : (frobenius (PerfectClosure K p) p
)^[n] (mk K p ⟨n, x⟩) = of K p x
参数：n : Nat；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PerfectClosure.frobenius_mk`：frobenius_mk (x : Nat × K) : (frobenius (Pe
rfectClosure K p) p : PerfectClosure K p -> PerfectClosure K p) (mk K p x) = mk 
_ _ (x.1, x.2 ^ p…
· 使用定理 `PerfectClosure.mk_succ_pow`：∀ (K : Type u) [inst : CommRing K] (p : ℕ) [
inst_1 : Fact (Nat.Prime p)] [inst_2 : CharP K p] (m : ℕ) (x : K),   PerfectClos
ure.mk K p (m + …
-/
theorem iterate_frobenius_mk (n : ℕ) (x : K) :
    (frobenius (PerfectClosure K p) p)^[n] (mk K p ⟨n, x⟩) = of K p x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, ← ih, frobenius_mk, mk_succ_pow]

/-- Given a ring `K` of characteristic `p` and a perfect ring `L` of the same characteristic,
any homomorphism `K →+* L` can be lifted to `PerfectClosure K p`. -/
/-
**PerfectClosure.lift** 是 Mathlib 中的一个定义，位于命名空间 `PerfectClosure`。
形式化陈述：lift (L : Type v) [CommSemiring L] [CharP L p] [PerfectRing L p] : (K ->+*
 L) ≃ (PerfectClosure K p ->+* L) where toFun f
参数：L : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a ring `K` of characteristic `p` and a perfect ring `L` of the same charac
teristic,
any homomorphism `K →+* L` can be lifted to `PerfectClosure K p`.
-/
noncomputable def lift (L : Type v) [CommSemiring L] [CharP L p] [PerfectRing L p] :
    (K →+* L) ≃ (PerfectClosure K p →+* L) where
  toFun f :=
    { toFun := by
        refine fun e => liftOn e (fun x => (frobeniusEquiv L p).symm^[x.1] (f x.2)) ?_
        rintro - - ⟨n, x⟩
        simp [f.map_frobenius]
      map_one' := f.map_one
      map_zero' := f.map_zero
      map_mul' := by
        rintro ⟨n, x⟩ ⟨m, y⟩
        simp only [quot_mk_eq_mk, liftOn_mk, f.map_iterate_frobenius, mk_mul_mk, map_mul,
          iterate_map_mul]
        have := LeftInverse.iterate (frobeniusEquiv_symm_apply_frobenius L p)
        rw [iterate_add_apply, this _ _, add_comm, iterate_add_apply, this _ _]
      map_add' := by
        rintro ⟨n, x⟩ ⟨m, y⟩
        simp only [quot_mk_eq_mk, liftOn_mk, f.map_iterate_frobenius, mk_add_mk, map_add,
          iterate_map_add]
        have := LeftInverse.iterate (frobeniusEquiv_symm_apply_frobenius L p)
        rw [iterate_add_apply, this _ _, add_comm n, iterate_add_apply, this _ _] }
  invFun f := f.comp (of K p)
  right_inv f := by
    ext ⟨n, x⟩
    simp only [quot_mk_eq_mk, RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      liftOn_mk]
    apply (injective_frobenius L p).iterate n
    rw [← f.map_iterate_frobenius, iterate_frobenius_mk,
      RightInverse.iterate (frobenius_apply_frobeniusEquiv_symm L p) n]

end Ring

/-
**PerfectClosure.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：eq_iff [CommRing K] [IsReduced K] (p : Nat) [Fact p.Prime] [CharP K p] (x 
y : Nat × K) : mk K p x = mk K p y ↔ (frobenius K p)^[y.1] x.2 = (frobenius K p)
^[x.1] y.2
参数：p : Nat；x y : Nat × K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PerfectClosure.mk_eq_iff`：mk_eq_iff (x y : Nat × K) : mk K p x = mk K p 
y ↔ exists z, (frobenius K p)^[y.1 + z] x.2 = (frobenius K p)^[x.1 + z] y.2
· 使用定理 `Function.Injective.iterate`：∀ {α : Type u} {f : α → α}, Function.Injecti
ve f → ∀ (n : ℕ), Function.Injective f^[n]
· 使用定理 `frobenius_inj`：frobenius_inj : Function.Injective (frobenius R p)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_add`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m + n] = 
f^[m] ∘ f^[n]
-/
theorem eq_iff [CommRing K] [IsReduced K] (p : ℕ) [Fact p.Prime] [CharP K p] (x y : ℕ × K) :
    mk K p x = mk K p y ↔ (frobenius K p)^[y.1] x.2 = (frobenius K p)^[x.1] y.2 :=
  (mk_eq_iff K p x y).trans
    ⟨fun ⟨z, H⟩ => (frobenius_inj K p).iterate z <| by simpa only [add_comm, iterate_add] using! H,
      fun H => ⟨0, H⟩⟩
/-
**PerfectClosure.** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing K] [IsReduced K] (p : ℕ) [Fact p.Prime] [CharP K p] [Nontrivial K] :
    Nontrivial (PerfectClosure K p) where
  exists_pair_ne := ⟨0, 1, fun H => zero_ne_one ((eq_iff _ _ _ _).1 H)⟩

section Field

variable [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-
**PerfectClosure.instInv** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instInv : Inv (PerfectClosure K p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInv : Inv (PerfectClosure K p) :=
  ⟨Quot.lift (fun x : ℕ × K => Quot.mk (R K p) (x.1, x.2⁻¹)) fun x y (H : R K p x y) =>
      match x, y, H with
      | _, _, R.intro n x =>
        Quot.sound <| by
          simp only [frobenius_def]
          rw [← inv_pow]
          apply R.intro⟩

@[simp]
/-
**PerfectClosure.mk_inv** 是 Mathlib 中的一个定理，位于命名空间 `PerfectClosure`。
形式化陈述：mk_inv (x : Nat × K) : (mk K p x)⁻¹ = mk K p (x.1, x.2⁻¹)
参数：x : Nat × K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_inv (x : ℕ × K) : (mk K p x)⁻¹ = mk K p (x.1, x.2⁻¹) :=
  rfl
/-
**PerfectClosure.instDivisionRing** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instDivisionRing : DivisionRing (PerfectClosure K p) where mul_inv_cancel 
e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDivisionRing : DivisionRing (PerfectClosure K p) where
  mul_inv_cancel e := induction_on e fun ⟨m, x⟩ H ↦ by
    have := mt (eq_iff _ _ _ _).2 H
    rw [mk_inv, mk_mul_mk]
    refine (eq_iff K p _ _).2 ?_
    simp only [iterate_map_one, iterate_map_zero, iterate_zero_apply, ← iterate_map_mul] at this ⊢
    rw [mul_inv_cancel₀ this, iterate_map_one]
  inv_zero := congr_arg (Quot.mk (R K p)) (by rw [inv_zero])
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
/-
**PerfectClosure.instField** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instField : Field (PerfectClosure K p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instField : Field (PerfectClosure K p) :=
  { (inferInstance : DivisionRing (PerfectClosure K p)),
    (inferInstance : CommRing (PerfectClosure K p)) with }
/-
**PerfectClosure.instPerfectField** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：instPerfectField : PerfectField (PerfectClosure K p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `PerfectRing.toPerfectField`：PerfectRing.toPerfectField (K : Type*) (p : 
Nat) [Field K] [ExpChar K p] [PerfectRing K p] : PerfectField K
-/
instance instPerfectField : PerfectField (PerfectClosure K p) := PerfectRing.toPerfectField _ p

end Field

end PerfectClosure

