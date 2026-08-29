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

variable (K : Type u) [CommRing K] (p : Nat) [Fact p.Prime] [CharP K p]

/-- `PerfectClosure.R` is the relation `(n, x) ∼ (n + 1, x ^ p)` for `n : ℕ` and `x : K`.
`PerfectClosure K p` is the quotient by this relation. -/
@[mk_iff]
/--
Inductive type `PerfectClosure.R` / 归纳类型 `PerfectClosure.R`

English:
inductive PerfectClosure.R
  parameters: : Nat × K -> Nat × K -> Prop
  constructors (1):
    - intro: forall n x, PerfectClosure.R (n, x) (n + 1, frobenius K p x)

中文:
归纳类型 完美闭包.R
  参数: : 自然数 × K -> 自然数 × K -> 命题
  构造子 (1 个):
    - intro: 对任意 n x, 完美闭包.R (n, x) (n + 1, frobenius K p x)
-/
inductive PerfectClosure.R : Nat × K -> Nat × K -> Prop
  | intro : forall n x, PerfectClosure.R (n, x) (n + 1, frobenius K p x)

/--
Definition of `PerfectClosure` / `PerfectClosure` 的定义

English:
definition PerfectClosure
  signature: : Type u
  body: Quot (PerfectClosure.R K p)

中文:
定义 完美闭包
  签名: : 类型u
  定义体: Quot (PerfectClosure.R K p)

Depends on / 依赖: PerfectClosure, PerfectClosure.R
-/
def PerfectClosure : Type u :=
  Quot (PerfectClosure.R K p)

end

namespace PerfectClosure

variable (K : Type u)

section Ring

variable [CommRing K] (p : Nat) [Fact p.Prime] [CharP K p]

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x : Nat × K)
  body: Quot.mk (R K p) x

中文:
定义 mk
  签名: (x : 自然数 × K)
  定义体: Quot.mk (R K p) x

Depends on / 依赖: Quot.mk
-/
def mk (x : Nat × K) : PerfectClosure K p :=
  Quot.mk (R K p) x

/--
theorem `mk_surjective` / 定理 `mk_surjective`

English:
theorem mk_surjective
  statement: Function.Surjective (mk K p)
  proof: Quot.mk_surjective

中文:
定理 mk_surjective
  结论: 函数.满射 (mk K p)
  证明: Quot.mk_surjective

Depends on / 依赖: Quot.mk_surjective, mk_surjective
-/
theorem mk_surjective : Function.Surjective (mk K p) := Quot.mk_surjective

/--
theorem `mk_succ_pow` / 定理 `mk_succ_pow`

English:
theorem mk_succ_pow
  given: (m : Nat) (x : K)
  statement: mk K p ⟨m + 1, x ^ p⟩ = mk K p ⟨m, x⟩
  proof: Eq.symm Quot.sound (R.intro m x)

@[simp]

中文:
定理 mk_succ_pow
  条件: (m : 自然数) (x : K)
  结论: mk K p ⟨m + 1, x ^ p⟩ = mk K p ⟨m, x⟩
  证明: Eq.symm Quot.sound (R.intro m x)

@[simp]
-/
@[simp] theorem mk_succ_pow (m : Nat) (x : K) : mk K p ⟨m + 1, x ^ p⟩ = mk K p ⟨m, x⟩ :=
Eq.symm Quot.sound (R.intro m x)

@[simp]
/--
theorem `quot_mk_eq_mk` / 定理 `quot_mk_eq_mk`

English:
theorem quot_mk_eq_mk
  given: (x : Nat × K)
  statement: (Quot.mk (R K p) x : PerfectClosure K p) = mk K p x
  proof: rfl

中文:
定理 quot_mk_eq_mk
  条件: (x : 自然数 × K)
  结论: (商.mk (R K p) x : 完美闭包 K p) = mk K p x
  证明: rfl
-/
theorem quot_mk_eq_mk (x : Nat × K) : (Quot.mk (R K p) x : PerfectClosure K p) = mk K p x :=
  rfl

variable {K p}

/--
Definition of `liftOn` / `liftOn` 的定义

English:
definition liftOn
  signature: {L : Type*} (x : PerfectClosure K p) (f : Nat × K -> L)
  body: Quot.liftOn x f hf

@[simp]

中文:
定义 liftOn
  签名: {L : 类型} (x : 完美闭包 K p) (f : 自然数 × K -> L)
  定义体: Quot.liftOn x f hf

@[simp]

Depends on / 依赖: Quot.liftOn, liftOn
-/
def liftOn {L : Type*} (x : PerfectClosure K p) (f : Nat × K -> L)
    (hf : forall x y, R K p x y -> f x = f y) : L :=
  Quot.liftOn x f hf

@[simp]
/--
theorem `liftOn_mk` / 定理 `liftOn_mk`

English:
theorem liftOn_mk
  given: {L : Sort _} (f : Nat × K -> L) (hf : forall x y, R K p x y -> f x = f y) (x : Nat × K)
  proof: rfl

@[elab_as_elim]

中文:
定理 liftOn_mk
  条件: {L : 类型层 _} (f : 自然数 × K -> L) (hf : 对任意 x y, R K p x y -> f x = f y) (x : 自然数 × K)
  证明: rfl

@[elab_as_elim]
-/
theorem liftOn_mk {L : Sort _} (f : Nat × K -> L) (hf : forall x y, R K p x y -> f x = f y) (x : Nat × K) :
    (mk K p x).liftOn f hf = f x :=
  rfl

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: (x : PerfectClosure K p) {q : PerfectClosure K p -> Prop}
  proof: Quot.inductionOn x h

中文:
定理 induction_on
  结论: (x : 完美闭包 K p) {q : 完美闭包 K p -> 命题}
  证明: Quot.inductionOn x h

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem induction_on (x : PerfectClosure K p) {q : PerfectClosure K p -> Prop}
    (h : forall x, q (mk K p x)) : q x :=
  Quot.inductionOn x h

variable (K p)

set_option backward.privateInPublic true in
/--
theorem `mul_aux_left` / 定理 `mul_aux_left`

English:
theorem mul_aux_left
  given: (x1 x2 y : Nat × K) (H : R K p x1 x2)
  proof: match x1, x2, H with
  | _, _, R.intro n x =>
Quot.sound by
      rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [← map_mul]; rw [Nat.succ_add]
      apply R.intro

中文:
定理 mul_aux_left
  条件: (x1 x2 y : 自然数 × K) (H : R K p x1 x2)
  证明: match x1, x2, H with
  | _, _, R.intro n x =>
Quot.sound by
      rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [← map_mul]; rw [Nat.succ_add]
      apply R.intro
-/
private theorem mul_aux_left (x1 x2 y : Nat × K) (H : R K p x1 x2) :
    mk K p (x1.1 + y.1, (frobenius K p)^[y.1] x1.2 * (frobenius K p)^[x1.1] y.2) =
      mk K p (x2.1 + y.1, (frobenius K p)^[y.1] x2.2 * (frobenius K p)^[x2.1] y.2) :=
  match x1, x2, H with
  | _, _, R.intro n x =>
Quot.sound by
      rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [← map_mul]; rw [Nat.succ_add]
      apply R.intro

set_option backward.privateInPublic true in
/--
theorem `mul_aux_right` / 定理 `mul_aux_right`

English:
theorem mul_aux_right
  given: (x y1 y2 : Nat × K) (H : R K p y1 y2)
  proof: match y1, y2, H with
  | _, _, R.intro n y =>
Quot.sound by
      rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [← map_mul]
      apply R.intro

中文:
定理 mul_aux_right
  条件: (x y1 y2 : 自然数 × K) (H : R K p y1 y2)
  证明: match y1, y2, H with
  | _, _, R.intro n y =>
Quot.sound by
      rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [← map_mul]
      apply R.intro
-/
private theorem mul_aux_right (x y1 y2 : Nat × K) (H : R K p y1 y2) :
    mk K p (x.1 + y1.1, (frobenius K p)^[y1.1] x.2 * (frobenius K p)^[x.1] y1.2) =
      mk K p (x.1 + y2.1, (frobenius K p)^[y2.1] x.2 * (frobenius K p)^[x.1] y2.2) :=
  match y1, y2, H with
  | _, _, R.intro n y =>
Quot.sound by
      rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [← map_mul]
      apply R.intro

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (PerfectClosure K p)
  body: ⟨Quot.lift
      (fun x : Nat × K =>
        Quot.lift
          (fun y : Nat × K =>
            mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 * (frobenius K p)^[x.1] y.2))
          (mul_aux_right K p x))
      fun x1 x2 (H : R K p x1 x2) =>
      funext fun e => Quot.inductionOn e fun y => mul_aux_left K p x1 x2 y H⟩

@[simp]

中文:
实例 instMul
  签名: : 乘法 (完美闭包 K p)
  定义体: ⟨Quot.lift
      (fun x : Nat × K =>
        Quot.lift
          (fun y : Nat × K =>
            mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 * (frobenius K p)^[x.1] y.2))
          (mul_aux_right K p x))
      fun x1 x2 (H : R K p x1 x2) =>
      funext fun e => Quot.inductionOn e fun y => mul_aux_left K p x1 x2 y H⟩

@[simp]

Depends on / 依赖: Quot.inductionOn, Quot.lift, frobenius, inductionOn, mul_aux_left, mul_aux_right
-/
instance instMul : Mul (PerfectClosure K p) :=
  ⟨Quot.lift
      (fun x : Nat × K =>
        Quot.lift
          (fun y : Nat × K =>
            mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 * (frobenius K p)^[x.1] y.2))
          (mul_aux_right K p x))
      fun x1 x2 (H : R K p x1 x2) =>
      funext fun e => Quot.inductionOn e fun y => mul_aux_left K p x1 x2 y H⟩

@[simp]
/--
theorem `mk_mul_mk` / 定理 `mk_mul_mk`

English:
theorem mk_mul_mk
  given: (x y : Nat × K)
  proof: rfl

中文:
定理 mk_mul_mk
  条件: (x y : 自然数 × K)
  证明: rfl
-/
theorem mk_mul_mk (x y : Nat × K) :
    mk K p x * mk K p y =
      mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 * (frobenius K p)^[x.1] y.2) :=
  rfl

/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: : CommMonoid (PerfectClosure K p)
  body: { (inferInstance : Mul (PerfectClosure K p)) with
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
congr_arg (Quot.mk _) by
          simp only [iterate_map_one, iterate_zero_apply, one_mul, zero_add]
    mul_one := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
congr_arg (Quot.mk _) by
          simp only [iterate_map_one, iterate_zero_apply, mul_one, add_zero]
    mul_comm := fun e f =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
congr_arg (Quot.mk _) by simp only [add_comm, mul_comm] }

中文:
实例 instCommMonoid
  签名: : 交换幺半群 (完美闭包 K p)
  定义体: { (inferInstance : Mul (PerfectClosure K p)) with
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
congr_arg (Quot.mk _) by
          simp only [iterate_map_one, iterate_zero_apply, one_mul, zero_add]
    mul_one := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
congr_arg (Quot.mk _) by
          simp only [iterate_map_one, iterate_zero_apply, mul_one, add_zero]
    mul_comm := fun e f =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
congr_arg (Quot.mk _) by simp only [add_comm, mul_comm] }

Depends on / 依赖: PerfectClosure, Quot.inductionOn, Quot.mk, add_comm, add_left_comm, congr_arg, inductionOn, iterate_add_apply, iterate_map_mul, iterate_map_one, iterate_zero_apply, mul_assoc, mul_one, one_mul, zero_add
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
congr_arg (Quot.mk _) by
          simp only [iterate_map_one, iterate_zero_apply, one_mul, zero_add]
    mul_one := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
congr_arg (Quot.mk _) by
          simp only [iterate_map_one, iterate_zero_apply, mul_one, add_zero]
    mul_comm := fun e f =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
congr_arg (Quot.mk _) by simp only [add_comm, mul_comm] }

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : PerfectClosure K p) = mk K p (0, 1)
  proof: rfl

中文:
定理 one_def
  结论: (1 : 完美闭包 K p) = mk K p (0, 1)
  证明: rfl
-/
theorem one_def : (1 : PerfectClosure K p) = mk K p (0, 1) :=
  rfl

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (PerfectClosure K p)
  body: ⟨1⟩

中文:
实例 instInhabited
  签名: : 可居 (完美闭包 K p)
  定义体: ⟨1⟩
-/
instance instInhabited : Inhabited (PerfectClosure K p) :=
  ⟨1⟩

set_option backward.privateInPublic true in
/--
theorem `add_aux_left` / 定理 `add_aux_left`

English:
theorem add_aux_left
  given: (x1 x2 y : Nat × K) (H : R K p x1 x2)
  proof: match x1, x2, H with
  | _, _, R.intro n x =>
Quot.sound by
      rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [← map_add]; rw [Nat.succ_add]
      apply R.intro

中文:
定理 add_aux_left
  条件: (x1 x2 y : 自然数 × K) (H : R K p x1 x2)
  证明: match x1, x2, H with
  | _, _, R.intro n x =>
Quot.sound by
      rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [← map_add]; rw [Nat.succ_add]
      apply R.intro
-/
private theorem add_aux_left (x1 x2 y : Nat × K) (H : R K p x1 x2) :
    mk K p (x1.1 + y.1, (frobenius K p)^[y.1] x1.2 + (frobenius K p)^[x1.1] y.2) =
      mk K p (x2.1 + y.1, (frobenius K p)^[y.1] x2.2 + (frobenius K p)^[x2.1] y.2) :=
  match x1, x2, H with
  | _, _, R.intro n x =>
Quot.sound by
      rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [← map_add]; rw [Nat.succ_add]
      apply R.intro

set_option backward.privateInPublic true in
/--
theorem `add_aux_right` / 定理 `add_aux_right`

English:
theorem add_aux_right
  given: (x y1 y2 : Nat × K) (H : R K p y1 y2)
  proof: match y1, y2, H with
  | _, _, R.intro n y =>
Quot.sound by
      rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [← map_add]
      apply R.intro

中文:
定理 add_aux_right
  条件: (x y1 y2 : 自然数 × K) (H : R K p y1 y2)
  证明: match y1, y2, H with
  | _, _, R.intro n y =>
Quot.sound by
      rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [← map_add]
      apply R.intro
-/
private theorem add_aux_right (x y1 y2 : Nat × K) (H : R K p y1 y2) :
    mk K p (x.1 + y1.1, (frobenius K p)^[y1.1] x.2 + (frobenius K p)^[x.1] y1.2) =
      mk K p (x.1 + y2.1, (frobenius K p)^[y2.1] x.2 + (frobenius K p)^[x.1] y2.2) :=
  match y1, y2, H with
  | _, _, R.intro n y =>
Quot.sound by
      rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [← map_add]
      apply R.intro

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add (PerfectClosure K p)
  body: ⟨Quot.lift
      (fun x : Nat × K =>
        Quot.lift
          (fun y : Nat × K =>
            mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 + (frobenius K p)^[x.1] y.2))
          (add_aux_right K p x))
      fun x1 x2 (H : R K p x1 x2) =>
      funext fun e => Quot.inductionOn e fun y => add_aux_left K p x1 x2 y H⟩

@[simp]

中文:
实例 instAdd
  签名: : 加法 (完美闭包 K p)
  定义体: ⟨Quot.lift
      (fun x : Nat × K =>
        Quot.lift
          (fun y : Nat × K =>
            mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 + (frobenius K p)^[x.1] y.2))
          (add_aux_right K p x))
      fun x1 x2 (H : R K p x1 x2) =>
      funext fun e => Quot.inductionOn e fun y => add_aux_left K p x1 x2 y H⟩

@[simp]

Depends on / 依赖: Quot.inductionOn, Quot.lift, add_aux_left, add_aux_right, frobenius, inductionOn
-/
instance instAdd : Add (PerfectClosure K p) :=
  ⟨Quot.lift
      (fun x : Nat × K =>
        Quot.lift
          (fun y : Nat × K =>
            mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 + (frobenius K p)^[x.1] y.2))
          (add_aux_right K p x))
      fun x1 x2 (H : R K p x1 x2) =>
      funext fun e => Quot.inductionOn e fun y => add_aux_left K p x1 x2 y H⟩

@[simp]
/--
theorem `mk_add_mk` / 定理 `mk_add_mk`

English:
theorem mk_add_mk
  given: (x y : Nat × K)
  proof: rfl

中文:
定理 mk_add_mk
  条件: (x y : 自然数 × K)
  证明: rfl
-/
theorem mk_add_mk (x y : Nat × K) :
    mk K p x + mk K p y =
      mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 + (frobenius K p)^[x.1] y.2) :=
  rfl

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg (PerfectClosure K p)
  body: ⟨Quot.lift (fun x : Nat × K => mk K p (x.1, -x.2)) fun x y (H : R K p x y) =>
      match x, y, H with
| _, _, R.intro n x => Quot.sound by rw [← map_neg]; apply R.intro⟩

@[simp]

中文:
实例 instNeg
  签名: : 取负 (完美闭包 K p)
  定义体: ⟨Quot.lift (fun x : Nat × K => mk K p (x.1, -x.2)) fun x y (H : R K p x y) =>
      match x, y, H with
| _, _, R.intro n x => Quot.sound by rw [← map_neg]; apply R.intro⟩

@[simp]

Depends on / 依赖: Quot.lift, Quot.sound, R.intro, map_neg
-/
instance instNeg : Neg (PerfectClosure K p) :=
  ⟨Quot.lift (fun x : Nat × K => mk K p (x.1, -x.2)) fun x y (H : R K p x y) =>
      match x, y, H with
| _, _, R.intro n x => Quot.sound by rw [← map_neg]; apply R.intro⟩

@[simp]
/--
theorem `neg_mk` / 定理 `neg_mk`

English:
theorem neg_mk
  given: (x : Nat × K)
  statement: -mk K p x = mk K p (x.1, -x.2)
  proof: rfl

中文:
定理 neg_mk
  条件: (x : 自然数 × K)
  结论: -mk K p x = mk K p (x.1, -x.2)
  证明: rfl
-/
theorem neg_mk (x : Nat × K) : -mk K p x = mk K p (x.1, -x.2) :=
  rfl

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (PerfectClosure K p)
  body: ⟨mk K p (0, 0)⟩

中文:
实例 instZero
  签名: : 零 (完美闭包 K p)
  定义体: ⟨mk K p (0, 0)⟩
-/
instance instZero : Zero (PerfectClosure K p) :=
  ⟨mk K p (0, 0)⟩

/--
theorem `zero_def` / 定理 `zero_def`

English:
theorem zero_def
  statement: (0 : PerfectClosure K p) = mk K p (0, 0)
  proof: rfl

中文:
定理 zero_def
  结论: (0 : 完美闭包 K p) = mk K p (0, 0)
  证明: rfl
-/
theorem zero_def : (0 : PerfectClosure K p) = mk K p (0, 0) :=
  rfl

/-- Prior to https://github.com/leanprover-community/mathlib4/pull/15862, this lemma was called `mk_zero_zero`.
See `mk_zero_right` for the lemma used to be called `mk_zero`. -/
@[simp]
/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  statement: mk K p 0 = 0
  proof: rfl

@[simp]

中文:
定理 mk_zero
  结论: mk K p 0 = 0
  证明: rfl

@[simp]
-/
theorem mk_zero : mk K p 0 = 0 :=
  rfl

@[simp]
/--
theorem `mk_zero_right` / 定理 `mk_zero_right`

English:
theorem mk_zero_right
  given: (n : Nat)
  statement: mk K p (n, 0) = 0
  proof: by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    apply (Quot.sound _).symm
    have := R.intro (p := p) n (0 : K)
    rwa [map_zero] at this

中文:
定理 mk_zero_right
  条件: (n : 自然数)
  结论: mk K p (n, 0) = 0
  证明: by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    apply (Quot.sound _).symm
    have := R.intro (p := p) n (0 : K)
    rwa [map_zero] at this

Depends on / 依赖: Quot.sound, R.intro, map_zero
-/
theorem mk_zero_right (n : Nat) : mk K p (n, 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    apply (Quot.sound _).symm
    have := R.intro (p := p) n (0 : K)
    rwa [map_zero] at this

/--
theorem `R.sound` / 定理 `R.sound`

English:
theorem R.sound
  given: (m n : Nat) (x y : K) (H : (frobenius K p)^[m] x = y)
  proof: by
  subst H
  induction m with
  | zero => simp only [zero_add, iterate_zero_apply]
  | succ m ih =>
    rw [ih]; rw [Nat.succ_add]; rw [iterate_succ']
    apply Quot.sound
    apply R.intro

中文:
定理 R.sound
  条件: (m n : 自然数) (x y : K) (H : (frobenius K p)^[m] x = y)
  证明: by
  subst H
  induction m with
  | zero => simp only [zero_add, iterate_zero_apply]
  | succ m ih =>
    rw [ih]; rw [Nat.succ_add]; rw [iterate_succ']
    apply Quot.sound
    apply R.intro

Depends on / 依赖: Nat.succ_add, Quot.sound, R.intro, iterate_succ, iterate_zero_apply, succ_add, zero_add
-/
theorem R.sound (m n : Nat) (x y : K) (H : (frobenius K p)^[m] x = y) :
    mk K p (n, x) = mk K p (m + n, y) := by
  subst H
  induction m with
  | zero => simp only [zero_add, iterate_zero_apply]
  | succ m ih =>
    rw [ih]; rw [Nat.succ_add]; rw [iterate_succ']
    apply Quot.sound
    apply R.intro

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: : AddCommGroup (PerfectClosure K p)
  body: { (inferInstance : Add (PerfectClosure K p)),
    (inferInstance : Neg (PerfectClosure K p)) with
    add_assoc := fun e f g =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          Quot.inductionOn g fun ⟨s, z⟩ => by
            apply congr_arg (Quot.mk _)
            simp only [iterate_map_add, ← iterate_add_apply, add_assoc, add_comm s _]
    zero_add := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
congr_arg (Quot.mk _) by
          simp only [iterate_map_zero, iterate_zero_apply, zero_add]
    add_zero := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
congr_arg (Quot.mk _) by
          simp only [iterate_map_zero, iterate_zero_apply, add_zero]
    sub_eq_add_neg := fun _ _ => rfl
    neg_add_cancel := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ => by
        simp only [quot_mk_eq_mk, neg_mk, mk_add_mk, iterate_map_neg, neg_add_cancel, mk_zero_right]
    add_comm := fun e f =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
Quot.inductionOn f fun ⟨n, y⟩ => congr_arg (Quot.mk _) by simp only [add_comm]
    nsmul := nsmulRec
    zsmul := zsmulRec }

中文:
实例 instAddCommGroup
  签名: : 加法交换群 (完美闭包 K p)
  定义体: { (inferInstance : Add (PerfectClosure K p)),
    (inferInstance : Neg (PerfectClosure K p)) with
    add_assoc := fun e f g =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          Quot.inductionOn g fun ⟨s, z⟩ => by
            apply congr_arg (Quot.mk _)
            simp only [iterate_map_add, ← iterate_add_apply, add_assoc, add_comm s _]
    zero_add := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
congr_arg (Quot.mk _) by
          simp only [iterate_map_zero, iterate_zero_apply, zero_add]
    add_zero := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
congr_arg (Quot.mk _) by
          simp only [iterate_map_zero, iterate_zero_apply, add_zero]
    sub_eq_add_neg := fun _ _ => rfl
    neg_add_cancel := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ => by
        simp only [quot_mk_eq_mk, neg_mk, mk_add_mk, iterate_map_neg, neg_add_cancel, mk_zero_right]
    add_comm := fun e f =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
Quot.inductionOn f fun ⟨n, y⟩ => congr_arg (Quot.mk _) by simp only [add_comm]
    nsmul := nsmulRec
    zsmul := zsmulRec }

Depends on / 依赖: PerfectClosure, Quot.inductionOn, Quot.mk, add_assoc, add_comm, add_zero, congr_arg, inductionOn, iterate_add_apply, iterate_map_add, iterate_map_zero, iterate_zero_apply, zero_add
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
congr_arg (Quot.mk _) by
          simp only [iterate_map_zero, iterate_zero_apply, zero_add]
    add_zero := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
congr_arg (Quot.mk _) by
          simp only [iterate_map_zero, iterate_zero_apply, add_zero]
    sub_eq_add_neg := fun _ _ => rfl
    neg_add_cancel := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ => by
        simp only [quot_mk_eq_mk, neg_mk, mk_add_mk, iterate_map_neg, neg_add_cancel, mk_zero_right]
    add_comm := fun e f =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
Quot.inductionOn f fun ⟨n, y⟩ => congr_arg (Quot.mk _) by simp only [add_comm]
    nsmul := nsmulRec
    zsmul := zsmulRec }

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: : CommRing (PerfectClosure K p)
  body: { instAddCommGroup K p, AddMonoidWithOne.unary,
    (inferInstance : CommMonoid (PerfectClosure K p)) with
    zero_mul := fun a => by
      refine Quot.inductionOn a fun ⟨m, x⟩ => ?_
      rw [zero_def]; rw [quot_mk_eq_mk]; rw [mk_mul_mk]
      simp only [zero_add, iterate_zero, id_eq, iterate_map_zero, zero_mul, mk_zero_right]
    mul_zero := fun a => by
      refine Quot.inductionOn a fun ⟨m, x⟩ => ?_
      rw [zero_def]; rw [quot_mk_eq_mk]; rw [mk_mul_mk]
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

中文:
实例 instCommRing
  签名: : 交换环 (完美闭包 K p)
  定义体: { instAddCommGroup K p, AddMonoidWithOne.unary,
    (inferInstance : CommMonoid (PerfectClosure K p)) with
    zero_mul := fun a => by
      refine Quot.inductionOn a fun ⟨m, x⟩ => ?_
      rw [zero_def]; rw [quot_mk_eq_mk]; rw [mk_mul_mk]
      simp only [zero_add, iterate_zero, id_eq, iterate_map_zero, zero_mul, mk_zero_right]
    mul_zero := fun a => by
      refine Quot.inductionOn a fun ⟨m, x⟩ => ?_
      rw [zero_def]; rw [quot_mk_eq_mk]; rw [mk_mul_mk]
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

Depends on / 依赖: AddMonoidWithOne, AddMonoidWithOne.unary, CommMonoid, PerfectClosure, Quot.inductionOn, id_eq, inductionOn, instAddCommGroup, iterate_map_zero, iterate_zero, mk_mul_mk, mk_zero_right, mul_zero, quot_mk_eq_mk, zero_add, zero_def, zero_mul
-/
instance instCommRing : CommRing (PerfectClosure K p) :=
  { instAddCommGroup K p, AddMonoidWithOne.unary,
    (inferInstance : CommMonoid (PerfectClosure K p)) with
    zero_mul := fun a => by
      refine Quot.inductionOn a fun ⟨m, x⟩ => ?_
      rw [zero_def]; rw [quot_mk_eq_mk]; rw [mk_mul_mk]
      simp only [zero_add, iterate_zero, id_eq, iterate_map_zero, zero_mul, mk_zero_right]
    mul_zero := fun a => by
      refine Quot.inductionOn a fun ⟨m, x⟩ => ?_
      rw [zero_def]; rw [quot_mk_eq_mk]; rw [mk_mul_mk]
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

/--
theorem `mk_eq_iff` / 定理 `mk_eq_iff`

English:
theorem mk_eq_iff
  given: (x y : Nat × K)
  proof: by
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
      rw [← add_assoc]; rw [iterate_add_apply]; rw [ih1]
      rw [← iterate_add_apply]; rw [add_comm]; rw [iterate_add_apply]; rw [ih2]
      rw [← iterate_add_apply]
      simp only [add_comm, add_left_comm]
  intro H
  obtain ⟨m, x⟩ := x
  obtain ⟨n, y⟩ := y
  obtain ⟨z, H⟩ := H; dsimp only at H
  rw [R.sound K p (n + z) m x _ rfl]; rw [R.sound K p (m + z) n y _ rfl]; rw [H]
  rw [add_assoc]; rw [add_comm]; rw [add_comm z]

@[simp]

中文:
定理 mk_eq_iff
  条件: (x y : 自然数 × K)
  证明: by
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
      rw [← add_assoc]; rw [iterate_add_apply]; rw [ih1]
      rw [← iterate_add_apply]; rw [add_comm]; rw [iterate_add_apply]; rw [ih2]
      rw [← iterate_add_apply]
      simp only [add_comm, add_left_comm]
  intro H
  obtain ⟨m, x⟩ := x
  obtain ⟨n, y⟩ := y
  obtain ⟨z, H⟩ := H; dsimp only at H
  rw [R.sound K p (n + z) m x _ rfl]; rw [R.sound K p (m + z) n y _ rfl]; rw [H]
  rw [add_assoc]; rw [add_comm]; rw [add_comm z]

@[simp]

Depends on / 依赖: Quot.eqvGen_exact, add_assoc, add_comm, add_left_comm, eqvGen_exact, ih.symm, iterate_add_apply, replace
-/
theorem mk_eq_iff (x y : Nat × K) :
    mk K p x = mk K p y ↔ exists z, (frobenius K p)^[y.1 + z] x.2 = (frobenius K p)^[x.1 + z] y.2 := by
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
      rw [← add_assoc]; rw [iterate_add_apply]; rw [ih1]
      rw [← iterate_add_apply]; rw [add_comm]; rw [iterate_add_apply]; rw [ih2]
      rw [← iterate_add_apply]
      simp only [add_comm, add_left_comm]
  intro H
  obtain ⟨m, x⟩ := x
  obtain ⟨n, y⟩ := y
  obtain ⟨z, H⟩ := H; dsimp only at H
  rw [R.sound K p (n + z) m x _ rfl]; rw [R.sound K p (m + z) n y _ rfl]; rw [H]
  rw [add_assoc]; rw [add_comm]; rw [add_comm z]

@[simp]
/--
theorem `mk_pow` / 定理 `mk_pow`

English:
theorem mk_pow
  given: (x : Nat × K) (n : Nat)
  statement: mk K p x ^ n = mk K p (x.1, x.2 ^ n)
  proof: by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]; rw [one_def]; rw [mk_eq_iff]
    exact ⟨0, by simp_rw [← coe_iterateFrobenius, map_one]⟩
  | succ n ih =>
    rw [pow_succ]; rw [pow_succ]; rw [ih]; rw [mk_mul_mk]; rw [mk_eq_iff]
    exact ⟨0, by simp_rw [iterate_frobenius, add_zero, mul_pow, ← pow_mul,
      ← pow_add, mul_assoc, ← pow_add]⟩

中文:
定理 mk_pow
  条件: (x : 自然数 × K) (n : 自然数)
  结论: mk K p x ^ n = mk K p (x.1, x.2 ^ n)
  证明: by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]; rw [one_def]; rw [mk_eq_iff]
    exact ⟨0, by simp_rw [← coe_iterateFrobenius, map_one]⟩
  | succ n ih =>
    rw [pow_succ]; rw [pow_succ]; rw [ih]; rw [mk_mul_mk]; rw [mk_eq_iff]
    exact ⟨0, by simp_rw [iterate_frobenius, add_zero, mul_pow, ← pow_mul,
      ← pow_add, mul_assoc, ← pow_add]⟩

Depends on / 依赖: add_zero, coe_iterateFrobenius, iterate_frobenius, map_one, mk_eq_iff, mk_mul_mk, mul_assoc, mul_pow, one_def, pow_add, pow_mul, pow_succ, pow_zero, simp_rw
-/
theorem mk_pow (x : Nat × K) (n : Nat) : mk K p x ^ n = mk K p (x.1, x.2 ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]; rw [one_def]; rw [mk_eq_iff]
    exact ⟨0, by simp_rw [← coe_iterateFrobenius, map_one]⟩
  | succ n ih =>
    rw [pow_succ]; rw [pow_succ]; rw [ih]; rw [mk_mul_mk]; rw [mk_eq_iff]
    exact ⟨0, by simp_rw [iterate_frobenius, add_zero, mul_pow, ← pow_mul,
      ← pow_add, mul_assoc, ← pow_add]⟩

/--
theorem `natCast` / 定理 `natCast`

English:
theorem natCast
  given: (n x : Nat)
  statement: (x : PerfectClosure K p) = mk K p (n, x)
  proof: by
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

中文:
定理 natCast
  条件: (n x : 自然数)
  结论: (x : 完美闭包 K p) = mk K p (n, x)
  证明: by
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

Depends on / 依赖: Nat.cast_succ, Nat.succ, Quot.sound, R.intro, cast_succ, frobenius, map_natCast, one_def
-/
theorem natCast (n x : Nat) : (x : PerfectClosure K p) = mk K p (n, x) := by
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

/--
theorem `intCast` / 定理 `intCast`

English:
theorem intCast
  given: (x : Int)
  statement: (x : PerfectClosure K p) = mk K p (0, x)
  proof: by
  cases x <;> simp [natCast K p 0]

中文:
定理 intCast
  条件: (x : 整数)
  结论: (x : 完美闭包 K p) = mk K p (0, x)
  证明: by
  cases x <;> simp [natCast K p 0]

Depends on / 依赖: Countable, Finsupp, Finsupp.mem_span_range_iff_exists_finsupp.mp, Set.Countable.mono, Set.countable_coe_iff.mpr, Set.countable_range, SetLike, SetLike.mem_coe.mp, c.sum, countable_coe_iff, countable_range, mem_coe, mem_span_range_iff_exists_finsupp, natCast
-/
theorem intCast (x : Int) : (x : PerfectClosure K p) = mk K p (0, x) := by
  cases x <;> simp [natCast K p 0]

/--
theorem `natCast_eq_iff` / 定理 `natCast_eq_iff`

English:
theorem natCast_eq_iff
  given: (x y : Nat)
  statement: (x : PerfectClosure K p) = y ↔ (x : K) = y
  proof: by
  constructor <;> intro H
  · rw [natCast K p 0, natCast K p 0, mk_eq_iff] at H
    obtain ⟨z, H⟩ := H
    simpa only [zero_add, iterate_fixed (map_natCast _ _)] using H
  rw [natCast K p 0]; rw [natCast K p 0]; rw [H]

中文:
定理 natCast_eq_iff
  条件: (x y : 自然数)
  结论: (x : 完美闭包 K p) = y ↔ (x : K) = y
  证明: by
  constructor <;> intro H
  · rw [natCast K p 0, natCast K p 0, mk_eq_iff] at H
    obtain ⟨z, H⟩ := H
    simpa only [zero_add, iterate_fixed (map_natCast _ _)] using H
  rw [natCast K p 0]; rw [natCast K p 0]; rw [H]

Depends on / 依赖: iterate_fixed, map_natCast, mk_eq_iff, natCast, zero_add
-/
theorem natCast_eq_iff (x y : Nat) : (x : PerfectClosure K p) = y ↔ (x : K) = y := by
  constructor <;> intro H
  · rw [natCast K p 0, natCast K p 0, mk_eq_iff] at H
    obtain ⟨z, H⟩ := H
    simpa only [zero_add, iterate_fixed (map_natCast _ _)] using H
  rw [natCast K p 0]; rw [natCast K p 0]; rw [H]

/--
Instance `instCharP` / 实例 `instCharP`

English:
instance instCharP
  signature: : CharP (PerfectClosure K p) p
  body: by
  constructor; intro x; rw [← CharP.cast_eq_zero_iff K]
  rw [← Nat.cast_zero]; rw [natCast_eq_iff]; rw [Nat.cast_zero]

中文:
实例 instCharP
  签名: : 特征p (完美闭包 K p) p
  定义体: by
  constructor; intro x; rw [← CharP.cast_eq_zero_iff K]
  rw [← Nat.cast_zero]; rw [natCast_eq_iff]; rw [Nat.cast_zero]

Depends on / 依赖: CharP.cast_eq_zero_iff, Nat.cast_zero, cast_eq_zero_iff, cast_zero, natCast_eq_iff
-/
instance instCharP : CharP (PerfectClosure K p) p := by
  constructor; intro x; rw [← CharP.cast_eq_zero_iff K]
  rw [← Nat.cast_zero]; rw [natCast_eq_iff]; rw [Nat.cast_zero]

/--
theorem `frobenius_mk` / 定理 `frobenius_mk`

English:
theorem frobenius_mk
  given: (x : Nat × K)
  proof: by
  simp only [frobenius_def]
  exact mk_pow K p x p

中文:
定理 frobenius_mk
  条件: (x : 自然数 × K)
  证明: by
  simp only [frobenius_def]
  exact mk_pow K p x p

Depends on / 依赖: frobenius_def, mk_pow
-/
theorem frobenius_mk (x : Nat × K) :
    (frobenius (PerfectClosure K p) p : PerfectClosure K p -> PerfectClosure K p) (mk K p x) =
      mk _ _ (x.1, x.2 ^ p) := by
  simp only [frobenius_def]
  exact mk_pow K p x p

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : K ->+* PerfectClosure K p where
  body: mk _ _ (0, x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

中文:
定义 of
  签名: : K ->+* 完美闭包 K p where
  定义体: mk _ _ (0, x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
-/
def of : K ->+* PerfectClosure K p where
  toFun x := mk _ _ (0, x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/--
theorem `of_apply` / 定理 `of_apply`

English:
theorem of_apply
  given: (x : K)
  statement: of K p x = mk _ _ (0, x)
  proof: rfl

中文:
定理 of_apply
  条件: (x : K)
  结论: of K p x = mk _ _ (0, x)
  证明: rfl
-/
theorem of_apply (x : K) : of K p x = mk _ _ (0, x) :=
  rfl

/--
Instance `instReduced` / 实例 `instReduced`

English:
instance instReduced
  signature: : IsReduced (PerfectClosure K p) where
  body: induction_on x fun x ⟨n, h⟩ => by
    replace h : mk K p x ^ p ^ n = 0 := by
      rw [← Nat.sub_add_cancel ((n.lt_pow_self (Fact.out : p.Prime).one_lt).le)]; rw [pow_add]; rw [h]; rw [mul_zero]
    simp only [zero_def, mk_pow, mk_eq_iff, zero_add, ← coe_iterateFrobenius, map_zero] at h ⊢
    obtain ⟨m, h⟩ := h
    exact ⟨n + m, by simpa only [iterateFrobenius_def, pow_add, pow_mul] using h⟩

中文:
实例 instReduced
  签名: : 是既约 (完美闭包 K p) where
  定义体: induction_on x fun x ⟨n, h⟩ => by
    replace h : mk K p x ^ p ^ n = 0 := by
      rw [← Nat.sub_add_cancel ((n.lt_pow_self (Fact.out : p.Prime).one_lt).le)]; rw [pow_add]; rw [h]; rw [mul_zero]
    simp only [zero_def, mk_pow, mk_eq_iff, zero_add, ← coe_iterateFrobenius, map_zero] at h ⊢
    obtain ⟨m, h⟩ := h
    exact ⟨n + m, by simpa only [iterateFrobenius_def, pow_add, pow_mul] using h⟩

Depends on / 依赖: Fact.out, Nat.sub_add_cancel, coe_iterateFrobenius, induction_on, iterateFrobenius_def, lt_pow_self, map_zero, mk_eq_iff, mk_pow, mul_zero, n.lt_pow_self, one_lt, p.Prime, pow_add, pow_mul, replace, sub_add_cancel, zero_add, zero_def
-/
instance instReduced : IsReduced (PerfectClosure K p) where
  eq_zero x := induction_on x fun x ⟨n, h⟩ => by
    replace h : mk K p x ^ p ^ n = 0 := by
      rw [← Nat.sub_add_cancel ((n.lt_pow_self (Fact.out : p.Prime).one_lt).le)]; rw [pow_add]; rw [h]; rw [mul_zero]
    simp only [zero_def, mk_pow, mk_eq_iff, zero_add, ← coe_iterateFrobenius, map_zero] at h ⊢
    obtain ⟨m, h⟩ := h
    exact ⟨n + m, by simpa only [iterateFrobenius_def, pow_add, pow_mul] using h⟩

/--
Instance `instPerfectRing` / 实例 `instPerfectRing`

English:
instance instPerfectRing
  signature: : PerfectRing (PerfectClosure K p) p where
  body: by
    simp_rw [← frobenius_def]
    let f : PerfectClosure K p -> PerfectClosure K p := fun e =>
      liftOn e (fun x => mk K p (x.1 + 1, x.2)) fun x y H =>
      match x, y, H with
      | _, _, R.intro n x => Quot.sound (R.intro _ _)
    refine bijective_iff_has_inverse.mpr ⟨f, fun e => induction_on e fun ⟨n, x⟩ => ?_,
      fun e => induction_on e fun ⟨n, x⟩ => ?_⟩ <;>
      simp only [f, liftOn_mk, frobenius_mk, mk_succ_pow]

@[simp]

中文:
实例 instPerfectRing
  签名: : 完美环 (完美闭包 K p) p where
  定义体: by
    simp_rw [← frobenius_def]
    let f : PerfectClosure K p -> PerfectClosure K p := fun e =>
      liftOn e (fun x => mk K p (x.1 + 1, x.2)) fun x y H =>
      match x, y, H with
      | _, _, R.intro n x => Quot.sound (R.intro _ _)
    refine bijective_iff_has_inverse.mpr ⟨f, fun e => induction_on e fun ⟨n, x⟩ => ?_,
      fun e => induction_on e fun ⟨n, x⟩ => ?_⟩ <;>
      simp only [f, liftOn_mk, frobenius_mk, mk_succ_pow]

@[simp]

Depends on / 依赖: PerfectClosure, Quot.sound, R.intro, bijective_iff_has_inverse, bijective_iff_has_inverse.mpr, frobenius_def, frobenius_mk, induction_on, liftOn, liftOn_mk, mk_succ_pow, simp_rw
-/
instance instPerfectRing : PerfectRing (PerfectClosure K p) p where
  bijective_frobenius := by
    simp_rw [← frobenius_def]
    let f : PerfectClosure K p -> PerfectClosure K p := fun e =>
      liftOn e (fun x => mk K p (x.1 + 1, x.2)) fun x y H =>
      match x, y, H with
      | _, _, R.intro n x => Quot.sound (R.intro _ _)
    refine bijective_iff_has_inverse.mpr ⟨f, fun e => induction_on e fun ⟨n, x⟩ => ?_,
      fun e => induction_on e fun ⟨n, x⟩ => ?_⟩ <;>
      simp only [f, liftOn_mk, frobenius_mk, mk_succ_pow]

@[simp]
/--
theorem `iterate_frobenius_mk` / 定理 `iterate_frobenius_mk`

English:
theorem iterate_frobenius_mk
  given: (n : Nat) (x : K)
  proof: by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, ← ih, frobenius_mk, mk_succ_pow]

中文:
定理 iterate_frobenius_mk
  条件: (n : 自然数) (x : K)
  证明: by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, ← ih, frobenius_mk, mk_succ_pow]

Depends on / 依赖: frobenius_mk, iterate_succ_apply, mk_succ_pow
-/
theorem iterate_frobenius_mk (n : Nat) (x : K) :
    (frobenius (PerfectClosure K p) p)^[n] (mk K p ⟨n, x⟩) = of K p x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, ← ih, frobenius_mk, mk_succ_pow]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (L : Type v) [CommSemiring L] [CharP L p] [PerfectRing L p]
  body: { toFun := by
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
        rw [iterate_add_apply]; rw [this _ _]; rw [add_comm]; rw [iterate_add_apply]; rw [this _ _]
      map_add' := by
        rintro ⟨n, x⟩ ⟨m, y⟩
        simp only [quot_mk_eq_mk, liftOn_mk, f.map_iterate_frobenius, mk_add_mk, map_add,
          iterate_map_add]
        have := LeftInverse.iterate (frobeniusEquiv_symm_apply_frobenius L p)
        rw [iterate_add_apply]; rw [this _ _]; rw [add_comm n]; rw [iterate_add_apply]; rw [this _ _] }
  invFun f := f.comp (of K p)
  right_inv f := by
    ext ⟨n, x⟩
    simp only [quot_mk_eq_mk, RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      liftOn_mk]
    apply (injective_frobenius L p).iterate n
    rw [← f.map_iterate_frobenius]; rw [iterate_frobenius_mk]; rw [RightInverse.iterate (frobenius_apply_frobeniusEquiv_symm L p) n]

中文:
定义 lift
  签名: (L : 类型v) [交换半环 L] [特征p L p] [完美环 L p]
  定义体: { toFun := by
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
        rw [iterate_add_apply]; rw [this _ _]; rw [add_comm]; rw [iterate_add_apply]; rw [this _ _]
      map_add' := by
        rintro ⟨n, x⟩ ⟨m, y⟩
        simp only [quot_mk_eq_mk, liftOn_mk, f.map_iterate_frobenius, mk_add_mk, map_add,
          iterate_map_add]
        have := LeftInverse.iterate (frobeniusEquiv_symm_apply_frobenius L p)
        rw [iterate_add_apply]; rw [this _ _]; rw [add_comm n]; rw [iterate_add_apply]; rw [this _ _] }
  invFun f := f.comp (of K p)
  right_inv f := by
    ext ⟨n, x⟩
    simp only [quot_mk_eq_mk, RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      liftOn_mk]
    apply (injective_frobenius L p).iterate n
    rw [← f.map_iterate_frobenius]; rw [iterate_frobenius_mk]; rw [RightInverse.iterate (frobenius_apply_frobeniusEquiv_symm L p) n]

Depends on / 依赖: LeftInverse, LeftInverse.iterate, add_comm, f.map_frobenius, f.map_iterate_frobenius, f.map_one, f.map_zero, frobeniusEquiv, frobeniusEquiv_symm_apply_frobenius, iterate, iterate_add_apply, iterate_map_mul, liftOn, liftOn_mk, map_add, map_frobenius, map_iterate_frobenius, map_mul, map_one, map_zero
-/
noncomputable def lift (L : Type v) [CommSemiring L] [CharP L p] [PerfectRing L p] :
    (K ->+* L) ≃ (PerfectClosure K p ->+* L) where
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
        rw [iterate_add_apply]; rw [this _ _]; rw [add_comm]; rw [iterate_add_apply]; rw [this _ _]
      map_add' := by
        rintro ⟨n, x⟩ ⟨m, y⟩
        simp only [quot_mk_eq_mk, liftOn_mk, f.map_iterate_frobenius, mk_add_mk, map_add,
          iterate_map_add]
        have := LeftInverse.iterate (frobeniusEquiv_symm_apply_frobenius L p)
        rw [iterate_add_apply]; rw [this _ _]; rw [add_comm n]; rw [iterate_add_apply]; rw [this _ _] }
  invFun f := f.comp (of K p)
  right_inv f := by
    ext ⟨n, x⟩
    simp only [quot_mk_eq_mk, RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      liftOn_mk]
    apply (injective_frobenius L p).iterate n
    rw [← f.map_iterate_frobenius]; rw [iterate_frobenius_mk]; rw [RightInverse.iterate (frobenius_apply_frobeniusEquiv_symm L p) n]

end Ring

/--
theorem `eq_iff` / 定理 `eq_iff`

English:
theorem eq_iff
  given: [CommRing K] [IsReduced K] (p : Nat) [Fact p.Prime] [CharP K p] (x y : Nat × K)
  proof: (mk_eq_iff K p x y).trans
⟨fun ⟨z, H⟩ => (frobenius_inj K p).iterate z by simpa only [add_comm, iterate_add] using! H,
      fun H => ⟨0, H⟩⟩

中文:
定理 eq_iff
  条件: [交换环 K] [是既约 K] (p : 自然数) [Fact p.素] [特征p K p] (x y : 自然数 × K)
  证明: (mk_eq_iff K p x y).trans
⟨fun ⟨z, H⟩ => (frobenius_inj K p).iterate z by simpa only [add_comm, iterate_add] using! H,
      fun H => ⟨0, H⟩⟩

Depends on / 依赖: add_comm, frobenius_inj, iterate, iterate_add, mk_eq_iff
-/
theorem eq_iff [CommRing K] [IsReduced K] (p : Nat) [Fact p.Prime] [CharP K p] (x y : Nat × K) :
    mk K p x = mk K p y ↔ (frobenius K p)^[y.1] x.2 = (frobenius K p)^[x.1] y.2 :=
  (mk_eq_iff K p x y).trans
⟨fun ⟨z, H⟩ => (frobenius_inj K p).iterate z by simpa only [add_comm, iterate_add] using! H,
      fun H => ⟨0, H⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: K] [IsReduced K] (p
  body: ⟨0, 1, fun H => zero_ne_one ((eq_iff _ _ _ _).1 H)⟩

中文:
实例 [交换环
  签名: K] [是既约 K] (p
  定义体: ⟨0, 1, fun H => zero_ne_one ((eq_iff _ _ _ _).1 H)⟩

Depends on / 依赖: eq_iff, zero_ne_one
-/
instance [CommRing K] [IsReduced K] (p : Nat) [Fact p.Prime] [CharP K p] [Nontrivial K] :
    Nontrivial (PerfectClosure K p) where
  exists_pair_ne := ⟨0, 1, fun H => zero_ne_one ((eq_iff _ _ _ _).1 H)⟩

section Field

variable [Field K] (p : Nat) [Fact p.Prime] [CharP K p]

/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: : Inv (PerfectClosure K p)
  body: ⟨Quot.lift (fun x : Nat × K => Quot.mk (R K p) (x.1, x.2⁻¹)) fun x y (H : R K p x y) =>
      match x, y, H with
      | _, _, R.intro n x =>
Quot.sound by
          simp only [frobenius_def]
          rw [← inv_pow]
          apply R.intro⟩

@[simp]

中文:
实例 instInv
  签名: : 取逆 (完美闭包 K p)
  定义体: ⟨Quot.lift (fun x : Nat × K => Quot.mk (R K p) (x.1, x.2⁻¹)) fun x y (H : R K p x y) =>
      match x, y, H with
      | _, _, R.intro n x =>
Quot.sound by
          simp only [frobenius_def]
          rw [← inv_pow]
          apply R.intro⟩

@[simp]

Depends on / 依赖: Quot.lift, Quot.mk, Quot.sound, R.intro, frobenius_def, inv_pow
-/
instance instInv : Inv (PerfectClosure K p) :=
  ⟨Quot.lift (fun x : Nat × K => Quot.mk (R K p) (x.1, x.2⁻¹)) fun x y (H : R K p x y) =>
      match x, y, H with
      | _, _, R.intro n x =>
Quot.sound by
          simp only [frobenius_def]
          rw [← inv_pow]
          apply R.intro⟩

@[simp]
/--
theorem `mk_inv` / 定理 `mk_inv`

English:
theorem mk_inv
  given: (x : Nat × K)
  statement: (mk K p x)⁻¹ = mk K p (x.1, x.2⁻¹)
  proof: rfl

中文:
定理 mk_inv
  条件: (x : 自然数 × K)
  结论: (mk K p x)⁻¹ = mk K p (x.1, x.2⁻¹)
  证明: rfl
-/
theorem mk_inv (x : Nat × K) : (mk K p x)⁻¹ = mk K p (x.1, x.2⁻¹) :=
  rfl

/--
Instance `instDivisionRing` / 实例 `instDivisionRing`

English:
instance instDivisionRing
  signature: : DivisionRing (PerfectClosure K p) where
  body: induction_on e fun ⟨m, x⟩ H => by
    have := mt (eq_iff _ _ _ _).2 H
    rw [mk_inv]; rw [mk_mul_mk]
    refine (eq_iff K p _ _).2 ?_
    simp only [iterate_map_one, iterate_map_zero, iterate_zero_apply, ← iterate_map_mul] at this ⊢
    rw [mul_inv_cancel₀ this]; rw [iterate_map_one]
  inv_zero := congr_arg (Quot.mk (R K p)) (by rw [inv_zero])
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

中文:
实例 instDivisionRing
  签名: : 除环 (完美闭包 K p) where
  定义体: induction_on e fun ⟨m, x⟩ H => by
    have := mt (eq_iff _ _ _ _).2 H
    rw [mk_inv]; rw [mk_mul_mk]
    refine (eq_iff K p _ _).2 ?_
    simp only [iterate_map_one, iterate_map_zero, iterate_zero_apply, ← iterate_map_mul] at this ⊢
    rw [mul_inv_cancel₀ this]; rw [iterate_map_one]
  inv_zero := congr_arg (Quot.mk (R K p)) (by rw [inv_zero])
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

Depends on / 依赖: Quot.mk, congr_arg, eq_iff, induction_on, inv_zero, iterate_map_mul, iterate_map_one, iterate_map_zero, iterate_zero_apply, mk_inv, mk_mul_mk, nnqsmul, nnqsmul_def, qsmul_def
-/
instance instDivisionRing : DivisionRing (PerfectClosure K p) where
  mul_inv_cancel e := induction_on e fun ⟨m, x⟩ H => by
    have := mt (eq_iff _ _ _ _).2 H
    rw [mk_inv]; rw [mk_mul_mk]
    refine (eq_iff K p _ _).2 ?_
    simp only [iterate_map_one, iterate_map_zero, iterate_zero_apply, ← iterate_map_mul] at this ⊢
    rw [mul_inv_cancel₀ this]; rw [iterate_map_one]
  inv_zero := congr_arg (Quot.mk (R K p)) (by rw [inv_zero])
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/--
Instance `instField` / 实例 `instField`

English:
instance instField
  signature: : Field (PerfectClosure K p)
  body: { (inferInstance : DivisionRing (PerfectClosure K p)),
    (inferInstance : CommRing (PerfectClosure K p)) with }

中文:
实例 instField
  签名: : 域 (完美闭包 K p)
  定义体: { (inferInstance : DivisionRing (PerfectClosure K p)),
    (inferInstance : CommRing (PerfectClosure K p)) with }

Depends on / 依赖: CommRing, DivisionRing, PerfectClosure
-/
instance instField : Field (PerfectClosure K p) :=
  { (inferInstance : DivisionRing (PerfectClosure K p)),
    (inferInstance : CommRing (PerfectClosure K p)) with }

/--
Instance `instPerfectField` / 实例 `instPerfectField`

English:
instance instPerfectField
  signature: : PerfectField (PerfectClosure K p)
  body: PerfectRing.toPerfectField _ p

中文:
实例 instPerfectField
  签名: : 完美域 (完美闭包 K p)
  定义体: PerfectRing.toPerfectField _ p

Depends on / 依赖: PerfectRing, PerfectRing.toPerfectField, toPerfectField
-/
instance instPerfectField : PerfectField (PerfectClosure K p) := PerfectRing.toPerfectField _ p

end Field

end PerfectClosure
