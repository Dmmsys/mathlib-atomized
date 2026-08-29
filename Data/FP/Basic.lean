/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Semiquot
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic

/-!
# Implementation of floating-point numbers (experimental).
-/

@[expose] public section

-- TODO add docs and remove `@[nolint docBlame]`

@[nolint docBlame]
/--
Definition of `Int.shift2` / `Int.shift2` 的定义

English:
definition Int.shift2
  signature: (a b : Nat)

中文:
定义 整数.shift2
  签名: (a b : 自然数)
-/
def Int.shift2 (a b : Nat) : Int -> Nat × Nat
  | Int.ofNat e => (a <<< e, b)
  | Int.negSucc e => (a, b <<< e.succ)

namespace FP

@[nolint docBlame]
/--
Inductive type `RMode` / 归纳类型 `RMode`

English:
inductive RMode
  constructors (1):
    - NE: -- round to nearest even

中文:
归纳类型 RMode
  构造子 (1 个):
    - NE: -- round to nearest even
-/
inductive RMode
  | NE -- round to nearest even
  deriving Inhabited

@[nolint docBlame]
/--
Definition of `FloatCfg` / `FloatCfg` 的定义

English:
class FloatCfg
  parameters: where
  axioms and operations (3):
    - (prec(emax) : Nat)
    - precPos : 0 < prec
    - precMax : prec <= emax

中文:
类 FloatCfg
  参数: where
  公理与运算 (3 个):
    - (prec(emax) : 自然数)
    - precPos : 0 < prec
    - precMax : prec <= emax
-/
class FloatCfg where
  (prec emax : Nat)
  precPos : 0 < prec
  precMax : prec <= emax
attribute [nolint docBlame] FloatCfg.prec FloatCfg.emax FloatCfg.precPos FloatCfg.precMax

variable [C : FloatCfg]

@[nolint docBlame]
/--
Definition of `prec` / `prec` 的定义

English:
definition prec
  body: C.prec

@[nolint docBlame]

中文:
定义 prec
  定义体: C.prec

@[nolint docBlame]

Depends on / 依赖: C.prec
-/
def prec :=
  C.prec

@[nolint docBlame]
/--
Definition of `emax` / `emax` 的定义

English:
definition emax
  body: C.emax

@[nolint docBlame]

中文:
定义 emax
  定义体: C.emax

@[nolint docBlame]

Depends on / 依赖: C.emax
-/
def emax :=
  C.emax

@[nolint docBlame]
/--
Definition of `emin` / `emin` 的定义

English:
definition emin
  signature: : Int
  body: 1 - C.emax

@[nolint docBlame]

中文:
定义 emin
  签名: : 整数
  定义体: 1 - C.emax

@[nolint docBlame]

Depends on / 依赖: C.emax
-/
def emin : Int :=
  1 - C.emax

@[nolint docBlame]
/--
Definition of `ValidFinite` / `ValidFinite` 的定义

English:
definition ValidFinite
  signature: (e : Int) (m : Nat)
  body: emin <= e + prec - 1 ∧ e + prec - 1 <= emax ∧ e = max (e + m.size - prec) emin
deriving Decidable

@[nolint docBlame]

中文:
定义 ValidFinite
  签名: (e : 整数) (m : 自然数)
  定义体: emin <= e + prec - 1 ∧ e + prec - 1 <= emax ∧ e = max (e + m.size - prec) emin
deriving Decidable

@[nolint docBlame]

Depends on / 依赖: m.size
-/
def ValidFinite (e : Int) (m : Nat) : Prop :=
  emin <= e + prec - 1 ∧ e + prec - 1 <= emax ∧ e = max (e + m.size - prec) emin
deriving Decidable

@[nolint docBlame]
/--
Inductive type `Float` / 归纳类型 `Float`

English:
inductive Float
  constructors (3):
    - inf: Bool -> Float
    - nan: Float
    - finite: Bool -> forall e m, ValidFinite e m -> Float

中文:
归纳类型 Float
  构造子 (3 个):
    - inf: 布尔值 -> Float
    - nan: Float
    - finite: 布尔值 -> 对任意 e m, ValidFinite e m -> Float
-/
inductive Float
  | inf : Bool -> Float
  | nan : Float
  | finite : Bool -> forall e m, ValidFinite e m -> Float

@[nolint docBlame]
/--
Definition of `Float.isFinite` / `Float.isFinite` 的定义

English:
definition Float.isFinite
  signature: : Float -> Bool

中文:
定义 Float.isFinite
  签名: : Float -> 布尔值
-/
def Float.isFinite : Float -> Bool
  | Float.finite _ _ _ _ => true
  | _ => false

@[nolint docBlame]
/--
Definition of `toRat` / `toRat` 的定义

English:
definition toRat
  signature: : forall f : Float, f.isFinite -> Rat
  body: Int.shift2 m 1 e
    let r := mkRat n d
    if s then -r else r

中文:
定义 toRat
  签名: : 对任意 f : Float, f.isFinite -> 有理数
  定义体: Int.shift2 m 1 e
    let r := mkRat n d
    if s then -r else r

Depends on / 依赖: Int.shift2, shift2
-/
def toRat : forall f : Float, f.isFinite -> Rat
  | Float.finite s e m _, _ =>
    let (n, d) := Int.shift2 m 1 e
    let r := mkRat n d
    if s then -r else r

/--
theorem `Float.Zero.valid` / 定理 `Float.Zero.valid`

English:
theorem Float.Zero.valid
  statement: ValidFinite emin 0
  proof: ⟨by
    rw [add_sub_assoc]
    apply le_add_of_nonneg_right
    apply sub_nonneg_of_le
    apply Int.ofNat_le_ofNat_of_le
    exact C.precPos,
    suffices prec <= 2 * emax by
      rw [← Int.ofNat_le] at this
      rw [← sub_nonneg] at *
      simp only [emin, emax] at *
      lia
    le_trans C.pr

中文:
定理 Float.零.valid
  结论: ValidFinite emin 0
  证明: ⟨by
    rw [add_sub_assoc]
    apply le_add_of_nonneg_right
    apply sub_nonneg_of_le
    apply Int.ofNat_le_ofNat_of_le
    exact C.precPos,
    suffices prec <= 2 * emax by
      rw [← Int.ofNat_le] at this
      rw [← sub_nonneg] at *
      simp only [emin, emax] at *
      lia
    le_trans C.pr

Depends on / 依赖: C.precMax, C.precPos, Int.natCast_nonneg, Int.ofNat_le, Int.ofNat_le_ofNat_of_le, Nat.le_mul_of_pos_left, Nat.zero_lt_two, add_sub_assoc, le_add_of_nonneg_right, le_mul_of_pos_left, le_trans, natCast_nonneg, ofNat_le, ofNat_le_ofNat_of_le, precMax, precPos, sub_eq_add_neg, sub_nonneg, sub_nonneg_of_le, zero_lt_two
-/
theorem Float.Zero.valid : ValidFinite emin 0 :=
  ⟨by
    rw [add_sub_assoc]
    apply le_add_of_nonneg_right
    apply sub_nonneg_of_le
    apply Int.ofNat_le_ofNat_of_le
    exact C.precPos,
    suffices prec <= 2 * emax by
      rw [← Int.ofNat_le] at this
      rw [← sub_nonneg] at *
      simp only [emin, emax] at *
      lia
    le_trans C.precMax (Nat.le_mul_of_pos_left _ Nat.zero_lt_two),
    by (simp [sub_eq_add_neg, Int.natCast_nonneg])⟩

@[nolint docBlame]
/--
Definition of `Float.zero` / `Float.zero` 的定义

English:
definition Float.zero
  signature: (s : Bool)
  body: Float.finite s emin 0 Float.Zero.valid

中文:
定义 Float.zero
  签名: (s : 布尔值)
  定义体: Float.finite s emin 0 Float.Zero.valid

Depends on / 依赖: Float.Zero.valid, Float.finite, finite
-/
def Float.zero (s : Bool) : Float :=
  Float.finite s emin 0 Float.Zero.valid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Float
  body: ⟨Float.zero true⟩

@[nolint docBlame]

中文:
实例 :
  签名: 可居 Float
  定义体: ⟨Float.zero true⟩

@[nolint docBlame]

Depends on / 依赖: Float.zero
-/
instance : Inhabited Float :=
  ⟨Float.zero true⟩

@[nolint docBlame]
/--
Definition of `Float.sign'` / `Float.sign'` 的定义

English:
definition Float.sign'
  signature: : Float -> Semiquot Bool

中文:
定义 Float.sign'
  签名: : Float -> 半商 布尔值
-/
protected def Float.sign' : Float -> Semiquot Bool
  | Float.inf s => pure s
  | Float.nan => ⊤
  | Float.finite s _ _ _ => pure s

@[nolint docBlame]
/--
Definition of `Float.sign` / `Float.sign` 的定义

English:
definition Float.sign
  signature: : Float -> Bool

中文:
定义 Float.sign
  签名: : Float -> 布尔值
-/
protected def Float.sign : Float -> Bool
  | Float.inf s => s
  | Float.nan => false
  | Float.finite s _ _ _ => s

@[nolint docBlame]
/--
Definition of `Float.isZero` / `Float.isZero` 的定义

English:
definition Float.isZero
  signature: : Float -> Bool

中文:
定义 Float.isZero
  签名: : Float -> 布尔值
-/
protected def Float.isZero : Float -> Bool
  | Float.finite _ _ 0 _ => true
  | _ => false

@[nolint docBlame]
/--
Definition of `Float.neg` / `Float.neg` 的定义

English:
definition Float.neg
  signature: : Float -> Float

中文:
定义 Float.neg
  签名: : Float -> Float
-/
protected def Float.neg : Float -> Float
  | Float.inf s => Float.inf (not s)
  | Float.nan => Float.nan
  | Float.finite s e m f => Float.finite (not s) e m f

@[nolint docBlame]
/--
Definition of `divNatLtTwoPow` / `divNatLtTwoPow` 的定义

English:
definition divNatLtTwoPow
  signature: (n d : Nat)

中文:
定义 div自然数LtTwoPow
  签名: (n d : 自然数)
-/
def divNatLtTwoPow (n d : Nat) : Int -> Bool
  | Int.ofNat e => n < d <<< e
  | Int.negSucc e => n <<< e.succ < d


-- TODO(Mario): Prove these and drop 'unsafe'
@[nolint docBlame]
unsafe def ofPosRatDn (n : Nat+) (d : Nat+) : Float × Bool := by
  let e₁ : Int := n.1.size - d.1.size - prec
  obtain ⟨d₁, n₁⟩ := Int.shift2 d.1 n.1 (e₁ + prec)
  let e₂ := if n₁ < d₁ then e₁ - 1 else e₁
  let e₃ := max e₂ emin
  obtain ⟨d₂, n₂⟩ := Int.shift2 d.1 n.1 (e₃ + prec)
  let r := mkRat n₂ d₂
  let m := r.floor
  refine (Float.finite Bool.false e₃ (Int.toNat m) ?_, r.den = 1)
  exact lcProof

@[nolint docBlame]
unsafe def nextUpPos (e m) (v : ValidFinite e m) : Float :=
  let m' := m.succ
  if ss : m'.size = m.size then
    Float.finite false e m' (by unfold ValidFinite at *; rw [ss]; exact v)
  else if h : e = emax then Float.inf false else Float.finite false e.succ (Nat.div2 m') lcProof

@[nolint docBlame]
unsafe def nextDnPos (e m) (v : ValidFinite e m) : Float :=
  match h : m with
  | 0 => nextUpPos _ _ Float.Zero.valid
  | Nat.succ m' =>
    if ss : m'.size = m.size then
      Float.finite false e m' (by subst h; unfold ValidFinite at *; rw [ss]; exact v)
    else
      if h : e = emin then Float.finite false emin m' lcProof
      else Float.finite false e.pred (2 * m' + 1) lcProof

@[nolint docBlame]
unsafe def nextUp : Float -> Float
  | Float.finite Bool.false e m f => nextUpPos e m f
| Float.finite Bool.true e m f => Float.neg nextDnPos e m f
  | f => f

@[nolint docBlame]
unsafe def nextDn : Float -> Float
  | Float.finite Bool.false e m f => nextDnPos e m f
| Float.finite Bool.true e m f => Float.neg nextUpPos e m f
  | f => f

@[nolint docBlame]
unsafe def ofRatUp : Rat -> Float
  | ⟨0, _, _, _⟩ => Float.zero false
  | ⟨Nat.succ n, d, h, _⟩ =>
    let (f, exact) := ofPosRatDn n.succPNat ⟨d, Nat.pos_of_ne_zero h⟩
    if exact then f else nextUp f
  | ⟨Int.negSucc n, d, h, _⟩ => Float.neg (ofPosRatDn n.succPNat ⟨d, Nat.pos_of_ne_zero h⟩).1

@[nolint docBlame]
unsafe def ofRatDn (r : Rat) : Float :=
Float.neg ofRatUp (-r)

@[nolint docBlame]
unsafe def ofRat : RMode -> Rat -> Float
  | RMode.NE, r =>
    let low := ofRatDn r
    let high := ofRatUp r
    if hf : high.isFinite then
      if r = toRat _ hf then high
      else
        if lf : low.isFinite then
          if r - toRat _ lf > toRat _ hf - r then high
          else
            if r - toRat _ lf < toRat _ hf - r then low
            else
              match low, lf with
              | Float.finite _ _ m _, _ => if 2 ∣ m then low else high
        else Float.inf true
    else Float.inf false

namespace Float

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg Float
  body: ⟨Float.neg⟩

@[nolint docBlame]
unsafe def add (mode : RMode) : Float -> Float -> Float
  | nan, _ => nan
  | _, nan => nan
  | inf Bool.true, inf Bool.false => nan
  | inf Bool.false, inf Bool.true => nan
  | inf s₁, _ => inf s₁
  | _, inf s₂ => inf s₂
  | finite s₁ e₁ m₁ v₁, finite s₂ e₂ m₂ v₂ =>


中文:
实例 :
  签名: 取负 Float
  定义体: ⟨Float.neg⟩

@[nolint docBlame]
unsafe def add (mode : RMode) : Float -> Float -> Float
  | nan, _ => nan
  | _, nan => nan
  | inf Bool.true, inf Bool.false => nan
  | inf Bool.false, inf Bool.true => nan
  | inf s₁, _ => inf s₁
  | _, inf s₂ => inf s₂
  | finite s₁ e₁ m₁ v₁, finite s₂ e₂ m₂ v₂ =>


Depends on / 依赖: Float.neg
-/
instance : Neg Float :=
  ⟨Float.neg⟩

@[nolint docBlame]
unsafe def add (mode : RMode) : Float -> Float -> Float
  | nan, _ => nan
  | _, nan => nan
  | inf Bool.true, inf Bool.false => nan
  | inf Bool.false, inf Bool.true => nan
  | inf s₁, _ => inf s₁
  | _, inf s₂ => inf s₂
  | finite s₁ e₁ m₁ v₁, finite s₂ e₂ m₂ v₂ =>
    let f₁ := finite s₁ e₁ m₁ v₁
    let f₂ := finite s₂ e₂ m₂ v₂
    ofRat mode (toRat f₁ rfl + toRat f₂ rfl)

unsafe instance : Add Float :=
  ⟨Float.add RMode.NE⟩

@[nolint docBlame]
unsafe def sub (mode : RMode) (f1 f2 : Float) : Float :=
  add mode f1 (-f2)

unsafe instance : Sub Float :=
  ⟨Float.sub RMode.NE⟩

@[nolint docBlame]
unsafe def mul (mode : RMode) : Float -> Float -> Float
  | nan, _ => nan
  | _, nan => nan
  | inf s₁, f₂ => if f₂.isZero then nan else inf (xor s₁ f₂.sign)
  | f₁, inf s₂ => if f₁.isZero then nan else inf (xor f₁.sign s₂)
  | finite s₁ e₁ m₁ v₁, finite s₂ e₂ m₂ v₂ =>
    let f₁ := finite s₁ e₁ m₁ v₁
    let f₂ := finite s₂ e₂ m₂ v₂
    ofRat mode (toRat f₁ rfl * toRat f₂ rfl)

@[nolint docBlame]
unsafe def div (mode : RMode) : Float -> Float -> Float
  | nan, _ => nan
  | _, nan => nan
  | inf _, inf _ => nan
  | inf s₁, f₂ => inf (xor s₁ f₂.sign)
  | f₁, inf s₂ => zero (xor f₁.sign s₂)
  | finite s₁ e₁ m₁ v₁, finite s₂ e₂ m₂ v₂ =>
    let f₁ := finite s₁ e₁ m₁ v₁
    let f₂ := finite s₂ e₂ m₂ v₂
    if f₂.isZero then inf (xor s₁ s₂) else ofRat mode (toRat f₁ rfl / toRat f₂ rfl)

end Float

end FP
