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
/-
**Int.shift2** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：ℕ → ℕ → ℤ → ℕ × ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Int.shift2 (a b : ℕ) : ℤ → ℕ × ℕ
  | Int.ofNat e => (a <<< e, b)
  | Int.negSucc e => (a, b <<< e.succ)

namespace FP

@[nolint docBlame]
/-
**FP.RMode** 是 Mathlib 中的一个归纳类型，位于命名空间 `FP`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
inductive RMode
  | NE -- round to nearest even
  deriving Inhabited

@[nolint docBlame]
/-
**FP.FloatCfg** 是 Mathlib 中的一个归纳类型，位于命名空间 `FP`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class FloatCfg where
  (prec emax : ℕ)
  precPos : 0 < prec
  precMax : prec ≤ emax
attribute [nolint docBlame] FloatCfg.prec FloatCfg.emax FloatCfg.precPos FloatCfg.precMax

variable [C : FloatCfg]

@[nolint docBlame]
/-
**FP.prec** 是 Mathlib 中的一个定义，位于命名空间 `FP`。
形式化陈述：prec
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prec :=
  C.prec

@[nolint docBlame]
/-
**FP.emax** 是 Mathlib 中的一个定义，位于命名空间 `FP`。
形式化陈述：emax
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def emax :=
  C.emax

@[nolint docBlame]
/-
**FP.emin** 是 Mathlib 中的一个定义，位于命名空间 `FP`。
形式化陈述：emin : Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def emin : ℤ :=
  1 - C.emax

@[nolint docBlame]
/-
**FP.ValidFinite** 是 Mathlib 中的一个定义，位于命名空间 `FP`。
形式化陈述：ValidFinite (e : Int) (m : Nat) : Prop
参数：e : Int；m : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ValidFinite (e : ℤ) (m : ℕ) : Prop :=
  emin ≤ e + prec - 1 ∧ e + prec - 1 ≤ emax ∧ e = max (e + m.size - prec) emin
deriving Decidable

@[nolint docBlame]
/-
**FP.Float** 是 Mathlib 中的一个归纳类型，位于命名空间 `FP`。
形式化陈述：[C : FP.FloatCfg] → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
inductive Float
  | inf : Bool → Float
  | nan : Float
  | finite : Bool → ∀ e m, ValidFinite e m → Float

@[nolint docBlame]
/-
**FP.Float.isFinite** 是 Mathlib 中的一个定义，位于命名空间 `FP.Float`。
形式化陈述：[C : FP.FloatCfg] → FP.Float → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Float.isFinite : Float → Bool
  | Float.finite _ _ _ _ => true
  | _ => false

@[nolint docBlame]
/-
**FP.toRat** 是 Mathlib 中的一个定义，位于命名空间 `FP`。
形式化陈述：toRat : forall f : Float, f.isFinite -> Rat | Float.finite s e m _, _ => l
et (n, d)
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toRat : ∀ f : Float, f.isFinite → ℚ
  | Float.finite s e m _, _ =>
    let (n, d) := Int.shift2 m 1 e
    let r := mkRat n d
    if s then -r else r
/-
**FP.Float.Zero.valid** 是 Mathlib 中的一个定理，位于命名空间 `FP.Float.Zero`。
形式化陈述：∀ [C : FP.FloatCfg], FP.ValidFinite FP.emin 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.ofNat_le_ofNat_of_le`：∀ {m n : ℕ}, m ≤ n → ↑m ≤ ↑n
· 使用定理 `FP.FloatCfg.precPos`：∀ [self : FP.FloatCfg], 0 < FP.FloatCfg.prec
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `FP.FloatCfg.precMax`：∀ [self : FP.FloatCfg], FP.FloatCfg.prec ≤ FP.Float
Cfg.emax
· 使用定理 `Nat.le_mul_of_pos_left`：∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
· 使用定理 `Nat.zero_lt_two`：0 < 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `Int.ofNat_le`：∀ {m n : ℕ}, ↑m ≤ ↑n ↔ m ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Float.Zero.valid : ValidFinite emin 0 :=
  ⟨by
    rw [add_sub_assoc]
    apply le_add_of_nonneg_right
    apply sub_nonneg_of_le
    apply Int.ofNat_le_ofNat_of_le
    exact C.precPos,
    suffices prec ≤ 2 * emax by
      rw [← Int.ofNat_le] at this
      rw [← sub_nonneg] at *
      simp only [emin, emax] at *
      lia
    le_trans C.precMax (Nat.le_mul_of_pos_left _ Nat.zero_lt_two),
    by (simp [sub_eq_add_neg, Int.natCast_nonneg])⟩

@[nolint docBlame]
/-
**FP.Float.zero** 是 Mathlib 中的一个定义，位于命名空间 `FP.Float`。
形式化陈述：[C : FP.FloatCfg] → Bool → FP.Float
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FP.Float.Zero.valid`：∀ [C : FP.FloatCfg], FP.ValidFinite FP.emin 0
-/
def Float.zero (s : Bool) : Float :=
  Float.finite s emin 0 Float.Zero.valid
/-
**FP.** 是 Mathlib 中的一个实例，位于命名空间 `FP`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Float :=
  ⟨Float.zero true⟩

@[nolint docBlame]
/-
**FP.Float.sign'** 是 Mathlib 中的一个定义，位于命名空间 `FP.Float`。
形式化陈述：[C : FP.FloatCfg] → FP.Float → Semiquot Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def Float.sign' : Float → Semiquot Bool
  | Float.inf s => pure s
  | Float.nan => ⊤
  | Float.finite s _ _ _ => pure s

@[nolint docBlame]
/-
**FP.Float.sign** 是 Mathlib 中的一个定义，位于命名空间 `FP.Float`。
形式化陈述：[C : FP.FloatCfg] → FP.Float → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def Float.sign : Float → Bool
  | Float.inf s => s
  | Float.nan => false
  | Float.finite s _ _ _ => s

@[nolint docBlame]
/-
**FP.Float.isZero** 是 Mathlib 中的一个定义，位于命名空间 `FP.Float`。
形式化陈述：[C : FP.FloatCfg] → FP.Float → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def Float.isZero : Float → Bool
  | Float.finite _ _ 0 _ => true
  | _ => false

@[nolint docBlame]
/-
**FP.Float.neg** 是 Mathlib 中的一个定义，位于命名空间 `FP.Float`。
形式化陈述：[C : FP.FloatCfg] → FP.Float → FP.Float
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def Float.neg : Float → Float
  | Float.inf s => Float.inf (not s)
  | Float.nan => Float.nan
  | Float.finite s e m f => Float.finite (not s) e m f

@[nolint docBlame]
/-
**FP.divNatLtTwoPow** 是 Mathlib 中的一个定义，位于命名空间 `FP`。
形式化陈述：ℕ → ℕ → ℤ → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def divNatLtTwoPow (n d : ℕ) : ℤ → Bool
  | Int.ofNat e => n < d <<< e
  | Int.negSucc e => n <<< e.succ < d


-- TODO(Mario): Prove these and drop 'unsafe'
@[nolint docBlame]
/-
**FP.ofPosRatDn** 是 Mathlib 中的一个unsafe-def，位于命名空间 `FP`。
形式化陈述：[C : FP.FloatCfg] → ℕ+ → ℕ+ → FP.Float × Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe def ofPosRatDn (n : ℕ+) (d : ℕ+) : Float × Bool := by
  let e₁ : ℤ := n.1.size - d.1.size - prec
  obtain ⟨d₁, n₁⟩ := Int.shift2 d.1 n.1 (e₁ + prec)
  let e₂ := if n₁ < d₁ then e₁ - 1 else e₁
  let e₃ := max e₂ emin
  obtain ⟨d₂, n₂⟩ := Int.shift2 d.1 n.1 (e₃ + prec)
  let r := mkRat n₂ d₂
  let m := r.floor
  refine (Float.finite Bool.false e₃ (Int.toNat m) ?_, r.den = 1)
  exact lcProof

@[nolint docBlame]
/-
**FP.nextUpPos** 是 Mathlib 中的一个unsafe-def，位于命名空间 `FP`。
形式化陈述：[C : FP.FloatCfg] → (e : ℤ) → (m : ℕ) → FP.ValidFinite e m → FP.Float
参数：e : ℤ；m : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe def nextUpPos (e m) (v : ValidFinite e m) : Float :=
  let m' := m.succ
  if ss : m'.size = m.size then
    Float.finite false e m' (by unfold ValidFinite at *; rw [ss]; exact v)
  else if h : e = emax then Float.inf false else Float.finite false e.succ (Nat.div2 m') lcProof

@[nolint docBlame]
/-
**FP.nextDnPos** 是 Mathlib 中的一个unsafe-def，位于命名空间 `FP`。
形式化陈述：[C : FP.FloatCfg] → (e : ℤ) → (m : ℕ) → FP.ValidFinite e m → FP.Float
参数：e : ℤ；m : ℕ。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FP.Float.Zero.valid`：∀ [C : FP.FloatCfg], FP.ValidFinite FP.emin 0
-/
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
/-
**FP.nextUp** 是 Mathlib 中的一个unsafe-def，位于命名空间 `FP`。
形式化陈述：[C : FP.FloatCfg] → FP.Float → FP.Float
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe def nextUp : Float → Float
  | Float.finite Bool.false e m f => nextUpPos e m f
  | Float.finite Bool.true e m f => Float.neg <| nextDnPos e m f
  | f => f

@[nolint docBlame]
/-
**FP.nextDn** 是 Mathlib 中的一个unsafe-def，位于命名空间 `FP`。
形式化陈述：[C : FP.FloatCfg] → FP.Float → FP.Float
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe def nextDn : Float → Float
  | Float.finite Bool.false e m f => nextDnPos e m f
  | Float.finite Bool.true e m f => Float.neg <| nextUpPos e m f
  | f => f

@[nolint docBlame]
/-
**FP.ofRatUp** 是 Mathlib 中的一个unsafe-def，位于命名空间 `FP`。
形式化陈述：[C : FP.FloatCfg] → ℚ → FP.Float
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
unsafe def ofRatUp : ℚ → Float
  | ⟨0, _, _, _⟩ => Float.zero false
  | ⟨Nat.succ n, d, h, _⟩ =>
    let (f, exact) := ofPosRatDn n.succPNat ⟨d, Nat.pos_of_ne_zero h⟩
    if exact then f else nextUp f
  | ⟨Int.negSucc n, d, h, _⟩ => Float.neg (ofPosRatDn n.succPNat ⟨d, Nat.pos_of_ne_zero h⟩).1

@[nolint docBlame]
/-
**FP.ofRatDn** 是 Mathlib 中的一个unsafe-def，位于命名空间 `FP`。
形式化陈述：[C : FP.FloatCfg] → ℚ → FP.Float
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe def ofRatDn (r : ℚ) : Float :=
  Float.neg <| ofRatUp (-r)

@[nolint docBlame]
/-
**FP.ofRat** 是 Mathlib 中的一个unsafe-def，位于命名空间 `FP`。
形式化陈述：[C : FP.FloatCfg] → FP.RMode → ℚ → FP.Float
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe def ofRat : RMode → ℚ → Float
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

/-
**FP.Float.** 是 Mathlib 中的一个实例，位于命名空间 `FP.Float`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg Float :=
  ⟨Float.neg⟩

@[nolint docBlame]
/-
**FP.Float.add** 是 Mathlib 中的一个unsafe-def，位于命名空间 `FP.Float`。
形式化陈述：[C : FP.FloatCfg] → FP.RMode → FP.Float → FP.Float → FP.Float
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe def add (mode : RMode) : Float → Float → Float
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
/-
**FP.Float.** 是 Mathlib 中的一个实例，位于命名空间 `FP.Float`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe instance : Add Float :=
  ⟨Float.add RMode.NE⟩

@[nolint docBlame]
/-
**FP.Float.sub** 是 Mathlib 中的一个unsafe-def，位于命名空间 `FP.Float`。
形式化陈述：[C : FP.FloatCfg] → FP.RMode → FP.Float → FP.Float → FP.Float
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe def sub (mode : RMode) (f1 f2 : Float) : Float :=
  add mode f1 (-f2)
/-
**FP.Float.** 是 Mathlib 中的一个实例，位于命名空间 `FP.Float`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe instance : Sub Float :=
  ⟨Float.sub RMode.NE⟩

@[nolint docBlame]
/-
**FP.Float.mul** 是 Mathlib 中的一个unsafe-def，位于命名空间 `FP.Float`。
形式化陈述：[C : FP.FloatCfg] → FP.RMode → FP.Float → FP.Float → FP.Float
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe def mul (mode : RMode) : Float → Float → Float
  | nan, _ => nan
  | _, nan => nan
  | inf s₁, f₂ => if f₂.isZero then nan else inf (xor s₁ f₂.sign)
  | f₁, inf s₂ => if f₁.isZero then nan else inf (xor f₁.sign s₂)
  | finite s₁ e₁ m₁ v₁, finite s₂ e₂ m₂ v₂ =>
    let f₁ := finite s₁ e₁ m₁ v₁
    let f₂ := finite s₂ e₂ m₂ v₂
    ofRat mode (toRat f₁ rfl * toRat f₂ rfl)

@[nolint docBlame]
/-
**FP.Float.div** 是 Mathlib 中的一个unsafe-def，位于命名空间 `FP.Float`。
形式化陈述：[C : FP.FloatCfg] → FP.RMode → FP.Float → FP.Float → FP.Float
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe def div (mode : RMode) : Float → Float → Float
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

