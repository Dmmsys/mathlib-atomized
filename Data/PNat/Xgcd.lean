/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
module

public import Mathlib.Tactic.Ring
public import Mathlib.Data.PNat.Prime

/-!
# Euclidean algorithm for ℕ

This file sets up a version of the Euclidean algorithm that only works with natural numbers.
Given `0 < a, b`, it computes the unique `(w, x, y, z, d)` such that the following identities hold:
* `a = (w + x) d`
* `b = (y + z) d`
* `w * z = x * y + 1`

`d` is then the gcd of `a` and `b`, and `a' := a / d = w + x` and `b' := b / d = y + z` are coprime.

This story is closely related to the structure of SL₂(ℕ) (as a free monoid on two generators) and
the theory of continued fractions.

## Main declarations

* `XgcdType`: Helper type in defining the gcd. Encapsulates `(wp, x, y, zp, ap, bp)`. where `wp`
  `zp`, `ap`, `bp` are the variables getting changed through the algorithm.
* `IsSpecial`: States `wp * zp = x * y + 1`
* `IsReduced`: States `ap = a ∧ bp = b`

## Notes

See `Nat.Xgcd` for a very similar algorithm allowing values in `ℤ`.
-/

@[expose] public section


open Nat

namespace PNat

/-- A term of `XgcdType` is a system of six naturals.  They should
be thought of as representing the matrix
`[[w, x], [y, z]] = [[wp + 1, x], [y, zp + 1]]`
together with the vector `[a, b] = [ap + 1, bp + 1]`.
-/
/-
**PNat.XgcdType** 是 Mathlib 中的一个归纳类型，位于命名空间 `PNat`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A term of `XgcdType` is a system of six naturals.  They should
be thought of as representing the matrix
`[[w, x], [y, z]] = [[wp + 1, x], [y, zp + 1]]`
together with the vector `[a, b] = [ap + 1, bp + 1]`.
-/
structure XgcdType where
  /-- `wp` is a variable which changes through the algorithm. -/
  wp : ℕ
  /-- `x` satisfies `a / d = w + x` at the final step. -/
  x : ℕ
  /-- `y` satisfies `b / d = z + y` at the final step. -/
  y : ℕ
  /-- `zp` is a variable which changes through the algorithm. -/
  zp : ℕ
  /-- `ap` is a variable which changes through the algorithm. -/
  ap : ℕ
  /-- `bp` is a variable which changes through the algorithm. -/
  bp : ℕ
  deriving Inhabited

namespace XgcdType

variable (u : XgcdType)

/-
**PNat.XgcdType.** 是 Mathlib 中的一个实例，位于命名空间 `PNat.XgcdType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SizeOf XgcdType :=
  ⟨fun u => u.bp⟩

/-- The `Repr` instance converts terms to strings in a way that
reflects the matrix/vector interpretation as above. -/
/-
**PNat.XgcdType.** 是 Mathlib 中的一个实例，位于命名空间 `PNat.XgcdType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Repr` instance converts terms to strings in a way that
reflects the matrix/vector interpretation as above.
-/
instance : Repr XgcdType where
  reprPrec
  | g, _ => s!"[[[{repr (g.wp + 1)}, {repr g.x}], \
                 [{repr g.y}, {repr (g.zp + 1)}]], \
                [{repr (g.ap + 1)}, {repr (g.bp + 1)}]]"

/-- Another `mk` using ℕ and ℕ+ -/
/-
**PNat.XgcdType.mk'** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：mk' (w : Nat+) (x : Nat) (y : Nat) (z : Nat+) (a : Nat+) (b : Nat+) : Xgcd
Type
参数：w : Nat+；x : Nat；y : Nat；z : Nat+；a : Nat+；b : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Another `mk` using ℕ and ℕ+
-/
def mk' (w : ℕ+) (x : ℕ) (y : ℕ) (z : ℕ+) (a : ℕ+) (b : ℕ+) : XgcdType :=
  mk w.val.pred x y z.val.pred a.val.pred b.val.pred

/-- `w = wp + 1` -/
/-
**PNat.XgcdType.w** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：w : Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`w = wp + 1`
-/
def w : ℕ+ :=
  succPNat u.wp

/-- `z = zp + 1` -/
/-
**PNat.XgcdType.z** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：z : Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`z = zp + 1`
-/
def z : ℕ+ :=
  succPNat u.zp

/-- `a = ap + 1` -/
/-
**PNat.XgcdType.a** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：a : Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a = ap + 1`
-/
def a : ℕ+ :=
  succPNat u.ap

/-- `b = bp + 1` -/
/-
**PNat.XgcdType.b** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：b : Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`b = bp + 1`
-/
def b : ℕ+ :=
  succPNat u.bp

/-- `r = a % b`: remainder -/
/-
**PNat.XgcdType.r** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：r : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`r = a % b`: remainder
-/
def r : ℕ :=
  (u.ap + 1) % (u.bp + 1)

/-- `q = ap / bp`: quotient -/
/-
**PNat.XgcdType.q** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：q : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`q = ap / bp`: quotient
-/
def q : ℕ :=
  (u.ap + 1) / (u.bp + 1)

/-- `qp = q - 1` -/
/-
**PNat.XgcdType.qp** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：qp : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`qp = q - 1`
-/
def qp : ℕ :=
  u.q - 1

/-- The map `v` gives the product of the matrix
`[[w, x], [y, z]] = [[wp + 1, x], [y, zp + 1]]`
and the vector `[a, b] = [ap + 1, bp + 1]`.  The map
`vp` gives `[sp, tp]` such that `v = [sp + 1, tp + 1]`.
-/
/-
**PNat.XgcdType.vp** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：vp : Nat × Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `v` gives the product of the matrix
`[[w, x], [y, z]] = [[wp + 1, x], [y, zp + 1]]`
and the vector `[a, b] = [ap + 1, bp + 1]`.  The map
`vp` gives `[sp, tp]` such that `v = [sp + 1, tp + 1]`.
-/
def vp : ℕ × ℕ :=
  ⟨u.wp + u.x + u.ap + u.wp * u.ap + u.x * u.bp, u.y + u.zp + u.bp + u.y * u.ap + u.zp * u.bp⟩

/-- `v = [sp + 1, tp + 1]`, check `vp` -/
/-
**PNat.XgcdType.v** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：v : Nat × Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`v = [sp + 1, tp + 1]`, check `vp`
-/
def v : ℕ × ℕ :=
  ⟨u.w * u.a + u.x * u.b, u.y * u.a + u.z * u.b⟩

/-- `succ₂ [t.1, t.2] = [t.1.succ, t.2.succ]` -/
/-
**PNat.XgcdType.succ** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`succ₂ [t.1, t.2] = [t.1.succ, t.2.succ]`
-/
def succ₂ (t : ℕ × ℕ) : ℕ × ℕ :=
  ⟨t.1.succ, t.2.succ⟩
/-
**PNat.XgcdType.v_eq_succ_vp** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：v_eq_succ_vp : u.v = succ₂ u.vp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.RingNF.add_assoc_rev`：add_assoc_rev (a b c : R) : a + (b 
+ c) = a + b + c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.RingNF.nat_rawCast_1`：nat_rawCast_1 : (Nat.rawCast 1 : R)
 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.RingNF.mul_assoc_rev`：mul_assoc_rev (a b c : R) : a * (b 
* c) = a * b * c
（共 32 条，此处仅展示前 30 条）
-/
theorem v_eq_succ_vp : u.v = succ₂ u.vp := by
  ext <;> dsimp [v, vp, w, z, a, b, succ₂] <;> ring_nf

/-- `IsSpecial` holds if the matrix has determinant one. -/
/-
**PNat.XgcdType.IsSpecial** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：IsSpecial : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsSpecial` holds if the matrix has determinant one.
-/
def IsSpecial : Prop :=
  u.wp + u.zp + u.wp * u.zp = u.x * u.y

/-- `IsSpecial'` is an alternative of `IsSpecial`. -/
/-
**PNat.XgcdType.IsSpecial'** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：IsSpecial' : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsSpecial'` is an alternative of `IsSpecial`.
-/
def IsSpecial' : Prop :=
  u.w * u.z = succPNat (u.x * u.y)

set_option backward.isDefEq.respectTransparency false in
/-
**PNat.XgcdType.isSpecial_iff** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：isSpecial_iff : u.IsSpecial ↔ u.IsSpecial'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.mul_add`：∀ (n m k : ℕ), n * (m + k) = n * m + n * k
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.add_mul`：∀ (n m k : ℕ), (n + m) * k = n * k + m * k
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem isSpecial_iff : u.IsSpecial ↔ u.IsSpecial' := by
  dsimp [IsSpecial, IsSpecial']
  let ⟨wp, x, y, zp, ap, bp⟩ := u
  constructor <;> intro h <;> simp only [w, succPNat, succ_eq_add_one, z] at * <;>
    simp only [← coe_inj, mul_coe, mk_coe] at *
  · simp_all [← h]; ring
  · simp only [Nat.mul_add, Nat.add_mul, one_mul, mul_one, ← Nat.add_assoc,
      Nat.add_right_cancel_iff] at h
    rw [← h]; ring

/-- `IsReduced` holds if the two entries in the vector are the
same.  The reduction algorithm will produce a system with this
property, whose product vector is the same as for the original
system. -/
/-
**PNat.XgcdType.IsReduced** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：IsReduced : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsReduced` holds if the two entries in the vector are the
same.  The reduction algorithm will produce a system with this
property, whose product vector is the same as for the original
system.
-/
def IsReduced : Prop :=
  u.ap = u.bp

/-- `IsReduced'` is an alternative of `IsReduced`. -/
/-
**PNat.XgcdType.IsReduced'** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：IsReduced' : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsReduced'` is an alternative of `IsReduced`.
-/
def IsReduced' : Prop :=
  u.a = u.b
/-
**PNat.XgcdType.isReduced_iff** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：isReduced_iff : u.IsReduced ↔ u.IsReduced'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Nat.succPNat_inj`：succPNat_inj {n m : Nat} : succPNat n = succPNat m ↔ n
 = m
-/
theorem isReduced_iff : u.IsReduced ↔ u.IsReduced' :=
  succPNat_inj.symm

/-- `flip` flips the placement of variables during the algorithm. -/
/-
**PNat.XgcdType.flip** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：flip : XgcdType where wp
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`flip` flips the placement of variables during the algorithm.
-/
def flip : XgcdType where
  wp := u.zp
  x := u.y
  y := u.x
  zp := u.wp
  ap := u.bp
  bp := u.ap

@[simp]
/-
**PNat.XgcdType.flip_w** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：flip_w : (flip u).w = u.z
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_w : (flip u).w = u.z :=
  rfl

@[simp]
/-
**PNat.XgcdType.flip_x** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：flip_x : (flip u).x = u.y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_x : (flip u).x = u.y :=
  rfl

@[simp]
/-
**PNat.XgcdType.flip_y** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：flip_y : (flip u).y = u.x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_y : (flip u).y = u.x :=
  rfl

@[simp]
/-
**PNat.XgcdType.flip_z** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：flip_z : (flip u).z = u.w
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_z : (flip u).z = u.w :=
  rfl

@[simp]
/-
**PNat.XgcdType.flip_a** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：flip_a : (flip u).a = u.b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_a : (flip u).a = u.b :=
  rfl

@[simp]
/-
**PNat.XgcdType.flip_b** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：flip_b : (flip u).b = u.a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_b : (flip u).b = u.a :=
  rfl
/-
**PNat.XgcdType.flip_isReduced** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：flip_isReduced : (flip u).IsReduced ↔ u.IsReduced
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem flip_isReduced : (flip u).IsReduced ↔ u.IsReduced := by
  dsimp [IsReduced, flip]
  constructor <;> intro h <;> exact h.symm
/-
**PNat.XgcdType.flip_isSpecial** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：flip_isSpecial : (flip u).IsSpecial ↔ u.IsSpecial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem flip_isSpecial : (flip u).IsSpecial ↔ u.IsSpecial := by
  dsimp [IsSpecial, flip]
  rw [mul_comm u.x, mul_comm u.zp, add_comm u.zp]
/-
**PNat.XgcdType.flip_v** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：flip_v : (flip u).v = u.v.swap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
-/
theorem flip_v : (flip u).v = u.v.swap := by
  dsimp [v]
  ext
  · simp only
    ring
  · simp only
    ring

/-- Properties of division with remainder for a / b. -/
/-
**PNat.XgcdType.rq_eq** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：rq_eq : u.r + (u.bp + 1) * u.q = u.ap + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m

--- 原说明 ---
Properties of division with remainder for a / b.
-/
theorem rq_eq : u.r + (u.bp + 1) * u.q = u.ap + 1 :=
  Nat.mod_add_div (u.ap + 1) (u.bp + 1)
/-
**PNat.XgcdType.qp_eq** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：qp_eq (hr : u.r = 0) : u.q = u.qp + 1
参数：hr : u.r = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.XgcdType.rq_eq`：rq_eq : u.r + (u.bp + 1) * u.q = u.ap + 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
theorem qp_eq (hr : u.r = 0) : u.q = u.qp + 1 := by
  by_cases hq : u.q = 0
  · let h := u.rq_eq
    rw [hr, hq, mul_zero, add_zero] at h
    cases h
  · exact (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hq)).symm

/-- The following function provides the starting point for
our algorithm.  We will apply an iterative reduction process
to it, which will produce a system satisfying IsReduced.
The gcd can be read off from this final system.
-/
/-
**PNat.XgcdType.start** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：start (a b : Nat+) : XgcdType
参数：a b : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The following function provides the starting point for
our algorithm.  We will apply an iterative reduction process
to it, which will produce a system satisfying IsReduced.
The gcd can be read off from this final system.
-/
def start (a b : ℕ+) : XgcdType :=
  ⟨0, 0, 0, 0, a - 1, b - 1⟩
/-
**PNat.XgcdType.start_isSpecial** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：start_isSpecial (a b : Nat+) : (start a b).IsSpecial
参数：a b : Nat+。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem start_isSpecial (a b : ℕ+) : (start a b).IsSpecial := by
  dsimp [start, IsSpecial]
/-
**PNat.XgcdType.start_v** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：start_v (a b : Nat+) : (start a b).v = ⟨a, b⟩
参数：a b : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.pos`：pos (n : Nat+) : 0 < (n : Nat)
-/
theorem start_v (a b : ℕ+) : (start a b).v = ⟨a, b⟩ := by
  dsimp [start, v, XgcdType.a, XgcdType.b, w, z]
  have := a.pos
  have := b.pos
  #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
  we need to re-enable model-based theory combination in `lia` for this to go through. -/
  lia +mbtc

/-- `finish` happens when the reducing process ends. -/
/-
**PNat.XgcdType.finish** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：finish : XgcdType
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`finish` happens when the reducing process ends.
-/
def finish : XgcdType :=
  XgcdType.mk u.wp ((u.wp + 1) * u.qp + u.x) u.y (u.y * u.qp + u.zp) u.bp u.bp
/-
**PNat.XgcdType.finish_isReduced** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：finish_isReduced : u.finish.IsReduced
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finish_isReduced : u.finish.IsReduced := by
  dsimp [IsReduced]
  rfl
/-
**PNat.XgcdType.finish_isSpecial** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：finish_isSpecial (hs : u.IsSpecial) : u.finish.IsSpecial
参数：hs : u.IsSpecial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
-/
theorem finish_isSpecial (hs : u.IsSpecial) : u.finish.IsSpecial := by
  dsimp [IsSpecial, finish] at hs ⊢
  rw [add_mul _ _ u.y, add_comm _ (u.x * u.y), ← hs]
  ring
/-
**PNat.XgcdType.finish_v** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：finish_v (hr : u.r = 0) : u.finish.v = u.v
参数：hr : u.r = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.XgcdType.rq_eq`：rq_eq : u.r + (u.bp + 1) * u.q = u.ap + 1
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `PNat.XgcdType.qp_eq`：qp_eq (hr : u.r = 0) : u.q = u.qp + 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
-/
theorem finish_v (hr : u.r = 0) : u.finish.v = u.v := by
  let ha : u.r + u.b * u.q = u.a := u.rq_eq
  rw [hr, zero_add] at ha
  ext
  · change (u.wp + 1) * u.b + ((u.wp + 1) * u.qp + u.x) * u.b = u.w * u.a + u.x * u.b
    have : u.wp + 1 = u.w := rfl
    rw [this, ← ha, u.qp_eq hr]
    ring
  · change u.y * u.b + (u.y * u.qp + u.z) * u.b = u.y * u.a + u.z * u.b
    rw [← ha, u.qp_eq hr]
    ring

/-- This is the main reduction step, which is used when u.r ≠ 0, or
equivalently b does not divide a. -/
/-
**PNat.XgcdType.step** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：step : XgcdType
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the main reduction step, which is used when u.r ≠ 0, or
equivalently b does not divide a.
-/
def step : XgcdType :=
  XgcdType.mk (u.y * u.q + u.zp) u.y ((u.wp + 1) * u.q + u.x) u.wp u.bp (u.r - 1)

/-- We will apply the above step recursively.  The following result
is used to ensure that the process terminates. -/
/-
**PNat.XgcdType.step_wf** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：step_wf (hr : u.r != 0) : SizeOf.sizeOf u.step < SizeOf.sizeOf u
参数：hr : u.r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
We will apply the above step recursively.  The following result
is used to ensure that the process terminates.
-/
theorem step_wf (hr : u.r ≠ 0) : SizeOf.sizeOf u.step < SizeOf.sizeOf u := by
  change u.r - 1 < u.bp
  have h₀ : u.r - 1 + 1 = u.r := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hr)
  have h₁ : u.r < u.bp + 1 := Nat.mod_lt (u.ap + 1) u.bp.succ_pos
  rw [← h₀] at h₁
  exact lt_of_succ_lt_succ h₁
/-
**PNat.XgcdType.step_isSpecial** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：step_isSpecial (hs : u.IsSpecial) : u.step.IsSpecial
参数：hs : u.IsSpecial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
-/
theorem step_isSpecial (hs : u.IsSpecial) : u.step.IsSpecial := by
  dsimp [IsSpecial, step] at hs ⊢
  rw [mul_add, mul_comm u.y u.x, ← hs]
  ring

/-- The reduction step does not change the product vector. -/
/-
**PNat.XgcdType.step_v** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：step_v (hr : u.r != 0) : u.step.v = u.v.swap
参数：hr : u.r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.XgcdType.rq_eq`：rq_eq : u.r + (u.bp + 1) * u.q = u.ap + 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c

--- 原说明 ---
The reduction step does not change the product vector.
-/
theorem step_v (hr : u.r ≠ 0) : u.step.v = u.v.swap := by
  let ha : u.r + u.b * u.q = u.a := u.rq_eq
  let hr : u.r - 1 + 1 = u.r := (add_comm _ 1).trans (add_tsub_cancel_of_le (Nat.pos_of_ne_zero hr))
  ext
  · change ((u.y * u.q + u.z) * u.b + u.y * (u.r - 1 + 1) : ℕ) = u.y * u.a + u.z * u.b
    rw [← ha, hr]
    ring
  · change ((u.w * u.q + u.x) * u.b + u.w * (u.r - 1 + 1) : ℕ) = u.w * u.a + u.x * u.b
    rw [← ha, hr]
    ring

/-- We can now define the full reduction function, which applies
step as long as possible, and then applies finish. Note that the
"have" statement puts a fact in the local context, and the
equation compiler uses this fact to help construct the full
definition in terms of well-founded recursion.  The same fact
needs to be introduced in all the inductive proofs of properties
given below. -/
/-
**PNat.XgcdType.reduce** 是 Mathlib 中的一个定义，位于命名空间 `PNat.XgcdType`。
形式化陈述：reduce (u : XgcdType) : XgcdType
参数：u : XgcdType。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can now define the full reduction function, which applies
step as long as possible, and then applies finish. Note that the
"have" statement puts a fact in the local context, and the
equation compiler uses this fact to help construct the full
definition in terms of well-founded recursion.  The same fact
needs to be introduced in all the inductive proofs of properties
given below.
-/
def reduce (u : XgcdType) : XgcdType :=
  dite (u.r = 0) (fun _ => u.finish) fun _h =>
    flip (reduce u.step)
decreasing_by apply u.step_wf _h
/-
**PNat.XgcdType.reduce_a** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：reduce_a {u : XgcdType} (h : u.r = 0) : u.reduce = u.finish
参数：h : u.r = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.XgcdType.reduce.eq_1`：∀ (u : PNat.XgcdType), u.reduce = if x : u.r 
= 0 then u.finish else u.step.reduce.flip
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem reduce_a {u : XgcdType} (h : u.r = 0) : u.reduce = u.finish := by
  rw [reduce]
  exact if_pos h
/-
**PNat.XgcdType.reduce_b** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：reduce_b {u : XgcdType} (h : u.r != 0) : u.reduce = u.step.reduce.flip
参数：h : u.r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.XgcdType.reduce.eq_1`：∀ (u : PNat.XgcdType), u.reduce = if x : u.r 
= 0 then u.finish else u.step.reduce.flip
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem reduce_b {u : XgcdType} (h : u.r ≠ 0) : u.reduce = u.step.reduce.flip := by
  rw [reduce]
  exact if_neg h
/-
**PNat.XgcdType.reduce_isReduced** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：reduce_isReduced : forall u : XgcdType, u.reduce.IsReduced | u => dite (u.
r = 0) (fun h => by rw [reduce_a h] exact u.finish_isReduced) fun h => by have :
 SizeOf.sizeOf u.step < SizeOf.sizeOf u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.XgcdType.reduce_a`：reduce_a {u : XgcdType} (h : u.r = 0) : u.reduce
 = u.finish
· 使用定理 `PNat.XgcdType.finish_isReduced`：finish_isReduced : u.finish.IsReduced
· 使用定理 `PNat.XgcdType.step_wf`：step_wf (hr : u.r != 0) : SizeOf.sizeOf u.step < 
SizeOf.sizeOf u
· 使用定理 `PNat.XgcdType.reduce_b`：reduce_b {u : XgcdType} (h : u.r != 0) : u.reduc
e = u.step.reduce.flip
· 使用定理 `PNat.XgcdType.flip_isReduced`：flip_isReduced : (flip u).IsReduced ↔ u.Is
Reduced
-/
theorem reduce_isReduced : ∀ u : XgcdType, u.reduce.IsReduced
  | u =>
    dite (u.r = 0)
      (fun h => by
        rw [reduce_a h]
        exact u.finish_isReduced)
      fun h => by
      have : SizeOf.sizeOf u.step < SizeOf.sizeOf u := u.step_wf h
      rw [reduce_b h, flip_isReduced]
      apply reduce_isReduced
/-
**PNat.XgcdType.reduce_isReduced'** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：reduce_isReduced' (u : XgcdType) : u.reduce.IsReduced'
参数：u : XgcdType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PNat.XgcdType.isReduced_iff`：isReduced_iff : u.IsReduced ↔ u.IsReduced'
· 使用定理 `PNat.XgcdType.reduce_isReduced`：reduce_isReduced : forall u : XgcdType, 
u.reduce.IsReduced | u => dite (u.r = 0) (fun h => by rw [reduce_a h] exact u.fi
nish_isReduced) fun …
-/
theorem reduce_isReduced' (u : XgcdType) : u.reduce.IsReduced' :=
  (isReduced_iff _).mp u.reduce_isReduced
/-
**PNat.XgcdType.reduce_isSpecial** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：reduce_isSpecial : forall u : XgcdType, u.IsSpecial -> u.reduce.IsSpecial 
| u => dite (u.r = 0) (fun h hs => by rw [reduce_a h] exact u.finish_isSpecial h
s) fun h hs => by have : SizeOf.sizeOf u.step < SizeOf.sizeOf u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.XgcdType.reduce_a`：reduce_a {u : XgcdType} (h : u.r = 0) : u.reduce
 = u.finish
· 使用定理 `PNat.XgcdType.finish_isSpecial`：finish_isSpecial (hs : u.IsSpecial) : u.
finish.IsSpecial
· 使用定理 `PNat.XgcdType.step_wf`：step_wf (hr : u.r != 0) : SizeOf.sizeOf u.step < 
SizeOf.sizeOf u
· 使用定理 `PNat.XgcdType.reduce_b`：reduce_b {u : XgcdType} (h : u.r != 0) : u.reduc
e = u.step.reduce.flip
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PNat.XgcdType.flip_isSpecial`：flip_isSpecial : (flip u).IsSpecial ↔ u.Is
Special
· 使用定理 `PNat.XgcdType.step_isSpecial`：step_isSpecial (hs : u.IsSpecial) : u.step
.IsSpecial
-/
theorem reduce_isSpecial : ∀ u : XgcdType, u.IsSpecial → u.reduce.IsSpecial
  | u =>
    dite (u.r = 0)
      (fun h hs => by
        rw [reduce_a h]
        exact u.finish_isSpecial hs)
      fun h hs => by
      have : SizeOf.sizeOf u.step < SizeOf.sizeOf u := u.step_wf h
      rw [reduce_b h]
      exact (flip_isSpecial _).mpr (reduce_isSpecial _ (u.step_isSpecial hs))
/-
**PNat.XgcdType.reduce_isSpecial'** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：reduce_isSpecial' (u : XgcdType) (hs : u.IsSpecial) : u.reduce.IsSpecial'
参数：u : XgcdType；hs : u.IsSpecial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PNat.XgcdType.isSpecial_iff`：isSpecial_iff : u.IsSpecial ↔ u.IsSpecial'
· 使用定理 `PNat.XgcdType.reduce_isSpecial`：reduce_isSpecial : forall u : XgcdType, 
u.IsSpecial -> u.reduce.IsSpecial | u => dite (u.r = 0) (fun h hs => by rw [redu
ce_a h] exact u.fini…
-/
theorem reduce_isSpecial' (u : XgcdType) (hs : u.IsSpecial) : u.reduce.IsSpecial' :=
  (isSpecial_iff _).mp (u.reduce_isSpecial hs)
/-
**PNat.XgcdType.reduce_v** 是 Mathlib 中的一个定理，位于命名空间 `PNat.XgcdType`。
形式化陈述：reduce_v : forall u : XgcdType, u.reduce.v = u.v | u => dite (u.r = 0) (fu
n h => by rw [reduce_a h, finish_v u h]) fun h => by have : SizeOf.sizeOf u.step
 < SizeOf.sizeOf u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.XgcdType.reduce_a`：reduce_a {u : XgcdType} (h : u.r = 0) : u.reduce
 = u.finish
· 使用定理 `PNat.XgcdType.finish_v`：finish_v (hr : u.r = 0) : u.finish.v = u.v
· 使用定理 `PNat.XgcdType.step_wf`：step_wf (hr : u.r != 0) : SizeOf.sizeOf u.step < 
SizeOf.sizeOf u
· 使用定理 `PNat.XgcdType.reduce_b`：reduce_b {u : XgcdType} (h : u.r != 0) : u.reduc
e = u.step.reduce.flip
· 使用定理 `PNat.XgcdType.flip_v`：flip_v : (flip u).v = u.v.swap
· 使用定理 `PNat.XgcdType.step_v`：step_v (hr : u.r != 0) : u.step.v = u.v.swap
· 使用定理 `Prod.swap_swap`：∀ {α : Type u_1} {β : Type u_2} (x : α × β), x.swap.swap
 = x
-/
theorem reduce_v : ∀ u : XgcdType, u.reduce.v = u.v
  | u =>
    dite (u.r = 0) (fun h => by rw [reduce_a h, finish_v u h]) fun h => by
      have : SizeOf.sizeOf u.step < SizeOf.sizeOf u := u.step_wf h
      rw [reduce_b h, flip_v, reduce_v (step u), step_v u h, Prod.swap_swap]

end XgcdType

section gcd

variable (a b : ℕ+)

/-- Extended Euclidean algorithm -/
/-
**PNat.xgcd** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：xgcd : XgcdType
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extended Euclidean algorithm
-/
def xgcd : XgcdType :=
  (XgcdType.start a b).reduce

/-- `gcdD a b = gcd a b` -/
/-
**PNat.gcdD** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：gcdD : Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`gcdD a b = gcd a b`
-/
def gcdD : ℕ+ :=
  (xgcd a b).a

/-- Final value of `w` -/
/-
**PNat.gcdW** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：gcdW : Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Final value of `w`
-/
def gcdW : ℕ+ :=
  (xgcd a b).w

/-- Final value of `x` -/
/-
**PNat.gcdX** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：gcdX : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Final value of `x`
-/
def gcdX : ℕ :=
  (xgcd a b).x

/-- Final value of `y` -/
/-
**PNat.gcdY** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：gcdY : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Final value of `y`
-/
def gcdY : ℕ :=
  (xgcd a b).y

/-- Final value of `z` -/
/-
**PNat.gcdZ** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：gcdZ : Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Final value of `z`
-/
def gcdZ : ℕ+ :=
  (xgcd a b).z

/-- Final value of `a / d` -/
/-
**PNat.gcdA'** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：gcdA' : Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Final value of `a / d`
-/
def gcdA' : ℕ+ :=
  succPNat ((xgcd a b).wp + (xgcd a b).x)

/-- Final value of `b / d` -/
/-
**PNat.gcdB'** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：gcdB' : Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Final value of `b / d`
-/
def gcdB' : ℕ+ :=
  succPNat ((xgcd a b).y + (xgcd a b).zp)
/-
**PNat.gcdA'_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：∀ (a b : ℕ+), ↑(a.gcdA' b) = ↑(a.gcdW b) + a.gcdX b
参数：a b : ℕ+；a.gcdA' b；a.gcdW b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
-/
theorem gcdA'_coe : (gcdA' a b : ℕ) = gcdW a b + gcdX a b := by
  dsimp [gcdA', gcdX, gcdW, XgcdType.w]
  rw [add_right_comm]
/-
**PNat.gcdB'_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：∀ (a b : ℕ+), ↑(a.gcdB' b) = a.gcdY b + ↑(a.gcdZ b)
参数：a b : ℕ+；a.gcdB' b；a.gcdZ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem gcdB'_coe : (gcdB' a b : ℕ) = gcdY a b + gcdZ a b := by
  dsimp [gcdB', gcdY, gcdZ, XgcdType.z]
  rw [add_assoc]
/-
**PNat.gcd_props** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_props : let d
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.XgcdType.reduce_isReduced'`：reduce_isReduced' (u : XgcdType) : u.re
duce.IsReduced'
· 使用定理 `PNat.gcdA'_coe`：∀ (a b : ℕ+), ↑(a.gcdA' b) = ↑(a.gcdW b) + a.gcdX b
· 使用定理 `PNat.gcdB'_coe`：∀ (a b : ℕ+), ↑(a.gcdB' b) = a.gcdY b + ↑(a.gcdZ b)
· 使用定理 `PNat.XgcdType.reduce_isSpecial'`：reduce_isSpecial' (u : XgcdType) (hs : 
u.IsSpecial) : u.reduce.IsSpecial'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.mul_coe`：mul_coe (m n : Nat+) : ((m * n : Nat+) : Nat) = m * n
· 使用定理 `Nat.succPNat_coe`：succPNat_coe (n : Nat) : (succPNat n : Nat) = succ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PNat.XgcdType.reduce_v`：reduce_v : forall u : XgcdType, u.reduce.v = u.v
 | u => dite (u.r = 0) (fun h => by rw [reduce_a h, finish_v u h]) fun h => by h
ave : SizeOf…
· 使用定理 `PNat.XgcdType.start_v`：start_v (a b : Nat+) : (start a b).v = ⟨a, b⟩
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `PNat.eq`：eq {m n : Nat+} : (m : Nat) = n -> m = n
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 38 条，此处仅展示前 30 条）
-/
theorem gcd_props :
    let d := gcdD a b
    let w := gcdW a b
    let x := gcdX a b
    let y := gcdY a b
    let z := gcdZ a b
    let a' := gcdA' a b
    let b' := gcdB' a b
    w * z = succPNat (x * y) ∧
      a = a' * d ∧
        b = b' * d ∧
          z * a' = succPNat (x * b') ∧
            w * b' = succPNat (y * a') ∧ (z * a : ℕ) = x * b + d ∧ (w * b : ℕ) = y * a + d := by
  intro d w x y z a' b'
  let u := XgcdType.start a b
  let ur := u.reduce
  have hb : d = ur.b := u.reduce_isReduced'
  have ha' : (a' : ℕ) = w + x := gcdA'_coe a b
  have hb' : (b' : ℕ) = y + z := gcdB'_coe a b
  have hdet : w * z = succPNat (x * y) := u.reduce_isSpecial' rfl
  constructor
  · exact hdet
  have hdet' : (w * z : ℕ) = x * y + 1 := by rw [← mul_coe, hdet, succPNat_coe]
  let hv : Prod.mk (w * d + x * ur.b : ℕ) (y * d + z * ur.b : ℕ) = ⟨a, b⟩ :=
    u.reduce_v.trans (XgcdType.start_v a b)
  rw [← hb, ← add_mul, ← add_mul, ← ha', ← hb'] at hv
  have ha'' : (a : ℕ) = a' * d := (congr_arg Prod.fst hv).symm
  have hb'' : (b : ℕ) = b' * d := (congr_arg Prod.snd hv).symm
  constructor
  · exact eq ha''
  constructor
  · exact eq hb''
  have hza' : (z * a' : ℕ) = x * b' + 1 := by
    rw [ha', hb', mul_add, mul_add, mul_comm (z : ℕ), hdet']
    ring
  have hwb' : (w * b' : ℕ) = y * a' + 1 := by
    rw [ha', hb', mul_add, mul_add, hdet']
    ring
  constructor
  · apply eq
    rw [succPNat_coe, Nat.succ_eq_add_one, mul_coe, hza']
  constructor
  · apply eq
    rw [succPNat_coe, Nat.succ_eq_add_one, mul_coe, hwb']
  grind
/-
**PNat.gcd_eq** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_eq : gcdD a b = gcd a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.gcd_props`：gcd_props : let d
· 使用定理 `PNat.dvd_antisymm`：dvd_antisymm {m n : Nat+} : m ∣ n -> n ∣ m -> m = n
· 使用定理 `PNat.dvd_gcd`：dvd_gcd {m n k : Nat+} (hm : k ∣ m) (hn : k ∣ n) : k ∣ gcd
 m n
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.dvd_iff`：dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.dvd_add_iff_right`：∀ {k m n : ℕ}, k ∣ m → (k ∣ n ↔ k ∣ m + n)
-/
theorem gcd_eq : gcdD a b = gcd a b := by
  rcases gcd_props a b with ⟨_, h₁, h₂, _, _, h₅, _⟩
  apply dvd_antisymm
  · apply dvd_gcd
    · exact Dvd.intro (gcdA' a b) (h₁.trans (mul_comm _ _)).symm
    · exact Dvd.intro (gcdB' a b) (h₂.trans (mul_comm _ _)).symm
  · have h₇ : (gcd a b : ℕ) ∣ gcdZ a b * a := (Nat.gcd_dvd_left a b).trans (dvd_mul_left _ _)
    have h₈ : (gcd a b : ℕ) ∣ gcdX a b * b := (Nat.gcd_dvd_right a b).trans (dvd_mul_left _ _)
    rw [h₅] at h₇
    rw [dvd_iff]
    exact (Nat.dvd_add_iff_right h₈).mpr h₇
/-
**PNat.gcd_det_eq** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_det_eq : gcdW a b * gcdZ a b = succPNat (gcdX a b * gcdY a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PNat.gcd_props`：gcd_props : let d
-/
theorem gcd_det_eq : gcdW a b * gcdZ a b = succPNat (gcdX a b * gcdY a b) :=
  (gcd_props a b).1
/-
**PNat.gcd_a_eq** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_a_eq : a = gcdA' a b * gcd a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PNat.gcd_props`：gcd_props : let d
· 使用定理 `PNat.gcd_eq`：gcd_eq : gcdD a b = gcd a b
-/
theorem gcd_a_eq : a = gcdA' a b * gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.1
/-
**PNat.gcd_b_eq** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_b_eq : b = gcdB' a b * gcd a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PNat.gcd_props`：gcd_props : let d
· 使用定理 `PNat.gcd_eq`：gcd_eq : gcdD a b = gcd a b
-/
theorem gcd_b_eq : b = gcdB' a b * gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.1
/-
**PNat.gcd_rel_left'** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_rel_left' : gcdZ a b * gcdA' a b = succPNat (gcdX a b * gcdB' a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PNat.gcd_props`：gcd_props : let d
-/
theorem gcd_rel_left' : gcdZ a b * gcdA' a b = succPNat (gcdX a b * gcdB' a b) :=
  (gcd_props a b).2.2.2.1
/-
**PNat.gcd_rel_right'** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_rel_right' : gcdW a b * gcdB' a b = succPNat (gcdY a b * gcdA' a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PNat.gcd_props`：gcd_props : let d
-/
theorem gcd_rel_right' : gcdW a b * gcdB' a b = succPNat (gcdY a b * gcdA' a b) :=
  (gcd_props a b).2.2.2.2.1
/-
**PNat.gcd_rel_left** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_rel_left : (gcdZ a b * a : Nat) = gcdX a b * b + gcd a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PNat.gcd_props`：gcd_props : let d
· 使用定理 `PNat.gcd_eq`：gcd_eq : gcdD a b = gcd a b
-/
theorem gcd_rel_left : (gcdZ a b * a : ℕ) = gcdX a b * b + gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.2.2.2.1
/-
**PNat.gcd_rel_right** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_rel_right : (gcdW a b * b : Nat) = gcdY a b * a + gcd a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PNat.gcd_props`：gcd_props : let d
· 使用定理 `PNat.gcd_eq`：gcd_eq : gcdD a b = gcd a b
-/
theorem gcd_rel_right : (gcdW a b * b : ℕ) = gcdY a b * a + gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.2.2.2.2

end gcd

end PNat

