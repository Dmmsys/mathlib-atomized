/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller, Eric Wieser
-/
module

public meta import Mathlib.Data.Int.GCD
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Tactic.NormNum

/-! # `norm_num` extensions for GCD-adjacent functions

This module defines some `norm_num` extensions for functions such as
`Nat.gcd`, `Nat.lcm`, `Int.gcd`, and `Int.lcm`.

Note that `Nat.coprime` is reducible and defined in terms of `Nat.gcd`, so the `Nat.gcd` extension
also indirectly provides a `Nat.coprime` extension.
-/

public meta section

namespace Mathlib.Meta

namespace NormNum

/-
**Mathlib.Meta.NormNum.int_gcd_helper'** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：int_gcd_helper' {d : Nat} {x y : Int} (a b : Int) (h₁ : (d : Int) ∣ x) (h₂
 : (d : Int) ∣ y) (h₃ : x * a + y * b = d) : Int.gcd x y = d
参数：a b : Int；h₁ : (d : Int) ∣ x；h₂ : (d : Int) ∣ y；h₃ : x * a + y * b = d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Dvd.dvd.mul_right`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α}, a ∣ 
b → ∀ (c : α), a ∣ b * c
· 使用定理 `Int.gcd_dvd_left`：∀ (a b : ℤ), ↑(a.gcd b) ∣ a
· 使用定理 `Int.gcd_dvd_right`：∀ (a b : ℤ), ↑(a.gcd b) ∣ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.dvd_coe_gcd`：∀ {a b c : ℤ}, c ∣ a → c ∣ b → c ∣ ↑(a.gcd b)
-/
theorem int_gcd_helper' {d : ℕ} {x y : ℤ} (a b : ℤ) (h₁ : (d : ℤ) ∣ x) (h₂ : (d : ℤ) ∣ y)
    (h₃ : x * a + y * b = d) : Int.gcd x y = d := by
  refine Nat.dvd_antisymm ?_ (Int.natCast_dvd_natCast.1 (Int.dvd_coe_gcd h₁ h₂))
  rw [← Int.natCast_dvd_natCast, ← h₃]
  apply dvd_add
  · exact (Int.gcd_dvd_left ..).mul_right _
  · exact (Int.gcd_dvd_right ..).mul_right _
/-
**Mathlib.Meta.NormNum.nat_gcd_helper_dvd_left** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Meta.NormNum`。
形式化陈述：nat_gcd_helper_dvd_left (x y : Nat) (h : y % x = 0) : Nat.gcd x y = x
参数：x y : Nat；h : y % x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.gcd_eq_left`：∀ {m n : ℕ}, m ∣ n → m.gcd n = m
· 使用定理 `Nat.dvd_of_mod_eq_zero`：∀ {m n : ℕ}, n % m = 0 → m ∣ n
-/
theorem nat_gcd_helper_dvd_left (x y : ℕ) (h : y % x = 0) : Nat.gcd x y = x :=
  Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero h)
/-
**Mathlib.Meta.NormNum.nat_gcd_helper_dvd_right** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Meta.NormNum`。
形式化陈述：nat_gcd_helper_dvd_right (x y : Nat) (h : x % y = 0) : Nat.gcd x y = y
参数：x y : Nat；h : x % y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.gcd_eq_right`：∀ {m n : ℕ}, n ∣ m → m.gcd n = n
· 使用定理 `Nat.dvd_of_mod_eq_zero`：∀ {m n : ℕ}, n % m = 0 → m ∣ n
-/
theorem nat_gcd_helper_dvd_right (x y : ℕ) (h : x % y = 0) : Nat.gcd x y = y :=
  Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h)
/-
**Mathlib.Meta.NormNum.nat_gcd_helper_2** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：nat_gcd_helper_2 (d x y a b : Nat) (hu : x % d = 0) (hv : y % d = 0) (h : 
x * a = y * b + d) : Nat.gcd x y = d
参数：d x y a b : Nat；hu : x % d = 0；hv : y % d = 0；h : x * a = y * b + d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.gcd_natCast_natCast`：∀ (a b : ℕ), (↑a).gcd ↑b = a.gcd b
· 使用定理 `Mathlib.Meta.NormNum.int_gcd_helper'`：int_gcd_helper' {d : Nat} {x y : I
nt} (a b : Int) (h₁ : (d : Int) ∣ x) (h₂ : (d : Int) ∣ y) (h₃ : x * a + y * b = 
d) : Int.gcd x y = d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Nat.dvd_of_mod_eq_zero`：∀ {m n : ℕ}, n % m = 0 → m ∣ n
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem nat_gcd_helper_2 (d x y a b : ℕ) (hu : x % d = 0) (hv : y % d = 0)
    (h : x * a = y * b + d) : Nat.gcd x y = d := by
  rw [← Int.gcd_natCast_natCast]
  apply int_gcd_helper' a (-b)
    (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hu))
    (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hv))
  rw [mul_neg, ← sub_eq_add_neg, sub_eq_iff_eq_add']
  exact mod_cast h
/-
**Mathlib.Meta.NormNum.nat_gcd_helper_1** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：nat_gcd_helper_1 (d x y a b : Nat) (hu : x % d = 0) (hv : y % d = 0) (h : 
y * b = x * a + d) : Nat.gcd x y = d
参数：d x y a b : Nat；hu : x % d = 0；hv : y % d = 0；h : y * b = x * a + d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.gcd_comm`：∀ (m n : ℕ), m.gcd n = n.gcd m
· 使用定理 `Mathlib.Meta.NormNum.nat_gcd_helper_2`：nat_gcd_helper_2 (d x y a b : Nat
) (hu : x % d = 0) (hv : y % d = 0) (h : x * a = y * b + d) : Nat.gcd x y = d
-/
theorem nat_gcd_helper_1 (d x y a b : ℕ) (hu : x % d = 0) (hv : y % d = 0)
    (h : y * b = x * a + d) : Nat.gcd x y = d :=
  (Nat.gcd_comm _ _).trans <| nat_gcd_helper_2 _ _ _ _ _ hv hu h
/-
**Mathlib.Meta.NormNum.nat_gcd_helper_1'** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta
.NormNum`。
形式化陈述：nat_gcd_helper_1' (x y a b : Nat) (h : y * b = x * a + 1) : Nat.gcd x y = 
1
参数：x y a b : Nat；h : y * b = x * a + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.NormNum.nat_gcd_helper_1`：nat_gcd_helper_1 (d x y a b : Nat
) (hu : x % d = 0) (hv : y % d = 0) (h : y * b = x * a + d) : Nat.gcd x y = d
· 使用定理 `Nat.mod_one`：∀ (x : ℕ), x % 1 = 0
-/
theorem nat_gcd_helper_1' (x y a b : ℕ) (h : y * b = x * a + 1) :
    Nat.gcd x y = 1 :=
  nat_gcd_helper_1 1 _ _ _ _ (Nat.mod_one _) (Nat.mod_one _) h
/-
**Mathlib.Meta.NormNum.nat_gcd_helper_2'** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta
.NormNum`。
形式化陈述：nat_gcd_helper_2' (x y a b : Nat) (h : x * a = y * b + 1) : Nat.gcd x y = 
1
参数：x y a b : Nat；h : x * a = y * b + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.NormNum.nat_gcd_helper_2`：nat_gcd_helper_2 (d x y a b : Nat
) (hu : x % d = 0) (hv : y % d = 0) (h : x * a = y * b + d) : Nat.gcd x y = d
· 使用定理 `Nat.mod_one`：∀ (x : ℕ), x % 1 = 0
-/
theorem nat_gcd_helper_2' (x y a b : ℕ) (h : x * a = y * b + 1) :
    Nat.gcd x y = 1 :=
  nat_gcd_helper_2 1 _ _ _ _ (Nat.mod_one _) (Nat.mod_one _) h
/-
**Mathlib.Meta.NormNum.nat_lcm_helper** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：nat_lcm_helper (x y d m : Nat) (hd : Nat.gcd x y = d) (d0 : Nat.beq d 0 = 
false) (dm : x * y = d * m) : Nat.lcm x y = m
参数：x y d m : Nat；hd : Nat.gcd x y = d；d0 : Nat.beq d 0 = false；dm : x * y = d * 
m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_right_injective₀`：mul_right_injective₀ (ha : a != 0) : Function.Inje
ctive (a * ·)
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Nat.ne_of_beq_eq_false`：∀ {n m : ℕ}, n.beq m = false → ¬n = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.gcd_mul_lcm`：∀ (m n : ℕ), m.gcd n * m.lcm n = m * n
-/
theorem nat_lcm_helper (x y d m : ℕ) (hd : Nat.gcd x y = d)
    (d0 : Nat.beq d 0 = false)
    (dm : x * y = d * m) : Nat.lcm x y = m :=
  mul_right_injective₀ (Nat.ne_of_beq_eq_false d0) <| by
    dsimp only
    rw [← dm, ← hd, Nat.gcd_mul_lcm]
/-
**Mathlib.Meta.NormNum.int_gcd_helper** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：int_gcd_helper {x y : Int} {x' y' d : Nat} (hx : x.natAbs = x') (hy : y.na
tAbs = y') (h : Nat.gcd x' y' = d) : Int.gcd x y = d
参数：hx : x.natAbs = x'；hy : y.natAbs = y'；h : Nat.gcd x' y' = d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.gcd_def`：gcd_def (i j : Int) : gcd i j = Nat.gcd i.natAbs j.natAbs
-/
theorem int_gcd_helper {x y : ℤ} {x' y' d : ℕ}
    (hx : x.natAbs = x') (hy : y.natAbs = y') (h : Nat.gcd x' y' = d) :
    Int.gcd x y = d := by subst_vars; rw [Int.gcd_def]
/-
**Mathlib.Meta.NormNum.int_lcm_helper** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：int_lcm_helper {x y : Int} {x' y' d : Nat} (hx : x.natAbs = x') (hy : y.na
tAbs = y') (h : Nat.lcm x' y' = d) : Int.lcm x y = d
参数：hx : x.natAbs = x'；hy : y.natAbs = y'；h : Nat.lcm x' y' = d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.lcm_def`：lcm_def (i j : Int) : lcm i j = Nat.lcm (natAbs i) (natAbs 
j)
-/
theorem int_lcm_helper {x y : ℤ} {x' y' d : ℕ}
    (hx : x.natAbs = x') (hy : y.natAbs = y') (h : Nat.lcm x' y' = d) :
    Int.lcm x y = d := by subst_vars; rw [Int.lcm_def]

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum
/-
**Mathlib.Meta.NormNum.isNat_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {x y nx ny z : ℕ},   Mathlib.Meta.NormNum.IsNat x nx →     Mathlib.Meta.
NormNum.IsNat y ny → nx.gcd ny = z → Mathlib.Meta.NormNum.IsNat (x.gcd y) z
参数：x.gcd y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNat_gcd : {x y nx ny z : ℕ} →
    IsNat x nx → IsNat y ny → Nat.gcd nx ny = z → IsNat (Nat.gcd x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩
/-
**Mathlib.Meta.NormNum.isNat_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {x y nx ny z : ℕ},   Mathlib.Meta.NormNum.IsNat x nx →     Mathlib.Meta.
NormNum.IsNat y ny → nx.lcm ny = z → Mathlib.Meta.NormNum.IsNat (x.lcm y) z
参数：x.lcm y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNat_lcm : {x y nx ny z : ℕ} →
    IsNat x nx → IsNat y ny → Nat.lcm nx ny = z → IsNat (Nat.lcm x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩
/-
**Mathlib.Meta.NormNum.isInt_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {x y nx ny : ℤ} {z : ℕ},   Mathlib.Meta.NormNum.IsInt x nx →     Mathlib
.Meta.NormNum.IsInt y ny → nx.gcd ny = z → Mathlib.Meta.NormNum.IsNat (x.gcd y) 
z
参数：x.gcd y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isInt_gcd : {x y nx ny : ℤ} → {z : ℕ} →
    IsInt x nx → IsInt y ny → Int.gcd nx ny = z → IsNat (Int.gcd x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩
/-
**Mathlib.Meta.NormNum.isInt_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：∀ {x y nx ny : ℤ} {z : ℕ},   Mathlib.Meta.NormNum.IsInt x nx →     Mathlib
.Meta.NormNum.IsInt y ny → nx.lcm ny = z → Mathlib.Meta.NormNum.IsNat (x.lcm y) 
z
参数：x.lcm y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isInt_lcm : {x y nx ny : ℤ} → {z : ℕ} →
    IsInt x nx → IsInt y ny → Int.lcm nx ny = z → IsNat (Int.lcm x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/-- Given natural number literals `ex` and `ey`, return their GCD as a natural number literal
and an equality proof. Panics if `ex` or `ey` aren't natural number literals. -/
/-
**Mathlib.Meta.NormNum.proveNatGCD** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：proveNatGCD (ex ey : Q(Nat)) : (ed : Q(Nat)) × Q(Nat.gcd $ex $ey = $ed)
参数：ex ey : Q(Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given natural number literals `ex` and `ey`, return their GCD as a natural numbe
r literal
and an equality proof. Panics if `ex` or `ey` aren't natural number literals.
-/
def proveNatGCD (ex ey : Q(ℕ)) : (ed : Q(ℕ)) × Q(Nat.gcd $ex $ey = $ed) :=
  match ex.natLit!, ey.natLit! with
  | 0, _ => have : $ex =Q nat_lit 0 := ⟨⟩; ⟨ey, q(Nat.gcd_zero_left $ey)⟩
  | _, 0 => have : $ey =Q nat_lit 0 := ⟨⟩; ⟨ex, q(Nat.gcd_zero_right $ex)⟩
  | 1, _ => have : $ex =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.gcd_one_left $ey)⟩
  | _, 1 => have : $ey =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.gcd_one_right $ex)⟩
  | x, y =>
    let (d, a, b) := Nat.xgcdAux x 1 0 y 0 1
    if d = x then
      have pq : Q(Nat.mod $ey $ex = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
      ⟨ex, q(nat_gcd_helper_dvd_left $ex $ey $pq)⟩
    else if d = y then
      have pq : Q(Nat.mod $ex $ey = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
      ⟨ey, q(nat_gcd_helper_dvd_right $ex $ey $pq)⟩
    else
      have ea' : Q(ℕ) := mkRawNatLit a.natAbs
      have eb' : Q(ℕ) := mkRawNatLit b.natAbs
      if d = 1 then
        if a ≥ 0 then
          have pt : Q($ex * $ea' = $ey * $eb' + 1) := (q(Eq.refl ($ex * $ea')) : Expr)
          ⟨q(nat_lit 1), q(nat_gcd_helper_2' $ex $ey $ea' $eb' $pt)⟩
        else
          have pt : Q($ey * $eb' = $ex * $ea' + 1) := (q(Eq.refl ($ey * $eb')) : Expr)
          ⟨q(nat_lit 1), q(nat_gcd_helper_1' $ex $ey $ea' $eb' $pt)⟩
      else
        have ed : Q(ℕ) := mkRawNatLit d
        have pu : Q(Nat.mod $ex $ed = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
        have pv : Q(Nat.mod $ey $ed = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
        if a ≥ 0 then
          have pt : Q($ex * $ea' = $ey * $eb' + $ed) := (q(Eq.refl ($ex * $ea')) : Expr)
          ⟨ed, q(nat_gcd_helper_2 $ed $ex $ey $ea' $eb' $pu $pv $pt)⟩
        else
          have pt : Q($ey * $eb' = $ex * $ea' + $ed) := (q(Eq.refl ($ey * $eb')) : Expr)
          ⟨ed, q(nat_gcd_helper_1 $ed $ex $ey $ea' $eb' $pu $pv $pt)⟩

/-- Evaluate the `Nat.gcd` function. -/
@[norm_num Nat.gcd _ _]
/-
**Mathlib.Meta.NormNum.evalNatGCD** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：evalNatGCD : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate the `Nat.gcd` function.
-/
def evalNatGCD : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℕ))) (y : Q(ℕ)) ← Meta.whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q Nat.gcd $x $y := ⟨⟩
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sℕ
  let ⟨ey, q⟩ ← deriveNat y sℕ
  let ⟨ed, pf⟩ := proveNatGCD ex ey
  return .isNat sℕ ed q(isNat_gcd $p $q $pf)

/-- Given natural number literals `ex` and `ey`, return their LCM as a natural number literal
and an equality proof. Panics if `ex` or `ey` aren't natural number literals. -/
/-
**Mathlib.Meta.NormNum.proveNatLCM** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：proveNatLCM (ex ey : Q(Nat)) : (ed : Q(Nat)) × Q(Nat.lcm $ex $ey = $ed)
参数：ex ey : Q(Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given natural number literals `ex` and `ey`, return their LCM as a natural numbe
r literal
and an equality proof. Panics if `ex` or `ey` aren't natural number literals.
-/
def proveNatLCM (ex ey : Q(ℕ)) : (ed : Q(ℕ)) × Q(Nat.lcm $ex $ey = $ed) :=
  match ex.natLit!, ey.natLit! with
  | 0, _ =>
    show (ed : Q(ℕ)) × Q(Nat.lcm 0 $ey = $ed) from ⟨q(nat_lit 0), q(Nat.lcm_zero_left $ey)⟩
  | _, 0 =>
    show (ed : Q(ℕ)) × Q(Nat.lcm $ex 0 = $ed) from ⟨q(nat_lit 0), q(Nat.lcm_zero_right $ex)⟩
  | 1, _ => show (ed : Q(ℕ)) × Q(Nat.lcm 1 $ey = $ed) from ⟨ey, q(Nat.lcm_one_left $ey)⟩
  | _, 1 => show (ed : Q(ℕ)) × Q(Nat.lcm $ex 1 = $ed) from ⟨ex, q(Nat.lcm_one_right $ex)⟩
  | x, y =>
    let ⟨ed, pd⟩ := proveNatGCD ex ey
    have p0 : Q(Nat.beq $ed 0 = false) := (q(Eq.refl false) : Expr)
    have em : Q(ℕ) := mkRawNatLit (x * y / ed.natLit!)
    have pm : Q($ex * $ey = $ed * $em) := (q(Eq.refl ($ex * $ey)) : Expr)
    ⟨em, q(nat_lcm_helper $ex $ey $ed $em $pd $p0 $pm)⟩

/-- Evaluates the `Nat.lcm` function. -/
@[norm_num Nat.lcm _ _]
/-
**Mathlib.Meta.NormNum.evalNatLCM** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：evalNatLCM : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `Nat.lcm` function.
-/
def evalNatLCM : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℕ))) (y : Q(ℕ)) ← Meta.whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q Nat.lcm $x $y := ⟨⟩
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sℕ
  let ⟨ey, q⟩ ← deriveNat y sℕ
  let ⟨ed, pf⟩ := proveNatLCM ex ey
  return .isNat sℕ ed q(isNat_lcm $p $q $pf)

/-- Given two integers, return their GCD and an equality proof.
Panics if `ex` or `ey` aren't integer literals. -/
/-
**Mathlib.Meta.NormNum.proveIntGCD** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：proveIntGCD (ex ey : Q(Int)) : (ed : Q(Nat)) × Q(Int.gcd $ex $ey = $ed)
参数：ex ey : Q(Int)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two integers, return their GCD and an equality proof.
Panics if `ex` or `ey` aren't integer literals.
-/
def proveIntGCD (ex ey : Q(ℤ)) : (ed : Q(ℕ)) × Q(Int.gcd $ex $ey = $ed) :=
  let ⟨ex', hx⟩ := rawIntLitNatAbs ex
  let ⟨ey', hy⟩ := rawIntLitNatAbs ey
  let ⟨ed, pf⟩ := proveNatGCD ex' ey'
  ⟨ed, q(int_gcd_helper $hx $hy $pf)⟩

/-- Evaluates the `Int.gcd` function. -/
@[norm_num Int.gcd _ _]
/-
**Mathlib.Meta.NormNum.evalIntGCD** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：evalIntGCD : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `Int.gcd` function.
-/
def evalIntGCD : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℤ))) (y : Q(ℤ)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q Int.gcd $x $y := ⟨⟩
  let ⟨ed, pf⟩ := proveIntGCD ex ey
  return .isNat _ ed q(isInt_gcd $p $q $pf)

/-- Given two integers, return their LCM and an equality proof.
Panics if `ex` or `ey` aren't integer literals. -/
/-
**Mathlib.Meta.NormNum.proveIntLCM** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormN
um`。
形式化陈述：proveIntLCM (ex ey : Q(Int)) : (ed : Q(Nat)) × Q(Int.lcm $ex $ey = $ed)
参数：ex ey : Q(Int)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two integers, return their LCM and an equality proof.
Panics if `ex` or `ey` aren't integer literals.
-/
def proveIntLCM (ex ey : Q(ℤ)) : (ed : Q(ℕ)) × Q(Int.lcm $ex $ey = $ed) :=
  let ⟨ex', hx⟩ := rawIntLitNatAbs ex
  let ⟨ey', hy⟩ := rawIntLitNatAbs ey
  let ⟨ed, pf⟩ := proveNatLCM ex' ey'
  ⟨ed, q(int_lcm_helper $hx $hy $pf)⟩

/-- Evaluates the `Int.lcm` function. -/
@[norm_num Int.lcm _ _]
/-
**Mathlib.Meta.NormNum.evalIntLCM** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：evalIntLCM : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `Int.lcm` function.
-/
def evalIntLCM : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℤ))) (y : Q(ℤ)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q Int.lcm $x $y := ⟨⟩
  let ⟨ed, pf⟩ := proveIntLCM ex ey
  return .isNat _ ed q(isInt_lcm $p $q $pf)
/-
**Mathlib.Meta.NormNum.isInt_ratNum** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：isInt_ratNum : forall {q : Rat} {n : Int} {n' : Nat} {d : Nat}, IsRat q n 
d -> n.natAbs = n' -> n'.gcd d = 1 -> IsInt q.num n | _, n, _, d, ⟨hi, rfl⟩, rfl
, h => by constructor have : 0 < d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.mul_num`：mul_num (q₁ q₂ : Rat) : (q₁ * q₂).num = q₁.num * q₂.num / N
at.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Rat.inv_natCast_den_of_pos`：inv_natCast_den_of_pos {a : Nat} (ha0 : 0 < 
a) : (a : Rat)⁻¹.den = a
· 使用定理 `Rat.inv_natCast_num_of_pos`：inv_natCast_num_of_pos {a : Nat} (ha0 : 0 < 
a) : (a : Rat)⁻¹.num = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.ediv_one`：∀ (a : ℤ), a / 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isInt_ratNum : ∀ {q : ℚ} {n : ℤ} {n' : ℕ} {d : ℕ},
    IsRat q n d → n.natAbs = n' → n'.gcd d = 1 → IsInt q.num n
  | _, n, _, d, ⟨hi, rfl⟩, rfl, h => by
    constructor
    have : 0 < d := Nat.pos_iff_ne_zero.mpr <| by simpa using hi.ne_zero
    simp_rw [Rat.mul_num, Rat.den_intCast, invOf_eq_inv,
      Rat.inv_natCast_den_of_pos this, Rat.inv_natCast_num_of_pos this,
      Rat.num_intCast, one_mul, mul_one, h, Nat.cast_one, Int.ediv_one, Int.cast_id]
/-
**Mathlib.Meta.NormNum.isNat_ratDen** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：isNat_ratDen : forall {q : Rat} {n : Int} {n' : Nat} {d : Nat}, IsRat q n 
d -> n.natAbs = n' -> n'.gcd d = 1 -> IsNat q.den d | _, n, _, d, ⟨hi, rfl⟩, rfl
, h => by constructor have : 0 < d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.mul_den`：mul_den (q₁ q₂ : Rat) : (q₁ * q₂).den = q₁.den * q₂.den / N
at.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Rat.inv_natCast_den_of_pos`：inv_natCast_den_of_pos {a : Nat} (ha0 : 0 < 
a) : (a : Rat)⁻¹.den = a
· 使用定理 `Rat.inv_natCast_num_of_pos`：inv_natCast_num_of_pos {a : Nat} (ha0 : 0 < 
a) : (a : Rat)⁻¹.num = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNat_ratDen : ∀ {q : ℚ} {n : ℤ} {n' : ℕ} {d : ℕ},
    IsRat q n d → n.natAbs = n' → n'.gcd d = 1 → IsNat q.den d
  | _, n, _, d, ⟨hi, rfl⟩, rfl, h => by
    constructor
    have : 0 < d := Nat.pos_iff_ne_zero.mpr <| by simpa using hi.ne_zero
    simp_rw [Rat.mul_den, Rat.den_intCast, invOf_eq_inv,
      Rat.inv_natCast_den_of_pos this, Rat.inv_natCast_num_of_pos this,
      Rat.num_intCast, one_mul, mul_one, Nat.cast_id, h, Nat.div_one]

/-- Evaluates the `Rat.num` function. -/
@[nolint unusedHavesSuffices, norm_num Rat.num _]
/-
**Mathlib.Meta.NormNum.evalRatNum** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：evalRatNum : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `Rat.num` function.
-/
def evalRatNum : NormNumExt where eval {u α} e := do
  let .proj _ _ (q : Q(ℚ)) ← Meta.whnfR e | failure
  have : u =QL 0 := ⟨⟩; have : $α =Q ℤ := ⟨⟩; have : $e =Q Rat.num $q := ⟨⟩
  let ⟨q', n, d, eq⟩ ← deriveRat q (_inst := q(inferInstance))
  let ⟨n', hn⟩ := rawIntLitNatAbs n
  -- deriveRat ensures these are coprime, so the gcd will be 1
  let ⟨gcd, pf⟩ := proveNatGCD q($n') q($d)
  have : $gcd =Q nat_lit 1 := ⟨⟩
  return .isInt _ n q'.num q(isInt_ratNum $eq $hn $pf)

/-- Evaluates the `Rat.den` function. -/
@[nolint unusedHavesSuffices, norm_num Rat.den _]
/-
**Mathlib.Meta.NormNum.evalRatDen** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：evalRatDen : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `Rat.den` function.
-/
def evalRatDen : NormNumExt where eval {u α} e := do
  let .proj _ _ (q : Q(ℚ)) ← Meta.whnfR e | failure
  have : u =QL 0 := ⟨⟩; have : $α =Q ℕ := ⟨⟩; have : $e =Q Rat.den $q := ⟨⟩
  let ⟨q', n, d, eq⟩ ← deriveRat q (_inst := q(inferInstance))
  let ⟨n', hn⟩ := rawIntLitNatAbs n
  -- deriveRat ensures these are coprime, so the gcd will be 1
  let ⟨gcd, pf⟩ := proveNatGCD q($n') q($d)
  have : $gcd =Q nat_lit 1 := ⟨⟩
  return .isNat _ d q(isNat_ratDen $eq $hn $pf)

end NormNum

end Mathlib.Meta

