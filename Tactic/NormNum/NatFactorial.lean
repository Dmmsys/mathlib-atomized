/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer
-/
module

public meta import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.NormNum

/-! # `norm_num` extensions for factorials

Extensions for `norm_num` that compute `Nat.factorial`, `Nat.ascFactorial` and `Nat.descFactorial`.

This is done by reducing each of these to `ascFactorial`, which is computed using a divide and
conquer strategy that improves performance and avoids exceeding the recursion depth.

-/

public meta section

namespace Mathlib.Meta.NormNum

open Nat Qq Lean Elab.Tactic Meta

/-
**Mathlib.Meta.NormNum.asc_factorial_aux** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta
.NormNum`。
形式化陈述：asc_factorial_aux (n l m a b : Nat) (h₁ : n.ascFactorial l = a) (h₂ : (n +
 l).ascFactorial m = b) : n.ascFactorial (l + m) = a * b
参数：n l m a b : Nat；h₁ : n.ascFactorial l = a；h₂ : (n + l).ascFactorial m = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ascFactorial_mul_ascFactorial`：ascFactorial_mul_ascFactorial (n l k 
: Nat) : n.ascFactorial l * (n + l).ascFactorial k = n.ascFactorial (l + k)
-/
lemma asc_factorial_aux (n l m a b : ℕ) (h₁ : n.ascFactorial l = a)
    (h₂ : (n + l).ascFactorial m = b) : n.ascFactorial (l + m) = a * b := by
  rw [← h₁, ← h₂]
  symm
  apply ascFactorial_mul_ascFactorial

/-- Calculate `n.ascFactorial l` and return this value along with a proof of the result. -/
/-
**Mathlib.Meta.NormNum.proveAscFactorial** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.M
eta.NormNum`。
形式化陈述：ℕ → ℕ → (en el : Q(ℕ)) → ℕ × (eresult : Q(ℕ)) × Q(«$en».ascFactorial «$el»
 = «$eresult»)
参数：en el : Q(ℕ)；eresult : Q(ℕ)；«$en».ascFactorial «$el» = «$eresult»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Calculate `n.ascFactorial l` and return this value along with a proof of the res
ult.
-/
partial def proveAscFactorial (n l : ℕ) (en el : Q(ℕ)) :
    ℕ × (eresult : Q(ℕ)) × Q(($en).ascFactorial $el = $eresult) :=
  if l ≤ 50 then
    have res : ℕ := n.ascFactorial l
    have eres : Q(ℕ) := mkRawNatLit (n.ascFactorial l)
    have : ($en).ascFactorial $el =Q $eres := ⟨⟩
    ⟨res, eres, q(Eq.refl $eres)⟩
  else
    have m : ℕ := l / 2
    have em : Q(ℕ) := mkRawNatLit m
    have : $em =Q $el / 2 := ⟨⟩

    have r : ℕ := l - m
    have er : Q(ℕ) := mkRawNatLit r
    have : $er =Q $el - $em := ⟨⟩
    have : $el =Q ($em + $er) := ⟨⟩

    have nm : ℕ := n + m
    have enm : Q(ℕ) := mkRawNatLit nm
    have : $enm =Q $en + $em := ⟨⟩

    let ⟨a, ea, a_prf⟩ := proveAscFactorial n m en em
    let ⟨b, eb, b_prf⟩ := proveAscFactorial (n + m) r enm er
    have eab : Q(ℕ) := mkRawNatLit (a * b)
    have : $eab =Q $ea * $eb := ⟨⟩
    ⟨a * b, eab, q(by convert! asc_factorial_aux «$en» «$em» «$er» «$ea» «$eb» «$a_prf» «$b_prf»)⟩
/-
**Mathlib.Meta.NormNum.isNat_factorial** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：isNat_factorial {n x : Nat} (h₁ : IsNat n x) (a : Nat) (h₂ : (1).ascFactor
ial x = a) : IsNat (n !) a
参数：h₁ : IsNat n x；a : Nat；h₂ : (1).ascFactorial x = a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.one_ascFactorial`：∀ (k : ℕ), Nat.ascFactorial 1 k = k.factorial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isNat_factorial {n x : ℕ} (h₁ : IsNat n x) (a : ℕ) (h₂ : (1).ascFactorial x = a) :
    IsNat (n !) a := by
  constructor
  simp only [h₁.out, cast_id, ← h₂, one_ascFactorial]

/-- Evaluates the `Nat.factorial` function. -/
@[nolint unusedHavesSuffices, norm_num Nat.factorial _]
/-
**Mathlib.Meta.NormNum.evalNatFactorial** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：evalNatFactorial : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `Nat.factorial` function.
-/
def evalNatFactorial : NormNumExt where eval {u α} e := do
  let .app _ (x : Q(ℕ)) ← Meta.whnfR e | failure
  have : u =QL 0 := ⟨⟩; have : $α =Q ℕ := ⟨⟩; have : $e =Q Nat.factorial $x := ⟨⟩
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sℕ
  let ⟨_, val, ascPrf⟩ := proveAscFactorial 1 ex.natLit! q(nat_lit 1) ex
  return .isNat sℕ q($val) q(isNat_factorial $p $val $ascPrf)
/-
**Mathlib.Meta.NormNum.isNat_ascFactorial** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Met
a.NormNum`。
形式化陈述：isNat_ascFactorial {n x l y : Nat} (h₁ : IsNat n x) (h₂ : IsNat l y) (a : 
Nat) (p : x.ascFactorial y = a) : IsNat (n.ascFactorial l) a
参数：h₁ : IsNat n x；h₂ : IsNat l y；a : Nat；p : x.ascFactorial y = a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isNat_ascFactorial {n x l y : ℕ} (h₁ : IsNat n x) (h₂ : IsNat l y) (a : ℕ)
    (p : x.ascFactorial y = a) : IsNat (n.ascFactorial l) a := by
  constructor
  simp [h₁.out, h₂.out, ← p]

/-- Evaluates the Nat.ascFactorial function. -/
@[nolint unusedHavesSuffices, norm_num Nat.ascFactorial _ _]
/-
**Mathlib.Meta.NormNum.evalNatAscFactorial** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Me
ta.NormNum`。
形式化陈述：evalNatAscFactorial : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the Nat.ascFactorial function.
-/
def evalNatAscFactorial : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℕ))) (y : Q(ℕ)) ← Meta.whnfR e | failure
  have : u =QL 0 := ⟨⟩; have : $α =Q ℕ := ⟨⟩; have : $e =Q Nat.ascFactorial $x $y := ⟨⟩
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨ex₁, p₁⟩ ← deriveNat x sℕ
  let ⟨ex₂, p₂⟩ ← deriveNat y sℕ
  let ⟨_, val, ascPrf⟩ := proveAscFactorial ex₁.natLit! ex₂.natLit! ex₁ ex₂
  return .isNat sℕ q($val) q(isNat_ascFactorial $p₁ $p₂ $val $ascPrf)
/-
**Mathlib.Meta.NormNum.isNat_descFactorial** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Me
ta.NormNum`。
形式化陈述：isNat_descFactorial {n x l y : Nat} (z : Nat) (h₁ : IsNat n x) (h₂ : IsNat
 l y) (h₃ : x = z + y) (a : Nat) (p : (z + 1).ascFactorial y = a) : IsNat (n.des
cFactorial l) a
参数：z : Nat；h₁ : IsNat n x；h₂ : IsNat l y；h₃ : x = z + y；a : Nat；p : (z + 1).ascF
actorial y = a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_descFactorial_eq_ascFactorial`：∀ (n k : ℕ), (n + k).descFactoria
l k = (n + 1).ascFactorial k
-/
lemma isNat_descFactorial {n x l y : ℕ} (z : ℕ) (h₁ : IsNat n x) (h₂ : IsNat l y)
    (h₃ : x = z + y) (a : ℕ) (p : (z + 1).ascFactorial y = a) : IsNat (n.descFactorial l) a := by
  constructor
  simpa [h₁.out, h₂.out, ← p, h₃] using Nat.add_descFactorial_eq_ascFactorial _ _
/-
**Mathlib.Meta.NormNum.isNat_descFactorial_zero** 是 Mathlib 中的一个引理，位于命名空间 `Mathl
ib.Meta.NormNum`。
形式化陈述：isNat_descFactorial_zero {n x l y : Nat} (z : Nat) (h₁ : IsNat n x) (h₂ : 
IsNat l y) (h₃ : y = z + x + 1) : IsNat (n.descFactorial l) 0
参数：z : Nat；h₁ : IsNat n x；h₂ : IsNat l y；h₃ : y = z + x + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isNat_descFactorial_zero {n x l y : ℕ} (z : ℕ) (h₁ : IsNat n x) (h₂ : IsNat l y)
    (h₃ : y = z + x + 1) : IsNat (n.descFactorial l) 0 := by
  constructor
  simp [h₁.out, h₂.out, h₃]
/-
**Mathlib.Meta.NormNum.evalNatDescFactorialNotZero** 是 Mathlib 中的一个定义，位于命名空间 `Ma
thlib.Meta.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private partial def evalNatDescFactorialNotZero {x' y' : Q(ℕ)} (x y z : Q(ℕ))
    (_hx : $x =Q $z + $y)
    (px : Q(IsNat $x' $x)) (py : Q(IsNat $y' $y)) :
    (n : Q(ℕ)) × Q(IsNat (descFactorial $x' $y') $n) :=
  have zp1 :Q(ℕ) := mkRawNatLit (z.natLit! + 1)
  have : $zp1 =Q $z + 1 := ⟨⟩
  let ⟨_, val, ascPrf⟩ := proveAscFactorial (z.natLit! + 1) y.natLit! zp1 y
  ⟨val, q(isNat_descFactorial $z $px $py rfl $val $ascPrf)⟩
/-
**Mathlib.Meta.NormNum.evalNatDescFactorialZero** 是 Mathlib 中的一个定义，位于命名空间 `Mathl
ib.Meta.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private partial def evalNatDescFactorialZero {x' y' : Q(ℕ)} (x y z : Q(ℕ))
    (_hy : $y =Q $z + $x + 1)
    (px : Q(IsNat $x' $x)) (py : Q(IsNat $y' $y)) :
    (n : Q(ℕ)) × Q(IsNat (descFactorial $x' $y') $n) :=
  ⟨q(nat_lit 0), q(isNat_descFactorial_zero $z $px $py rfl)⟩

/-- Evaluates the `Nat.descFactorial` function. -/
@[nolint unusedHavesSuffices, norm_num Nat.descFactorial _ _]
/-
**Mathlib.Meta.NormNum.evalNatDescFactorial** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.M
eta.NormNum`。
形式化陈述：evalNatDescFactorial : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `Nat.descFactorial` function.
-/
def evalNatDescFactorial : NormNumExt where eval {u α} e := do
  let .app (.app _ (x' : Q(ℕ))) (y' : Q(ℕ)) ← Meta.whnfR e | failure
  have : u =QL 0 := ⟨⟩
  have : $α =Q ℕ := ⟨⟩
  have : $e =Q Nat.descFactorial $x' $y' := ⟨⟩
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨x, p₁⟩ ← deriveNat x' sℕ
  let ⟨y, p₂⟩ ← deriveNat y' sℕ
  if x.natLit! ≥ y.natLit! then
    have z : Q(ℕ) := mkRawNatLit (x.natLit! - y.natLit!)
    have : $x =Q $z + $y := ⟨⟩
    let ⟨val, prf⟩ := evalNatDescFactorialNotZero (x' := x') (y' := y') x y z ‹_› p₁ p₂
    return .isNat sℕ val q($prf)
  else
    have z : Q(ℕ) := mkRawNatLit (y.natLit! - x.natLit! - 1)
    have : $y =Q $z + $x + 1 := ⟨⟩
    let ⟨val, prf⟩ := evalNatDescFactorialZero (x' := x') (y' := y') x y z ‹_› p₁ p₂
    return .isNat sℕ val q($prf)

end NormNum

end Meta

end Mathlib

