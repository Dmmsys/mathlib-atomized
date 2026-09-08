/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Thomas Murrills
-/
module

public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Tactic.NormNum.Basic

/-!
## `norm_num` plugin for scientific notation.
-/

public meta section

namespace Mathlib
open Lean
open Meta

namespace Meta.NormNum
open Qq

variable {α : Type*}

-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true** 是 Mathlib 中的一个定理，位于命名空间 `M
athlib.Meta.NormNum`。
形式化陈述：∀ {α : Type u_1} [inst : DivisionSemiring α] {m e n d : ℕ},   Mathlib.Meta
.NormNum.IsNNRat (↑(NNRat.divNat m (10 ^ e))) n d →     Mathlib.Meta.NormNum.IsN
NRat (OfScientific.ofScientific m true e) n d
参数：↑(NNRat.divNat m (10 ^ e))；OfScientific.ofScientific m true e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNRatCast.ofScientific_eq_ite`：NNRatCast.ofScientific_eq_ite {K} [NNRatC
ast K] (m : Nat) (b : Bool) (d : Nat) : (OfScientific.ofScientific m b d : K) = 
if b = true then NN…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem isNNRat_ofScientific_of_true [DivisionSemiring α] :
    {m e : ℕ} → {n : ℕ} → {d : ℕ} →
    IsNNRat (NNRat.divNat m (10 ^ e) : α) n d → IsNNRat (OfScientific.ofScientific m true e : α) n d
  | _, _, _, _, ⟨_, eq⟩ => ⟨‹_›, by rwa [NNRatCast.ofScientific_eq_ite, if_pos rfl]⟩

-- see note [norm_num lemma function equality]
/-
**Mathlib.Meta.NormNum.isNat_ofScientific_of_false** 是 Mathlib 中的一个定理，位于命名空间 `Ma
thlib.Meta.NormNum`。
形式化陈述：∀ {α : Type u_1} [inst : DivisionSemiring α] {m e nm ne n : ℕ},   Mathlib.
Meta.NormNum.IsNat m nm →     Mathlib.Meta.NormNum.IsNat e ne →       n = nm.mul
 (10 ^ ne) → Mathlib.Meta.NormNum.IsNat (OfScientific.ofScientific m false e) n
参数：10 ^ ne；OfScientific.ofScientific m false e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNRatCast.ofScientific_eq_ite`：NNRatCast.ofScientific_eq_ite {K} [NNRatC
ast K] (m : Nat) (b : Bool) (d : Nat) : (OfScientific.ofScientific m b d : K) = 
if b = true then NN…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Bool.false_ne_true`：false ≠ true
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
-/
theorem isNat_ofScientific_of_false [DivisionSemiring α] : {m e nm ne n : ℕ} →
    IsNat m nm → IsNat e ne → n = Nat.mul nm ((10 : ℕ) ^ ne) →
    IsNat (OfScientific.ofScientific m false e : α) n
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, (rfl : (_ : ℕ) = _ * _) => ⟨by
    rw [NNRatCast.ofScientific_eq_ite, if_neg Bool.false_ne_true]
    norm_cast⟩

/-- The `norm_num` extension which identifies expressions in scientific notation, normalizing them
to rat casts if the scientific notation is inherited from the one for rationals. -/
/-
**Mathlib.Meta.NormNum.evalOfScientific** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions in scientific notation, no
rmalizing them
to rat casts if the scientific notation is inherited from the one for rationals.
-/
@[norm_num OfScientific.ofScientific _ _ _] def evalOfScientific :
    NormNumExt where eval {u α} e := do
  let mkApp3 f (m : Q(ℕ)) (b : Q(Bool)) (exp : Q(ℕ)) ← whnfR e | failure
  let dα ← inferDivisionSemiring α
  guard <|← withNewMCtxDepth <| isDefEq f q(OfScientific.ofScientific (α := $α))
  haveI' : $e =Q OfScientific.ofScientific $m $b $exp := ⟨⟩
  match b with
  | ~q(true) =>
    let rme ← derive (q(NNRat.divNat $m (10 ^ $exp)) : Q($α))
    let some ⟨q, n, d, p⟩ := rme.toNNRat' dα | failure
    return .isNNRat dα q n d q(isNNRat_ofScientific_of_true $p)
  | ~q(false) =>
    let ⟨nm, pm⟩ ← deriveNat m q(AddCommMonoidWithOne.toAddMonoidWithOne)
    let ⟨ne, pe⟩ ← deriveNat exp q(AddCommMonoidWithOne.toAddMonoidWithOne)
    have pm : Q(IsNat $m $nm) := pm
    have pe : Q(IsNat $exp $ne) := pe
    let m' := nm.natLit!
    let exp' := ne.natLit!
    let n' := Nat.mul m' (Nat.pow (10 : ℕ) exp')
    have n : Q(ℕ) := mkRawNatLit n'
    haveI : $n =Q Nat.mul $nm ((10 : ℕ) ^ $ne) := ⟨⟩
    return .isNat _ n q(isNat_ofScientific_of_false $pm $pe (.refl $n))

end NormNum

end Meta

end Mathlib

