/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Ring.TransferInstance

/-! # Transfer star (algebraic) structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

variable {R S : Type*}

@[expose] public section

namespace Equiv

variable (e : R ≃ S)

-- See note [instance transfer via equivalence]
/-- Transfer `Star` across an `Equiv`. See note [reducible non-instances].

For `star : R → R` bundled as an `Equiv`, see `Equiv.Perm.star`. -/
/-
**Equiv.star** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{R : Type u_1} → {S : Type u_2} → R ≃ S → [Star S] → Star R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `Star` across an `Equiv`. See note [reducible non-instances].

For `star : R → R` bundled as an `Equiv`, see `Equiv.Perm.star`.
-/
protected abbrev star [Star S] : Star R where
  star r := e.invFun (star (e.toFun r))

/-- Transfer `InvolutiveStar` across an `Equiv`. See note [reducible non-instances]. -/
/-
**Equiv.involutiveStar** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{R : Type u_1} → {S : Type u_2} → R ≃ S → [InvolutiveStar S] → InvolutiveS
tar R
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `InvolutiveStar` across an `Equiv`. See note [reducible non-instances].
-/
protected abbrev involutiveStar [InvolutiveStar S] : InvolutiveStar R :=
  let _ := e.star
  e.injective.involutiveStar _ fun _ ↦ e.apply_symm_apply _

/-- Transfer `StarMul` across an `Equiv`. See note [reducible non-instances]. -/
/-
**Equiv.starMul** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{R : Type u_1} → {S : Type u_2} → (e : R ≃ S) → [inst : Mul S] → [StarMul 
S] → StarMul R
参数：e : R ≃ S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `StarMul` across an `Equiv`. See note [reducible non-instances].
-/
protected abbrev starMul [Mul S] [StarMul S] :
    letI := e.mul
    StarMul R := by
  let := e.star
  let := e.mul
  apply e.injective.starMul <;> (intros; exact e.apply_symm_apply _)

/-- Transfer `StarAddMonoid` across an `Equiv`. See note [reducible non-instances]. -/
/-
**Equiv.starAddMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{R : Type u_1} → {S : Type u_2} → (e : R ≃ S) → [inst : AddMonoid S] → [St
arAddMonoid S] → StarAddMonoid R
参数：e : R ≃ S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `StarAddMonoid` across an `Equiv`. See note [reducible non-instances].
-/
protected abbrev starAddMonoid [AddMonoid S] [StarAddMonoid S] :
    letI := e.addMonoid
    StarAddMonoid R := by
  let := e.star
  let := e.addMonoid
  apply e.injective.starAddMonoid <;> (intros; exact e.apply_symm_apply _)

/-- Transfer `StarRing` across an `Equiv`. See note [reducible non-instances]. -/
/-
**Equiv.starRing** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{R : Type u_1} → {S : Type u_2} → (e : R ≃ S) → [inst : NonUnitalNonAssocS
emiring S] → [StarRing S] → StarRing R
参数：e : R ≃ S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `StarRing` across an `Equiv`. See note [reducible non-instances].
-/
protected abbrev starRing [NonUnitalNonAssocSemiring S] [StarRing S] :
    letI := e.nonUnitalNonAssocSemiring
    StarRing R := by
  let := e.star
  let := e.nonUnitalNonAssocSemiring
  apply e.injective.starRing <;> (intros; exact e.apply_symm_apply _)

/-- Transfer `StarModule` across an `Equiv` -/
/-
**Equiv.starModule** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} (e : R ≃ S) (𝕜 : Type u_3) [inst : Star 𝕜]
 [inst_1 : Star S] [inst_2 : SMul 𝕜 S]   [StarModule 𝕜 S], StarModule 𝕜 R
参数：e : R ≃ S；𝕜 : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.starModule`：∀ {R : Type u} {S : Type v} (f : R → S) (
𝕜 : Type u_1) [inst : Star 𝕜] [inst_1 : SMul 𝕜 R] [inst_2 : Star R]   [inst_3 : 
SMul 𝕜 S] [inst_4 :…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x

--- 原说明 ---
Transfer `StarModule` across an `Equiv`
-/
protected lemma starModule (𝕜 : Type*)
    [Star 𝕜] [Star S] [SMul 𝕜 S] [StarModule 𝕜 S] :
    letI := e.star
    letI := e.smul 𝕜
    StarModule 𝕜 R := by
  let := e.star
  let := e.smul 𝕜
  apply e.injective.starModule _ 𝕜 <;> (intros; exact e.apply_symm_apply _)

end Equiv

