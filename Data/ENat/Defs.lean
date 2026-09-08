/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Yury Kudryashov
-/
module

public import Batteries.Tactic.Alias
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.TypeTags

/-! # Definition and notation for extended natural numbers -/

@[expose] public section

/-- Extended natural numbers `ℕ∞ = WithTop ℕ`. -/
/-
**ENat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ENat : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extended natural numbers `ℕ∞ = WithTop ℕ`.
-/
def ENat : Type := WithTop ℕ deriving Top, Inhabited

@[inherit_doc] notation "ℕ∞" => ENat

namespace ENat

/-
**ENat.instNatCast** 是 Mathlib 中的一个实例，位于命名空间 `ENat`。
形式化陈述：instNatCast : NatCast Nat∞
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNatCast : NatCast ℕ∞ := ⟨WithTop.some⟩

/-- Recursor for `ENat` using the preferred forms `⊤` and `↑a`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/-
**ENat.recTopCoe** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
形式化陈述：{C : ℕ∞ → Sort u_1} → C ⊤ → ((a : ℕ) → C ↑a) → (n : ℕ∞) → C n
参数：(a : ℕ) → C ↑a；n : ℕ∞。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursor for `ENat` using the preferred forms `⊤` and `↑a`.
-/
def recTopCoe {C : ℕ∞ → Sort*} (top : C ⊤) (coe : ∀ a : ℕ, C a) : ∀ n : ℕ∞, C n
  | none => top
  | Option.some a => coe a

@[simp]
/-
**ENat.recTopCoe_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：recTopCoe_top {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a) : @r
ecTopCoe C d f ⊤ = d
参数：d : C ⊤；f : forall a : Nat, C a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem recTopCoe_top {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) :
    @recTopCoe C d f ⊤ = d :=
  rfl

@[simp]
/-
**ENat.recTopCoe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：recTopCoe_natCast {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a) 
(x : Nat) : @recTopCoe C d f ↑x = f x
参数：d : C ⊤；f : forall a : Nat, C a；x : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem recTopCoe_natCast {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) (x : ℕ) :
    @recTopCoe C d f ↑x = f x :=
  rfl

@[deprecated (since := "2026-07-17")] alias recTopCoe_coe := recTopCoe_natCast

end ENat

