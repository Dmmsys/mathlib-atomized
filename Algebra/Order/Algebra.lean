/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Tactic.Positivity.Core

/-!
# Ordered algebras

An ordered algebra is an ordered semiring, which is an algebra over an ordered commutative semiring,
for which scalar multiplication is "compatible" with the two orders.

The prototypical example is 2x2 matrices over the reals or complexes (or indeed any C^* algebra)
where the ordering the one determined by the positive cone of positive operators,
i.e. `A ≤ B` iff `B - A = star R * R` for some `R`.
(We don't yet have this example in mathlib.)

## Implementation

Because the axioms for an ordered algebra are exactly the same as those for the underlying
module being ordered, we don't actually introduce a new class, but just use the `IsOrderedModule`
and `IsStrictOrderedModule` mixins.

## Tags

ordered algebra

## TODO

`positivity` extension for `algebraMap`
-/

public section

variable {α β : Type*} [CommSemiring α] [PartialOrder α] [Semiring β] [PartialOrder β] [Algebra α β]

/-
**IsOrderedModule.of_algebraMap_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOrderedModule.of_algebraMap_mono [PosMulMono β] [MulPosMono β] (h : Mono
tone (algebraMap α β)) : IsOrderedModule α β
参数：h : Monotone (algebraMap α β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOrderedModule.of_smul_one_mono`：IsOrderedModule.of_smul_one_mono [MulO
neClass β] [PosMulMono β] [MulPosMono β] [IsScalarTower α β β] (h : Monotone (fu
n x : α => x • (1 : β)…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem IsOrderedModule.of_algebraMap_mono [PosMulMono β] [MulPosMono β]
    (h : Monotone (algebraMap α β)) : IsOrderedModule α β :=
  .of_smul_one_mono (by simpa [Algebra.smul_def] using h)

section ZeroLEOneClass
variable [ZeroLEOneClass β]

section SMulPosMono
variable (β) [SMulPosMono α β]

@[gcongr, mono]
/-
**algebraMap_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_mono : Monotone (algebraMap α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_one_mono`：smul_one_mono [One β] [ZeroLEOneClass β] [SMulPosMono α β
] : Monotone (fun x : α => x • (1 : β))
-/
lemma algebraMap_mono : Monotone (algebraMap α β) := by
  simpa [Algebra.smul_def] using smul_one_mono (α := α) β
/-
**algebraMap_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_nonneg {a : α} (ha : 0 <= a) : 0 <= algebraMap α β a
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `algebraMap_mono`：algebraMap_mono : Monotone (algebraMap α β)
-/
lemma algebraMap_nonneg {a : α} (ha : 0 ≤ a) : 0 ≤ algebraMap α β a := by
  simpa using algebraMap_mono β ha

end SMulPosMono

/-
**isOrderedModule_iff_algebraMap_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOrderedModule_iff_algebraMap_mono [PosMulMono β] [MulPosMono β] : IsOrde
redModule α β ↔ Monotone (algebraMap α β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOrderedModule_iff_algebraMap_mono [PosMulMono β] [MulPosMono β] :
    IsOrderedModule α β ↔ Monotone (algebraMap α β) := by
  simp [isOrderedModule_iff_smul_one_mono, Algebra.smul_def]

section Nontrivial
variable [Nontrivial β]

@[simp]
/-
**algebraMap_le_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_le_algebraMap [SMulPosMono α β] [SMulPosReflectLE α β] {a₁ a₂ :
 α} : algebraMap α β a₁ <= algebraMap α β a₂ ↔ a₁ <= a₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma algebraMap_le_algebraMap [SMulPosMono α β] [SMulPosReflectLE α β] {a₁ a₂ : α} :
    algebraMap α β a₁ ≤ algebraMap α β a₂ ↔ a₁ ≤ a₂ := by
  simp [Algebra.algebraMap_eq_smul_one]

section SMulPosStrictMono
variable (β) [SMulPosStrictMono α β]

@[gcongr, mono]
/-
**algebraMap_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_strictMono : StrictMono (algebraMap α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_one_strictMono`：smul_one_strictMono [Preorder α] [PartialOrder β] [
Zero β] [One β] [ZeroLEOneClass β] [NeZero (1 : β)] [SMulPosStrictMono α β] : St
rictMono …
-/
lemma algebraMap_strictMono : StrictMono (algebraMap α β) := by
  simpa [Algebra.smul_def] using smul_one_strictMono (α := α) β
/-
**algebraMap_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_pos {a : α} (ha : 0 < a) : 0 < algebraMap α β a
参数：ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `algebraMap_strictMono`：algebraMap_strictMono : StrictMono (algebraMap α 
β)
-/
lemma algebraMap_pos {a : α} (ha : 0 < a) : 0 < algebraMap α β a := by
  simpa using algebraMap_strictMono β ha

variable {β} in
@[simp]
/-
**algebraMap_lt_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_lt_algebraMap [SMulPosReflectLT α β] {a₁ a₂ : α} : algebraMap α
 β a₁ < algebraMap α β a₂ ↔ a₁ < a₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma algebraMap_lt_algebraMap [SMulPosReflectLT α β] {a₁ a₂ : α} :
    algebraMap α β a₁ < algebraMap α β a₂ ↔ a₁ < a₂ := by
  simp [Algebra.algebraMap_eq_smul_one]

end SMulPosStrictMono
end Nontrivial
end ZeroLEOneClass

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

/-- Extension for `algebraMap`. -/
@[positivity algebraMap _ _ _]
meta def evalAlgebraMap : PositivityExt where eval {u β} _zβ pβ? e :=
  match pβ? with | none => pure .none | some _ => do
  let ~q(@algebraMap $α _ $instα $instβ $instαβ $a) := e | throwError "not `algebraMap`"
  let some pα ← try? <| synthInstanceQ q(PartialOrder $α) | pure .none
  match ← core q(inferInstance) (some pα) a with
  | .positive pa =>
    let _instαSemiring ← synthInstanceQ q(Semiring $α)
    try
      let _instβSemiring ← synthInstanceQ q(Semiring $β)
      let _instβPartialOrder ← synthInstanceQ q(PartialOrder $β)
      let _instβIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $β)
      let _instαβsmul ← synthInstanceQ q(SMulPosStrictMono $α $β)
      assertInstancesCommute
      return .positive q(algebraMap_pos $β $pa)
    catch _ =>
      let _instβSemiring ← synthInstanceQ q(Semiring $β)
      let _instβPartialOrder ← synthInstanceQ q(PartialOrder $β)
      let _instβIsOrderedRing ← synthInstanceQ q(IsOrderedRing $β)
      let _instαβsmul ← synthInstanceQ q(SMulPosMono $α $β)
      assertInstancesCommute
      return .nonnegative q(algebraMap_nonneg $β <| le_of_lt $pa)
  | .nonnegative pa =>
    let _instαSemiring ← synthInstanceQ q(CommSemiring $α)
    let _instβSemiring ← synthInstanceQ q(Semiring $β)
    let _instβPartialOrder ← synthInstanceQ q(PartialOrder $β)
    let _instβIsOrderedRing ← synthInstanceQ q(IsOrderedRing $β)
    let _instαβsmul ← synthInstanceQ q(SMulPosMono $α $β)
    assertInstancesCommute
    return .nonnegative q(algebraMap_nonneg $β $pa)
  | _ => pure .none

/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [IsOrderedRing β] [SMulPosMono α β]
    {a : α} (ha : 0 ≤ a) :
    0 ≤ algebraMap α β a := by positivity
/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [IsOrderedRing β] [SMulPosMono α β]
    {a : α} (ha : 0 < a) :
    0 ≤ algebraMap α β a := by positivity
/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [IsStrictOrderedRing β] [SMulPosStrictMono α β]
    {a : α} (ha : 0 < a) :
    0 < algebraMap α β a := by positivity

end Mathlib.Meta.Positivity

