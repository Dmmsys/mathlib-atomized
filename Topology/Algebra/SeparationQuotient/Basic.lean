/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Algebraic operations on `SeparationQuotient`

In this file we define algebraic operations (multiplication, addition etc)
on the separation quotient of a topological space with corresponding operation,
provided that the original operation is continuous.

We also prove continuity of these operations
and show that they satisfy the same kind of laws (`Monoid` etc) as the original ones.

Finally, we construct a section of the quotient map
which is a continuous linear map `SeparationQuotient E →L[K] E`.
-/

@[expose] public section

assert_not_exists LinearIndependent

open scoped Topology

namespace SeparationQuotient

section SMul

variable {M X : Type*} [TopologicalSpace X] [SMul M X] [ContinuousConstSMul M X]

@[to_additive]
/-
**SeparationQuotient.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instSMul : SMul M (SeparationQuotient X) where smul c
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
· 使用定理 `Inseparable.const_smul`：Inseparable.const_smul {x y : α} (h : Inseparabl
e x y) (c : M) : Inseparable (c • x) (c • y)
-/
instance instSMul : SMul M (SeparationQuotient X) where
  smul c := Quotient.map' (c • ·) fun _ _ h ↦ h.const_smul c

@[to_additive (attr := simp)]
/-
**SeparationQuotient.mk_smul** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：mk_smul (c : M) (x : X) : mk (c • x) = c • mk x
参数：c : M；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_smul (c : M) (x : X) : mk (c • x) = c • mk x := rfl

@[to_additive]
/-
**SeparationQuotient.instContinuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 `Separati
onQuotient`。
形式化陈述：instContinuousConstSMul : ContinuousConstSMul M (SeparationQuotient X) whe
re continuous_const_smul c
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `SeparationQuotient.isQuotientMap_mk`：isQuotientMap_mk : IsQuotientMap (m
k : X -> SeparationQuotient X)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `SeparationQuotient.continuous_mk`：continuous_mk : Continuous (mk : X -> 
SeparationQuotient X)
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
-/
instance instContinuousConstSMul : ContinuousConstSMul M (SeparationQuotient X) where
  continuous_const_smul c := isQuotientMap_mk.continuous_iff.2 <|
    continuous_mk.comp <| continuous_const_smul c

@[to_additive]
/-
**SeparationQuotient.instIsPretransitiveSMul** 是 Mathlib 中的一个实例，位于命名空间 `Separati
onQuotient`。
形式化陈述：instIsPretransitiveSMul [MulAction.IsPretransitive M X] : MulAction.IsPret
ransitive M (SeparationQuotient X) where exists_smul_eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall₂`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}
,   Function.Surjective f → ∀ {p : β → β → Prop}, (∀ (y₁ y₂ : β), p y₁ y₂) ↔ ∀ (
x₁ x₂ : α), p (f …
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
-/
instance instIsPretransitiveSMul [MulAction.IsPretransitive M X] :
    MulAction.IsPretransitive M (SeparationQuotient X) where
  exists_smul_eq := surjective_mk.forall₂.2 fun x y ↦
    (MulAction.exists_smul_eq M x y).imp fun _ ↦ congr_arg mk

@[to_additive]
/-
**SeparationQuotient.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQu
otient`。
形式化陈述：instIsCentralScalar [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] : IsCentralScalar 
M (SeparationQuotient X) where op_smul_eq_smul a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance instIsCentralScalar [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] :
    IsCentralScalar M (SeparationQuotient X) where
  op_smul_eq_smul a := surjective_mk.forall.2 (congr_arg mk <| op_smul_eq_smul a ·)

variable {N : Type*} [SMul N X]

@[to_additive]
/-
**SeparationQuotient.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuot
ient`。
形式化陈述：instSMulCommClass [ContinuousConstSMul N X] [SMulCommClass M N X] : SMulCo
mmClass M N (SeparationQuotient X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Surjective.smulCommClass`：Function.Surjective.smulCommClass [SM
ul M α] [SMul N α] [SMul M β] [SMul N β] [SMulCommClass M N α] {f : α -> β} (hf 
: Surjective f) (h₁ : f…
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
· 使用定理 `SeparationQuotient.mk_smul`：mk_smul (c : M) (x : X) : mk (c • x) = c • m
k x
-/
instance instSMulCommClass [ContinuousConstSMul N X] [SMulCommClass M N X] :
    SMulCommClass M N (SeparationQuotient X) :=
  surjective_mk.smulCommClass mk_smul mk_smul

@[to_additive]
/-
**SeparationQuotient.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuot
ient`。
形式化陈述：instIsScalarTower [SMul M N] [ContinuousConstSMul N X] [IsScalarTower M N 
X] : IsScalarTower M N (SeparationQuotient X) where smul_assoc a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance instIsScalarTower [SMul M N] [ContinuousConstSMul N X] [IsScalarTower M N X] :
    IsScalarTower M N (SeparationQuotient X) where
  smul_assoc a b := surjective_mk.forall.2 fun x ↦ congr_arg mk <| smul_assoc a b x

end SMul

/-
**SeparationQuotient.instContinuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuo
tient`。
形式化陈述：instContinuousSMul {M X : Type*} [SMul M X] [TopologicalSpace M] [Topologi
calSpace X] [ContinuousSMul M X] : ContinuousSMul M (SeparationQuotient X) where
 continuous_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `IsOpenQuotientMap.isQuotientMap`：isQuotientMap (h : IsOpenQuotientMap f)
 : IsQuotientMap f
· 使用定理 `IsOpenQuotientMap.prodMap`：IsOpenQuotientMap.prodMap {f : X -> Y} {g : Z
 -> W} (hf : IsOpenQuotientMap f) (hg : IsOpenQuotientMap g) : IsOpenQuotientMap
 (Prod.map f g)
· 使用定理 `IsOpenQuotientMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOp
enQuotientMap id
· 使用定理 `SeparationQuotient.isOpenQuotientMap_mk`：isOpenQuotientMap_mk : IsOpenQu
otientMap (mk : X -> SeparationQuotient X)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `SeparationQuotient.continuous_mk`：continuous_mk : Continuous (mk : X -> 
SeparationQuotient X)
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
-/
instance instContinuousSMul {M X : Type*} [SMul M X] [TopologicalSpace M] [TopologicalSpace X]
    [ContinuousSMul M X] : ContinuousSMul M (SeparationQuotient X) where
  continuous_smul := by
    rw [(IsOpenQuotientMap.id.prodMap isOpenQuotientMap_mk).isQuotientMap.continuous_iff]
    exact continuous_mk.comp continuous_smul
/-
**SeparationQuotient.instSMulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuot
ient`。
形式化陈述：instSMulZeroClass {M X : Type*} [Zero X] [SMulZeroClass M X] [TopologicalS
pace X] [ContinuousConstSMul M X] : SMulZeroClass M (SeparationQuotient X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.mk_zero`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [inst_1 : Zero X], SeparationQuotient.mk 0 = 0
-/
instance instSMulZeroClass {M X : Type*} [Zero X] [SMulZeroClass M X] [TopologicalSpace X]
    [ContinuousConstSMul M X] : SMulZeroClass M (SeparationQuotient X) :=
  ZeroHom.smulZeroClass ⟨mk, mk_zero⟩ mk_smul

@[to_additive]
/-
**SeparationQuotient.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient
`。
形式化陈述：instMulAction {M X : Type*} [Monoid M] [MulAction M X] [TopologicalSpace X
] [ContinuousConstSMul M X] : MulAction M (SeparationQuotient X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
-/
instance instMulAction {M X : Type*} [Monoid M] [MulAction M X] [TopologicalSpace X]
    [ContinuousConstSMul M X] : MulAction M (SeparationQuotient X) :=
  surjective_mk.mulAction mk mk_smul

section Monoid

variable {M : Type*} [TopologicalSpace M]

@[to_additive]
/-
**SeparationQuotient.instMul** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instMul [Mul M] [ContinuousMul M] : Mul (SeparationQuotient M) where mul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.mul`：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : 
Mul M] [ContinuousMul M] {a b c d : M},   Inseparable a b → Inseparable c d → In
separ…
-/
instance instMul [Mul M] [ContinuousMul M] : Mul (SeparationQuotient M) where
  mul := Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ ↦ Inseparable.mul h₁ h₂

@[to_additive (attr := simp)]
/-
**SeparationQuotient.mk_mul** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：mk_mul [Mul M] [ContinuousMul M] (a b : M) : mk (a * b) = mk a * mk b
参数：a b : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mul [Mul M] [ContinuousMul M] (a b : M) : mk (a * b) = mk a * mk b := rfl

@[to_additive]
/-
**SeparationQuotient.instContinuousMul** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuot
ient`。
形式化陈述：instContinuousMul [Mul M] [ContinuousMul M] : ContinuousMul (SeparationQuo
tient M) where continuous_mul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `SeparationQuotient.isQuotientMap_prodMap_mk`：isQuotientMap_prodMap_mk : 
IsQuotientMap (Prod.map mk mk : X × Y -> _)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `SeparationQuotient.continuous_mk`：continuous_mk : Continuous (mk : X -> 
SeparationQuotient X)
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
-/
instance instContinuousMul [Mul M] [ContinuousMul M] : ContinuousMul (SeparationQuotient M) where
  continuous_mul := isQuotientMap_prodMap_mk.continuous_iff.2 <| continuous_mk.comp continuous_mul

@[to_additive]
/-
**SeparationQuotient.instCommMagma** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient
`。
形式化陈述：instCommMagma [CommMagma M] [ContinuousMul M] : CommMagma (SeparationQuoti
ent M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMagma [CommMagma M] [ContinuousMul M] : CommMagma (SeparationQuotient M) :=
  fast_instance% surjective_mk.commMagma mk mk_mul

@[to_additive]
/-
**SeparationQuotient.instSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient
`。
形式化陈述：instSemigroup [Semigroup M] [ContinuousMul M] : Semigroup (SeparationQuoti
ent M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroup [Semigroup M] [ContinuousMul M] : Semigroup (SeparationQuotient M) :=
  fast_instance% surjective_mk.semigroup mk mk_mul

@[to_additive]
/-
**SeparationQuotient.instCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuot
ient`。
形式化陈述：instCommSemigroup [CommSemigroup M] [ContinuousMul M] : CommSemigroup (Sep
arationQuotient M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemigroup [CommSemigroup M] [ContinuousMul M] :
    CommSemigroup (SeparationQuotient M) :=
  fast_instance% surjective_mk.commSemigroup mk mk_mul

@[to_additive]
/-
**SeparationQuotient.instMulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotie
nt`。
形式化陈述：instMulOneClass [MulOneClass M] [ContinuousMul M] : MulOneClass (Separatio
nQuotient M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulOneClass [MulOneClass M] [ContinuousMul M] :
    MulOneClass (SeparationQuotient M) :=
  fast_instance% surjective_mk.mulOneClass mk mk_one mk_mul

/-- `SeparationQuotient.mk` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `SeparationQuotient.mk` as an `AddMonoidHom`. -/]
/-
**SeparationQuotient.mkMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `SeparationQuotient`。
形式化陈述：mkMonoidHom [MulOneClass M] [ContinuousMul M] : M ->* SeparationQuotient M
 where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SeparationQuotient.mk` as a `MonoidHom`.
-/
def mkMonoidHom [MulOneClass M] [ContinuousMul M] : M →* SeparationQuotient M where
  toFun := mk
  map_mul' := mk_mul
  map_one' := mk_one
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) instNSMul [AddMonoid M] [ContinuousAdd M] :
    SMul ℕ (SeparationQuotient M) :=
  inferInstance

@[to_additive existing]
/-
**SeparationQuotient.instPow** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instPow [Monoid M] [ContinuousMul M] : Pow (SeparationQuotient M) Nat wher
e pow x n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
· 使用定理 `Inseparable.pow`：∀ {M : Type u_6} [inst : Monoid M] [inst_1 : Topologica
lSpace M] [ContinuousMul M] {a b : M},   Inseparable a b → ∀ (n : ℕ), Inseparabl
e (a …
-/
instance instPow [Monoid M] [ContinuousMul M] : Pow (SeparationQuotient M) ℕ where
  pow x n := Quotient.map' (s₁ := inseparableSetoid M) (· ^ n) (fun _ _ h ↦ Inseparable.pow h n) x

@[to_additive, simp] -- `mk_nsmul` is not a `simp` lemma because we have `mk_smul`
/-
**SeparationQuotient.mk_pow** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：mk_pow [Monoid M] [ContinuousMul M] (x : M) (n : Nat) : mk (x ^ n) = (mk x
) ^ n
参数：x : M；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_pow [Monoid M] [ContinuousMul M] (x : M) (n : ℕ) : mk (x ^ n) = (mk x) ^ n := rfl

@[to_additive]
/-
**SeparationQuotient.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instMonoid [Monoid M] [ContinuousMul M] : Monoid (SeparationQuotient M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid [Monoid M] [ContinuousMul M] : Monoid (SeparationQuotient M) :=
  fast_instance% surjective_mk.monoid mk mk_one mk_mul mk_pow

@[to_additive]
/-
**SeparationQuotient.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotien
t`。
形式化陈述：instCommMonoid [CommMonoid M] [ContinuousMul M] : CommMonoid (SeparationQu
otient M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoid [CommMonoid M] [ContinuousMul M] : CommMonoid (SeparationQuotient M) :=
  fast_instance% surjective_mk.commMonoid mk mk_one mk_mul mk_pow

end Monoid

section Group

variable {G : Type*} [TopologicalSpace G]

@[to_additive]
/-
**SeparationQuotient.instInv** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instInv [Inv G] [ContinuousInv G] : Inv (SeparationQuotient G) where inv
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
· 使用定理 `Inseparable.inv`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : In
v G] [ContinuousInv G] {x y : G},   Inseparable x y → Inseparable x⁻¹ y⁻¹
-/
instance instInv [Inv G] [ContinuousInv G] : Inv (SeparationQuotient G) where
  inv := Quotient.map' (·⁻¹) fun _ _ ↦ Inseparable.inv

@[to_additive (attr := simp)]
/-
**SeparationQuotient.mk_inv** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：mk_inv [Inv G] [ContinuousInv G] (x : G) : mk x⁻¹ = (mk x)⁻¹
参数：x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_inv [Inv G] [ContinuousInv G] (x : G) : mk x⁻¹ = (mk x)⁻¹ := rfl

@[to_additive]
/-
**SeparationQuotient.instContinuousInv** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuot
ient`。
形式化陈述：instContinuousInv [Inv G] [ContinuousInv G] : ContinuousInv (SeparationQuo
tient G) where continuous_inv
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `SeparationQuotient.isQuotientMap_mk`：isQuotientMap_mk : IsQuotientMap (m
k : X -> SeparationQuotient X)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `SeparationQuotient.continuous_mk`：continuous_mk : Continuous (mk : X -> 
SeparationQuotient X)
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
instance instContinuousInv [Inv G] [ContinuousInv G] : ContinuousInv (SeparationQuotient G) where
  continuous_inv := isQuotientMap_mk.continuous_iff.2 <| continuous_mk.comp continuous_inv

@[to_additive]
/-
**SeparationQuotient.instInvolutiveInv** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuot
ient`。
形式化陈述：instInvolutiveInv [InvolutiveInv G] [ContinuousInv G] : InvolutiveInv (Sep
arationQuotient G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
-/
instance instInvolutiveInv [InvolutiveInv G] [ContinuousInv G] :
    InvolutiveInv (SeparationQuotient G) :=
  surjective_mk.involutiveInv mk mk_inv

@[to_additive]
/-
**SeparationQuotient.instInvOneClass** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotie
nt`。
形式化陈述：instInvOneClass [InvOneClass G] [ContinuousInv G] : InvOneClass (Separatio
nQuotient G) where inv_one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInvOneClass [InvOneClass G] [ContinuousInv G] :
    InvOneClass (SeparationQuotient G) where
  inv_one := congr_arg mk inv_one

@[to_additive]
/-
**SeparationQuotient.instDiv** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instDiv [Div G] [ContinuousDiv G] : Div (SeparationQuotient G) where div
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDiv [Div G] [ContinuousDiv G] : Div (SeparationQuotient G) where
  div := Quotient.map₂ (· / ·) fun _ _ h₁ _ _ h₂ ↦ (Inseparable.prod h₁ h₂).map continuous_div'

@[to_additive (attr := simp)]
/-
**SeparationQuotient.mk_div** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：mk_div [Div G] [ContinuousDiv G] (x y : G) : mk (x / y) = mk x / mk y
参数：x y : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_div [Div G] [ContinuousDiv G] (x y : G) : mk (x / y) = mk x / mk y := rfl

@[to_additive]
/-
**SeparationQuotient.instContinuousDiv** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuot
ient`。
形式化陈述：instContinuousDiv [Div G] [ContinuousDiv G] : ContinuousDiv (SeparationQuo
tient G) where continuous_div'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `SeparationQuotient.isQuotientMap_prodMap_mk`：isQuotientMap_prodMap_mk : 
IsQuotientMap (Prod.map mk mk : X × Y -> _)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `SeparationQuotient.continuous_mk`：continuous_mk : Continuous (mk : X -> 
SeparationQuotient X)
· 使用定理 `ContinuousDiv.continuous_div'`：∀ {G : Type u_4} {inst : TopologicalSpace
 G} {inst_1 : Div G} [self : ContinuousDiv G], Continuous fun p => p.1 / p.2
-/
instance instContinuousDiv [Div G] [ContinuousDiv G] : ContinuousDiv (SeparationQuotient G) where
  continuous_div' := isQuotientMap_prodMap_mk.continuous_iff.2 <| continuous_mk.comp continuous_div'
/-
**SeparationQuotient.instZSMul** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instZSMul [AddGroup G] [IsTopologicalAddGroup G] : SMul Int (SeparationQuo
tient G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZSMul [AddGroup G] [IsTopologicalAddGroup G] : SMul ℤ (SeparationQuotient G) :=
  inferInstance

@[to_additive existing]
/-
**SeparationQuotient.instZPow** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instZPow [Group G] [IsTopologicalGroup G] : Pow (SeparationQuotient G) Int
 where pow x n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
-/
instance instZPow [Group G] [IsTopologicalGroup G] : Pow (SeparationQuotient G) ℤ where
  pow x n := Quotient.map' (s₁ := inseparableSetoid G) (· ^ n) (fun _ _ h ↦ Inseparable.zpow h n) x

@[to_additive, simp] -- `mk_zsmul` is not a `simp` lemma because we have `mk_smul`
/-
**SeparationQuotient.mk_zpow** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：mk_zpow [Group G] [IsTopologicalGroup G] (x : G) (n : Int) : mk (x ^ n) = 
(mk x) ^ n
参数：x : G；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_zpow [Group G] [IsTopologicalGroup G] (x : G) (n : ℤ) : mk (x ^ n) = (mk x) ^ n := rfl

@[to_additive]
/-
**SeparationQuotient.instGroup** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instGroup [Group G] [IsTopologicalGroup G] : Group (SeparationQuotient G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `IsTopologicalGroup.to_continuousDiv`：∀ {G : Type u} [inst : TopologicalS
pace G] [inst_1 : Group G] [IsTopologicalGroup G], ContinuousDiv G
-/
instance instGroup [Group G] [IsTopologicalGroup G] : Group (SeparationQuotient G) :=
  fast_instance% surjective_mk.group mk mk_one mk_mul mk_inv mk_div mk_pow mk_zpow

@[to_additive]
/-
**SeparationQuotient.instCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient
`。
形式化陈述：instCommGroup [CommGroup G] [IsTopologicalGroup G] : CommGroup (Separation
Quotient G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommGroup [CommGroup G] [IsTopologicalGroup G] : CommGroup (SeparationQuotient G) :=
  fast_instance% surjective_mk.commGroup mk mk_one mk_mul mk_inv mk_div mk_pow mk_zpow

@[to_additive]
/-
**SeparationQuotient.instIsTopologicalGroup** 是 Mathlib 中的一个定理，位于命名空间 `Separatio
nQuotient`。
形式化陈述：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : Group G] [inst_2 : 
IsTopologicalGroup G],   IsTopologicalGroup (SeparationQuotient G)
参数：SeparationQuotient G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
-/
instance instIsTopologicalGroup [Group G] [IsTopologicalGroup G] :
    IsTopologicalGroup (SeparationQuotient G) where

end Group

section IsUniformGroup

@[to_additive]
/-
**SeparationQuotient.instIsUniformGroup** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuo
tient`。
形式化陈述：instIsUniformGroup {G : Type*} [Group G] [UniformSpace G] [IsUniformGroup 
G] : IsUniformGroup (SeparationQuotient G) where uniformContinuous_div
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeparationQuotient.uniformContinuous_dom₂`：uniformContinuous_dom₂ {f : S
eparationQuotient α × SeparationQuotient β -> γ} : UniformContinuous f ↔ Uniform
Continuous fun p : α × β => f (…
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `SeparationQuotient.uniformContinuous_mk`：uniformContinuous_mk : UniformC
ontinuous (mk : α -> SeparationQuotient α)
· 使用定理 `uniformContinuous_div`：uniformContinuous_div : UniformContinuous fun p :
 α × α => p.1 / p.2
-/
instance instIsUniformGroup {G : Type*} [Group G] [UniformSpace G] [IsUniformGroup G] :
    IsUniformGroup (SeparationQuotient G) where
  uniformContinuous_div := by
    rw [uniformContinuous_dom₂]
    exact uniformContinuous_mk.comp uniformContinuous_div

end IsUniformGroup

section MonoidWithZero

variable {M₀ : Type*} [TopologicalSpace M₀]

/-
**SeparationQuotient.instMulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuoti
ent`。
形式化陈述：instMulZeroClass [MulZeroClass M₀] [ContinuousMul M₀] : MulZeroClass (Sepa
rationQuotient M₀)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulZeroClass [MulZeroClass M₀] [ContinuousMul M₀] :
    MulZeroClass (SeparationQuotient M₀) :=
  fast_instance% surjective_mk.mulZeroClass mk mk_zero mk_mul
/-
**SeparationQuotient.instSemigroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Separation
Quotient`。
形式化陈述：instSemigroupWithZero [SemigroupWithZero M₀] [ContinuousMul M₀] : Semigrou
pWithZero (SeparationQuotient M₀)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroupWithZero [SemigroupWithZero M₀] [ContinuousMul M₀] :
    SemigroupWithZero (SeparationQuotient M₀) :=
  fast_instance% surjective_mk.semigroupWithZero mk mk_zero mk_mul
/-
**SeparationQuotient.instMulZeroOneClass** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQu
otient`。
形式化陈述：instMulZeroOneClass [MulZeroOneClass M₀] [ContinuousMul M₀] : MulZeroOneCl
ass (SeparationQuotient M₀)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulZeroOneClass [MulZeroOneClass M₀] [ContinuousMul M₀] :
    MulZeroOneClass (SeparationQuotient M₀) :=
  fast_instance% surjective_mk.mulZeroOneClass mk mk_zero mk_one mk_mul
/-
**SeparationQuotient.instMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuo
tient`。
形式化陈述：instMonoidWithZero [MonoidWithZero M₀] [ContinuousMul M₀] : MonoidWithZero
 (SeparationQuotient M₀)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidWithZero [MonoidWithZero M₀] [ContinuousMul M₀] :
    MonoidWithZero (SeparationQuotient M₀) :=
  fast_instance% surjective_mk.monoidWithZero mk mk_zero mk_one mk_mul mk_pow
/-
**SeparationQuotient.instCommMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Separatio
nQuotient`。
形式化陈述：instCommMonoidWithZero [CommMonoidWithZero M₀] [ContinuousMul M₀] : CommMo
noidWithZero (SeparationQuotient M₀)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoidWithZero [CommMonoidWithZero M₀] [ContinuousMul M₀] :
    CommMonoidWithZero (SeparationQuotient M₀) :=
  fast_instance% surjective_mk.commMonoidWithZero mk mk_zero mk_one mk_mul mk_pow

end MonoidWithZero

section Ring

variable {R : Type*} [TopologicalSpace R]

/-
**SeparationQuotient.instDistrib** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instDistrib [Distrib R] [ContinuousMul R] [ContinuousAdd R] : Distrib (Sep
arationQuotient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistrib [Distrib R] [ContinuousMul R] [ContinuousAdd R] :
    Distrib (SeparationQuotient R) :=
  fast_instance% surjective_mk.distrib mk mk_add mk_mul
/-
**SeparationQuotient.instLeftDistribClass** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQ
uotient`。
形式化陈述：instLeftDistribClass [Mul R] [Add R] [LeftDistribClass R] [ContinuousMul R
] [ContinuousAdd R] : LeftDistribClass (SeparationQuotient R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.leftDistribClass`：leftDistribClass [Mul R] [Add R] [
LeftDistribClass R] (add : forall x y, f (x + y) = f x + f y) (mul : forall x y,
 f (x * y) = f x * f y) : …
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
· 使用定理 `SeparationQuotient.mk_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] 
[inst_1 : Add M] [inst_2 : ContinuousAdd M] (a b : M),   SeparationQuotient.mk (
a + b) = Separa…
· 使用定理 `SeparationQuotient.mk_mul`：mk_mul [Mul M] [ContinuousMul M] (a b : M) : 
mk (a * b) = mk a * mk b
-/
instance instLeftDistribClass [Mul R] [Add R] [LeftDistribClass R]
    [ContinuousMul R] [ContinuousAdd R] :
    LeftDistribClass (SeparationQuotient R) :=
  surjective_mk.leftDistribClass mk mk_add mk_mul
/-
**SeparationQuotient.instRightDistribClass** 是 Mathlib 中的一个实例，位于命名空间 `Separation
Quotient`。
形式化陈述：instRightDistribClass [Mul R] [Add R] [RightDistribClass R] [ContinuousMul
 R] [ContinuousAdd R] : RightDistribClass (SeparationQuotient R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.rightDistribClass`：rightDistribClass [Mul R] [Add R]
 [RightDistribClass R] (add : forall x y, f (x + y) = f x + f y) (mul : forall x
 y, f (x * y) = f x * f y) …
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
· 使用定理 `SeparationQuotient.mk_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] 
[inst_1 : Add M] [inst_2 : ContinuousAdd M] (a b : M),   SeparationQuotient.mk (
a + b) = Separa…
· 使用定理 `SeparationQuotient.mk_mul`：mk_mul [Mul M] [ContinuousMul M] (a b : M) : 
mk (a * b) = mk a * mk b
-/
instance instRightDistribClass [Mul R] [Add R] [RightDistribClass R]
    [ContinuousMul R] [ContinuousAdd R] :
    RightDistribClass (SeparationQuotient R) :=
  surjective_mk.rightDistribClass mk mk_add mk_mul
/-
**SeparationQuotient.instNonUnitalnonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Se
parationQuotient`。
形式化陈述：instNonUnitalnonAssocSemiring [NonUnitalNonAssocSemiring R] [IsTopological
Semiring R] : NonUnitalNonAssocSemiring (SeparationQuotient R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
-/
instance instNonUnitalnonAssocSemiring [NonUnitalNonAssocSemiring R]
    [IsTopologicalSemiring R] : NonUnitalNonAssocSemiring (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalNonAssocSemiring mk mk_zero mk_add mk_mul mk_smul
/-
**SeparationQuotient.instIsTopologicalSemiring** 是 Mathlib 中的一个定理，位于命名空间 `Separa
tionQuotient`。
形式化陈述：∀ {R : Type u_1} [inst : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSe
miring R] [inst_2 : IsTopologicalSemiring R],   IsTopologicalSemiring (Separatio
nQuotient R)
参数：SeparationQuotient R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.instContinuousAdd`：∀ {M : Type u_1} [inst : Topologic
alSpace M] [inst_1 : Add M] [inst_2 : ContinuousAdd M],   ContinuousAdd (Separat
ionQuotient M)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
-/
instance instIsTopologicalSemiring [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring (SeparationQuotient R) where
/-
**SeparationQuotient.instNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Separation
Quotient`。
形式化陈述：instNonUnitalSemiring [NonUnitalSemiring R] [IsTopologicalSemiring R] : No
nUnitalSemiring (SeparationQuotient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalSemiring [NonUnitalSemiring R] [IsTopologicalSemiring R] :
    NonUnitalSemiring (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalSemiring mk mk_zero mk_add mk_mul mk_smul
/-
**SeparationQuotient.instNatCast** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instNatCast [NatCast R] : NatCast (SeparationQuotient R) where natCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNatCast [NatCast R] : NatCast (SeparationQuotient R) where
  natCast n := mk n

@[simp, norm_cast]
/-
**SeparationQuotient.mk_natCast** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：mk_natCast [NatCast R] (n : Nat) : mk (n : R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_natCast [NatCast R] (n : ℕ) : mk (n : R) = n := rfl

@[simp]
/-
**SeparationQuotient.mk_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：mk_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] : mk (ofNat(n) : R) = OfNat.
ofNat n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    mk (ofNat(n) : R) = OfNat.ofNat n :=
  rfl
/-
**SeparationQuotient.instIntCast** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instIntCast [IntCast R] : IntCast (SeparationQuotient R) where intCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIntCast [IntCast R] : IntCast (SeparationQuotient R) where
  intCast n := mk n

@[simp, norm_cast]
/-
**SeparationQuotient.mk_intCast** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：mk_intCast [IntCast R] (n : Int) : mk (n : R) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_intCast [IntCast R] (n : ℤ) : mk (n : R) = n := rfl
/-
**SeparationQuotient.instNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQ
uotient`。
形式化陈述：instNonAssocSemiring [NonAssocSemiring R] [IsTopologicalSemiring R] : NonA
ssocSemiring (SeparationQuotient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocSemiring [NonAssocSemiring R] [IsTopologicalSemiring R] :
    NonAssocSemiring (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonAssocSemiring mk mk_zero mk_one mk_add mk_mul mk_smul mk_natCast
/-
**SeparationQuotient.instNonUnitalNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `Separa
tionQuotient`。
形式化陈述：instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] [IsTopologicalRing R] 
: NonUnitalNonAssocRing (SeparationQuotient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] [IsTopologicalRing R] :
    NonUnitalNonAssocRing (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalNonAssocRing mk mk_zero mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul
/-
**SeparationQuotient.instIsTopologicalRing** 是 Mathlib 中的一个定理，位于命名空间 `Separation
Quotient`。
形式化陈述：∀ {R : Type u_1} [inst : TopologicalSpace R] [inst_1 : NonUnitalNonAssocRi
ng R] [inst_2 : IsTopologicalRing R],   IsTopologicalRing (SeparationQuotient R)
参数：SeparationQuotient R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.instIsTopologicalSemiring`：∀ {R : Type u_1} [inst : T
opologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [inst_2 : IsTopologica
lSemiring R],   IsTopologicalSemir…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `SeparationQuotient.instContinuousNeg`：∀ {G : Type u_1} [inst : Topologic
alSpace G] [inst_1 : Neg G] [inst_2 : ContinuousNeg G],   ContinuousNeg (Separat
ionQuotient G)
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
-/
instance instIsTopologicalRing [NonUnitalNonAssocRing R] [IsTopologicalRing R] :
    IsTopologicalRing (SeparationQuotient R) where
/-
**SeparationQuotient.instNonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuot
ient`。
形式化陈述：instNonUnitalRing [NonUnitalRing R] [IsTopologicalRing R] : NonUnitalRing 
(SeparationQuotient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalRing [NonUnitalRing R] [IsTopologicalRing R] :
    NonUnitalRing (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalRing mk mk_zero mk_add mk_mul mk_neg mk_sub mk_smul mk_smul
/-
**SeparationQuotient.instNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuoti
ent`。
形式化陈述：instNonAssocRing [NonAssocRing R] [IsTopologicalRing R] : NonAssocRing (Se
parationQuotient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocRing [NonAssocRing R] [IsTopologicalRing R] :
    NonAssocRing (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonAssocRing mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul mk_natCast mk_intCast
/-
**SeparationQuotient.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`
。
形式化陈述：instSemiring [Semiring R] [IsTopologicalSemiring R] : Semiring (Separation
Quotient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring [Semiring R] [IsTopologicalSemiring R] :
    Semiring (SeparationQuotient R) :=
  fast_instance% surjective_mk.semiring mk mk_zero mk_one mk_add mk_mul mk_smul mk_pow mk_natCast
/-
**SeparationQuotient.instRing** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instRing [Ring R] [IsTopologicalRing R] : Ring (SeparationQuotient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing [Ring R] [IsTopologicalRing R] :
    Ring (SeparationQuotient R) :=
  fast_instance% surjective_mk.ring mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub mk_smul
    mk_smul mk_pow mk_natCast mk_intCast
/-
**SeparationQuotient.instNonUnitalNonAssocCommSemiring** 是 Mathlib 中的一个实例，位于命名空间
 `SeparationQuotient`。
形式化陈述：instNonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring R] [IsTop
ologicalSemiring R] : NonUnitalNonAssocCommSemiring (SeparationQuotient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring R]
    [IsTopologicalSemiring R] :
    NonUnitalNonAssocCommSemiring (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalNonAssocCommSemiring mk mk_zero mk_add mk_mul mk_smul
/-
**SeparationQuotient.instNonUnitalCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Separa
tionQuotient`。
形式化陈述：instNonUnitalCommSemiring [NonUnitalCommSemiring R] [IsTopologicalSemiring
 R] : NonUnitalCommSemiring (SeparationQuotient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] [IsTopologicalSemiring R] :
    NonUnitalCommSemiring (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalCommSemiring mk mk_zero mk_add mk_mul mk_smul
/-
**SeparationQuotient.instCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuoti
ent`。
形式化陈述：instCommSemiring [CommSemiring R] [IsTopologicalSemiring R] : CommSemiring
 (SeparationQuotient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemiring [CommSemiring R] [IsTopologicalSemiring R] :
    CommSemiring (SeparationQuotient R) :=
  fast_instance% surjective_mk.commSemiring mk mk_zero mk_one mk_add mk_mul mk_smul
    mk_pow mk_natCast
/-
**SeparationQuotient.instHasDistribNeg** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuot
ient`。
形式化陈述：instHasDistribNeg [Mul R] [HasDistribNeg R] [ContinuousMul R] [ContinuousN
eg R] : HasDistribNeg (SeparationQuotient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHasDistribNeg [Mul R] [HasDistribNeg R] [ContinuousMul R] [ContinuousNeg R] :
    HasDistribNeg (SeparationQuotient R) :=
  fast_instance% surjective_mk.hasDistribNeg mk mk_neg mk_mul
/-
**SeparationQuotient.instNonUnitalNonAssocCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Se
parationQuotient`。
形式化陈述：instNonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing R] [IsTopological
Ring R] : NonUnitalNonAssocCommRing (SeparationQuotient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing R] [IsTopologicalRing R] :
    NonUnitalNonAssocCommRing (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalNonAssocCommRing mk mk_zero mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul
/-
**SeparationQuotient.instNonUnitalCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Separation
Quotient`。
形式化陈述：instNonUnitalCommRing [NonUnitalCommRing R] [IsTopologicalRing R] : NonUni
talCommRing (SeparationQuotient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalCommRing [NonUnitalCommRing R] [IsTopologicalRing R] :
    NonUnitalCommRing (SeparationQuotient R) :=
  fast_instance% surjective_mk.nonUnitalCommRing mk mk_zero mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul
/-
**SeparationQuotient.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`
。
形式化陈述：instCommRing [CommRing R] [IsTopologicalRing R] : CommRing (SeparationQuot
ient R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommRing [CommRing R] [IsTopologicalRing R] :
    CommRing (SeparationQuotient R) :=
  fast_instance% surjective_mk.commRing mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub
    mk_smul mk_smul mk_pow mk_natCast mk_intCast

/-- `SeparationQuotient.mk` as a `RingHom`. -/
@[simps]
/-
**SeparationQuotient.mkRingHom** 是 Mathlib 中的一个定义，位于命名空间 `SeparationQuotient`。
形式化陈述：mkRingHom [NonAssocSemiring R] [IsTopologicalSemiring R] : R ->+* Separati
onQuotient R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SeparationQuotient.mk` as a `RingHom`.
-/
def mkRingHom [NonAssocSemiring R] [IsTopologicalSemiring R] : R →+* SeparationQuotient R where
  toFun := mk
  map_one' := mk_one; map_zero' := mk_zero; map_add' := mk_add; map_mul' := mk_mul

end Ring

section DistribSMul

variable {M A : Type*} [TopologicalSpace A]

/-
**SeparationQuotient.instDistribSMul** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotie
nt`。
形式化陈述：instDistribSMul [AddZeroClass A] [DistribSMul M A] [ContinuousAdd A] [Cont
inuousConstSMul M A] : DistribSMul M (SeparationQuotient A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribSMul [AddZeroClass A] [DistribSMul M A]
    [ContinuousAdd A] [ContinuousConstSMul M A] :
    DistribSMul M (SeparationQuotient A) :=
  fast_instance% surjective_mk.distribSMul mkAddMonoidHom mk_smul
/-
**SeparationQuotient.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQ
uotient`。
形式化陈述：instDistribMulAction [Monoid M] [AddMonoid A] [DistribMulAction M A] [Cont
inuousAdd A] [ContinuousConstSMul M A] : DistribMulAction M (SeparationQuotient 
A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction [Monoid M] [AddMonoid A] [DistribMulAction M A]
    [ContinuousAdd A] [ContinuousConstSMul M A] :
    DistribMulAction M (SeparationQuotient A) :=
  fast_instance% surjective_mk.distribMulAction mkAddMonoidHom mk_smul
/-
**SeparationQuotient.instMulDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Separati
onQuotient`。
形式化陈述：instMulDistribMulAction [Monoid M] [Monoid A] [MulDistribMulAction M A] [C
ontinuousMul A] [ContinuousConstSMul M A] : MulDistribMulAction M (SeparationQuo
tient A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulDistribMulAction [Monoid M] [Monoid A] [MulDistribMulAction M A]
    [ContinuousMul A] [ContinuousConstSMul M A] :
    MulDistribMulAction M (SeparationQuotient A) :=
  fast_instance% surjective_mk.mulDistribMulAction mkMonoidHom mk_smul

end DistribSMul

section Module

variable {R S M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
    [Semiring S] [AddCommMonoid N] [Module S N]
    [TopologicalSpace N]

/-
**SeparationQuotient.instModule** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instModule : Module R (SeparationQuotient M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule : Module R (SeparationQuotient M) :=
  fast_instance% surjective_mk.module R mkAddMonoidHom mk_smul

variable (R M)

/-- `SeparationQuotient.mk` as a continuous linear map. -/
@[simps]
/-
**SeparationQuotient.mkCLM** 是 Mathlib 中的一个定义，位于命名空间 `SeparationQuotient`。
形式化陈述：mkCLM : M ->L[R] SeparationQuotient M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SeparationQuotient.mk` as a continuous linear map.
-/
def mkCLM : M →L[R] SeparationQuotient M where
  toFun := mk
  map_add' := mk_add
  map_smul' := mk_smul

variable {R M}

/-- The lift (as a continuous linear map) of `f` with `f x = f y` for `Inseparable x y`. -/
@[simps]
/-
**SeparationQuotient.liftCLM** 是 Mathlib 中的一个定义，位于命名空间 `SeparationQuotient`。
形式化陈述：liftCLM {σ : R ->+* S} (f : M ->SL[σ] N) (hf : forall x y, Inseparable x y
 -> f x = f y) : SeparationQuotient M ->SL[σ] N where toFun
参数：f : M ->SL[σ] N；hf : forall x y, Inseparable x y -> f x = f y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lift (as a continuous linear map) of `f` with `f x = f y` for `Inseparable x
 y`.
-/
noncomputable def liftCLM {σ : R →+* S} (f : M →SL[σ] N) (hf : ∀ x y, Inseparable x y → f x = f y) :
    SeparationQuotient M →SL[σ] N where
  toFun := SeparationQuotient.lift f hf
  map_add' := Quotient.ind₂ <| map_add f
  map_smul' {r} := Quotient.ind <| map_smulₛₗ f r
  cont := by fun_prop

@[simp]
/-
**SeparationQuotient.liftCLM_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：liftCLM_mk {σ : R ->+* S} (f : M ->SL[σ] N) (hf : forall x y, Inseparable 
x y -> f x = f y) (x : M) : liftCLM f hf (mk x) = f x
参数：f : M ->SL[σ] N；hf : forall x y, Inseparable x y -> f x = f y；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftCLM_mk {σ : R →+* S} (f : M →SL[σ] N) (hf : ∀ x y, Inseparable x y → f x = f y)
    (x : M) : liftCLM f hf (mk x) = f x := rfl

end Module

section Algebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [TopologicalSpace A] [IsTopologicalSemiring A] [ContinuousConstSMul R A]

/-
**SeparationQuotient.instAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instAlgebra : Algebra R (SeparationQuotient A) where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAlgebra : Algebra R (SeparationQuotient A) where
  algebraMap := mkRingHom.comp (algebraMap R A)
  commutes' r := Quotient.ind fun a => congrArg _ <| Algebra.commutes r a
  smul_def' r := Quotient.ind fun a => congrArg _ <| Algebra.smul_def r a

@[simp]
/-
**SeparationQuotient.mk_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient
`。
形式化陈述：mk_algebraMap (r : R) : mk (algebraMap R A r) = algebraMap R (SeparationQu
otient A) r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_algebraMap (r : R) : mk (algebraMap R A r) = algebraMap R (SeparationQuotient A) r :=
  rfl

end Algebra

end SeparationQuotient

