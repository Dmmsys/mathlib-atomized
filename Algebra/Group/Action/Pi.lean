/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Set.Piecewise

/-!
# Pi instances for multiplicative actions

This file defines instances for `MulAction` and related structures on `Pi` types.

## See also

* `Mathlib/Algebra/Group/Action/Option.lean`
* `Mathlib/Algebra/Group/Action/Prod.lean`
* `Mathlib/Algebra/Group/Action/Sigma.lean`
* `Mathlib/Algebra/Group/Action/Sum.lean`
-/

public section

assert_not_exists MonoidWithZero

variable {ι M N : Type*} {α β γ : ι → Type*} (i : ι)

namespace Pi

@[to_additive]
/-
**Pi.smul'** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：smul' [forall i, SMul (α i) (β i)] : SMul (forall i, α i) (forall i, β i) 
where smul s x i
参数：α i；β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smul' [∀ i, SMul (α i) (β i)] : SMul (∀ i, α i) (∀ i, β i) where smul s x i := s i • x i

@[to_additive (attr := push ←)]
/-
**Pi.smul_def'** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：smul_def' [forall i, SMul (α i) (β i)] (s : forall i, α i) (x : forall i, 
β i) : s • x = fun i => s i • x i
参数：α i；β i；s : forall i, α i；x : forall i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_def' [∀ i, SMul (α i) (β i)] (s : ∀ i, α i) (x : ∀ i, β i) : s • x = fun i ↦ s i • x i :=
  rfl

@[to_additive (attr := simp)]
/-
**Pi.smul_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：smul_apply' [forall i, SMul (α i) (β i)] (s : forall i, α i) (x : forall i
, β i) : (s • x) i = s i • x i
参数：α i；β i；s : forall i, α i；x : forall i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_apply' [∀ i, SMul (α i) (β i)] (s : ∀ i, α i) (x : ∀ i, β i) : (s • x) i = s i • x i :=
  rfl

@[to_additive]
/-
**Pi.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：isScalarTower [SMul M N] [forall i, SMul N (α i)] [forall i, SMul M (α i)]
 [forall i, IsScalarTower M N (α i)] : IsScalarTower M N (forall i, α i) where s
mul_assoc x y z
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower [SMul M N] [∀ i, SMul N (α i)] [∀ i, SMul M (α i)]
    [∀ i, IsScalarTower M N (α i)] : IsScalarTower M N (∀ i, α i) where
  smul_assoc x y z := funext fun i ↦ smul_assoc x y (z i)

@[to_additive]
/-
**Pi.isScalarTower'** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：isScalarTower' [forall i, SMul M (α i)] [forall i, SMul (α i) (β i)] [fora
ll i, SMul M (β i)] [forall i, IsScalarTower M (α i) (β i)] : IsScalarTower M (f
orall i, α i) (forall i, β i) where smul_assoc x y z
参数：α i；α i；β i；β i；α i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower' [∀ i, SMul M (α i)] [∀ i, SMul (α i) (β i)] [∀ i, SMul M (β i)]
    [∀ i, IsScalarTower M (α i) (β i)] : IsScalarTower M (∀ i, α i) (∀ i, β i) where
  smul_assoc x y z := funext fun i ↦ smul_assoc x (y i) (z i)

@[to_additive]
/-
**Pi.isScalarTower''** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：isScalarTower'' [forall i, SMul (α i) (β i)] [forall i, SMul (β i) (γ i)] 
[forall i, SMul (α i) (γ i)] [forall i, IsScalarTower (α i) (β i) (γ i)] : IsSca
larTower (forall i, α i) (forall i, β i) (forall i, γ i) where smul_assoc x y z
参数：α i；β i；β i；γ i；α i；γ i；α i；β i；γ i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower'' [∀ i, SMul (α i) (β i)] [∀ i, SMul (β i) (γ i)] [∀ i, SMul (α i) (γ i)]
    [∀ i, IsScalarTower (α i) (β i) (γ i)] : IsScalarTower (∀ i, α i) (∀ i, β i) (∀ i, γ i) where
  smul_assoc x y z := funext fun i ↦ smul_assoc (x i) (y i) (z i)

@[to_additive]
/-
**Pi.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：smulCommClass [forall i, SMul M (α i)] [forall i, SMul N (α i)] [forall i,
 SMulCommClass M N (α i)] : SMulCommClass M N (forall i, α i) where smul_comm x 
y z
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass [∀ i, SMul M (α i)] [∀ i, SMul N (α i)] [∀ i, SMulCommClass M N (α i)] :
    SMulCommClass M N (∀ i, α i) where
  smul_comm x y z := funext fun i ↦ smul_comm x y (z i)

@[to_additive]
/-
**Pi.smulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：smulCommClass' [forall i, SMul M (β i)] [forall i, SMul (α i) (β i)] [fora
ll i, SMulCommClass M (α i) (β i)] : SMulCommClass M (forall i, α i) (forall i, 
β i)
参数：β i；α i；β i；α i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass' [∀ i, SMul M (β i)] [∀ i, SMul (α i) (β i)]
    [∀ i, SMulCommClass M (α i) (β i)] : SMulCommClass M (∀ i, α i) (∀ i, β i) :=
  ⟨fun x y z => funext fun i ↦ smul_comm x (y i) (z i)⟩

@[to_additive]
/-
**Pi.smulCommClass''** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：smulCommClass'' [forall i, SMul (β i) (γ i)] [forall i, SMul (α i) (γ i)] 
[forall i, SMulCommClass (α i) (β i) (γ i)] : SMulCommClass (forall i, α i) (for
all i, β i) (forall i, γ i) where smul_comm x y z
参数：β i；γ i；α i；γ i；α i；β i；γ i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass'' [∀ i, SMul (β i) (γ i)] [∀ i, SMul (α i) (γ i)]
    [∀ i, SMulCommClass (α i) (β i) (γ i)] : SMulCommClass (∀ i, α i) (∀ i, β i) (∀ i, γ i) where
  smul_comm x y z := funext fun i ↦ smul_comm (x i) (y i) (z i)

@[to_additive]
/-
**Pi.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：isCentralScalar [forall i, SMul M (α i)] [forall i, SMul Mᵐᵒᵖ (α i)] [fora
ll i, IsCentralScalar M (α i)] : IsCentralScalar M (forall i, α i) where op_smul
_eq_smul _ _
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance isCentralScalar [∀ i, SMul M (α i)] [∀ i, SMul Mᵐᵒᵖ (α i)] [∀ i, IsCentralScalar M (α i)] :
    IsCentralScalar M (∀ i, α i) where
  op_smul_eq_smul _ _ := funext fun _ ↦ op_smul_eq_smul _ _

/-- If `α i` has a faithful scalar action for a given `i`, then so does `Π i, α i`. This is
not an instance as `i` cannot be inferred. -/
@[to_additive
/-- If `α i` has a faithful additive action for a given `i`, then
so does `Π i, α i`. This is not an instance as `i` cannot be inferred -/]
/-
**Pi.faithfulSMul_at** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：faithfulSMul_at [forall i, SMul M (α i)] [forall i, Nonempty (α i)] (i : ι
) [FaithfulSMul M (α i)] : FaithfulSMul M (forall i, α i) where eq_of_smul_eq_sm
ul h
参数：α i；α i；i : ι；α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
lemma faithfulSMul_at [∀ i, SMul M (α i)] [∀ i, Nonempty (α i)] (i : ι) [FaithfulSMul M (α i)] :
    FaithfulSMul M (∀ i, α i) where
  eq_of_smul_eq_smul h := eq_of_smul_eq_smul fun a : α i => by
    classical
    simpa using
      congr_fun (h <| Function.update (fun j => Classical.choice (‹∀ i, Nonempty (α i)› j)) i a) i

@[to_additive]
/-
**Pi.faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：faithfulSMul [Nonempty ι] [forall i, SMul M (α i)] [forall i, Nonempty (α 
i)] [forall i, FaithfulSMul M (α i)] : FaithfulSMul M (forall i, α i)
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.faithfulSMul_at`：faithfulSMul_at [forall i, SMul M (α i)] [forall i, 
Nonempty (α i)] (i : ι) [FaithfulSMul M (α i)] : FaithfulSMul M (forall i, α i) 
where eq…
-/
instance faithfulSMul [Nonempty ι] [∀ i, SMul M (α i)] [∀ i, Nonempty (α i)]
    [∀ i, FaithfulSMul M (α i)] : FaithfulSMul M (∀ i, α i) :=
  let ⟨i⟩ := ‹Nonempty ι›
  faithfulSMul_at i

@[to_additive]
/-
**Pi.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：mulAction (M) {m : Monoid M} [forall i, MulAction M (α i)] : @MulAction M 
(forall i, α i) m where mul_smul _ _ _
参数：M；α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction (M) {m : Monoid M} [∀ i, MulAction M (α i)] : @MulAction M (∀ i, α i) m where
  mul_smul _ _ _ := funext fun _ ↦ mul_smul _ _ _
  one_smul _ := funext fun _ ↦ one_smul _ _

@[to_additive]
/-
**Pi.mulAction'** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：mulAction' {m : forall i, Monoid (α i)} [forall i, MulAction (α i) (β i)] 
: @MulAction (forall i, α i) (forall i, β i) (@Pi.monoid ι α m) where mul_smul _
 _ _
参数：α i；α i；β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction' {m : ∀ i, Monoid (α i)} [∀ i, MulAction (α i) (β i)] :
    @MulAction (∀ i, α i) (∀ i, β i)
      (@Pi.monoid ι α m) where
  mul_smul _ _ _ := funext fun _ ↦ mul_smul _ _ _
  one_smul _ := funext fun _ ↦ one_smul _ _

end Pi

namespace Function

/-- Non-dependent version of `Pi.smul`. Lean gets confused by the dependent instance if this
is not present. -/
@[to_additive
/-- Non-dependent version of `Pi.vadd`. Lean gets confused by the dependent instance
if this is not present. -/]
/-
**Function.hasSMul** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
形式化陈述：hasSMul {α : Type*} [SMul M α] : SMul M (ι -> α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasSMul {α : Type*} [SMul M α] : SMul M (ι → α) := Pi.instSMul

/-- Non-dependent version of `Pi.smulCommClass`. Lean gets confused by the dependent instance if
this is not present. -/
@[to_additive
  /-- Non-dependent version of `Pi.vaddCommClass`. Lean gets confused by the dependent
/-
**Function.if** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
  instance if this is not present. -/]
/-
**Function.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
形式化陈述：smulCommClass {α : Type*} [SMul M α] [SMul N α] [SMulCommClass M N α] : SM
ulCommClass M N (ι -> α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulCommClass {α : Type*} [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M N (ι → α) := Pi.smulCommClass

@[to_additive]
/-
**Function.update_smul** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：update_smul [forall i, SMul M (α i)] [DecidableEq ι] (c : M) (f₁ : forall 
i, α i) (i : ι) (x₁ : α i) : update (c • f₁) i (c • x₁) = c • update f₁ i x₁
参数：α i；c : M；f₁ : forall i, α i；i : ι；x₁ : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.apply_update`：apply_update {ι : Sort*} [DecidableEq ι] {α β : ι
 -> Sort*} (f : forall i, α i -> β i) (g : forall i, α i) (i : ι) (v : α i) (j :
 ι) : f j (…
-/
lemma update_smul [∀ i, SMul M (α i)] [DecidableEq ι] (c : M) (f₁ : ∀ i, α i)
    (i : ι) (x₁ : α i) : update (c • f₁) i (c • x₁) = c • update f₁ i x₁ :=
  funext fun j => (apply_update (β := α) (fun _ ↦ (c • ·)) f₁ i x₁ j).symm

@[to_additive]
/-
**Function.extend_smul** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：extend_smul {M α β : Type*} [SMul M β] (r : M) (f : ι -> α) (g : ι -> β) (
e : α -> β) : extend f (r • g) (r • e) = r • extend f g e
参数：r : M；f : ι -> α；g : ι -> β；e : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.extend_def`：extend_def (f : α -> β) (g : α -> γ) (e' : β -> γ) 
(b : β) [Decidable (exists a, f a = b)] : extend f g e' b = if h : exists a, f a
 = b then…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma extend_smul {M α β : Type*} [SMul M β] (r : M) (f : ι → α) (g : ι → β) (e : α → β) :
    extend f (r • g) (r • e) = r • extend f g e := by
  funext x
  classical
  simp only [extend_def, Pi.smul_apply]
  split_ifs <;> rfl

end Function

namespace Set

@[to_additive]
/-
**Set.piecewise_smul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：piecewise_smul [forall i, SMul M (α i)] (s : Set ι) [forall i, Decidable (
i in s)] (c : M) (f₁ g₁ : forall i, α i) : s.piecewise (c • f₁) (c • g₁) = c • s
.piecewise f₁ g₁
参数：α i；s : Set ι；i in s；c : M；f₁ g₁ : forall i, α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piecewise_op`：piecewise_op {δ' : α -> Sort*} (h : forall i, δ i -> δ
' i) : (s.piecewise (fun x => h x (f x)) fun x => h x (g x)) = fun x => h x (s.p
iecewi…
-/
lemma piecewise_smul [∀ i, SMul M (α i)] (s : Set ι) [∀ i, Decidable (i ∈ s)]
    (c : M) (f₁ g₁ : ∀ i, α i) : s.piecewise (c • f₁) (c • g₁) = c • s.piecewise f₁ g₁ :=
  s.piecewise_op (δ' := α) f₁ _ fun _ ↦ (c • ·)

end Set

