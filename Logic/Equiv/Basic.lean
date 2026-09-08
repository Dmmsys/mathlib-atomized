/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Logic.Equiv.Option
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Tactic.Lift
public import Mathlib.Data.Int.Notation

/-!
# Equivalence between types

In this file we continue the work on equivalences begun in `Mathlib/Logic/Equiv/Defs.lean`, defining
a lot of equivalences between various types and operations on these equivalences.

More definitions of this kind can be found in other files.
E.g., `Mathlib/Algebra/Group/TransferInstance.lean` does it for `Group`,
`Mathlib/Algebra/Module/TransferInstance.lean` does it for `Module`, and similar files exist for
other algebraic type classes.

## Tags

equivalence, congruence, bijective map
-/

@[expose] public section

universe u v w z

open Function

-- Unless required to be `Type*`, all variables in this file are `Sort*`
variable {α α₁ α₂ β β₁ β₂ γ δ : Sort*}

namespace Equiv

/-- The product over `Option α` of `β a` is the binary product of the
product over `α` of `β (some α)` and `β none` -/
@[simps]
/-
**Equiv.piOptionEquivProd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piOptionEquivProd {α} {β : Option α -> Type*} : (forall a : Option α, β a)
 ≃ β none × forall a : α, β (some a) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product over `Option α` of `β a` is the binary product of the
product over `α` of `β (some α)` and `β none`
-/
def piOptionEquivProd {α} {β : Option α → Type*} :
    (∀ a : Option α, β a) ≃ β none × ∀ a : α, β (some a) where
  toFun f := (f none, fun a => f (some a))
  invFun x a := Option.casesOn a x.fst x.snd
  left_inv f := funext fun a => by cases a <;> rfl

section subtypeCongr

/-- Combines an `Equiv` between two subtypes with an `Equiv` between their complements to form a
  permutation. -/
/-
**Equiv.subtypeCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeCongr {α} {p q : α -> Prop} [DecidablePred p] [DecidablePred q] (e 
: { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x }) : Perm α
参数：e : { x // p x } ≃ { x // q x }；f : { x // ¬p x } ≃ { x // ¬q x }。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Combines an `Equiv` between two subtypes with an `Equiv` between their complemen
ts to form a
  permutation.
-/
def subtypeCongr {α} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x }) : Perm α :=
  (sumCompl p).symm.trans ((sumCongr e f).trans (sumCompl q))

variable {ε : Type*} {p : ε → Prop} [DecidablePred p]
variable (ep ep' : Perm { a // p a }) (en en' : Perm { a // ¬p a })

/-- Combining permutations on `ε` that permute only inside or outside the subtype
split induced by `p : ε → Prop` constructs a permutation on `ε`. -/
/-
**Equiv.Perm.subtypeCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：{ε : Type u_9} → {p : ε → Prop} → [DecidablePred p] → Equiv.Perm { a // p 
a } → Equiv.Perm { a // ¬p a } → Equiv.Perm ε
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combining permutations on `ε` that permute only inside or outside the subtype
split induced by `p : ε → Prop` constructs a permutation on `ε`.
-/
def Perm.subtypeCongr : Equiv.Perm ε :=
  permCongr (sumCompl p) (sumCongr ep en)
/-
**Equiv.Perm.subtypeCongr.apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.subtypeCon
gr`。
形式化陈述：∀ {ε : Type u_9} {p : ε → Prop} [inst : DecidablePred p] (ep : Equiv.Perm 
{ a // p a }) (en : Equiv.Perm { a // ¬p a })   (a : ε), (ep.subtypeCongr en) a 
= if h : p a then ↑(ep ⟨a, h⟩) else ↑(en ⟨a, h⟩)
参数：ep : Equiv.Perm { a // p a }；en : Equiv.Perm { a // ¬p a }；a : ε；ep.subtypeCo
ngr en。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.sumCompl_symm_apply_of_pos`：sumCompl_symm_apply_of_pos {α} {p : α 
-> Prop} [DecidablePred p] {a : α} (h : p a) : (sumCompl p).symm a = Sum.inl ⟨a,
 h⟩
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `Equiv.sumCompl_symm_apply_of_neg`：sumCompl_symm_apply_of_neg {α} {p : α 
-> Prop} [DecidablePred p] {a : α} (h : ¬p a) : (sumCompl p).symm a = Sum.inr ⟨a
, h⟩
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
theorem Perm.subtypeCongr.apply (a : ε) : ep.subtypeCongr en a =
    if h : p a then (ep ⟨a, h⟩ : ε) else en ⟨a, h⟩ := by
  by_cases h : p a <;> simp [Perm.subtypeCongr, h]

@[simp]
/-
**Equiv.Perm.subtypeCongr.left_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.subty
peCongr`。
形式化陈述：∀ {ε : Type u_9} {p : ε → Prop} [inst : DecidablePred p] (ep : Equiv.Perm 
{ a // p a }) (en : Equiv.Perm { a // ¬p a })   {a : ε} (h : p a), (ep.subtypeCo
ngr en) a = ↑(ep ⟨a, h⟩)
参数：ep : Equiv.Perm { a // p a }；en : Equiv.Perm { a // ¬p a }；h : p a；ep.subtype
Congr en；ep ⟨a, h⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.subtypeCongr.apply`：∀ {ε : Type u_9} {p : ε → Prop} [inst : D
ecidablePred p] (ep : Equiv.Perm { a // p a }) (en : Equiv.Perm { a // ¬p a })  
 (a : ε), (ep.subty…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Perm.subtypeCongr.left_apply {a : ε} (h : p a) : ep.subtypeCongr en a = ep ⟨a, h⟩ := by
  simp [Perm.subtypeCongr.apply, h]

@[simp]
/-
**Equiv.Perm.subtypeCongr.left_apply_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Pe
rm.subtypeCongr`。
形式化陈述：∀ {ε : Type u_9} {p : ε → Prop} [inst : DecidablePred p] (ep : Equiv.Perm 
{ a // p a }) (en : Equiv.Perm { a // ¬p a })   (a : { a // p a }), (ep.subtypeC
ongr en) ↑a = ↑(ep a)
参数：ep : Equiv.Perm { a // p a }；en : Equiv.Perm { a // ¬p a }；a : { a // p a }；e
p.subtypeCongr en；ep a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.subtypeCongr.left_apply`：∀ {ε : Type u_9} {p : ε → Prop} [ins
t : DecidablePred p] (ep : Equiv.Perm { a // p a }) (en : Equiv.Perm { a // ¬p a
 })   {a : ε} (h : p a),…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Perm.subtypeCongr.left_apply_subtype (a : { a // p a }) : ep.subtypeCongr en a = ep a :=
    Perm.subtypeCongr.left_apply ep en a.property

@[simp]
/-
**Equiv.Perm.subtypeCongr.right_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.subt
ypeCongr`。
形式化陈述：∀ {ε : Type u_9} {p : ε → Prop} [inst : DecidablePred p] (ep : Equiv.Perm 
{ a // p a }) (en : Equiv.Perm { a // ¬p a })   {a : ε} (h : ¬p a), (ep.subtypeC
ongr en) a = ↑(en ⟨a, h⟩)
参数：ep : Equiv.Perm { a // p a }；en : Equiv.Perm { a // ¬p a }；h : ¬p a；ep.subtyp
eCongr en；en ⟨a, h⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.subtypeCongr.apply`：∀ {ε : Type u_9} {p : ε → Prop} [inst : D
ecidablePred p] (ep : Equiv.Perm { a // p a }) (en : Equiv.Perm { a // ¬p a })  
 (a : ε), (ep.subty…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Perm.subtypeCongr.right_apply {a : ε} (h : ¬p a) : ep.subtypeCongr en a = en ⟨a, h⟩ := by
  simp [Perm.subtypeCongr.apply, h]

@[simp]
/-
**Equiv.Perm.subtypeCongr.right_apply_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.P
erm.subtypeCongr`。
形式化陈述：∀ {ε : Type u_9} {p : ε → Prop} [inst : DecidablePred p] (ep : Equiv.Perm 
{ a // p a }) (en : Equiv.Perm { a // ¬p a })   (a : { a // ¬p a }), (ep.subtype
Congr en) ↑a = ↑(en a)
参数：ep : Equiv.Perm { a // p a }；en : Equiv.Perm { a // ¬p a }；a : { a // ¬p a }；
ep.subtypeCongr en；en a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.subtypeCongr.right_apply`：∀ {ε : Type u_9} {p : ε → Prop} [in
st : DecidablePred p] (ep : Equiv.Perm { a // p a }) (en : Equiv.Perm { a // ¬p 
a })   {a : ε} (h : ¬p a)…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Perm.subtypeCongr.right_apply_subtype (a : { a // ¬p a }) : ep.subtypeCongr en a = en a :=
  Perm.subtypeCongr.right_apply ep en a.property

@[simp]
/-
**Equiv.Perm.subtypeCongr.refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.subtypeCong
r`。
形式化陈述：∀ {ε : Type u_9} {p : ε → Prop} [inst : DecidablePred p],   Equiv.Perm.sub
typeCongr (Equiv.refl { a // p a }) (Equiv.refl { a // ¬p a }) = Equiv.refl ε
参数：Equiv.refl { a // p a }；Equiv.refl { a // ¬p a }。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.subtypeCongr.left_apply`：∀ {ε : Type u_9} {p : ε → Prop} [ins
t : DecidablePred p] (ep : Equiv.Perm { a // p a }) (en : Equiv.Perm { a // ¬p a
 })   {a : ε} (h : p a),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.subtypeCongr.right_apply`：∀ {ε : Type u_9} {p : ε → Prop} [in
st : DecidablePred p] (ep : Equiv.Perm { a // p a }) (en : Equiv.Perm { a // ¬p 
a })   {a : ε} (h : ¬p a)…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Perm.subtypeCongr.refl :
    Perm.subtypeCongr (Equiv.refl { a // p a }) (Equiv.refl { a // ¬p a }) = Equiv.refl ε := by
  ext x
  by_cases h : p x <;> simp [h]

@[simp]
/-
**Equiv.Perm.subtypeCongr.symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.subtypeCong
r`。
形式化陈述：∀ {ε : Type u_9} {p : ε → Prop} [inst : DecidablePred p] (ep : Equiv.Perm 
{ a // p a }) (en : Equiv.Perm { a // ¬p a }),   Equiv.symm (ep.subtypeCongr en)
 = Equiv.Perm.subtypeCongr (Equiv.symm ep) (Equiv.symm en)
参数：ep : Equiv.Perm { a // p a }；en : Equiv.Perm { a // ¬p a }；ep.subtypeCongr en
；Equiv.symm ep；Equiv.symm en。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Perm.subtypeCongr.symm : (ep.subtypeCongr en).symm = Perm.subtypeCongr ep.symm en.symm :=
  rfl

@[simp]
/-
**Equiv.Perm.subtypeCongr.trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.subtypeCon
gr`。
形式化陈述：∀ {ε : Type u_9} {p : ε → Prop} [inst : DecidablePred p] (ep ep' : Equiv.P
erm { a // p a })   (en en' : Equiv.Perm { a // ¬p a }),   Equiv.trans (ep.subty
peCongr en) (ep'.subtypeCongr en') =     Equiv.Perm.subtypeCongr (Equiv.trans ep
 ep') (Equiv.trans en en')
参数：ep ep' : Equiv.Perm { a // p a }；en en' : Equiv.Perm { a // ¬p a }；ep.subtype
Congr en；ep'.subtypeCongr en'；Equiv.trans ep ep'；Equiv.trans en en'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Perm.subtypeCongr.trans :
    (ep.subtypeCongr en).trans (ep'.subtypeCongr en')
    = Perm.subtypeCongr (ep.trans ep') (en.trans en') := by
  grind [eq_def, coe_trans]

end subtypeCongr

section subtypePreimage

variable (p : α → Prop) [DecidablePred p] (x₀ : { a // p a } → β)

/-- For a fixed function `x₀ : {a // p a} → β` defined on a subtype of `α`,
the subtype of functions `x : α → β` that agree with `x₀` on the subtype `{a // p a}`
is naturally equivalent to the type of functions `{a // ¬ p a} → β`. -/
@[simps]
/-
**Equiv.subtypePreimage** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypePreimage : { x : α -> β // x ∘ Subtype.val = x₀ } ≃ ({ a // ¬p a } 
-> β) where toFun (x : { x : α -> β // x ∘ Subtype.val = x₀ }) a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a fixed function `x₀ : {a // p a} → β` defined on a subtype of `α`,
the subtype of functions `x : α → β` that agree with `x₀` on the subtype `{a // 
p a}`
is naturally equivalent to the type of functions `{a // ¬ p a} → β`.
-/
def subtypePreimage : { x : α → β // x ∘ Subtype.val = x₀ } ≃ ({ a // ¬p a } → β) where
  toFun (x : { x : α → β // x ∘ Subtype.val = x₀ }) a := (x : α → β) a
  invFun x := ⟨fun a => if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩, funext fun ⟨_, h⟩ => dif_pos h⟩
  left_inv := fun ⟨x, hx⟩ =>
    Subtype.val_injective <|
      funext fun a => by
        dsimp only
        split_ifs
        · rw [← hx]; rfl
        · rfl
  right_inv x :=
    funext fun ⟨a, h⟩ =>
      show dite (p a) _ _ = _ by
        dsimp only
        rw [dif_neg h]
/-
**Equiv.subtypePreimage_symm_apply_coe_pos** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：subtypePreimage_symm_apply_coe_pos (x : { a // ¬p a } -> β) (a : α) (h : p
 a) : ((subtypePreimage p x₀).symm x : α -> β) a = x₀ ⟨a, h⟩
参数：x : { a // ¬p a } -> β；a : α；h : p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem subtypePreimage_symm_apply_coe_pos (x : { a // ¬p a } → β) (a : α) (h : p a) :
    ((subtypePreimage p x₀).symm x : α → β) a = x₀ ⟨a, h⟩ :=
  dif_pos h
/-
**Equiv.subtypePreimage_symm_apply_coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：subtypePreimage_symm_apply_coe_neg (x : { a // ¬p a } -> β) (a : α) (h : ¬
p a) : ((subtypePreimage p x₀).symm x : α -> β) a = x ⟨a, h⟩
参数：x : { a // ¬p a } -> β；a : α；h : ¬p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem subtypePreimage_symm_apply_coe_neg (x : { a // ¬p a } → β) (a : α) (h : ¬p a) :
    ((subtypePreimage p x₀).symm x : α → β) a = x ⟨a, h⟩ :=
  dif_neg h

end subtypePreimage

section

/-- A family of equivalences `∀ a, β₁ a ≃ β₂ a` generates an equivalence between `∀ a, β₁ a` and
`∀ a, β₂ a`. -/
@[simps (attr := grind =)]
/-
**Equiv.piCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piCongrRight {β₁ β₂ : α -> Sort*} (F : forall a, β₁ a ≃ β₂ a) : (forall a,
 β₁ a) ≃ (forall a, β₂ a)
参数：F : forall a, β₁ a ≃ β₂ a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A family of equivalences `∀ a, β₁ a ≃ β₂ a` generates an equivalence between `∀ 
a, β₁ a` and
`∀ a, β₂ a`.
-/
def piCongrRight {β₁ β₂ : α → Sort*} (F : ∀ a, β₁ a ≃ β₂ a) : (∀ a, β₁ a) ≃ (∀ a, β₂ a) :=
  ⟨Pi.map fun a ↦ F a, Pi.map fun a ↦ (F a).symm, fun H => funext <| by simp,
    fun H => funext <| by simp⟩

@[simp]
/-
**Equiv.piCongrRight_refl** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：piCongrRight_refl {β : α -> Sort*} : piCongrRight (fun a => .refl (β a)) =
 .refl (forall a, β a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
lemma piCongrRight_refl {β : α → Sort*} : piCongrRight (fun a ↦ .refl (β a)) = .refl (∀ a, β a) :=
  rfl

/-- Given `φ : α → β → Sort*`, we have an equivalence between `∀ a b, φ a b` and `∀ b a, φ a b`.
This is `Function.swap` as an `Equiv`. -/
@[simps apply]
/-
**Equiv.piComm** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piComm (φ : α -> β -> Sort*) : (forall a b, φ a b) ≃ forall b a, φ a b
参数：φ : α -> β -> Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `φ : α → β → Sort*`, we have an equivalence between `∀ a b, φ a b` and `∀ 
b a, φ a b`.
This is `Function.swap` as an `Equiv`.
-/
def piComm (φ : α → β → Sort*) : (∀ a b, φ a b) ≃ ∀ b a, φ a b :=
  ⟨swap, swap, fun _ => rfl, fun _ => rfl⟩

@[simp]
/-
**Equiv.piComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：piComm_symm {φ : α -> β -> Sort*} : (piComm φ).symm = (piComm <| swap φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem piComm_symm {φ : α → β → Sort*} : (piComm φ).symm = (piComm <| swap φ) :=
  rfl

/-- Dependent `curry` equivalence: the type of dependent functions on `Σ i, β i` is equivalent
to the type of dependent functions of two arguments (i.e., functions to the space of functions).

This is `Sigma.curry` and `Sigma.uncurry` together as an equiv. -/
/-
**Equiv.piCurry** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piCurry {α} {β : α -> Type*} (γ : forall a, β a -> Type*) : (forall x : Σ 
i, β i, γ x.1 x.2) ≃ forall a b, γ a b where toFun
参数：γ : forall a, β a -> Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.curry_uncurry`：Sigma.curry_uncurry {γ : forall a, β a -> Type*} (f
 : forall (x) (y : β x), γ x y) : Sigma.curry (Sigma.uncurry f) = f

--- 原说明 ---
Dependent `curry` equivalence: the type of dependent functions on `Σ i, β i` is 
equivalent
to the type of dependent functions of two arguments (i.e., functions to the spac
e of functions).

This is `Sigma.curry` and `Sigma.uncurry` together as an equiv.
-/
def piCurry {α} {β : α → Type*} (γ : ∀ a, β a → Type*) :
    (∀ x : Σ i, β i, γ x.1 x.2) ≃ ∀ a b, γ a b where
  toFun := Sigma.curry
  invFun := Sigma.uncurry
  left_inv := Sigma.uncurry_curry
  right_inv := Sigma.curry_uncurry

-- `simps` overapplies these but `simps -fullyApplied` under-applies them
/-
**Equiv.piCurry_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_11} {β : α → Type u_9} (γ : (a : α) → β a → Type u_10) (f : 
(x : (i : α) × β i) → γ x.fst x.snd),   (Equiv.piCurry γ) f = Sigma.curry f
参数：γ : (a : α) → β a → Type u_10；f : (x : (i : α) × β i) → γ x.fst x.snd；Equiv.p
iCurry γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem piCurry_apply {α} {β : α → Type*} (γ : ∀ a, β a → Type*)
    (f : ∀ x : Σ i, β i, γ x.1 x.2) :
    piCurry γ f = Sigma.curry f :=
  rfl
/-
**Equiv.piCurry_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_11} {β : α → Type u_9} (γ : (a : α) → β a → Type u_10) (f : 
(a : α) → (b : β a) → γ a b),   (Equiv.piCurry γ).symm f = Sigma.uncurry f
参数：γ : (a : α) → β a → Type u_10；f : (a : α) → (b : β a) → γ a b；Equiv.piCurry γ
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem piCurry_symm_apply {α} {β : α → Type*} (γ : ∀ a, β a → Type*) (f : ∀ a b, γ a b) :
    (piCurry γ).symm f = Sigma.uncurry f :=
  rfl

end

section prodCongr

variable {α₁ α₂ β₁ β₂ : Type*} (e : α₁ → β₁ ≃ β₂)

-- See also `Equiv.ofPreimageEquiv`.
/-- A family of equivalences between fibers gives an equivalence between domains. -/
@[simps!]
/-
**Equiv.ofFiberEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：ofFiberEquiv {α β γ} {f : α -> γ} {g : β -> γ} (e : forall c, { a // f a =
 c } ≃ { b // g b = c }) : α ≃ β
参数：e : forall c, { a // f a = c } ≃ { b // g b = c }。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A family of equivalences between fibers gives an equivalence between domains.
-/
def ofFiberEquiv {α β γ} {f : α → γ} {g : β → γ}
    (e : ∀ c, { a // f a = c } ≃ { b // g b = c }) : α ≃ β :=
  (sigmaFiberEquiv f).symm.trans <| (Equiv.sigmaCongrRight e).trans (sigmaFiberEquiv g)
/-
**Equiv.ofFiberEquiv_map** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：ofFiberEquiv_map {α β γ} {f : α -> γ} {g : β -> γ} (e : forall c, { a // f
 a = c } ≃ { b // g b = c }) (a : α) : g (ofFiberEquiv e a) = f a
参数：e : forall c, { a // f a = c } ≃ { b // g b = c }；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem ofFiberEquiv_map {α β γ} {f : α → γ} {g : β → γ}
    (e : ∀ c, { a // f a = c } ≃ { b // g b = c }) (a : α) : g (ofFiberEquiv e a) = f a :=
  (_ : { b // g b = _ }).property

end prodCongr

section

open Sum

/-- An equivalence that separates out the 0th fiber of `(Σ (n : ℕ), f n)`. -/
/-
**Equiv.sigmaNatSucc** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaNatSucc (f : Nat -> Type u) : (Σ n, f n) ≃ f 0 oplus Σ n, f (n + 1)
参数：f : Nat -> Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence that separates out the 0th fiber of `(Σ (n : ℕ), f n)`.
-/
def sigmaNatSucc (f : ℕ → Type u) : (Σ n, f n) ≃ f 0 ⊕ Σ n, f (n + 1) :=
  ⟨fun x =>
    @Sigma.casesOn ℕ f (fun _ => f 0 ⊕ Σ n, f (n + 1)) x fun n =>
      @Nat.casesOn (fun i => f i → f 0 ⊕ Σ n : ℕ, f (n + 1)) n (fun x : f 0 => Sum.inl x)
        fun (n : ℕ) (x : f n.succ) => Sum.inr ⟨n, x⟩,
    Sum.elim (Sigma.mk 0) (Sigma.map Nat.succ fun _ => id), by rintro ⟨n | n, x⟩ <;> rfl, by
    rintro (x | ⟨n, x⟩) <;> rfl⟩

end

section

open Sum Nat

/-- The set of natural numbers is equivalent to `ℕ ⊕ PUnit`. -/
/-
**Equiv.natEquivNatSumPUnit** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：natEquivNatSumPUnit : Nat ≃ Nat oplus PUnit where toFun n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of natural numbers is equivalent to `ℕ ⊕ PUnit`.
-/
def natEquivNatSumPUnit : ℕ ≃ ℕ ⊕ PUnit where
  toFun n := Nat.casesOn n (inr PUnit.unit) inl
  invFun := Sum.elim Nat.succ fun _ => 0
  left_inv n := by cases n <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

/-- `ℕ ⊕ PUnit` is equivalent to `ℕ`. -/
/-
**Equiv.natSumPUnitEquivNat** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：natSumPUnitEquivNat : Nat oplus PUnit ≃ Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`ℕ ⊕ PUnit` is equivalent to `ℕ`.
-/
def natSumPUnitEquivNat : ℕ ⊕ PUnit ≃ ℕ :=
  natEquivNatSumPUnit.symm

/-- The type of integer numbers is equivalent to `ℕ ⊕ ℕ`. -/
/-
**Equiv.intEquivNatSumNat** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：intEquivNatSumNat : Int ≃ Nat oplus Nat where toFun z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of integer numbers is equivalent to `ℕ ⊕ ℕ`.
-/
def intEquivNatSumNat : ℤ ≃ ℕ ⊕ ℕ where
  toFun z := Int.casesOn z inl inr
  invFun := Sum.elim Int.ofNat Int.negSucc
  left_inv := by rintro (m | n) <;> rfl
  right_inv := by rintro (m | n) <;> rfl

end

/-- If `α` is equivalent to `β`, then `Unique α` is equivalent to `Unique β`. -/
/-
**Equiv.uniqueCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：uniqueCongr (e : α ≃ β) : Unique α ≃ Unique β where toFun h
参数：e : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α` is equivalent to `β`, then `Unique α` is equivalent to `Unique β`.
-/
def uniqueCongr (e : α ≃ β) : Unique α ≃ Unique β where
  toFun h := @Equiv.unique _ _ h e.symm
  invFun h := @Equiv.unique _ _ h e
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- If `α` is equivalent to `β`, then `IsEmpty α` is equivalent to `IsEmpty β`. -/
/-
**Equiv.isEmpty_congr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：isEmpty_congr (e : α ≃ β) : IsEmpty α ↔ IsEmpty β
参数：e : α ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α` is equivalent to `β`, then `IsEmpty α` is equivalent to `IsEmpty β`.
-/
theorem isEmpty_congr (e : α ≃ β) : IsEmpty α ↔ IsEmpty β :=
  ⟨fun h => @Function.isEmpty _ _ h e.symm, fun h => @Function.isEmpty _ _ h e⟩
/-
**Equiv.isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_4} (e : α ≃ β) [IsEmpty β], IsEmpty α
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.isEmpty_congr`：isEmpty_congr (e : α ≃ β) : IsEmpty α ↔ IsEmpty β
-/
protected theorem isEmpty (e : α ≃ β) [IsEmpty β] : IsEmpty α :=
  e.isEmpty_congr.mpr ‹_›

section

open Subtype

/-- If `α` is equivalent to `β` and the predicates `p : α → Prop` and `q : β → Prop` are equivalent
at corresponding points, then `{a // p a}` is equivalent to `{b // q b}`.
For the statement where `α = β`, that is, `e : perm α`, see `Perm.subtypePerm`. -/
@[simps apply]
/-
**Equiv.subtypeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeEquiv {p : α -> Prop} {q : β -> Prop} (e : α ≃ β) (h : forall a, p 
a ↔ q (e a)) : { a : α // p a } ≃ { b : β // q b } where toFun a
参数：e : α ≃ β；h : forall a, p a ↔ q (e a)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α` is equivalent to `β` and the predicates `p : α → Prop` and `q : β → Prop`
 are equivalent
at corresponding points, then `{a // p a}` is equivalent to `{b // q b}`.
For the statement where `α = β`, that is, `e : perm α`, see `Perm.subtypePerm`.
-/
def subtypeEquiv {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a, p a ↔ q (e a)) :
    { a : α // p a } ≃ { b : β // q b } where
  toFun a := ⟨e a, (h _).mp a.property⟩
  invFun b := ⟨e.symm b, (h _).mpr ((e.apply_symm_apply b).symm ▸ b.property)⟩
  left_inv a := Subtype.ext <| by simp
  right_inv b := Subtype.ext <| by simp
/-
**Equiv.coe_subtypeEquiv_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：coe_subtypeEquiv_eq_map {X Y} {p : X -> Prop} {q : Y -> Prop} (e : X ≃ Y) 
(h : forall x, p x ↔ q (e x)) : ⇑(e.subtypeEquiv h) = Subtype.map e (h · |>.mp)
参数：e : X ≃ Y；h : forall x, p x ↔ q (e x)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_subtypeEquiv_eq_map {X Y} {p : X → Prop} {q : Y → Prop} (e : X ≃ Y)
    (h : ∀ x, p x ↔ q (e x)) : ⇑(e.subtypeEquiv h) = Subtype.map e (h · |>.mp) :=
  rfl

@[simp]
/-
**Equiv.subtypeEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：subtypeEquiv_refl {p : α -> Prop} (h : forall a, p a ↔ p (Equiv.refl _ a)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem subtypeEquiv_refl {p : α → Prop} (h : ∀ a, p a ↔ p (Equiv.refl _ a) := fun _ => Iff.rfl) :
    (Equiv.refl α).subtypeEquiv h = Equiv.refl { a : α // p a } := by
  ext
  rfl

-- We use `as_aux_lemma` here to avoid creating large proof terms when using `simp`
@[simp]
/-
**Equiv.subtypeEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：subtypeEquiv_symm {p : α -> Prop} {q : β -> Prop} (e : α ≃ β) (h : forall 
a : α, p a ↔ q (e a)) : (e.subtypeEquiv h).symm = e.symm.subtypeEquiv (by as_aux
_lemma => grind)
参数：e : α ≃ β；h : forall a : α, p a ↔ q (e a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem subtypeEquiv_symm {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a : α, p a ↔ q (e a)) :
    (e.subtypeEquiv h).symm = e.symm.subtypeEquiv (by as_aux_lemma => grind) :=
  rfl

@[simp]
/-
**Equiv.subtypeEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：subtypeEquiv_trans {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (e : α 
≃ β) (f : β ≃ γ) (h : forall a : α, p a ↔ q (e a)) (h' : forall b : β, q b ↔ r (
f b)) : (e.subtypeEquiv h).trans (f.subtypeEquiv h') = (e.trans f).subtypeEquiv 
(by as_aux_lemma => exact fun a => (h a).trans (h' <| e a))
参数：e : α ≃ β；f : β ≃ γ；h : forall a : α, p a ↔ q (e a)；h' : forall b : β, q b ↔ 
r (f b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem subtypeEquiv_trans {p : α → Prop} {q : β → Prop} {r : γ → Prop} (e : α ≃ β) (f : β ≃ γ)
    (h : ∀ a : α, p a ↔ q (e a)) (h' : ∀ b : β, q b ↔ r (f b)) :
    (e.subtypeEquiv h).trans (f.subtypeEquiv h')
    = (e.trans f).subtypeEquiv (by as_aux_lemma => exact fun a => (h a).trans (h' <| e a)) :=
  rfl

/-- If two predicates `p` and `q` are pointwise equivalent, then `{x // p x}` is equivalent to
`{x // q x}`. -/
@[simps!]
/-
**Equiv.subtypeEquivRight** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeEquivRight {p q : α -> Prop} (e : forall x, p x ↔ q x) : { x // p x
 } ≃ { x // q x }
参数：e : forall x, p x ↔ q x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
If two predicates `p` and `q` are pointwise equivalent, then `{x // p x}` is equ
ivalent to
`{x // q x}`.
-/
def subtypeEquivRight {p q : α → Prop} (e : ∀ x, p x ↔ q x) : { x // p x } ≃ { x // q x } :=
  subtypeEquiv (Equiv.refl _) e
/-
**Equiv.subtypeEquivRight_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：subtypeEquivRight_apply {p q : α -> Prop} (e : forall x, p x ↔ q x) (z : {
 x // p x }) : subtypeEquivRight e z = ⟨z, (e z.1).mp z.2⟩
参数：e : forall x, p x ↔ q x；z : { x // p x }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtypeEquivRight_apply {p q : α → Prop} (e : ∀ x, p x ↔ q x)
    (z : { x // p x }) : subtypeEquivRight e z = ⟨z, (e z.1).mp z.2⟩ := rfl
/-
**Equiv.subtypeEquivRight_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：subtypeEquivRight_symm_apply {p q : α -> Prop} (e : forall x, p x ↔ q x) (
z : { x // q x }) : (subtypeEquivRight e).symm z = ⟨z, (e z.1).mpr z.2⟩
参数：e : forall x, p x ↔ q x；z : { x // q x }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma subtypeEquivRight_symm_apply {p q : α → Prop} (e : ∀ x, p x ↔ q x)
    (z : { x // q x }) : (subtypeEquivRight e).symm z = ⟨z, (e z.1).mpr z.2⟩ := rfl

/-- If `α ≃ β`, then for any predicate `p : β → Prop` the subtype `{a // p (e a)}` is equivalent
to the subtype `{b // p b}`. -/
/-
**Equiv.subtypeEquivOfSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeEquivOfSubtype {p : β -> Prop} (e : α ≃ β) : { a : α // p (e a) } ≃
 { b : β // p b }
参数：e : α ≃ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α ≃ β`, then for any predicate `p : β → Prop` the subtype `{a // p (e a)}` i
s equivalent
to the subtype `{b // p b}`.
-/
def subtypeEquivOfSubtype {p : β → Prop} (e : α ≃ β) : { a : α // p (e a) } ≃ { b : β // p b } :=
  subtypeEquiv e <| by simp

/-- If `α ≃ β`, then for any predicate `p : α → Prop` the subtype `{a // p a}` is equivalent
to the subtype `{b // p (e.symm b)}`. This version is used by `equiv_rw`. -/
/-
**Equiv.subtypeEquivOfSubtype'** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeEquivOfSubtype' {p : α -> Prop} (e : α ≃ β) : { a : α // p a } ≃ { 
b : β // p (e.symm b) }
参数：e : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α ≃ β`, then for any predicate `p : α → Prop` the subtype `{a // p a}` is eq
uivalent
to the subtype `{b // p (e.symm b)}`. This version is used by `equiv_rw`.
-/
def subtypeEquivOfSubtype' {p : α → Prop} (e : α ≃ β) :
    { a : α // p a } ≃ { b : β // p (e.symm b) } :=
  e.symm.subtypeEquivOfSubtype.symm

/-- If two predicates are equal, then the corresponding subtypes are equivalent. -/
/-
**Equiv.subtypeEquivProp** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeEquivProp {p q : α -> Prop} (h : p = q) : Subtype p ≃ Subtype q
参数：h : p = q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
If two predicates are equal, then the corresponding subtypes are equivalent.
-/
def subtypeEquivProp {p q : α → Prop} (h : p = q) : Subtype p ≃ Subtype q :=
  subtypeEquiv (Equiv.refl α) fun _ => h ▸ Iff.rfl

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. This
version allows the “inner” predicate to depend on `h : p a`. -/
@[simps]
/-
**Equiv.subtypeSubtypeEquivSubtypeExists** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeSubtypeEquivSubtypeExists (p : α -> Prop) (q : Subtype p -> Prop) :
 Subtype q ≃ { a : α // exists h : p a, q ⟨a, h⟩ }
参数：p : α -> Prop；q : Subtype p -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype of a subtype is equivalent to the subtype of elements satisfying both 
predicates. This
version allows the “inner” predicate to depend on `h : p a`.
-/
def subtypeSubtypeEquivSubtypeExists (p : α → Prop) (q : Subtype p → Prop) :
    Subtype q ≃ { a : α // ∃ h : p a, q ⟨a, h⟩ } :=
  ⟨fun a =>
    ⟨a.1, a.1.2, by
      rcases a with ⟨⟨a, hap⟩, haq⟩
      exact haq⟩,
    fun a => ⟨⟨a, a.2.fst⟩, a.2.snd⟩, fun ⟨⟨_, _⟩, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. -/
@[simps!]
/-
**Equiv.subtypeSubtypeEquivSubtypeInter** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeSubtypeEquivSubtypeInter {α : Type u} (p q : α -> Prop) : { x : Sub
type p // q x.1 } ≃ Subtype fun x => p x ∧ q x
参数：p q : α -> Prop。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
A subtype of a subtype is equivalent to the subtype of elements satisfying both 
predicates.
-/
def subtypeSubtypeEquivSubtypeInter {α : Type u} (p q : α → Prop) :
    { x : Subtype p // q x.1 } ≃ Subtype fun x => p x ∧ q x :=
  (subtypeSubtypeEquivSubtypeExists p _).trans <|
    subtypeEquivRight fun x => @exists_prop (q x) (p x)

/-- If the outer subtype has more restrictive predicate than the inner one,
then we can drop the latter. -/
@[simps!]
/-
**Equiv.subtypeSubtypeEquivSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeSubtypeEquivSubtype {α} {p q : α -> Prop} (h : forall {x}, q x -> p
 x) : { x : Subtype p // q x.1 } ≃ Subtype q
参数：h : forall {x}, q x -> p x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If the outer subtype has more restrictive predicate than the inner one,
then we can drop the latter.
-/
def subtypeSubtypeEquivSubtype {α} {p q : α → Prop} (h : ∀ {x}, q x → p x) :
    { x : Subtype p // q x.1 } ≃ Subtype q :=
  (subtypeSubtypeEquivSubtypeInter p _).trans <| subtypeEquivRight fun _ => and_iff_right_of_imp h

/-- If a proposition holds for all elements, then the subtype is
equivalent to the original type. -/
@[simps apply symm_apply]
/-
**Equiv.subtypeUnivEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeUnivEquiv {α} {p : α -> Prop} (h : forall x, p x) : Subtype p ≃ α
参数：h : forall x, p x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a proposition holds for all elements, then the subtype is
equivalent to the original type.
-/
def subtypeUnivEquiv {α} {p : α → Prop} (h : ∀ x, p x) : Subtype p ≃ α :=
  ⟨fun x => x, fun x => ⟨x, h x⟩, fun _ => Subtype.ext rfl, fun _ => rfl⟩

/-- A subtype of a sigma-type is a sigma-type over a subtype. -/
/-
**Equiv.subtypeSigmaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeSigmaEquiv {α} (p : α -> Type v) (q : α -> Prop) : { y : Sigma p //
 q y.1 } ≃ Σ x : Subtype q, p x.1
参数：p : α -> Type v；q : α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype of a sigma-type is a sigma-type over a subtype.
-/
def subtypeSigmaEquiv {α} (p : α → Type v) (q : α → Prop) : { y : Sigma p // q y.1 } ≃ Σ x :
    Subtype q, p x.1 :=
  ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun _ => rfl,
    fun _ => rfl⟩

/-- A sigma type over a subtype is equivalent to the sigma set over the original type,
if the fiber is empty outside of the subset -/
/-
**Equiv.sigmaSubtypeEquivOfSubset** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaSubtypeEquivOfSubset {α} (p : α -> Type v) (q : α -> Prop) (h : foral
l x, p x -> q x) : (Σ x : Subtype q, p x) ≃ Σ x : α, p x
参数：p : α -> Type v；q : α -> Prop；h : forall x, p x -> q x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A sigma type over a subtype is equivalent to the sigma set over the original typ
e,
if the fiber is empty outside of the subset
-/
def sigmaSubtypeEquivOfSubset {α} (p : α → Type v) (q : α → Prop) (h : ∀ x, p x → q x) :
    (Σ x : Subtype q, p x) ≃ Σ x : α, p x :=
  (subtypeSigmaEquiv p q).symm.trans <| subtypeUnivEquiv fun x => h x.1 x.2

/-- If a predicate `p : β → Prop` is true on the range of a map `f : α → β`, then
`Σ y : {y // p y}, {x // f x = y}` is equivalent to `α`. -/
/-
**Equiv.sigmaSubtypeFiberEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaSubtypeFiberEquiv {α β : Type*} (f : α -> β) (p : β -> Prop) (h : for
all x, p (f x)) : (Σ y : Subtype p, { x : α // f x = y }) ≃ α
参数：f : α -> β；p : β -> Prop；h : forall x, p (f x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a predicate `p : β → Prop` is true on the range of a map `f : α → β`, then
`Σ y : {y // p y}, {x // f x = y}` is equivalent to `α`.
-/
def sigmaSubtypeFiberEquiv {α β : Type*} (f : α → β) (p : β → Prop) (h : ∀ x, p (f x)) :
    (Σ y : Subtype p, { x : α // f x = y }) ≃ α :=
  calc
    _ ≃ Σ y : β, { x : α // f x = y } := sigmaSubtypeEquivOfSubset _ p fun _ ⟨x, h'⟩ => h' ▸ h x
    _ ≃ α := sigmaFiberEquiv f

/-- If for each `x` we have `p x ↔ q (f x)`, then `Σ y : {y // q y}, f ⁻¹' {y}` is equivalent
to `{x // p x}`. -/
/-
**Equiv.sigmaSubtypeFiberEquivSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaSubtypeFiberEquivSubtype {α β : Type*} (f : α -> β) {p : α -> Prop} {
q : β -> Prop} (h : forall x, p x ↔ q (f x)) : (Σ y : Subtype q, { x : α // f x 
= y }) ≃ Subtype p
参数：f : α -> β；h : forall x, p x ↔ q (f x)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If for each `x` we have `p x ↔ q (f x)`, then `Σ y : {y // q y}, f ⁻¹' {y}` is e
quivalent
to `{x // p x}`.
-/
def sigmaSubtypeFiberEquivSubtype {α β : Type*} (f : α → β) {p : α → Prop} {q : β → Prop}
    (h : ∀ x, p x ↔ q (f x)) : (Σ y : Subtype q, { x : α // f x = y }) ≃ Subtype p :=
  calc
    (Σ y : Subtype q, { x : α // f x = y }) ≃ Σ y :
        Subtype q, { x : Subtype p // Subtype.mk (f x) ((h x).1 x.2) = y } := by {
          apply sigmaCongrRight
          intro y
          apply Equiv.symm
          refine (subtypeSubtypeEquivSubtypeExists _ _).trans (subtypeEquivRight ?_)
          intro x
          exact ⟨fun ⟨hp, h'⟩ => congr_arg Subtype.val h', fun h' => ⟨(h x).2 (h'.symm ▸ y.2),
            Subtype.ext h'⟩⟩ }
    _ ≃ Subtype p := sigmaFiberEquiv fun x : Subtype p => (⟨f x, (h x).1 x.property⟩ : Subtype q)

/-- A sigma type over an `Option` is equivalent to the sigma set over the original type,
if the fiber is empty at none. -/
/-
**Equiv.sigmaOptionEquivOfSome** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaOptionEquivOfSome {α} (p : Option α -> Type v) (h : p none -> False) 
: (Σ x : Option α, p x) ≃ Σ x : α, p (some x)
参数：p : Option α -> Type v；h : p none -> False。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A sigma type over an `Option` is equivalent to the sigma set over the original t
ype,
if the fiber is empty at none.
-/
def sigmaOptionEquivOfSome {α} (p : Option α → Type v) (h : p none → False) :
    (Σ x : Option α, p x) ≃ Σ x : α, p (some x) :=
  haveI h' : ∀ x, p x → x.isSome := by
    intro x
    cases x
    · intro n
      exfalso
      exact h n
    · intro _
      exact rfl
  (sigmaSubtypeEquivOfSubset _ _ h').symm.trans (sigmaCongrLeft' (optionIsSomeEquiv α))

/-- The `Pi`-type `∀ i, π i` is equivalent to the type of sections `f : ι → Σ i, π i` of the
`Sigma` type such that for all `i` we have `(f i).fst = i`. -/
/-
**Equiv.piEquivSubtypeSigma** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piEquivSubtypeSigma (ι) (π : ι -> Type*) : (forall i, π i) ≃ { f : ι -> Σ 
i, π i // forall i, (f i).1 = i } where toFun
参数：ι；π : ι -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Pi`-type `∀ i, π i` is equivalent to the type of sections `f : ι → Σ i, π i
` of the
`Sigma` type such that for all `i` we have `(f i).fst = i`.
-/
def piEquivSubtypeSigma (ι) (π : ι → Type*) :
    (∀ i, π i) ≃ { f : ι → Σ i, π i // ∀ i, (f i).1 = i } where
  toFun := fun f => ⟨fun i => ⟨i, f i⟩, fun _ => rfl⟩
  invFun := fun f i => by rw [← f.2 i]; exact (f.1 i).2
  right_inv := fun ⟨f, hf⟩ =>
    Subtype.ext <| funext fun i =>
      Sigma.eq (hf i).symm <| eq_of_heq <| rec_heq_of_heq _ <| by simp

/-- The type of functions `f : ∀ a, β a` such that for all `a` we have `p a (f a)` is equivalent
to the type of functions `∀ a, {b : β a // p a b}`. -/
/-
**Equiv.subtypePiEquivPi** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypePiEquivPi {β : α -> Sort v} {p : forall a, β a -> Prop} : { f : for
all a, β a // forall a, p a (f a) } ≃ forall a, { b : β a // p a b } where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of functions `f : ∀ a, β a` such that for all `a` we have `p a (f a)` i
s equivalent
to the type of functions `∀ a, {b : β a // p a b}`.
-/
def subtypePiEquivPi {β : α → Sort v} {p : ∀ a, β a → Prop} :
    { f : ∀ a, β a // ∀ a, p a (f a) } ≃ ∀ a, { b : β a // p a b } where
  toFun := fun f a => ⟨f.1 a, f.2 a⟩
  invFun := fun f => ⟨fun a => (f a).1, fun a => (f a).2⟩
  left_inv := by
    rintro ⟨f, h⟩
    rfl
  right_inv := by
    rintro f
    funext a
    exact Subtype.ext rfl

/-- A sigma of a sigma whose second base does not depend on the first is equivalent
to a sigma whose base is a product. -/
@[simps!]
/-
**Equiv.sigmaAssocProd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaAssocProd {α β : Type*} {γ : α -> β -> Type*} : (ab : α × β) × γ ab.1
 ab.2 ≃ (a : α) × (b : β) × γ a b
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A sigma of a sigma whose second base does not depend on the first is equivalent
to a sigma whose base is a product.
-/
def sigmaAssocProd {α β : Type*} {γ : α → β → Type*} :
    (ab : α × β) × γ ab.1 ab.2 ≃ (a : α) × (b : β) × γ a b :=
  sigmaCongrLeft' (sigmaEquivProd _ _).symm |>.trans <| sigmaAssoc γ

/-- A subtype of a sigma which pins down the base of the sigma is equivalent to
the respective fiber. -/
@[simps]
/-
**Equiv.sigmaSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaSubtype {α : Type*} {β : α -> Type*} (a : α) : {s : Sigma β // s.1 = 
a} ≃ β a where toFun
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype of a sigma which pins down the base of the sigma is equivalent to
the respective fiber.
-/
def sigmaSubtype {α : Type*} {β : α → Type*} (a : α) :
    {s : Sigma β // s.1 = a} ≃ β a where
  toFun := fun ⟨⟨_, b⟩, h⟩ => h ▸ b
  invFun b := ⟨⟨a, b⟩, rfl⟩
  left_inv := fun ⟨a, h⟩ ↦ by cases h; simp
  right_inv b := by simp


section
attribute [local simp] Trans.trans sigmaAssoc subtypeSigmaEquiv uniqueSigma eqRec_eq_cast

set_option backward.isDefEq.respectTransparency.types false in
/-- A subtype of a dependent triple which pins down both bases is equivalent to the
respective fiber. -/
@[simps! +simpRhs apply]
/-
**Equiv.sigmaSigmaSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaSigmaSubtype {α : Type*} {β : α -> Type*} {γ : (a : α) -> β a -> Type
*} (p : (a : α) × β a -> Prop) [uniq : Unique {ab // p ab}] {a : α} {b : β a} (h
 : p ⟨a, b⟩) : {s : (a : α) × (b : β a) × γ a b // p ⟨s.1, s.2.1⟩} ≃ γ a b
参数：a : α；p : (a : α) × β a -> Prop；h : p ⟨a, b⟩。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A subtype of a dependent triple which pins down both bases is equivalent to the
respective fiber.
-/
def sigmaSigmaSubtype {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    (p : (a : α) × β a → Prop) [uniq : Unique {ab // p ab}] {a : α} {b : β a} (h : p ⟨a, b⟩) :
    {s : (a : α) × (b : β a) × γ a b // p ⟨s.1, s.2.1⟩} ≃ γ a b :=
  calc {s : (a : α) × (b : β a) × γ a b // p ⟨s.1, s.2.1⟩}
  _ ≃ _ := subtypeEquiv (p := fun ⟨a, b, c⟩ ↦ p ⟨a, b⟩) (q := (p ·.1))
    (sigmaAssoc γ).symm fun s ↦ by simp [sigmaAssoc]
  _ ≃ _ := subtypeSigmaEquiv _ _
  _ ≃ _ := uniqueSigma (fun ab ↦ γ (Sigma.fst <| Subtype.val ab) (Sigma.snd <| Subtype.val ab))
  _ ≃ γ a b := Equiv.cast <| by rw [← show ⟨⟨a, b⟩, h⟩ = uniq.default from uniq.uniq _]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Equiv.sigmaSigmaSubtype_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：sigmaSigmaSubtype_symm_apply {α : Type*} {β : α -> Type*} {γ : (a : α) -> 
β a -> Type*} (p : (a : α) × β a -> Prop) [uniq : Unique {ab // p ab}] {a : α} {
b : β a} (c : γ a b) (h : p ⟨a, b⟩) : (sigmaSigmaSubtype p h).symm c = ⟨⟨a, ⟨b, 
c⟩⟩, h⟩
参数：a : α；p : (a : α) × β a -> Prop；c : γ a b；h : p ⟨a, b⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.sigmaSigmaSubtype_apply`：∀ {α : Type u_9} {β : α → Type u_10} {γ :
 (a : α) → β a → Type u_11} (p : (a : α) × β a → Prop)   [uniq : Unique { ab // 
p ab }] {a : α} {b …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sigmaSigmaSubtype_symm_apply {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    (p : (a : α) × β a → Prop) [uniq : Unique {ab // p ab}]
    {a : α} {b : β a} (c : γ a b) (h : p ⟨a, b⟩) :
    (sigmaSigmaSubtype p h).symm c = ⟨⟨a, ⟨b, c⟩⟩, h⟩ := by
  rw [Equiv.symm_apply_eq]; simp

/-- A specialization of `sigmaSigmaSubtype` to the case where the second base
does not depend on the first, and the property being checked for is simple
equality. Useful e.g. when `γ` is `Hom` inside a category. -/
/-
**Equiv.sigmaSigmaSubtypeEq** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaSigmaSubtypeEq {α β : Type*} {γ : α -> β -> Type*} (a : α) (b : β) : 
{s : (a : α) × (b : β) × γ a b // s.1 = a ∧ s.2.1 = b} ≃ γ a b
参数：a : α；b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A specialization of `sigmaSigmaSubtype` to the case where the second base
does not depend on the first, and the property being checked for is simple
equality. Useful e.g. when `γ` is `Hom` inside a category.
-/
def sigmaSigmaSubtypeEq {α β : Type*} {γ : α → β → Type*} (a : α) (b : β) :
    {s : (a : α) × (b : β) × γ a b // s.1 = a ∧ s.2.1 = b} ≃ γ a b :=
  have : Unique (@Subtype ((_ : α) × β) (fun ⟨a', b'⟩ ↦ a' = a ∧ b' = b)) := {
    default := ⟨⟨a, b⟩, ⟨rfl, rfl⟩⟩
    uniq := by rintro ⟨⟨a', b'⟩, ⟨rfl, rfl⟩⟩; rfl }
  sigmaSigmaSubtype (fun ⟨a', b'⟩ ↦ a' = a ∧ b' = b) ⟨rfl, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Equiv.sigmaSigmaSubtypeEq_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：sigmaSigmaSubtypeEq_apply {α β : Type*} {γ : α -> β -> Type*} {a : α} {b :
 β} (s : {s : (a : α) × (b : β) × γ a b // s.1 = a ∧ s.2.1 = b}) : sigmaSigmaSub
typeEq a b s = cast (congrArg₂ γ s.2.1 s.2.2) s.1.2.2
参数：s : {s : (a : α) × (b : β) × γ a b // s.1 = a ∧ s.2.1 = b}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ
) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.sigmaSigmaSubtype_apply`：∀ {α : Type u_9} {β : α → Type u_10} {γ :
 (a : α) → β a → Type u_11} (p : (a : α) × β a → Prop)   [uniq : Unique { ab // 
p ab }] {a : α} {b …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sigmaSigmaSubtypeEq_apply {α β : Type*} {γ : α → β → Type*} {a : α} {b : β}
    (s : {s : (a : α) × (b : β) × γ a b // s.1 = a ∧ s.2.1 = b}) :
    sigmaSigmaSubtypeEq a b s = cast (congrArg₂ γ s.2.1 s.2.2) s.1.2.2 := by
  simp [sigmaSigmaSubtypeEq]

@[simp]
/-
**Equiv.sigmaSigmaSubtypeEq_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：sigmaSigmaSubtypeEq_symm_apply {α β : Type*} {γ : α -> β -> Type*} {a : α}
 {b : β} (c : γ a b) : (sigmaSigmaSubtypeEq a b).symm c = ⟨⟨a, ⟨b, c⟩⟩, ⟨rfl, rf
l⟩⟩
参数：c : γ a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equiv.sigmaSigmaSubtype_symm_apply`：sigmaSigmaSubtype_symm_apply {α : Ty
pe*} {β : α -> Type*} {γ : (a : α) -> β a -> Type*} (p : (a : α) × β a -> Prop) 
[uniq : Unique {ab // p …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sigmaSigmaSubtypeEq_symm_apply {α β : Type*} {γ : α → β → Type*} {a : α} {b : β} (c : γ a b) :
    (sigmaSigmaSubtypeEq a b).symm c = ⟨⟨a, ⟨b, c⟩⟩, ⟨rfl, rfl⟩⟩ := by
  simp [sigmaSigmaSubtypeEq]

end

end

section subtypeEquivCodomain

variable {X Y : Sort*} [DecidableEq X] {x : X}

/-- The type of all functions `X → Y` with prescribed values for all `x' ≠ x`
is equivalent to the codomain `Y`. -/
/-
**Equiv.subtypeEquivCodomain** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeEquivCodomain (f : { x' // x' != x } -> Y) : { g : X -> Y // g ∘ (↑
) = f } ≃ Y
参数：f : { x' // x' != x } -> Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The type of all functions `X → Y` with prescribed values for all `x' ≠ x`
is equivalent to the codomain `Y`.
-/
def subtypeEquivCodomain (f : { x' // x' ≠ x } → Y) :
    { g : X → Y // g ∘ (↑) = f } ≃ Y :=
  (subtypePreimage _ f).trans <|
    @funUnique { x' // ¬x' ≠ x } _ <|
      show Unique { x' // ¬x' ≠ x } from
        @Equiv.unique _ _
          (show Unique { x' // x' = x } from {
            default := ⟨x, rfl⟩, uniq := fun ⟨_, h⟩ => Subtype.val_injective h })
          (subtypeEquivRight fun _ => not_not)

@[simp]
/-
**Equiv.coe_subtypeEquivCodomain** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_subtypeEquivCodomain (f : { x' // x' != x } -> Y) : (subtypeEquivCodom
ain f : _ -> Y) = fun g : { g : X -> Y // g ∘ (↑) = f } => (g : X -> Y) x
参数：f : { x' // x' != x } -> Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtypeEquivCodomain (f : { x' // x' ≠ x } → Y) :
    (subtypeEquivCodomain f : _ → Y) =
      fun g : { g : X → Y // g ∘ (↑) = f } => (g : X → Y) x :=
  rfl

@[simp]
/-
**Equiv.subtypeEquivCodomain_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：subtypeEquivCodomain_apply (f : { x' // x' != x } -> Y) (g) : subtypeEquiv
Codomain f g = (g : X -> Y) x
参数：f : { x' // x' != x } -> Y；g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeEquivCodomain_apply (f : { x' // x' ≠ x } → Y) (g) :
    subtypeEquivCodomain f g = (g : X → Y) x :=
  rfl
/-
**Equiv.coe_subtypeEquivCodomain_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_subtypeEquivCodomain_symm (f : { x' // x' != x } -> Y) : ((subtypeEqui
vCodomain f).symm : Y -> _) = fun y => ⟨fun x' => if h : x' != x then f ⟨x', h⟩ 
else y, by grind⟩
参数：f : { x' // x' != x } -> Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_subtypeEquivCodomain_symm (f : { x' // x' ≠ x } → Y) :
    ((subtypeEquivCodomain f).symm : Y → _) = fun y =>
      ⟨fun x' => if h : x' ≠ x then f ⟨x', h⟩ else y, by grind⟩ :=
  rfl

@[simp]
/-
**Equiv.subtypeEquivCodomain_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：subtypeEquivCodomain_symm_apply (f : { x' // x' != x } -> Y) (y : Y) (x' :
 X) : ((subtypeEquivCodomain f).symm y : X -> Y) x' = if h : x' != x then f ⟨x',
 h⟩ else y
参数：f : { x' // x' != x } -> Y；y : Y；x' : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem subtypeEquivCodomain_symm_apply (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) :
    ((subtypeEquivCodomain f).symm y : X → Y) x' = if h : x' ≠ x then f ⟨x', h⟩ else y :=
  rfl
/-
**Equiv.subtypeEquivCodomain_symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：subtypeEquivCodomain_symm_apply_eq (f : { x' // x' != x } -> Y) (y : Y) : 
((subtypeEquivCodomain f).symm y : X -> Y) x = y
参数：f : { x' // x' != x } -> Y；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem subtypeEquivCodomain_symm_apply_eq (f : { x' // x' ≠ x } → Y) (y : Y) :
    ((subtypeEquivCodomain f).symm y : X → Y) x = y :=
  dif_neg (not_not.mpr rfl)
/-
**Equiv.subtypeEquivCodomain_symm_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：subtypeEquivCodomain_symm_apply_ne (f : { x' // x' != x } -> Y) (y : Y) (x
' : X) (h : x' != x) : ((subtypeEquivCodomain f).symm y : X -> Y) x' = f ⟨x', h⟩
参数：f : { x' // x' != x } -> Y；y : Y；x' : X；h : x' != x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem subtypeEquivCodomain_symm_apply_ne
    (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) (h : x' ≠ x) :
    ((subtypeEquivCodomain f).symm y : X → Y) x' = f ⟨x', h⟩ :=
  dif_pos h

end subtypeEquivCodomain

/-
**Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift (α → β) (α ≃ β) (↑) Bijective where prf f hf := ⟨ofBijective f hf, rfl⟩

section

variable {α' β' : Type*} (e : Perm α') {p : β' → Prop} [DecidablePred p] (f : α' ≃ Subtype p)

/-- Extend the domain of `e : Equiv.Perm α` to one that is over `β` via `f : α → Subtype p`,
where `p : β → Prop`, permuting only the `b : β` that satisfy `p b`.
This can be used to extend the domain across a function `f : α → β`,
keeping everything outside of `Set.range f` fixed. For this use-case `Equiv` given by `f` can
be constructed by `Equiv.of_leftInverse'` or `Equiv.of_leftInverse` when there is a known
inverse, or `Equiv.ofInjective` in the general case.
-/
/-
**Equiv.Perm.extendDomain** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：{α' : Type u_9} →   {β' : Type u_10} → Equiv.Perm α' → {p : β' → Prop} → [
DecidablePred p] → α' ≃ Subtype p → Equiv.Perm β'
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Extend the domain of `e : Equiv.Perm α` to one that is over `β` via `f : α → Sub
type p`,
where `p : β → Prop`, permuting only the `b : β` that satisfy `p b`.
This can be used to extend the domain across a function `f : α → β`,
keeping everything outside of `Set.range f` fixed. For this use-case `Equiv` giv
en by `f` can
be constructed by `Equiv.of_leftInverse'` or `Equiv.of_leftInverse` when there i
s a known
inverse, or `Equiv.ofInjective` in the general case.
-/
def Perm.extendDomain : Perm β' :=
  (permCongr f e).subtypeCongr (Equiv.refl _)

@[simp]
/-
**Equiv.Perm.extendDomain_apply_image** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α' : Type u_9} {β' : Type u_10} (e : Equiv.Perm α') {p : β' → Prop} [in
st : DecidablePred p] (f : α' ≃ Subtype p)   (a : α'), (e.extendDomain f) ↑(f a)
 = ↑(f (e a))
参数：e : Equiv.Perm α'；f : α' ≃ Subtype p；a : α'；e.extendDomain f；f a；f (e a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.Perm.subtypeCongr.left_apply_subtype`：∀ {ε : Type u_9} {p : ε → Pr
op} [inst : DecidablePred p] (ep : Equiv.Perm { a // p a }) (en : Equiv.Perm { a
 // ¬p a })   (a : { a // p a })…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Perm.extendDomain_apply_image (a : α') : e.extendDomain f (f a) = f (e a) := by
  simp [Perm.extendDomain]
/-
**Equiv.Perm.extendDomain_apply_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α' : Type u_9} {β' : Type u_10} (e : Equiv.Perm α') {p : β' → Prop} [in
st : DecidablePred p] (f : α' ≃ Subtype p)   {b : β'} (h : p b), (e.extendDomain
 f) b = ↑(f (e (f.symm ⟨b, h⟩)))
参数：e : Equiv.Perm α'；f : α' ≃ Subtype p；h : p b；e.extendDomain f；f (e (f.symm ⟨b
, h⟩))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.subtypeCongr.left_apply`：∀ {ε : Type u_9} {p : ε → Prop} [ins
t : DecidablePred p] (ep : Equiv.Perm { a // p a }) (en : Equiv.Perm { a // ¬p a
 })   {a : ε} (h : p a),…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Perm.extendDomain_apply_subtype {b : β'} (h : p b) :
    e.extendDomain f b = f (e (f.symm ⟨b, h⟩)) := by
  simp [Perm.extendDomain, h]
/-
**Equiv.Perm.extendDomain_apply_not_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
形式化陈述：∀ {α' : Type u_9} {β' : Type u_10} (e : Equiv.Perm α') {p : β' → Prop} [in
st : DecidablePred p] (f : α' ≃ Subtype p)   {b : β'}, ¬p b → (e.extendDomain f)
 b = b
参数：e : Equiv.Perm α'；f : α' ≃ Subtype p；e.extendDomain f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.subtypeCongr.right_apply`：∀ {ε : Type u_9} {p : ε → Prop} [in
st : DecidablePred p] (ep : Equiv.Perm { a // p a }) (en : Equiv.Perm { a // ¬p 
a })   {a : ε} (h : ¬p a)…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Perm.extendDomain_apply_not_subtype {b : β'} (h : ¬p b) : e.extendDomain f b = b := by
  simp [Perm.extendDomain, h]

@[simp]
/-
**Equiv.Perm.extendDomain_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α' : Type u_9} {β' : Type u_10} {p : β' → Prop} [inst : DecidablePred p
] (f : α' ≃ Subtype p),   Equiv.Perm.extendDomain (Equiv.refl α') f = Equiv.refl
 β'
参数：f : α' ≃ Subtype p；Equiv.refl α'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.subtypeCongr.congr_simp`：∀ {ε : Type u_9} {p : ε → Prop} {ins
t : DecidablePred p} [inst_1 : DecidablePred p] (ep ep_1 : Equiv.Perm { a // p a
 }),   ep = ep_1 → ∀ (en…
· 使用定理 `Equiv.permCongr_refl`：∀ {α' : Type u_1} {β' : Type u_2} (e : α' ≃ β'), e
.permCongr (Equiv.refl α') = Equiv.refl β'
· 使用定理 `Equiv.Perm.subtypeCongr.refl`：∀ {ε : Type u_9} {p : ε → Prop} [inst : De
cidablePred p],   Equiv.Perm.subtypeCongr (Equiv.refl { a // p a }) (Equiv.refl 
{ a // ¬p a }) = E…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Perm.extendDomain_refl : Perm.extendDomain (Equiv.refl _) f = Equiv.refl _ := by
  simp [Perm.extendDomain]

@[simp]
/-
**Equiv.Perm.extendDomain_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α' : Type u_9} {β' : Type u_10} (e : Equiv.Perm α') {p : β' → Prop} [in
st : DecidablePred p] (f : α' ≃ Subtype p),   Equiv.symm (e.extendDomain f) = Eq
uiv.Perm.extendDomain (Equiv.symm e) f
参数：e : Equiv.Perm α'；f : α' ≃ Subtype p；e.extendDomain f；Equiv.symm e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Perm.extendDomain_symm : (e.extendDomain f).symm = Perm.extendDomain e.symm f :=
  rfl
/-
**Equiv.Perm.extendDomain_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α' : Type u_9} {β' : Type u_10} {p : β' → Prop} [inst : DecidablePred p
] (f : α' ≃ Subtype p) (e e' : Equiv.Perm α'),   Equiv.trans (e.extendDomain f) 
(e'.extendDomain f) = Equiv.Perm.extendDomain (Equiv.trans e e') f
参数：f : α' ≃ Subtype p；e e' : Equiv.Perm α'；e.extendDomain f；e'.extendDomain f；Eq
uiv.trans e e'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.subtypeCongr.trans`：∀ {ε : Type u_9} {p : ε → Prop} [inst : D
ecidablePred p] (ep ep' : Equiv.Perm { a // p a })   (en en' : Equiv.Perm { a //
 ¬p a }),   Equiv.t…
· 使用定理 `Equiv.Perm.subtypeCongr.congr_simp`：∀ {ε : Type u_9} {p : ε → Prop} {ins
t : DecidablePred p} [inst_1 : DecidablePred p] (ep ep_1 : Equiv.Perm { a // p a
 }),   ep = ep_1 → ∀ (en…
· 使用定理 `Equiv.permCongr_trans`：permCongr_trans (p p' : Equiv.Perm α') : (e.permC
ongr p).trans (e.permCongr p') = e.permCongr (p.trans p')
· 使用定理 `Equiv.trans_refl`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans (Equi
v.refl β) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Perm.extendDomain_trans (e e' : Perm α') :
    (e.extendDomain f).trans (e'.extendDomain f) = Perm.extendDomain (e.trans e') f := by
  simp [Perm.extendDomain, permCongr_trans]

end

/-- Subtype of the quotient is equivalent to the quotient of the subtype. Let `α` be a setoid with
equivalence relation `~`. Let `p₂` be a predicate on the quotient type `α/~`, and `p₁` be the lift
of this predicate to `α`: `p₁ a ↔ p₂ ⟦a⟧`. Let `~₂` be the restriction of `~` to `{x // p₁ x}`.
Then `{x // p₂ x}` is equivalent to the quotient of `{x // p₁ x}` by `~₂`. -/
/-
**Equiv.subtypeQuotientEquivQuotientSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeQuotientEquivQuotientSubtype (p₁ : α -> Prop) {s₁ : Setoid α} {s₂ :
 Setoid (Subtype p₁)} (p₂ : Quotient s₁ -> Prop) (hp₂ : forall a, p₁ a ↔ p₂ ⟦a⟧)
 (h : forall x y : Subtype p₁, s₂.r x y ↔ s₁.r x y) : {x // p₂ x} ≃ Quotient s₂ 
where toFun a
参数：p₁ : α -> Prop；Subtype p₁；p₂ : Quotient s₁ -> Prop；hp₂ : forall a, p₁ a ↔ p₂ 
⟦a⟧；h : forall x y : Subtype p₁, s₂.r x y ↔ s₁.r x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subtype of the quotient is equivalent to the quotient of the subtype. Let `α` be
 a setoid with
equivalence relation `~`. Let `p₂` be a predicate on the quotient type `α/~`, an
d `p₁` be the lift
of this predicate to `α`: `p₁ a ↔ p₂ ⟦a⟧`. Let `~₂` be the restriction of `~` to
 `{x // p₁ x}`.
Then `{x // p₂ x}` is equivalent to the quotient of `{x // p₁ x}` by `~₂`.
-/
def subtypeQuotientEquivQuotientSubtype (p₁ : α → Prop) {s₁ : Setoid α} {s₂ : Setoid (Subtype p₁)}
    (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, s₂.r x y ↔ s₁.r x y) : {x // p₂ x} ≃ Quotient s₂ where
  toFun a :=
    Quotient.hrecOn a.1 (fun a h => ⟦⟨a, (hp₂ _).2 h⟩⟧)
      (fun a b hab => hfunext (by rw [Quotient.sound hab]) fun _ _ _ =>
        heq_of_eq (Quotient.sound ((h _ _).2 hab)))
      a.2
  invFun a :=
    Quotient.liftOn a (fun a => (⟨⟦a.1⟧, (hp₂ _).1 a.2⟩ : { x // p₂ x })) fun _ _ hab =>
      Subtype.ext (Quotient.sound ((h _ _).1 hab))
  left_inv a := by
    obtain ⟨a, ha⟩ := a
    induction a using Quotient.inductionOn
    rfl
  right_inv a := by induction a using Quotient.inductionOn; rfl

@[simp]
/-
**Equiv.subtypeQuotientEquivQuotientSubtype_mk** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`
。
形式化陈述：subtypeQuotientEquivQuotientSubtype_mk (p₁ : α -> Prop) [s₁ : Setoid α] [s
₂ : Setoid (Subtype p₁)] (p₂ : Quotient s₁ -> Prop) (hp₂ : forall a, p₁ a ↔ p₂ ⟦
a⟧) (h : forall x y : Subtype p₁, s₂ x y ↔ (x : α) ≈ y) (x hx) : subtypeQuotient
EquivQuotientSubtype p₁ p₂ hp₂ h ⟨⟦x⟧, hx⟩ = ⟦⟨x, (hp₂ _).2 hx⟩⟧
参数：p₁ : α -> Prop；Subtype p₁；p₂ : Quotient s₁ -> Prop；hp₂ : forall a, p₁ a ↔ p₂ 
⟦a⟧；h : forall x y : Subtype p₁, s₂ x y ↔ (x : α) ≈ y；x hx。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeQuotientEquivQuotientSubtype_mk (p₁ : α → Prop)
    [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)] (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, s₂ x y ↔ (x : α) ≈ y)
    (x hx) : subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h ⟨⟦x⟧, hx⟩ = ⟦⟨x, (hp₂ _).2 hx⟩⟧ :=
  rfl

@[simp]
/-
**Equiv.subtypeQuotientEquivQuotientSubtype_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `E
quiv`。
形式化陈述：subtypeQuotientEquivQuotientSubtype_symm_mk (p₁ : α -> Prop) [s₁ : Setoid 
α] [s₂ : Setoid (Subtype p₁)] (p₂ : Quotient s₁ -> Prop) (hp₂ : forall a, p₁ a ↔
 p₂ ⟦a⟧) (h : forall x y : Subtype p₁, s₂ x y ↔ (x : α) ≈ y) (x) : (subtypeQuoti
entEquivQuotientSubtype p₁ p₂ hp₂ h).symm ⟦x⟧ = ⟨⟦x⟧, (hp₂ _).1 x.property⟩
参数：p₁ : α -> Prop；Subtype p₁；p₂ : Quotient s₁ -> Prop；hp₂ : forall a, p₁ a ↔ p₂ 
⟦a⟧；h : forall x y : Subtype p₁, s₂ x y ↔ (x : α) ≈ y；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem subtypeQuotientEquivQuotientSubtype_symm_mk (p₁ : α → Prop)
    [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)] (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, s₂ x y ↔ (x : α) ≈ y) (x) :
    (subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h).symm ⟦x⟧ = ⟨⟦x⟧, (hp₂ _).1 x.property⟩ :=
  rfl

section Swap

variable [DecidableEq α]

/-- A helper function for `Equiv.swap`. -/
/-
**Equiv.swapCore** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：swapCore (a b r : α) : α
参数：a b r : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper function for `Equiv.swap`.
-/
def swapCore (a b r : α) : α :=
  if r = a then b else if r = b then a else r
/-
**Equiv.swapCore_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swapCore_self (r a : α) : swapCore a a r = r
参数：r a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem swapCore_self (r a : α) : swapCore a a r = r := by
  unfold swapCore
  split_ifs <;> simp [*]
/-
**Equiv.swapCore_swapCore** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swapCore_swapCore (r a b : α) : swapCore a b (swapCore a b r) = r
参数：r a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem swapCore_swapCore (r a b : α) : swapCore a b (swapCore a b r) = r := by
  unfold swapCore; split_ifs <;> grind
/-
**Equiv.swapCore_comm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swapCore_comm (r a b : α) : swapCore a b r = swapCore b a r
参数：r a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem swapCore_comm (r a b : α) : swapCore a b r = swapCore b a r := by
  unfold swapCore; split_ifs <;> grind

/-- `swap a b` is the permutation that swaps `a` and `b` and
  leaves other values as is. -/
/-
**Equiv.swap** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：swap (a b : α) : Perm α
参数：a b : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.swapCore_swapCore`：swapCore_swapCore (r a b : α) : swapCore a b (s
wapCore a b r) = r

--- 原说明 ---
`swap a b` is the permutation that swaps `a` and `b` and
  leaves other values as is.
-/
def swap (a b : α) : Perm α :=
  ⟨swapCore a b, swapCore a b, fun r => swapCore_swapCore r a b,
    fun r => swapCore_swapCore r a b⟩

@[simp]
/-
**Equiv.swap_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_self (a : α) : swap a a = Equiv.refl _
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.swapCore_self`：swapCore_self (r a : α) : swapCore a a r = r
-/
theorem swap_self (a : α) : swap a a = Equiv.refl _ :=
  ext fun r => swapCore_self r a
/-
**Equiv.swap_comm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_comm (a b : α) : swap a b = swap b a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.swapCore_comm`：swapCore_comm (r a b : α) : swapCore a b r = swapCo
re b a r
-/
theorem swap_comm (a b : α) : swap a b = swap b a :=
  ext fun r => swapCore_comm r _ _

@[aesop simp, grind =]
/-
**Equiv.swap_apply_def** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b th
en a else x
参数：a b x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b then a else x :=
  rfl

@[simp]
/-
**Equiv.swap_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_apply_left (a b : α) : swap a b a = b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem swap_apply_left (a b : α) : swap a b a = b :=
  if_pos rfl

@[simp]
/-
**Equiv.swap_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_apply_right (a b : α) : swap a b b = a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_apply_right (a b : α) : swap a b b = a := by
  grind
/-
**Equiv.swap_apply_of_ne_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_apply_of_ne_of_ne {a b x : α} : x != a -> x != b -> swap a b x = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_apply_of_ne_of_ne {a b x : α} : x ≠ a → x ≠ b → swap a b x = x := by
  grind
/-
**Equiv.eq_or_eq_of_swap_apply_ne_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：eq_or_eq_of_swap_apply_ne_self {a b x : α} (h : swap a b x != x) : x = a ∨
 x = b
参数：h : swap a b x != x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem eq_or_eq_of_swap_apply_ne_self {a b x : α} (h : swap a b x ≠ x) : x = a ∨ x = b := by
  contrapose! h
  exact swap_apply_of_ne_of_ne h.1 h.2

@[simp]
/-
**Equiv.swap_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_swap (a b : α) : (swap a b).trans (swap a b) = Equiv.refl _
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.swapCore_swapCore`：swapCore_swapCore (r a b : α) : swapCore a b (s
wapCore a b r) = r
-/
theorem swap_swap (a b : α) : (swap a b).trans (swap a b) = Equiv.refl _ :=
  ext fun _ => swapCore_swapCore _ _ _

@[simp]
/-
**Equiv.symm_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：symm_swap (a b : α) : (swap a b).symm = swap a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_swap (a b : α) : (swap a b).symm = swap a b :=
  rfl

@[simp]
/-
**Equiv.swap_eq_refl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_eq_refl_iff {x y : α} : swap x y = Equiv.refl _ ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem swap_eq_refl_iff {x y : α} : swap x y = Equiv.refl _ ↔ x = y :=
  ⟨fun h => (Equiv.refl _).injective (by grind), by grind⟩
/-
**Equiv.swap_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_comp_apply {a b x : α} (π : Perm α) : π.trans (swap a b) x = if π x =
 a then b else if π x = b then a else π x
参数：π : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem swap_comp_apply {a b x : α} (π : Perm α) :
    π.trans (swap a b) x = if π x = a then b else if π x = b then a else π x := by
  cases π
  rfl
/-
**Equiv.swap_eq_update** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_eq_update (i j : α) : (Equiv.swap i j : α -> α) = update (update id j
 i) i j
参数：i j : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_eq_update (i j : α) : (Equiv.swap i j : α → α) = update (update id j i) i j := by
  grind
/-
**Equiv.comp_swap_eq_update** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：comp_swap_eq_update (i j : α) (f : α -> β) : f ∘ Equiv.swap i j = update (
update f j (f i)) i (f j)
参数：i j : α；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_swap_eq_update (i j : α) (f : α → β) :
    f ∘ Equiv.swap i j = update (update f j (f i)) i (f j) := by
  grind

@[simp]
/-
**Equiv.symm_trans_swap_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：symm_trans_swap_trans [DecidableEq β] (a b : α) (e : α ≃ β) : (e.symm.tran
s (swap a b)).trans e = swap (e a) (e b)
参数：a b : α；e : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_swap_trans [DecidableEq β] (a b : α) (e : α ≃ β) :
    (e.symm.trans (swap a b)).trans e = swap (e a) (e b) := by
  grind

@[simp]
/-
**Equiv.trans_swap_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：trans_swap_trans_symm [DecidableEq β] (a b : β) (e : α ≃ β) : (e.trans (sw
ap a b)).trans e.symm = swap (e.symm a) (e.symm b)
参数：a b : β；e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_trans_swap_trans`：symm_trans_swap_trans [DecidableEq β] (a b 
: α) (e : α ≃ β) : (e.symm.trans (swap a b)).trans e = swap (e a) (e b)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem trans_swap_trans_symm [DecidableEq β] (a b : β) (e : α ≃ β) :
    (e.trans (swap a b)).trans e.symm = swap (e.symm a) (e.symm b) :=
  symm_trans_swap_trans a b e.symm

@[simp]
/-
**Equiv.swap_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_apply_self (i j a : α) : swap i j (swap i j a) = a
参数：i j a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_apply_self (i j a : α) : swap i j (swap i j a) = a := by
  grind

/-- A function is invariant to a swap if it is equal at both elements -/
/-
**Equiv.apply_swap_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：apply_swap_eq_self {v : α -> β} {i j : α} (hv : v i = v j) (k : α) : v (sw
ap i j k) = v k
参数：hv : v i = v j；k : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is invariant to a swap if it is equal at both elements
-/
theorem apply_swap_eq_self {v : α → β} {i j : α} (hv : v i = v j) (k : α) :
    v (swap i j k) = v k := by
  grind
/-
**Equiv.swap_apply_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_apply_eq_iff {x y z w : α} : swap x y z = w ↔ z = swap x y w
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_apply_eq_iff {x y z w : α} : swap x y z = w ↔ z = swap x y w := by
  grind
/-
**Equiv.swap_apply_ne_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_apply_ne_self_iff {a b x : α} : swap a b x != x ↔ a != b ∧ (x = a ∨ x
 = b)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_apply_ne_self_iff {a b x : α} : swap a b x ≠ x ↔ a ≠ b ∧ (x = a ∨ x = b) := by
  grind
/-
**Equiv.swap_injective_of_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_injective_of_left (a : α) : Function.Injective (fun x => Equiv.swap a
 x)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
-/
theorem swap_injective_of_left (a : α) :
    Function.Injective (fun x ↦ Equiv.swap a x) := fun c d h ↦ by
  simp only at h
  rw [← Equiv.swap_apply_left a c, h, Equiv.swap_apply_left]
/-
**Equiv.swap_injective_of_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_injective_of_right (a : α) : Function.Injective (fun x => Equiv.swap 
x a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.swap_comm`：swap_comm (a b : α) : swap a b = swap b a
· 使用定理 `Equiv.swap_injective_of_left`：swap_injective_of_left (a : α) : Function.
Injective (fun x => Equiv.swap a x)
-/
theorem swap_injective_of_right (a : α) :
    Function.Injective (fun x ↦ Equiv.swap x a) := by
  simp_rw [swap_comm _ a]
  exact swap_injective_of_left a
/-
**Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [Nontrivial α] : Nontrivial (Equiv.Perm α) := by
  classical
  obtain ⟨a : α⟩ := Nontrivial.to_nonempty (α := α)
  exact Function.Injective.nontrivial (Equiv.swap_injective_of_left a)
/-
**Equiv.image_swap_of_mem_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：image_swap_of_mem_of_notMem {α : Type*} [DecidableEq α] {s : Set α} {i j :
 α} (hi : i in s) (hj : j ∉ s) : s.image (swap i j) = insert j s \ {i}
参数：hi : i in s；hj : j ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
-/
lemma image_swap_of_mem_of_notMem {α : Type*} [DecidableEq α] {s : Set α} {i j : α}
    (hi : i ∈ s) (hj : j ∉ s) : s.image (swap i j) = insert j s \ {i} :=
  Set.ext fun a ↦ by
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain rfl | ne := eq_or_ne a i
      · rw [swap_apply_left]; exact ⟨.inl rfl, (ne_of_mem_of_not_mem hi hj).symm⟩
      · rw [swap_apply_of_ne_of_ne ne (ne_of_mem_of_not_mem ha hj)]; exact ⟨.inr ha, ne⟩
    · rintro ⟨rfl | has, hai⟩
      · exact ⟨i, hi, swap_apply_left ..⟩
      · exact ⟨a, has, swap_apply_of_ne_of_ne hai (ne_of_mem_of_not_mem has hj)⟩

namespace Perm

@[simp]
/-
**Equiv.Perm.sumCongr_swap_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sumCongr_swap_refl {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : α
) : Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.refl β) = Equiv.swap (Sum.inl i)
 (Sum.inl j)
参数：i j : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem sumCongr_swap_refl {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : α) :
    Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.refl β) = Equiv.swap (Sum.inl i) (Sum.inl j) := by
  aesop

@[simp]
/-
**Equiv.Perm.sumCongr_refl_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sumCongr_refl_swap {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : β
) : Equiv.Perm.sumCongr (Equiv.refl α) (Equiv.swap i j) = Equiv.swap (Sum.inr i)
 (Sum.inr j)
参数：i j : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem sumCongr_refl_swap {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : β) :
    Equiv.Perm.sumCongr (Equiv.refl α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) := by
  aesop

end Perm

/-- Augment an equivalence with a prescribed mapping `f a = b` -/
/-
**Equiv.setValue** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：setValue (f : α ≃ β) (a : α) (b : β) : α ≃ β
参数：f : α ≃ β；a : α；b : β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Augment an equivalence with a prescribed mapping `f a = b`
-/
def setValue (f : α ≃ β) (a : α) (b : β) : α ≃ β :=
  (swap a (f.symm b)).trans f

@[simp]
/-
**Equiv.setValue_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：setValue_eq (f : α ≃ β) (a : α) (b : β) : setValue f a b a = b
参数：f : α ≃ β；a : α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setValue_eq (f : α ≃ β) (a : α) (b : β) : setValue f a b a = b := by
  simp [setValue, swap_apply_left]

end Swap

end Equiv

namespace Function.Involutive

/-- Convert an involutive function `f` to a permutation with `toFun = invFun = f`. -/
/-
**Function.Involutive.toPerm** 是 Mathlib 中的一个定义，位于命名空间 `Function.Involutive`。
形式化陈述：toPerm (f : α -> α) (h : Involutive f) : Equiv.Perm α
参数：f : α -> α；h : Involutive f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.leftInverse`：∀ {α : Sort u} {f : α → α}, Function.In
volutive f → Function.LeftInverse f f
· 使用定理 `Function.Involutive.rightInverse`：∀ {α : Sort u} {f : α → α}, Function.I
nvolutive f → Function.RightInverse f f

--- 原说明 ---
Convert an involutive function `f` to a permutation with `toFun = invFun = f`.
-/
def toPerm (f : α → α) (h : Involutive f) : Equiv.Perm α :=
  ⟨f, f, h.leftInverse, h.rightInverse⟩

@[simp]
/-
**Function.Involutive.coe_toPerm** 是 Mathlib 中的一个定理，位于命名空间 `Function.Involutive`
。
形式化陈述：coe_toPerm {f : α -> α} (h : Involutive f) : (h.toPerm f : α -> α) = f
参数：h : Involutive f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toPerm {f : α → α} (h : Involutive f) : (h.toPerm f : α → α) = f :=
  rfl

@[simp]
/-
**Function.Involutive.toPerm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Function.Involutive
`。
形式化陈述：toPerm_symm {f : α -> α} (h : Involutive f) : (h.toPerm f).symm = h.toPerm
 f
参数：h : Involutive f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toPerm_symm {f : α → α} (h : Involutive f) : (h.toPerm f).symm = h.toPerm f :=
  rfl
/-
**Function.Involutive.toPerm_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Function.Invo
lutive`。
形式化陈述：toPerm_involutive {f : α -> α} (h : Involutive f) : Involutive (h.toPerm f
)
参数：h : Involutive f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPerm_involutive {f : α → α} (h : Involutive f) : Involutive (h.toPerm f) :=
  h
/-
**Function.Involutive.symm_eq_self_of_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Func
tion.Involutive`。
形式化陈述：symm_eq_self_of_involutive (f : Equiv.Perm α) (h : Involutive f) : f.symm 
= f
参数：f : Equiv.Perm α；h : Involutive f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Involutive.leftInverse_iff`：leftInverse_iff {g : α -> α} : g.Le
ftInverse f ↔ g = f
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem symm_eq_self_of_involutive (f : Equiv.Perm α) (h : Involutive f) : f.symm = f :=
  DFunLike.coe_injective (h.leftInverse_iff.mp f.left_inv)

end Function.Involutive

/-
**PLift.eq_up_iff_down_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PLift.eq_up_iff_down_eq {x : PLift α} {y : α} : x = PLift.up y ↔ x.down = 
y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem PLift.eq_up_iff_down_eq {x : PLift α} {y : α} : x = PLift.up y ↔ x.down = y :=
  Equiv.plift.eq_symm_apply
/-
**Function.Injective.map_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.map_swap [DecidableEq α] [DecidableEq β] {f : α -> β} (
hf : Function.Injective f) (x y z : α) : f (Equiv.swap x y z) = Equiv.swap (f x)
 (f y) (f z)
参数：hf : Function.Injective f；x y z : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Function.Injective.map_swap [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (x y z : α) :
    f (Equiv.swap x y z) = Equiv.swap (f x) (f y) (f z) := by
  grind

namespace Equiv

section

/-- Transport dependent functions through an equivalence of the base space.
-/
@[simps apply, simps -isSimp symm_apply]
/-
**Equiv.piCongrLeft'** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piCongrLeft' (P : α -> Sort*) (e : α ≃ β) : (forall a, P a) ≃ forall b, P 
(e.symm b) where toFun f x
参数：P : α -> Sort*；e : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x

--- 原说明 ---
Transport dependent functions through an equivalence of the base space.
-/
def piCongrLeft' (P : α → Sort*) (e : α ≃ β) : (∀ a, P a) ≃ ∀ b, P (e.symm b) where
  toFun f x := f (e.symm x)
  invFun f x := (e.symm_apply_apply x).ndrec (f (e x))
  left_inv f := by grind
  right_inv f := by grind

/-- Note: the "obvious" statement `(piCongrLeft' P e).symm g a = g (e a)` doesn't typecheck: the
LHS would have type `P a` while the RHS would have type `P (e.symm (e a))`. For that reason,
we have to explicitly substitute along `e.symm (e a) = a` in the statement of this lemma. -/
add_decl_doc Equiv.piCongrLeft'_symm_apply

set_option backward.isDefEq.respectTransparency.types false in
/-- This lemma is impractical to state in the dependent case. -/
@[simp]
/-
**Equiv.piCongrLeft'_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_4} (P : Sort u_9) (e : α ≃ β),   (Equiv.piCon
grLeft' (fun x => P) e).symm = Equiv.piCongrLeft' (fun a => P) e.symm
参数：P : Sort u_9；e : α ≃ β；Equiv.piCongrLeft' (fun x => P) e；fun a => P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This lemma is impractical to state in the dependent case.
-/
theorem piCongrLeft'_symm (P : Sort*) (e : α ≃ β) :
    (piCongrLeft' (fun _ => P) e).symm = piCongrLeft' _ e.symm := by ext; simp [piCongrLeft']

/-- Note: the "obvious" statement `(piCongrLeft' P e).symm g a = g (e a)` doesn't typecheck: the
LHS would have type `P a` while the RHS would have type `P (e.symm (e a))`. This lemma is a way
around it in the case where `a` is of the form `e.symm b`, so we can use `g b` instead of
`g (e (e.symm b))`. -/
@[simp]
/-
**Equiv.piCongrLeft'_symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_4} (P : α → Sort u_9) (e : α ≃ β) (g : (b : β
) → P (e.symm b)) (b : β),   (Equiv.piCongrLeft' P e).symm g (e.symm b) = g b
参数：P : α → Sort u_9；e : α ≃ β；g : (b : β) → P (e.symm b)；b : β；Equiv.piCongrLeft
' P e；e.symm b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.piCongrLeft'_symm_apply`：∀ {α : Sort u_1} {β : Sort u_4} (P : α → 
Sort u_9) (e : α ≃ β) (f : (b : β) → P (e.symm b)) (x : α),   (Equiv.piCongrLeft
' P e).symm f x = ⋯…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_iff_eq`：∀ {α : Sort u_1} {a b : α}, a ≍ b ↔ a = b
· 使用定理 `eqRec_heq_iff`：∀ {β : Sort v} {α : Sort u} {a : α} {motive : (b : α) → a
 = b → Sort v} {b : α} {refl : motive a ⋯} {h : a = b} {c : β},   h ▸ refl ≍ c ↔
 re…
· 使用定理 `congr_arg_heq`：∀ {α : Sort u_1} {β : α → Sort u_2} (f : (a : α) → β a) {
a₁ a₂ : α}, a₁ = a₂ → f a₁ ≍ f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x

--- 原说明 ---
Note: the "obvious" statement `(piCongrLeft' P e).symm g a = g (e a)` doesn't ty
pecheck: the
LHS would have type `P a` while the RHS would have type `P (e.symm (e a))`. This
 lemma is a way
around it in the case where `a` is of the form `e.symm b`, so we can use `g b` i
nstead of
`g (e (e.symm b))`.
-/
lemma piCongrLeft'_symm_apply_apply (P : α → Sort*) (e : α ≃ β) (g : ∀ b, P (e.symm b)) (b : β) :
    (piCongrLeft' P e).symm g (e.symm b) = g b := by
  rw [piCongrLeft'_symm_apply, ← heq_iff_eq, eqRec_heq_iff]
  exact congr_arg_heq _ (e.apply_symm_apply _)

@[simp]
/-
**Equiv.piCongrLeft'_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u_1} (P : α → Sort u_9), Equiv.piCongrLeft' P (Equiv.refl α) =
 Equiv.refl ((a : α) → P a)
参数：P : α → Sort u_9；Equiv.refl α；(a : α) → P a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
lemma piCongrLeft'_refl (P : α → Sort*) : piCongrLeft' P (.refl α) = .refl (∀ a, P a) := rfl

end

section

variable (P : β → Sort w) (e : α ≃ β)

/-- Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".
-/
/-
**Equiv.piCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piCongrLeft : (forall a, P (e a)) ≃ forall b, P b
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".
-/
def piCongrLeft : (∀ a, P (e a)) ≃ ∀ b, P b :=
  (piCongrLeft' P e.symm).symm

/-- Note: the "obvious" statement `(piCongrLeft P e) f b = f (e.symm b)` doesn't typecheck: the
LHS would have type `P b` while the RHS would have type `P (e (e.symm b))`. For that reason,
we have to explicitly substitute along `e (e.symm b) = b` in the statement of this lemma. -/
/-
**Equiv.piCongrLeft_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：piCongrLeft_apply (f : forall a, P (e a)) (b : β) : (piCongrLeft P e) f b 
= e.apply_symm_apply b ▸ f (e.symm b)
参数：f : forall a, P (e a)；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note: the "obvious" statement `(piCongrLeft P e) f b = f (e.symm b)` doesn't typ
echeck: the
LHS would have type `P b` while the RHS would have type `P (e (e.symm b))`. For 
that reason,
we have to explicitly substitute along `e (e.symm b) = b` in the statement of th
is lemma.
-/
lemma piCongrLeft_apply (f : ∀ a, P (e a)) (b : β) :
    (piCongrLeft P e) f b = e.apply_symm_apply b ▸ f (e.symm b) :=
  rfl

@[simp, grind =]
/-
**Equiv.piCongrLeft_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：piCongrLeft_symm_apply (g : forall b, P b) (a : α) : (piCongrLeft P e).sym
m g a = g (e a)
参数：g : forall b, P b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.piCongrLeft'_apply`：∀ {α : Sort u_1} {β : Sort u_4} (P : α → Sort 
u_9) (e : α ≃ β) (f : (a : α) → P a) (x : β),   (Equiv.piCongrLeft' P e) f x = f
 (e.symm x)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma piCongrLeft_symm_apply (g : ∀ b, P b) (a : α) :
    (piCongrLeft P e).symm g a = g (e a) :=
  piCongrLeft'_apply P e.symm g a

@[simp]
/-
**Equiv.piCongrLeft_refl** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：piCongrLeft_refl (P : α -> Sort*) : piCongrLeft P (.refl α) = .refl (foral
l a, P a)
参数：P : α -> Sort*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
lemma piCongrLeft_refl (P : α → Sort*) : piCongrLeft P (.refl α) = .refl (∀ a, P a) :=
  rfl

/-- Note: the "obvious" statement `(piCongrLeft P e) f b = f (e.symm b)` doesn't typecheck: the
LHS would have type `P b` while the RHS would have type `P (e (e.symm b))`. This lemma is a way
around it in the case where `b` is of the form `e a`, so we can use `f a` instead of
`f (e.symm (e a))`. -/
@[simp, grind =]
/-
**Equiv.piCongrLeft_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：piCongrLeft_apply_apply (f : forall a, P (e a)) (a : α) : (piCongrLeft P e
) f (e a) = f a
参数：f : forall a, P (e a)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.piCongrLeft'_symm_apply_apply`：∀ {α : Sort u_1} {β : Sort u_4} (P 
: α → Sort u_9) (e : α ≃ β) (g : (b : β) → P (e.symm b)) (b : β),   (Equiv.piCon
grLeft' P e).symm g (e.sy…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Note: the "obvious" statement `(piCongrLeft P e) f b = f (e.symm b)` doesn't typ
echeck: the
LHS would have type `P b` while the RHS would have type `P (e (e.symm b))`. This
 lemma is a way
around it in the case where `b` is of the form `e a`, so we can use `f a` instea
d of
`f (e.symm (e a))`.
-/
lemma piCongrLeft_apply_apply (f : ∀ a, P (e a)) (a : α) :
    (piCongrLeft P e) f (e a) = f a :=
  piCongrLeft'_symm_apply_apply P e.symm f a

open Sum
/-
**Equiv.piCongrLeft_apply_eq_cast** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：piCongrLeft_apply_eq_cast {P : β -> Sort v} {e : α ≃ β} (f : (a : α) -> P 
(e a)) (b : β) : piCongrLeft P e f b = cast (congr_arg P (e.apply_symm_apply b))
 (f (e.symm b))
参数：f : (a : α) -> P (e a)；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eqRec_eq_cast`：∀ {α : Sort u_1} {a : α} {motive : (a' : α) → a = a' → So
rt u_2} (x : motive a ⋯) {a' : α} (e : a = a'),   e ▸ x = cast ⋯ x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma piCongrLeft_apply_eq_cast {P : β → Sort v} {e : α ≃ β}
    (f : (a : α) → P (e a)) (b : β) :
    piCongrLeft P e f b = cast (congr_arg P (e.apply_symm_apply b)) (f (e.symm b)) :=
  eqRec_eq_cast _ _
/-
**Equiv.piCongrLeft_sumInl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：piCongrLeft_sumInl {ι ι' ι''} (π : ι'' -> Type*) (e : ι oplus ι' ≃ ι'') (f
 : forall i, π (e (inl i))) (g : forall i, π (e (inr i))) (i : ι) : piCongrLeft 
π e (sumPiEquivProdPi (fun x => π (e x)) |>.symm (f, g)) (e (inl i)) = f i
参数：π : ι'' -> Type*；e : ι oplus ι' ≃ ι''；f : forall i, π (e (inl i))；g : forall 
i, π (e (inr i))；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrLeft_sumInl {ι ι' ι''} (π : ι'' → Type*) (e : ι ⊕ ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
    (g : ∀ i, π (e (inr i))) (i : ι) :
    piCongrLeft π e (sumPiEquivProdPi (fun x => π (e x)) |>.symm (f, g)) (e (inl i)) = f i := by
  grind
/-
**Equiv.piCongrLeft_sumInr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：piCongrLeft_sumInr {ι ι' ι''} (π : ι'' -> Type*) (e : ι oplus ι' ≃ ι'') (f
 : forall i, π (e (inl i))) (g : forall i, π (e (inr i))) (j : ι') : piCongrLeft
 π e (sumPiEquivProdPi (fun x => π (e x)) |>.symm (f, g)) (e (inr j)) = g j
参数：π : ι'' -> Type*；e : ι oplus ι' ≃ ι''；f : forall i, π (e (inl i))；g : forall 
i, π (e (inr i))；j : ι'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrLeft_sumInr {ι ι' ι''} (π : ι'' → Type*) (e : ι ⊕ ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
    (g : ∀ i, π (e (inr i))) (j : ι') :
    piCongrLeft π e (sumPiEquivProdPi (fun x => π (e x)) |>.symm (f, g)) (e (inr j)) = g j := by
  grind

end

section

variable {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : ∀ a : α, W a ≃ Z (h₁ a))

/-- Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibers.
-/
/-
**Equiv.piCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piCongr : (forall a, W a) ≃ forall b, Z b
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibers.
-/
def piCongr : (∀ a, W a) ≃ ∀ b, Z b :=
  (Equiv.piCongrRight h₂).trans (Equiv.piCongrLeft _ h₁)

@[simp]
/-
**Equiv.coe_piCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_piCongr_symm : ((h₁.piCongr h₂).symm : (forall b, Z b) -> forall a, W 
a) = fun f a => (h₂ a).symm (f (h₁ a))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_piCongr_symm :
    ((h₁.piCongr h₂).symm : (∀ b, Z b) → ∀ a, W a) = fun f a => (h₂ a).symm (f (h₁ a)) :=
  rfl

@[simp, grind =]
/-
**Equiv.piCongr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：piCongr_symm_apply (f : forall b, Z b) : (h₁.piCongr h₂).symm f = fun a =>
 (h₂ a).symm (f (h₁ a))
参数：f : forall b, Z b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem piCongr_symm_apply (f : ∀ b, Z b) :
    (h₁.piCongr h₂).symm f = fun a => (h₂ a).symm (f (h₁ a)) :=
  rfl

@[simp, grind =]
/-
**Equiv.piCongr_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：piCongr_apply_apply (f : forall a, W a) (a : α) : h₁.piCongr h₂ f (h₁ a) =
 h₂ a (f a)
参数：f : forall a, W a；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.piCongr.eq_1`：∀ {α : Sort u_1} {β : Sort u_4} {W : α → Sort w} {Z 
: β → Sort z} (h₁ : α ≃ β) (h₂ : (a : α) → W a ≃ Z (h₁ a)),   h₁.piCongr h₂ = (E
quiv.piC…
· 使用定理 `Equiv.trans_apply`：∀ {α : Sort u} {β : Sort v} {γ : Sort w} (f : α ≃ β) 
(g : β ≃ γ) (a : α), (f.trans g) a = g (f a)
· 使用引理 `Equiv.piCongrLeft_apply_apply`：piCongrLeft_apply_apply (f : forall a, P 
(e a)) (a : α) : (piCongrLeft P e) f (e a) = f a
· 使用定理 `Equiv.piCongrRight_apply`：∀ {α : Sort u_1} {β₁ : α → Sort u_9} {β₂ : α →
 Sort u_10} (F : (a : α) → β₁ a ≃ β₂ a) (a : (i : α) → β₁ i) (i : α),   (Equiv.p
iCongrRight F)…
· 使用引理 `Pi.map_apply`：map_apply (f : forall i, α i -> β i) (a : forall i, α i) (
i : ι) : Pi.map f a i = f i (a i)
-/
theorem piCongr_apply_apply (f : ∀ a, W a) (a : α) : h₁.piCongr h₂ f (h₁ a) = h₂ a (f a) := by
  rw [piCongr, trans_apply, piCongrLeft_apply_apply, piCongrRight_apply, Pi.map_apply]

end

section

variable {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : ∀ b : β, W (h₁.symm b) ≃ Z b)

/-- Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibres.
-/
/-
**Equiv.piCongr'** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piCongr' : (forall a, W a) ≃ forall b, Z b
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibres.
-/
def piCongr' : (∀ a, W a) ≃ ∀ b, Z b :=
  (piCongr h₁.symm fun b => (h₂ b).symm).symm

@[simp]
/-
**Equiv.coe_piCongr'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_piCongr' : (h₁.piCongr' h₂ : (forall a, W a) -> forall b, Z b) = fun f
 b => h₂ b f h₁.symm b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_piCongr' :
    (h₁.piCongr' h₂ : (∀ a, W a) → ∀ b, Z b) = fun f b => h₂ b <| f <| h₁.symm b :=
  rfl
/-
**Equiv.piCongr'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_4} {W : α → Sort w} {Z : β → Sort z} (h₁ : α 
≃ β) (h₂ : (b : β) → W (h₁.symm b) ≃ Z b)   (f : (a : α) → W a), (h₁.piCongr' h₂
) f = fun b => (h₂ b) (f (h₁.symm b))
参数：h₁ : α ≃ β；h₂ : (b : β) → W (h₁.symm b) ≃ Z b；f : (a : α) → W a；h₁.piCongr' h
₂；h₂ b；f (h₁.symm b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem piCongr'_apply (f : ∀ a, W a) : h₁.piCongr' h₂ f = fun b => h₂ b <| f <| h₁.symm b :=
  rfl

@[simp]
/-
**Equiv.piCongr'_symm_apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_4} {W : α → Sort w} {Z : β → Sort z} (h₁ : α 
≃ β) (h₂ : (b : β) → W (h₁.symm b) ≃ Z b)   (f : (b : β) → Z b) (b : β), (h₁.piC
ongr' h₂).symm f (h₁.symm b) = (h₂ b).symm (f b)
参数：h₁ : α ≃ β；h₂ : (b : β) → W (h₁.symm b) ≃ Z b；f : (b : β) → Z b；b : β；h₁.piCo
ngr' h₂；h₁.symm b；h₂ b；f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.piCongr_apply_apply`：piCongr_apply_apply (f : forall a, W a) (a : 
α) : h₁.piCongr h₂ f (h₁ a) = h₂ a (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piCongr'_symm_apply_symm_apply (f : ∀ b, Z b) (b : β) :
    (h₁.piCongr' h₂).symm f (h₁.symm b) = (h₂ b).symm (f b) := by
  simp [piCongr', piCongr_apply_apply]

end

variable {α : Type*} {β : Type*} {f : α → β}

/-- A family of equivalences `∀ a, γ₁ a ≃ γ₂ a` generates an equivalence between the product
over the fibers of a function `f : α → β` on index types. -/
/-
**Equiv.piCongrSigmaFiber** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piCongrSigmaFiber {γ₁ γ₂ : α -> Sort*} (e : (a : α) -> γ₁ a ≃ γ₂ a) : ((σ 
: (y : β) × { x : α // f x = y }) -> γ₁ σ.2.1) ≃ ((a : α) -> γ₂ a)
参数：e : (a : α) -> γ₁ a ≃ γ₂ a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
A family of equivalences `∀ a, γ₁ a ≃ γ₂ a` generates an equivalence between the
 product
over the fibers of a function `f : α → β` on index types.
-/
def piCongrSigmaFiber {γ₁ γ₂ : α → Sort*} (e : (a : α) → γ₁ a ≃ γ₂ a) :
    ((σ : (y : β) × { x : α // f x = y }) → γ₁ σ.2.1) ≃ ((a : α) → γ₂ a) :=
  piCongrLeft γ₁ (sigmaFiberEquiv f) |>.trans (piCongrRight e)

@[simp]
/-
**Equiv.piCongrSigmaFiber_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：piCongrSigmaFiber_apply {γ₁ γ₂ : α -> Sort*} (e : (a : α) -> γ₁ a ≃ γ₂ a) 
(g : (σ : (y : β) × { x : α // f x = y }) -> γ₁ σ.2.1) (a : α) : piCongrSigmaFib
er e g a = e a (g ⟨f a, ⟨a, rfl⟩⟩)
参数：e : (a : α) -> γ₁ a ≃ γ₂ a；g : (σ : (y : β) × { x : α // f x = y }) -> γ₁ σ.2
.1；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrSigmaFiber_apply {γ₁ γ₂ : α → Sort*} (e : (a : α) → γ₁ a ≃ γ₂ a)
    (g : (σ : (y : β) × { x : α // f x = y }) → γ₁ σ.2.1) (a : α) :
    piCongrSigmaFiber e g a = e a (g ⟨f a, ⟨a, rfl⟩⟩) := rfl

@[simp]
/-
**Equiv.piCongrSigmaFiber_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：piCongrSigmaFiber_symm_apply {γ₁ γ₂ : α -> Sort*} (e : (a : α) -> γ₁ a ≃ γ
₂ a) (g : (a : α) -> γ₂ a) (σ : (y : β) × { x : α // f x = y }) : (piCongrSigmaF
iber e).symm g σ = (e σ.2.1).symm (g σ.2.1)
参数：e : (a : α) -> γ₁ a ≃ γ₂ a；g : (a : α) -> γ₂ a；σ : (y : β) × { x : α // f x =
 y }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem piCongrSigmaFiber_symm_apply {γ₁ γ₂ : α → Sort*} (e : (a : α) → γ₁ a ≃ γ₂ a)
    (g : (a : α) → γ₂ a) (σ : (y : β) × { x : α // f x = y }) :
    (piCongrSigmaFiber e).symm g σ = (e σ.2.1).symm (g σ.2.1) := rfl

/-- Let `f : α → β` be a function on index types. A family of equivalences, indexed by `b : β`,
between the product over the fiber of `b` under `f` given as
`∀ (σ : { a : α // f a = b }) → γ₁ σ.1) ≃ γ₂ b` lifts to an equivalence over the products
`∀ a, γ₁ a ≃ ∀ b, γ₂ b`. -/
/-
**Equiv.piCongrFiberwise** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piCongrFiberwise {γ₁ : α -> Type*} {γ₂ : β -> Type*} {f : α -> β} (e : (b 
: β) -> ((σ : { a : α // f a = b }) -> γ₁ σ.1) ≃ γ₂ b) : ((a : α) -> γ₁ a) ≃ ((b
 : β) -> γ₂ b)
参数：e : (b : β) -> ((σ : { a : α // f a = b }) -> γ₁ σ.1) ≃ γ₂ b。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Let `f : α → β` be a function on index types. A family of equivalences, indexed 
by `b : β`,
between the product over the fiber of `b` under `f` given as
`∀ (σ : { a : α // f a = b }) → γ₁ σ.1) ≃ γ₂ b` lifts to an equivalence over the
 products
`∀ a, γ₁ a ≃ ∀ b, γ₂ b`.
-/
def piCongrFiberwise {γ₁ : α → Type*} {γ₂ : β → Type*} {f : α → β}
    (e : (b : β) → ((σ : { a : α // f a = b }) → γ₁ σ.1) ≃ γ₂ b) :
    ((a : α) → γ₁ a) ≃ ((b : β) → γ₂ b) :=
  ((piCongrSigmaFiber (fun _ => Equiv.refl _)).symm.trans
    (piCurry fun b (x : { x : α // f x = b }) => γ₁ x.1)).trans
      (piCongrRight e)

@[simp]
/-
**Equiv.piCongrFiberwise_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：piCongrFiberwise_apply {γ₁ : α -> Type*} {γ₂ : β -> Type*} {f : α -> β} (e
 : (b : β) -> ((σ : { a : α // f a = b }) -> γ₁ σ.1) ≃ γ₂ b) (g : (a : α) -> γ₁ 
a) (b : β) : piCongrFiberwise e g b = e b fun σ => g σ.1
参数：e : (b : β) -> ((σ : { a : α // f a = b }) -> γ₁ σ.1) ≃ γ₂ b；g : (a : α) -> γ
₁ a；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrFiberwise_apply {γ₁ : α → Type*} {γ₂ : β → Type*} {f : α → β}
    (e : (b : β) → ((σ : { a : α // f a = b }) → γ₁ σ.1) ≃ γ₂ b) (g : (a : α) → γ₁ a) (b : β) :
    piCongrFiberwise e g b = e b fun σ => g σ.1 := rfl

@[simp]
/-
**Equiv.piCongrFiberwise_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：piCongrFiberwise_symm_apply {γ₁ : α -> Type*} {γ₂ : β -> Type*} {f : α -> 
β} (e : (b : β) -> ((σ : { a : α // f a = b }) -> γ₁ σ.1) ≃ γ₂ b) (g : (b : β) -
> γ₂ b) (a : α) : (piCongrFiberwise e).symm g a = (e (f a)).symm (g (f a)) ⟨a, r
fl⟩
参数：e : (b : β) -> ((σ : { a : α // f a = b }) -> γ₁ σ.1) ≃ γ₂ b；g : (b : β) -> γ
₂ b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem piCongrFiberwise_symm_apply {γ₁ : α → Type*} {γ₂ : β → Type*} {f : α → β}
    (e : (b : β) → ((σ : { a : α // f a = b }) → γ₁ σ.1) ≃ γ₂ b) (g : (b : β) → γ₂ b) (a : α) :
    (piCongrFiberwise e).symm g a = (e (f a)).symm (g (f a)) ⟨a, rfl⟩ := rfl

/-- Transport dependent functions through an equality of sets. -/
/-
**Equiv.piCongrSet** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_11} →   {W : α → Sort w} → {s t : Set α} → s = t → ((i : { i /
/ i ∈ s }) → W ↑i) ≃ ((i : { i // i ∈ t }) → W ↑i)
参数：(i : { i // i ∈ s }) → W ↑i；(i : { i // i ∈ t }) → W ↑i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport dependent functions through an equality of sets.
-/
@[simps!] def piCongrSet {α} {W : α → Sort w} {s t : Set α} (h : s = t) :
    (∀ i : {i // i ∈ s}, W i) ≃ (∀ i : {i // i ∈ t}, W i) where
  toFun f i := f ⟨i, h ▸ i.2⟩
  invFun f i := f ⟨i, h.symm ▸ i.2⟩
/-
**Equiv.eq_conj** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：eq_conj {α α' β β' : Sort*} (ε₁ : α ≃ α') (ε₂ : β' ≃ β) (f : α -> β) (f' :
 α' -> β') : ε₂.symm ∘ f ∘ ε₁.symm = f' ↔ f = ε₂ ∘ f' ∘ ε₁
参数：ε₁ : α ≃ α'；ε₂ : β' ≃ β；f : α -> β；f' : α' -> β'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_comp_eq`：symm_comp_eq {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ
 -> β) : e.symm ∘ g = f ↔ g = e ∘ f
· 使用定理 `Equiv.comp_symm_eq`：comp_symm_eq {α β γ} (e : α ≃ β) (f : β -> γ) (g : α
 -> γ) : g ∘ e.symm = f ↔ g = f ∘ e
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eq_conj {α α' β β' : Sort*} (ε₁ : α ≃ α') (ε₂ : β' ≃ β)
    (f : α → β) (f' : α' → β') : ε₂.symm ∘ f ∘ ε₁.symm = f' ↔ f = ε₂ ∘ f' ∘ ε₁ := by
  rw [Equiv.symm_comp_eq, Equiv.comp_symm_eq, Function.comp_assoc]

section BinaryOp

variable {α₁ β₁ : Type*} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁)

/-
**Equiv.semiconj_conj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：semiconj_conj (f : α₁ -> α₁) : Semiconj e f (e.conj f)
参数：f : α₁ -> α₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.conj_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (f : α → α) (a
 : β), e.conj f a = e (f (e.symm a))
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem semiconj_conj (f : α₁ → α₁) : Semiconj e f (e.conj f) := fun x => by simp
/-
**Equiv.semiconj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem semiconj₂_conj : Semiconj₂ e f (e.arrowCongr e.conj f) := fun x y => by simp [arrowCongr]
/-
**Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Associative f] : Std.Associative (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).isAssociative_right e.surjective
/-
**Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.IdempotentOp f] : Std.IdempotentOp (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).isIdempotent_right e.surjective

end BinaryOp

section ULift

@[simp]
/-
**Equiv.ulift_symm_down** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：ulift_symm_down {α} (x : α) : (Equiv.ulift.{u, v}.symm x).down = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem ulift_symm_down {α} (x : α) : (Equiv.ulift.{u, v}.symm x).down = x :=
  rfl

end ULift

end Equiv

/-
**Function.Injective.swap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.swap_apply [DecidableEq α] [DecidableEq β] {f : α -> β}
 (hf : Function.Injective f) (x y z : α) : Equiv.swap (f x) (f y) (f z) = f (Equ
iv.swap x y z)
参数：hf : Function.Injective f；x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.map_swap`：Function.Injective.map_swap [DecidableEq α]
 [DecidableEq β] {f : α -> β} (hf : Function.Injective f) (x y z : α) : f (Equiv
.swap x y z) = Eq…
-/
theorem Function.Injective.swap_apply
    [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f) (x y z : α) :
    Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z) :=
  Eq.symm (map_swap hf x y z)
/-
**Function.Injective.swap_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.swap_comp [DecidableEq α] [DecidableEq β] {f : α -> β} 
(hf : Function.Injective f) (x y : α) : Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.s
wap x y
参数：hf : Function.Injective f；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.swap_apply`：Function.Injective.swap_apply [DecidableE
q α] [DecidableEq β] {f : α -> β} (hf : Function.Injective f) (x y z : α) : Equi
v.swap (f x) (f y) …
-/
theorem Function.Injective.swap_comp
    [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f) (x y : α) :
    Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y :=
  funext fun _ => hf.swap_apply _ _ _

/-- To give an equivalence between two subsingleton types, it is sufficient to give any two
functions between them. -/
/-
**equivOfSubsingletonOfSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：equivOfSubsingletonOfSubsingleton [Subsingleton α] [Subsingleton β] (f : α
 -> β) (g : β -> α) : α ≃ β where toFun
参数：f : α -> β；g : β -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To give an equivalence between two subsingleton types, it is sufficient to give 
any two
functions between them.
-/
def equivOfSubsingletonOfSubsingleton [Subsingleton α] [Subsingleton β] (f : α → β) (g : β → α) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- A nonempty subsingleton type is (noncomputably) equivalent to `PUnit`. -/
/-
**Equiv.punitOfNonemptyOfSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equiv.punitOfNonemptyOfSubsingleton [h : Nonempty α] [Subsingleton α] : α 
≃ PUnit
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}

--- 原说明 ---
A nonempty subsingleton type is (noncomputably) equivalent to `PUnit`.
-/
noncomputable def Equiv.punitOfNonemptyOfSubsingleton [h : Nonempty α] [Subsingleton α] :
    α ≃ PUnit :=
  equivOfSubsingletonOfSubsingleton (fun _ => PUnit.unit) fun _ => h.some

/-- `Unique (Unique α)` is equivalent to `Unique α`. -/
/-
**uniqueUniqueEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：uniqueUniqueEquiv : Unique (Unique α) ≃ Unique α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Unique (Unique α)` is equivalent to `Unique α`.
-/
def uniqueUniqueEquiv : Unique (Unique α) ≃ Unique α :=
  equivOfSubsingletonOfSubsingleton (fun h => h.default) fun h =>
    { default := h, uniq := fun _ => Subsingleton.elim _ _ }

/-- If `Unique β`, then `Unique α` is equivalent to `α ≃ β`. -/
/-
**uniqueEquivEquivUnique** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：uniqueEquivEquivUnique (α : Sort u) (β : Sort v) [Unique β] : Unique α ≃ (
α ≃ β)
参数：α : Sort u；β : Sort v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Unique β`, then `Unique α` is equivalent to `α ≃ β`.
-/
def uniqueEquivEquivUnique (α : Sort u) (β : Sort v) [Unique β] : Unique α ≃ (α ≃ β) :=
  equivOfSubsingletonOfSubsingleton (fun _ => Equiv.ofUnique _ _) Equiv.unique

namespace Function

variable {α' : Sort*}

/-
**Function.update_comp_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_comp_equiv [DecidableEq α'] [DecidableEq α] (f : α -> β) (g : α' ≃ 
α) (a : α) (v : β) : update f a v ∘ g = update (f ∘ g) (g.symm a) v
参数：f : α -> β；g : α' ≃ α；a : α；v : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.update_comp_eq_of_injective`：update_comp_eq_of_injective {β : S
ort*} (g : α' -> β) {f : α -> α'} (hf : Function.Injective f) (i : α) (a : β) : 
Function.update g (f i) a …
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem update_comp_equiv [DecidableEq α'] [DecidableEq α] (f : α → β)
    (g : α' ≃ α) (a : α) (v : β) :
    update f a v ∘ g = update (f ∘ g) (g.symm a) v := by
  rw [← update_comp_eq_of_injective _ g.injective, g.apply_symm_apply]
/-
**Function.update_apply_equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_apply_equiv_apply [DecidableEq α'] [DecidableEq α] (f : α -> β) (g 
: α' ≃ α) (a : α) (v : β) (a' : α') : update f a v (g a') = update (f ∘ g) (g.sy
mm a) v a'
参数：f : α -> β；g : α' ≃ α；a : α；v : β；a' : α'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.update_comp_equiv`：update_comp_equiv [DecidableEq α'] [Decidabl
eEq α] (f : α -> β) (g : α' ≃ α) (a : α) (v : β) : update f a v ∘ g = update (f 
∘ g) (g.symm a) …
-/
theorem update_apply_equiv_apply [DecidableEq α'] [DecidableEq α] (f : α → β)
    (g : α' ≃ α) (a : α) (v : β) (a' : α') : update f a v (g a') = update (f ∘ g) (g.symm a) v a' :=
  congr_fun (update_comp_equiv f g a v) a'
/-
**Function.piCongrLeft'_update** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_4} [inst : DecidableEq α] [inst_1 : Decidable
Eq β] (P : α → Sort u_10) (e : α ≃ β)   (f : (a : α) → P a) (b : β) (x : P (e.sy
mm b)),   (Equiv.piCongrLeft' P e) (Function.update f (e.symm b) x) = Function.u
pdate ((Equiv.piCongrLeft' P e) f) b x
参数：P : α → Sort u_10；e : α ≃ β；f : (a : α) → P a；b : β；x : P (e.symm b)；Equiv.pi
CongrLeft' P e；Function.update f (e.symm b) x；(Equiv.piCongrLeft' P e) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.piCongrLeft'_apply`：∀ {α : Sort u_1} {β : Sort u_4} (P : α → Sort 
u_9) (e : α ≃ β) (f : (a : α) → P a) (x : β),   (Equiv.piCongrLeft' P e) f x = f
 (e.symm x)
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem piCongrLeft'_update [DecidableEq α] [DecidableEq β] (P : α → Sort*) (e : α ≃ β)
    (f : ∀ a, P a) (b : β) (x : P (e.symm b)) :
    e.piCongrLeft' P (update f (e.symm b) x) = update (e.piCongrLeft' P f) b x := by
  ext b'
  rcases eq_or_ne b' b with (rfl | h) <;> simp_all
/-
**Function.piCongrLeft'_symm_update** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_4} [inst : DecidableEq α] [inst_1 : Decidable
Eq β] (P : α → Sort u_10) (e : α ≃ β)   (f : (b : β) → P (e.symm b)) (b : β) (x 
: P (e.symm b)),   (Equiv.piCongrLeft' P e).symm (Function.update f b x) = Funct
ion.update ((Equiv.piCongrLeft' P e).symm f) (e.symm b) x
参数：P : α → Sort u_10；e : α ≃ β；f : (b : β) → P (e.symm b)；b : β；x : P (e.symm b)
；Equiv.piCongrLeft' P e；Function.update f b x；(Equiv.piCongrLeft' P e).symm f；e.
symm b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.piCongrLeft'_update`：∀ {α : Sort u_1} {β : Sort u_4} [inst : De
cidableEq α] [inst_1 : DecidableEq β] (P : α → Sort u_10) (e : α ≃ β)   (f : (a 
: α) → P a) (b : β…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piCongrLeft'_symm_update [DecidableEq α] [DecidableEq β] (P : α → Sort*) (e : α ≃ β)
    (f : ∀ b, P (e.symm b)) (b : β) (x : P (e.symm b)) :
    (e.piCongrLeft' P).symm (update f b x) = update ((e.piCongrLeft' P).symm f) (e.symm b) x := by
  simp [(e.piCongrLeft' P).symm_apply_eq, piCongrLeft'_update]

end Function

