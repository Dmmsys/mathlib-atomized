/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.AddConstMap.Basic

/-!
# Equivalences conjugating `(· + a)` to `(· + b)`

In this file we define `AddConstEquiv G H a b` (notation: `G ≃+c[a, b] H`)
to be the type of equivalences such that `∀ x, f (x + a) = f x + b`.

We also define the corresponding typeclass and prove some basic properties.
-/

@[expose] public section

assert_not_exists Finset

open Function
open scoped AddConstMap

/-- An equivalence between `G` and `H` conjugating `(· + a)` to `(· + b)`,
denoted as `G ≃+c[a, b] H`. -/
/-
**AddConstEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → (H : Type u_2) → [Add G] → [Add H] → G → H → Type (max u_
1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between `G` and `H` conjugating `(· + a)` to `(· + b)`,
denoted as `G ≃+c[a, b] H`.
-/
structure AddConstEquiv (G H : Type*) [Add G] [Add H] (a : G) (b : H)
  extends G ≃ H, G →+c[a, b] H

/-- Interpret an `AddConstEquiv` as an `Equiv`. -/
add_decl_doc AddConstEquiv.toEquiv

/-- Interpret an `AddConstEquiv` as an `AddConstMap`. -/
add_decl_doc AddConstEquiv.toAddConstMap

@[inherit_doc]
scoped[AddConstMap] notation:25 G " ≃+c[" a ", " b "] " H => AddConstEquiv G H a b

namespace AddConstEquiv

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

/-
**AddConstEquiv.toEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `AddConstEquiv`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Add G] [inst_1 : Add H] {a : G} {b
 : H},   Function.Injective AddConstEquiv.toEquiv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEquiv_injective : Injective (toEquiv : (G ≃+c[a, b] H) → G ≃ H)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
/-
**AddConstEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AddConstEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G H : Type*} [Add G] [Add H] {a : G} {b : H} :
    EquivLike (G ≃+c[a, b] H) G H where
  coe f := f.toEquiv
  inv f := f.toEquiv.symm
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toEquiv_injective <| DFunLike.ext' h
/-
**AddConstEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AddConstEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G H : Type*} [Add G] [Add H] {a : G} {b : H} :
    AddConstMapClass (G ≃+c[a, b] H) G H a b where
  map_add_const f x := f.map_add_const' x
/-
**AddConstEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `AddConstEquiv`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Add G] [inst_1 : Add H] {a : G} {b
 : H} {e₁ e₂ : AddConstEquiv G H a b},   (∀ (x : G), e₁ x = e₂ x) → e₁ = e₂
参数：∀ (x : G), e₁ x = e₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
@[ext] lemma ext {e₁ e₂ : G ≃+c[a, b] H} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ := DFunLike.ext _ _ h

@[simp]
/-
**AddConstEquiv.toEquiv_inj** 是 Mathlib 中的一个引理，位于命名空间 `AddConstEquiv`。
形式化陈述：toEquiv_inj {e₁ e₂ : G ≃+c[a, b] H} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AddConstEquiv.toEquiv_injective`：∀ {G : Type u_1} {H : Type u_2} [inst :
 Add G] [inst_1 : Add H] {a : G} {b : H},   Function.Injective AddConstEquiv.toE
quiv
-/
lemma toEquiv_inj {e₁ e₂ : G ≃+c[a, b] H} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff
/-
**AddConstEquiv.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AddConstEquiv`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Add G] [inst_1 : Add H] {a : G} {b
 : H} (e : AddConstEquiv G H a b),   ⇑e.toEquiv = ⇑e
参数：e : AddConstEquiv G H a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toEquiv (e : G ≃+c[a, b] H) : ⇑e.toEquiv = e := rfl

/-- Inverse map of an `AddConstEquiv`, as an `AddConstEquiv`. -/
/-
**AddConstEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `AddConstEquiv`。
形式化陈述：symm (e : G ≃+c[a, b] H) : H ≃+c[b, a] G where toEquiv
参数：e : G ≃+c[a, b] H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Inverse map of an `AddConstEquiv`, as an `AddConstEquiv`.
-/
def symm (e : G ≃+c[a, b] H) : H ≃+c[b, a] G where
  toEquiv := e.toEquiv.symm
  map_add_const' := (AddConstMapClass.semiconj e).inverse_left e.left_inv e.right_inv

/-- A custom projection for `simps`. -/
/-
**AddConstEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `AddConstEquiv.Simps`
。
形式化陈述：{G : Type u_1} → {H : Type u_2} → [inst : Add G] → [inst_1 : Add H] → {a :
 G} → {b : H} → AddConstEquiv G H a b → H → G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A custom projection for `simps`.
-/
def Simps.symm_apply (e : G ≃+c[a, b] H) : H → G := e.symm

initialize_simps_projections AddConstEquiv (toFun → apply, invFun → symm_apply)
/-
**AddConstEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `AddConstEquiv`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Add G] [inst_1 : Add H] {a : G} {b
 : H} (e : AddConstEquiv G H a b),   e.symm.symm = e
参数：e : AddConstEquiv G H a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symm_symm (e : G ≃+c[a, b] H) : e.symm.symm = e := rfl
/-
**AddConstEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddConstEquiv`。
形式化陈述：symm_apply_eq (e : G ≃+c[a, b] H) {a b} : e.symm a = b ↔ a = e b
参数：e : G ≃+c[a, b] H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq (e : G ≃+c[a, b] H) {a b} :
    e.symm a = b ↔ a = e b :=
  e.toEquiv.symm_apply_eq
/-
**AddConstEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddConstEquiv`。
形式化陈述：eq_symm_apply (e : G ≃+c[a, b] H) {a b} : b = e.symm a ↔ e b = a
参数：e : G ≃+c[a, b] H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply (e : G ≃+c[a, b] H) {a b} :
    b = e.symm a ↔ e b = a :=
  e.toEquiv.eq_symm_apply
/-
**AddConstEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddConstEquiv`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Add G] [inst_1 : Add H] {a : G} {b
 : H} (e : AddConstEquiv G H a b) (a_1 : H),   e (e.symm a_1) = a_1
参数：e : AddConstEquiv G H a b；a_1 : H；e.symm a_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
@[simp] theorem apply_symm_apply (e : G ≃+c[a, b] H) (a) :
    e (e.symm a) = a :=
  e.toEquiv.apply_symm_apply _
/-
**AddConstEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddConstEquiv`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Add G] [inst_1 : Add H] {a : G} {b
 : H} (e : AddConstEquiv G H a b) (a_1 : G),   e.symm (e a_1) = a_1
参数：e : AddConstEquiv G H a b；a_1 : G；e a_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
@[simp] theorem symm_apply_apply (e : G ≃+c[a, b] H) (a) :
    e.symm (e a) = a :=
  e.toEquiv.symm_apply_apply _

/-- The identity map as an `AddConstEquiv`. -/
@[simps! toEquiv apply]
/-
**AddConstEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `AddConstEquiv`。
形式化陈述：refl (a : G) : G ≃+c[a, a] G where toEquiv
参数：a : G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The identity map as an `AddConstEquiv`.
-/
def refl (a : G) : G ≃+c[a, a] G where
  toEquiv := .refl G
  map_add_const' _ := rfl
/-
**AddConstEquiv.symm_refl** 是 Mathlib 中的一个定理，位于命名空间 `AddConstEquiv`。
形式化陈述：∀ {G : Type u_1} [inst : Add G] (a : G), (AddConstEquiv.refl a).symm = Add
ConstEquiv.refl a
参数：a : G；AddConstEquiv.refl a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symm_refl (a : G) : (refl a).symm = refl a := rfl

/-- Composition of `AddConstEquiv`s, as an `AddConstEquiv`. -/
@[simps! +simpRhs toEquiv apply]
/-
**AddConstEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `AddConstEquiv`。
形式化陈述：trans (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K) : G ≃+c[a, c] K where toEq
uiv
参数：e₁ : G ≃+c[a, b] H；e₂ : H ≃+c[b, c] K。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Composition of `AddConstEquiv`s, as an `AddConstEquiv`.
-/
def trans (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K) : G ≃+c[a, c] K where
  toEquiv := e₁.toEquiv.trans e₂.toEquiv
  map_add_const' := (AddConstMapClass.semiconj e₁).trans (AddConstMapClass.semiconj e₂)
/-
**AddConstEquiv.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `AddConstEquiv`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Add G] [inst_1 : Add H] {a : G} {b
 : H} (e : AddConstEquiv G H a b),   e.trans (AddConstEquiv.refl b) = e
参数：e : AddConstEquiv G H a b；AddConstEquiv.refl b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma trans_refl (e : G ≃+c[a, b] H) : e.trans (.refl b) = e := rfl
/-
**AddConstEquiv.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `AddConstEquiv`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Add G] [inst_1 : Add H] {a : G} {b
 : H} (e : AddConstEquiv G H a b),   (AddConstEquiv.refl a).trans e = e
参数：e : AddConstEquiv G H a b；AddConstEquiv.refl a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma refl_trans (e : G ≃+c[a, b] H) : (refl a).trans e = e := rfl

@[simp]
/-
**AddConstEquiv.self_trans_symm** 是 Mathlib 中的一个引理，位于命名空间 `AddConstEquiv`。
形式化陈述：self_trans_symm (e : G ≃+c[a, b] H) : e.trans e.symm = .refl a
参数：e : G ≃+c[a, b] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstEquiv.toEquiv_injective`：∀ {G : Type u_1} {H : Type u_2} [inst :
 Add G] [inst_1 : Add H] {a : G} {b : H},   Function.Injective AddConstEquiv.toE
quiv
· 使用定理 `Equiv.self_trans_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans 
e.symm = Equiv.refl α
-/
lemma self_trans_symm (e : G ≃+c[a, b] H) : e.trans e.symm = .refl a :=
  toEquiv_injective e.toEquiv.self_trans_symm

@[simp]
/-
**AddConstEquiv.symm_trans_self** 是 Mathlib 中的一个引理，位于命名空间 `AddConstEquiv`。
形式化陈述：symm_trans_self (e : G ≃+c[a, b] H) : e.symm.trans e = .refl b
参数：e : G ≃+c[a, b] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstEquiv.toEquiv_injective`：∀ {G : Type u_1} {H : Type u_2} [inst :
 Add G] [inst_1 : Add H] {a : G} {b : H},   Function.Injective AddConstEquiv.toE
quiv
· 使用定理 `Equiv.symm_trans_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.t
rans e = Equiv.refl β
-/
lemma symm_trans_self (e : G ≃+c[a, b] H) : e.symm.trans e = .refl b :=
  toEquiv_injective e.toEquiv.symm_trans_self

@[simp]
/-
**AddConstEquiv.coe_symm_toEquiv** 是 Mathlib 中的一个引理，位于命名空间 `AddConstEquiv`。
形式化陈述：coe_symm_toEquiv (e : G ≃+c[a, b] H) : ⇑e.toEquiv.symm = e.symm
参数：e : G ≃+c[a, b] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma coe_symm_toEquiv (e : G ≃+c[a, b] H) : ⇑e.toEquiv.symm = e.symm := rfl

@[simp]
/-
**AddConstEquiv.toEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `AddConstEquiv`。
形式化陈述：toEquiv_symm (e : G ≃+c[a, b] H) : e.symm.toEquiv = e.toEquiv.symm
参数：e : G ≃+c[a, b] H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEquiv_symm (e : G ≃+c[a, b] H) : e.symm.toEquiv = e.toEquiv.symm := rfl

@[simp]
/-
**AddConstEquiv.toEquiv_trans** 是 Mathlib 中的一个引理，位于命名空间 `AddConstEquiv`。
形式化陈述：toEquiv_trans (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K) : (e₁.trans e₂).to
Equiv = e₁.toEquiv.trans e₂.toEquiv
参数：e₁ : G ≃+c[a, b] H；e₂ : H ≃+c[b, c] K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEquiv_trans (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K) :
    (e₁.trans e₂).toEquiv = e₁.toEquiv.trans e₂.toEquiv := rfl
/-
**AddConstEquiv.instOne** 是 Mathlib 中的一个实例，位于命名空间 `AddConstEquiv`。
形式化陈述：instOne : One (G ≃+c[a, a] G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne : One (G ≃+c[a, a] G) := ⟨.refl _⟩
/-
**AddConstEquiv.instMul** 是 Mathlib 中的一个实例，位于命名空间 `AddConstEquiv`。
形式化陈述：instMul : Mul (G ≃+c[a, a] G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (G ≃+c[a, a] G) := ⟨fun f g ↦ g.trans f⟩
/-
**AddConstEquiv.instInv** 是 Mathlib 中的一个实例，位于命名空间 `AddConstEquiv`。
形式化陈述：instInv : Inv (G ≃+c[a, a] G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInv : Inv (G ≃+c[a, a] G) := ⟨.symm⟩
/-
**AddConstEquiv.instDiv** 是 Mathlib 中的一个实例，位于命名空间 `AddConstEquiv`。
形式化陈述：instDiv : Div (G ≃+c[a, a] G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDiv : Div (G ≃+c[a, a] G) := ⟨fun f g ↦ f * g⁻¹⟩
/-
**AddConstEquiv.instPowNat** 是 Mathlib 中的一个实例，位于命名空间 `AddConstEquiv`。
形式化陈述：instPowNat : Pow (G ≃+c[a, a] G) Nat where pow e n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPowNat : Pow (G ≃+c[a, a] G) ℕ where
  pow e n := ⟨e^n, (e.toAddConstMap^n).map_add_const'⟩
/-
**AddConstEquiv.instPowInt** 是 Mathlib 中的一个实例，位于命名空间 `AddConstEquiv`。
形式化陈述：instPowInt : Pow (G ≃+c[a, a] G) Int where pow e n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPowInt : Pow (G ≃+c[a, a] G) ℤ where
  pow e n := ⟨e^n,
    match n with
    | .ofNat n => (e^n).map_add_const'
    | .negSucc n => (e.symm^(n + 1)).map_add_const'⟩
/-
**AddConstEquiv.instGroup** 是 Mathlib 中的一个实例，位于命名空间 `AddConstEquiv`。
形式化陈述：instGroup : Group (G ≃+c[a, a] G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstEquiv.toEquiv_injective`：∀ {G : Type u_1} {H : Type u_2} [inst :
 Add G] [inst_1 : Add H] {a : G} {b : H},   Function.Injective AddConstEquiv.toE
quiv
-/
instance instGroup : Group (G ≃+c[a, a] G) :=
  toEquiv_injective.group _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl

/-- Projection from `G ≃+c[a, a] G` to permutations `G ≃ G`, as a monoid homomorphism. -/
@[simps! apply]
/-
**AddConstEquiv.toPerm** 是 Mathlib 中的一个定义，位于命名空间 `AddConstEquiv`。
形式化陈述：toPerm : (G ≃+c[a, a] G) ->* Equiv.Perm G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projection from `G ≃+c[a, a] G` to permutations `G ≃ G`, as a monoid homomorphis
m.
-/
def toPerm : (G ≃+c[a, a] G) →* Equiv.Perm G :=
  .mk' toEquiv fun _ _ ↦ rfl

/-- Projection from `G ≃+c[a, a] G` to `G →+c[a, a] G`, as a monoid homomorphism. -/
@[simps! apply]
/-
**AddConstEquiv.toAddConstMapHom** 是 Mathlib 中的一个定义，位于命名空间 `AddConstEquiv`。
形式化陈述：toAddConstMapHom : (G ≃+c[a, a] G) ->* (G ->+c[a, a] G) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projection from `G ≃+c[a, a] G` to `G →+c[a, a] G`, as a monoid homomorphism.
-/
def toAddConstMapHom : (G ≃+c[a, a] G) →* (G →+c[a, a] G) where
  toFun := toAddConstMap
  map_mul' _ _ := rfl
  map_one' := rfl

/-- Group equivalence between `G ≃+c[a, a] G` and the units of `G →+c[a, a] G`. -/
@[simps!]
/-
**AddConstEquiv.equivUnits** 是 Mathlib 中的一个定义，位于命名空间 `AddConstEquiv`。
形式化陈述：equivUnits : (G ≃+c[a, a] G) ≃* (G ->+c[a, a] G)ˣ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Group equivalence between `G ≃+c[a, a] G` and the units of `G →+c[a, a] G`.
-/
def equivUnits : (G ≃+c[a, a] G) ≃* (G →+c[a, a] G)ˣ where
  toFun := toAddConstMapHom.toHomUnits
  invFun u :=
    { toEquiv := Equiv.Perm.equivUnitsEnd.symm <| Units.map AddConstMap.toEnd u
      map_add_const' := u.1.2 }
  map_mul' _ _ := rfl

end AddConstEquiv

