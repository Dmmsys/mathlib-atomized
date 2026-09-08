/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-! # The `WithLp` type synonym

`WithLp p V` is a copy of `V` with exactly the same vector space structure, but with the Lp norm
instead of any existing norm on `V`; recall that by default `ι → R` and `R × R` are equipped with
a norm defined as the supremum of the norms of their components.

This file defines the vector space structure for all types `V`; the norm structure is built for
different specializations of `V` in downstream files.

Note that this should not be used for infinite products, as in these cases the "right" Lp spaces is
not the same as the direct product of the spaces. See the docstring in `Mathlib/Analysis/PiLp` for
more details.

## Main definitions

* `WithLp p V`: a copy of `V` to be equipped with an L`p` norm.
* `WithLp.toLp`: the canonical inclusion from `V` to `WithLp p V`.
* `WithLp.ofLp`: the canonical inclusion from `WithLp p V` to `V`.
* `WithLp.linearEquiv p K V`: the canonical `K`-module isomorphism between `WithLp p V` and `V`.

## Implementation notes

The pattern here is the same one as is used by `Lex` for order structures; it avoids having a
separate synonym for each type (`ProdLp`, `PiLp`, etc), and allows all the structure-copying code
to be shared.

TODO: is it safe to copy across the topology and uniform space structure too for all reasonable
choices of `V`?
-/

@[expose] public section


open scoped ENNReal

/-- A type synonym for the given `V`, associated with the L`p` norm. Note that by default this just
forgets the norm structure on `V`; it is up to downstream users to implement the L`p` norm (for
instance, on `Prod` and finite `Pi` types). -/
/-
**WithLp** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：ENNReal → Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for the given `V`, associated with the L`p` norm. Note that by de
fault this just
forgets the norm structure on `V`; it is up to downstream users to implement the
 L`p` norm (for
instance, on `Prod` and finite `Pi` types).
-/
structure WithLp (p : ℝ≥0∞) (V : Type*) where
  /-- Converts an element of `V` to an element of `WithLp p V`. -/
  toLp (p) ::
  /-- Converts an element of `WithLp p V` to an element of `V`. -/
  ofLp : V

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `toLp p x` being printed as `{ ofLp := x }` by `delabStructureInstance`. -/
@[app_delab WithLp.toLp]
meta def WithLp.delabToLp : Delab := delabApp

end Notation

variable (p : ℝ≥0∞) (K K' : Type*) {K'' : Type*} (V : Type*) {V' V'' : Type*}

namespace WithLp

/-- `WithLp.ofLp` and `WithLp.toLp` as an equivalence. -/
@[simps]
/-
**WithLp.equiv** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：(p : ENNReal) → (V : Type u_4) → WithLp p V ≃ V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithLp.ofLp` and `WithLp.toLp` as an equivalence.
-/
protected def equiv : WithLp p V ≃ V where
  toFun := ofLp
  invFun := toLp p
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
/-
**WithLp.equiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：equiv_symm_apply : ⇑(WithLp.equiv p V).symm = toLp p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma equiv_symm_apply : ⇑(WithLp.equiv p V).symm = toLp p := rfl

/-! `WithLp p V` inherits various module-adjacent structures from `V`. -/

/-
**WithLp.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instNontrivial [Nontrivial V] : Nontrivial (WithLp p V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α

--- 原说明 ---
`WithLp p V` inherits various module-adjacent structures from `V`.
-/
instance instNontrivial [Nontrivial V] : Nontrivial (WithLp p V) := (WithLp.equiv p V).nontrivial
/-
**WithLp.instUnique** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instUnique [Unique V] : Unique (WithLp p V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUnique [Unique V] : Unique (WithLp p V) := (WithLp.equiv p V).unique
/-
**WithLp.instDecidableEq** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instDecidableEq [DecidableEq V] : DecidableEq (WithLp p V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableEq [DecidableEq V] : DecidableEq (WithLp p V) :=
  (WithLp.equiv p V).decidableEq
/-
**WithLp.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instAddCommGroup [AddCommGroup V] : AddCommGroup (WithLp p V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup [AddCommGroup V] : AddCommGroup (WithLp p V) :=
  (WithLp.equiv p V).addCommGroup
/-
**WithLp.instSMul** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：(p : ENNReal) → (K : Type u_1) → (V : Type u_4) → [SMul K V] → SMul K (Wit
hLp p V)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instSMul [SMul K V] : SMul K (WithLp p V) :=
  (WithLp.equiv p V).smul K
/-
**WithLp.instMulAction** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：(p : ENNReal) → (K : Type u_1) → (V : Type u_4) → [inst : Monoid K] → [Mul
Action K V] → MulAction K (WithLp p V)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instMulAction [Monoid K] [MulAction K V] : MulAction K (WithLp p V) :=
  fast_instance% (WithLp.equiv p V).mulAction K
/-
**WithLp.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instDistribMulAction [Monoid K] [AddCommGroup V] [DistribMulAction K V] : 
DistribMulAction K (WithLp p V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction [Monoid K] [AddCommGroup V] [DistribMulAction K V] :
    DistribMulAction K (WithLp p V) := fast_instance% (WithLp.equiv p V).distribMulAction K
/-
**WithLp.instModule** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instModule [Semiring K] [AddCommGroup V] [Module K V] : Module K (WithLp p
 V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule [Semiring K] [AddCommGroup V] [Module K V] : Module K (WithLp p V) :=
  fast_instance% (WithLp.equiv p V).module K

variable {K V}
/-
**WithLp.ofLp_toLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：ofLp_toLp (x : V) : ofLp (toLp p x) = x
参数：x : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofLp_toLp (x : V) : ofLp (toLp p x) = x := rfl
/-
**WithLp.toLp_ofLp** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) {V : Type u_4} (x : WithLp p V), WithLp.toLp p x.ofLp = x
参数：p : ENNReal；x : WithLp p V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLp_ofLp (x : WithLp p V) : toLp p (ofLp x) = x := rfl
/-
**WithLp.ext_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：ext_iff {x y : WithLp p V} : x = y ↔ x.ofLp = y.ofLp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma ext_iff {x y : WithLp p V} : x = y ↔ x.ofLp = y.ofLp :=
  (WithLp.equiv p V).injective.eq_iff.symm
/-
**WithLp.ofLp_surjective** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：ofLp_surjective : Function.Surjective (@ofLp p V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用引理 `WithLp.ofLp_toLp`：ofLp_toLp (x : V) : ofLp (toLp p x) = x
-/
lemma ofLp_surjective : Function.Surjective (@ofLp p V) :=
  Function.RightInverse.surjective <| ofLp_toLp _
/-
**WithLp.toLp_surjective** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：toLp_surjective : Function.Surjective (@toLp p V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `WithLp.toLp_ofLp`：∀ (p : ENNReal) {V : Type u_4} (x : WithLp p V), WithL
p.toLp p x.ofLp = x
-/
lemma toLp_surjective : Function.Surjective (@toLp p V) :=
  Function.RightInverse.surjective <| toLp_ofLp _
/-
**WithLp.ofLp_injective** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：ofLp_injective : Function.Injective (@ofLp p V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `WithLp.toLp_ofLp`：∀ (p : ENNReal) {V : Type u_4} (x : WithLp p V), WithL
p.toLp p x.ofLp = x
-/
lemma ofLp_injective : Function.Injective (@ofLp p V) :=
  Function.LeftInverse.injective <| toLp_ofLp _
/-
**WithLp.toLp_injective** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：toLp_injective : Function.Injective (@toLp p V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用引理 `WithLp.ofLp_toLp`：ofLp_toLp (x : V) : ofLp (toLp p x) = x
-/
lemma toLp_injective : Function.Injective (@toLp p V) :=
  Function.LeftInverse.injective <| ofLp_toLp _
/-
**WithLp.ofLp_bijective** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：ofLp_bijective : Function.Bijective (@ofLp p V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithLp.ofLp_injective`：ofLp_injective : Function.Injective (@ofLp p V)
· 使用引理 `WithLp.ofLp_surjective`：ofLp_surjective : Function.Surjective (@ofLp p V
)
-/
lemma ofLp_bijective : Function.Bijective (@ofLp p V) :=
  ⟨ofLp_injective p, ofLp_surjective p⟩
/-
**WithLp.toLp_bijective** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：toLp_bijective : Function.Bijective (@toLp p V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithLp.toLp_injective`：toLp_injective : Function.Injective (@toLp p V)
· 使用引理 `WithLp.toLp_surjective`：toLp_surjective : Function.Surjective (@toLp p V
)
-/
lemma toLp_bijective : Function.Bijective (@toLp p V) :=
  ⟨toLp_injective p, toLp_surjective p⟩

/-- Lift a function to `WithLp`. -/
@[simp]
/-
**WithLp.map** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：(p : ENNReal) → {V : Type u_4} → {V' : Type u_5} → (V → V') → WithLp p V →
 WithLp p V'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a function to `WithLp`.
-/
protected def map (f : V → V') (x : WithLp p V) : WithLp p V' :=
  toLp p (f x.ofLp)

@[simp]
/-
**WithLp.map_id** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：map_id : WithLp.map p (id (α
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_id : WithLp.map p (id (α := V)) = id :=
  rfl
/-
**WithLp.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：map_comp (f : V' -> V'') (g : V -> V') : WithLp.map p (f ∘ g) = WithLp.map
 p f ∘ WithLp.map p g
参数：f : V' -> V''；g : V -> V'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp (f : V' → V'') (g : V → V') :
    WithLp.map p (f ∘ g) = WithLp.map p f ∘ WithLp.map p g :=
  rfl

/-- Lift an equivalence to `WithLp`. -/
/-
**WithLp.congr** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：(p : ENNReal) → {V : Type u_4} → {V' : Type u_5} → V ≃ V' → WithLp p V ≃ W
ithLp p V'
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Lift an equivalence to `WithLp`.
-/
protected def congr (f : V ≃ V') : WithLp p V ≃ WithLp p V' :=
  (WithLp.equiv p V).trans <| f.trans <| (WithLp.equiv p V').symm

@[simp]
/-
**WithLp.coe_congr** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：coe_congr (f : V ≃ V') : ⇑(WithLp.congr p f) = WithLp.map p f
参数：f : V ≃ V'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_congr (f : V ≃ V') : ⇑(WithLp.congr p f) = WithLp.map p f :=
  rfl

@[simp]
/-
**WithLp.congr_refl** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：congr_refl : WithLp.congr p (Equiv.refl V) = Equiv.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem congr_refl : WithLp.congr p (Equiv.refl V) = Equiv.refl _ :=
  rfl

@[simp]
/-
**WithLp.congr_symm** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：congr_symm (f : V ≃ V') : (WithLp.congr p f).symm = WithLp.congr p f.symm
参数：f : V ≃ V'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem congr_symm (f : V ≃ V') : (WithLp.congr p f).symm = WithLp.congr p f.symm :=
  rfl
/-
**WithLp.congr_trans** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：congr_trans (f : V ≃ V') (g : V' ≃ V'') : WithLp.congr p (f.trans g) = (Wi
thLp.congr p f).trans (WithLp.congr p g)
参数：f : V ≃ V'；g : V' ≃ V''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem congr_trans (f : V ≃ V') (g : V' ≃ V'') :
    WithLp.congr p (f.trans g) = (WithLp.congr p f).trans (WithLp.congr p g) :=
  rfl

section AddCommGroup
variable [AddCommGroup V]

/-
**WithLp.toLp_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V], WithLp.toLp p 0 = 
0
参数：p : ENNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLp_zero : toLp p (0 : V) = 0 := rfl
/-
**WithLp.ofLp_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V], WithLp.ofLp 0 = 0
参数：p : ENNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofLp_zero : ofLp (0 : WithLp p V) = 0 := rfl
/-
**WithLp.toLp_add** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V] (x y : V),   WithLp
.toLp p (x + y) = WithLp.toLp p x + WithLp.toLp p y
参数：p : ENNReal；x y : V；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLp_add (x y : V) : toLp p (x + y) = toLp p x + toLp p y := rfl
/-
**WithLp.ofLp_add** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V] (x y : WithLp p V),
 (x + y).ofLp = x.ofLp + y.ofLp
参数：p : ENNReal；x y : WithLp p V；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofLp_add (x y : WithLp p V) : ofLp (x + y) = ofLp x + ofLp y := rfl
/-
**WithLp.toLp_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V] (x y : V),   WithLp
.toLp p (x - y) = WithLp.toLp p x - WithLp.toLp p y
参数：p : ENNReal；x y : V；x - y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLp_sub (x y : V) : toLp p (x - y) = toLp p x - toLp p y := rfl
/-
**WithLp.ofLp_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V] (x y : WithLp p V),
 (x - y).ofLp = x.ofLp - y.ofLp
参数：p : ENNReal；x y : WithLp p V；x - y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofLp_sub (x y : WithLp p V) : ofLp (x - y) = ofLp x - ofLp y := rfl
/-
**WithLp.toLp_neg** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V] (x : V), WithLp.toL
p p (-x) = -WithLp.toLp p x
参数：p : ENNReal；x : V；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLp_neg (x : V) : toLp p (-x) = -toLp p x := rfl
/-
**WithLp.ofLp_neg** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V] (x : WithLp p V), (
-x).ofLp = -x.ofLp
参数：p : ENNReal；x : WithLp p V；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofLp_neg (x : WithLp p V) : ofLp (-x) = -ofLp x := rfl
/-
**WithLp.toLp_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V] {x : V}, WithLp.toL
p p x = 0 ↔ x = 0
参数：p : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `WithLp.toLp_injective`：toLp_injective : Function.Injective (@toLp p V)
-/
@[simp] lemma toLp_eq_zero {x : V} : toLp p x = 0 ↔ x = 0 := (toLp_injective p).eq_iff
/-
**WithLp.ofLp_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V] {x : WithLp p V}, x
.ofLp = 0 ↔ x = 0
参数：p : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `WithLp.ofLp_injective`：ofLp_injective : Function.Injective (@ofLp p V)
-/
@[simp] lemma ofLp_eq_zero {x : WithLp p V} : ofLp x = 0 ↔ x = 0 := (ofLp_injective p).eq_iff

end AddCommGroup

/-
**WithLp.toLp_smul** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) {K : Type u_1} {V : Type u_4} [inst : SMul K V] (c : K) (x
 : V),   WithLp.toLp p (c • x) = c • WithLp.toLp p x
参数：p : ENNReal；c : K；x : V；c • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLp_smul [SMul K V] (c : K) (x : V) : toLp p (c • x) = c • (toLp p x) := rfl
/-
**WithLp.ofLp_smul** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) {K : Type u_1} {V : Type u_4} [inst : SMul K V] (c : K) (x
 : WithLp p V), (c • x).ofLp = c • x.ofLp
参数：p : ENNReal；c : K；x : WithLp p V；c • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofLp_smul [SMul K V] (c : K) (x : WithLp p V) : ofLp (c • x) = c • ofLp x := rfl

@[to_additive]
/-
**WithLp.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instIsScalarTower [SMul K K'] [SMul K V] [SMul K' V] [IsScalarTower K K' V
] : IsScalarTower K K' (WithLp p V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.isScalarTower`：∀ (M : Type u_1) (N : Type u_2) {α : Type u_4} {β :
 Type u_5} [inst : SMul M N] [inst_1 : SMul M β] [inst_2 : SMul N β]   (e : α ≃ 
β) [IsSca…
-/
instance instIsScalarTower [SMul K K'] [SMul K V] [SMul K' V] [IsScalarTower K K' V] :
    IsScalarTower K K' (WithLp p V) :=
  (WithLp.equiv p V).isScalarTower K K'

@[to_additive]
/-
**WithLp.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instSMulCommClass [SMul K V] [SMul K' V] [SMulCommClass K K' V] : SMulComm
Class K K' (WithLp p V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.smulCommClass`：∀ (M : Type u_1) (N : Type u_2) {α : Type u_4} {β :
 Type u_5} [inst : SMul M β] [inst_1 : SMul N β] (e : α ≃ β)   [SMulCommClass M 
N β], SMu…
-/
instance instSMulCommClass [SMul K V] [SMul K' V] [SMulCommClass K K' V] :
    SMulCommClass K K' (WithLp p V) :=
  (WithLp.equiv p V).smulCommClass K K'

variable (K V)

/-- `WithLp.equiv` as a group isomorphism. -/
@[simps apply symm_apply]
/-
**WithLp.addEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：(p : ENNReal) → (V : Type u_4) → [inst : AddCommGroup V] → WithLp p V ≃+ V
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WithLp.ofLp_add`：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V] 
(x y : WithLp p V), (x + y).ofLp = x.ofLp + y.ofLp

--- 原说明 ---
`WithLp.equiv` as a group isomorphism.
-/
protected def addEquiv [AddCommGroup V] : WithLp p V ≃+ V where
  toFun := ofLp
  invFun := toLp p
  map_add' := ofLp_add p
/-
**WithLp.coe_addEquiv** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：coe_addEquiv [AddCommGroup V] : ⇑(WithLp.addEquiv p V) = ofLp
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_addEquiv [AddCommGroup V] : ⇑(WithLp.addEquiv p V) = ofLp := rfl
/-
**WithLp.coe_symm_addEquiv** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：coe_symm_addEquiv [AddCommGroup V] : ⇑(WithLp.addEquiv p V).symm = toLp p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_symm_addEquiv [AddCommGroup V] : ⇑(WithLp.addEquiv p V).symm = toLp p := rfl

@[simp]
/-
**WithLp.ofLp_sum** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：ofLp_sum [AddCommGroup V] {ι : Type*} (s : Finset ι) (f : ι -> WithLp p V)
 : (∑ i in s, f i).ofLp = ∑ i in s, (f i).ofLp
参数：s : Finset ι；f : ι -> WithLp p V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma ofLp_sum [AddCommGroup V] {ι : Type*} (s : Finset ι) (f : ι → WithLp p V) :
    (∑ i ∈ s, f i).ofLp = ∑ i ∈ s, (f i).ofLp :=
  map_sum (WithLp.addEquiv _ _) _ _

@[simp]
/-
**WithLp.toLp_sum** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：toLp_sum [AddCommGroup V] {ι : Type*} (s : Finset ι) (f : ι -> V) : toLp p
 (∑ i in s, f i) = ∑ i in s, toLp p (f i)
参数：s : Finset ι；f : ι -> V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma toLp_sum [AddCommGroup V] {ι : Type*} (s : Finset ι) (f : ι → V) :
    toLp p (∑ i ∈ s, f i) = ∑ i ∈ s, toLp p (f i) :=
  map_sum (WithLp.addEquiv _ _).symm _ _

@[simp]
/-
**WithLp.ofLp_listSum** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：ofLp_listSum [AddCommGroup V] (l : List (WithLp p V)) : l.sum.ofLp = (l.ma
p ofLp).sum
参数：l : List (WithLp p V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma ofLp_listSum [AddCommGroup V] (l : List (WithLp p V)) :
    l.sum.ofLp = (l.map ofLp).sum :=
  map_list_sum (WithLp.addEquiv _ _) _

@[simp]
/-
**WithLp.toLp_listSum** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：toLp_listSum [AddCommGroup V] (l : List V) : toLp p l.sum = (l.map (toLp p
)).sum
参数：l : List V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma toLp_listSum [AddCommGroup V] (l : List V) :
    toLp p l.sum = (l.map (toLp p)).sum :=
  map_list_sum (WithLp.addEquiv _ _).symm _

@[simp]
/-
**WithLp.ofLp_multisetSum** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：ofLp_multisetSum [AddCommGroup V] (s : Multiset (WithLp p V)) : s.sum.ofLp
 = (s.map ofLp).sum
参数：s : Multiset (WithLp p V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma ofLp_multisetSum [AddCommGroup V] (s : Multiset (WithLp p V)) :
    s.sum.ofLp = (s.map ofLp).sum :=
  map_multiset_sum (WithLp.addEquiv _ _) _

@[simp]
/-
**WithLp.toLp_multisetSum** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：toLp_multisetSum [AddCommGroup V] (s : Multiset V) : toLp p s.sum = (s.map
 (toLp p)).sum
参数：s : Multiset V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma toLp_multisetSum [AddCommGroup V] (s : Multiset V) :
    toLp p s.sum = (s.map (toLp p)).sum :=
  map_multiset_sum (WithLp.addEquiv _ _).symm _

/-- `WithLp.equiv` as a linear equivalence. -/
@[simps apply symm_apply]
/-
**WithLp.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：(p : ENNReal) →   (K : Type u_1) →     (V : Type u_4) → [inst : Semiring K
] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module K V] → WithLp p V ≃ₗ[K] 
V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithLp.equiv` as a linear equivalence.
-/
protected def linearEquiv [Semiring K] [AddCommGroup V] [Module K V] : WithLp p V ≃ₗ[K] V where
  __ := WithLp.addEquiv p V
  map_smul' _ _ := rfl
/-
**WithLp.coe_linearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：coe_linearEquiv [Semiring K] [AddCommGroup V] [Module K V] : ⇑(WithLp.line
arEquiv p K V) = ofLp
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_linearEquiv [Semiring K] [AddCommGroup V] [Module K V] :
    ⇑(WithLp.linearEquiv p K V) = ofLp := rfl
/-
**WithLp.coe_symm_linearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：coe_symm_linearEquiv [Semiring K] [AddCommGroup V] [Module K V] : ⇑(WithLp
.linearEquiv p K V).symm = toLp p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_symm_linearEquiv [Semiring K] [AddCommGroup V] [Module K V] :
    ⇑(WithLp.linearEquiv p K V).symm = toLp p := rfl

@[simp]
/-
**WithLp.toAddEquiv_linearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：toAddEquiv_linearEquiv [Semiring K] [AddCommGroup V] [Module K V] : (WithL
p.linearEquiv p K V).toAddEquiv = WithLp.addEquiv p V
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAddEquiv_linearEquiv [Semiring K] [AddCommGroup V] [Module K V] :
    (WithLp.linearEquiv p K V).toAddEquiv = WithLp.addEquiv p V := rfl
/-
**WithLp.instModuleFinite** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instModuleFinite [Semiring K] [AddCommGroup V] [Module K V] [Module.Finite
 K V] : Module.Finite K (WithLp p V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
-/
instance instModuleFinite
    [Semiring K] [AddCommGroup V] [Module K V] [Module.Finite K V] :
    Module.Finite K (WithLp p V) :=
  Module.Finite.equiv (WithLp.linearEquiv p K V).symm

end WithLp

section

variable {K K' V} [Semiring K] [Semiring K'] [Semiring K'']
  {σ : K →+* K'} {σ' : K' →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  {τ : K' →+* K''} {τ' : K'' →+* K'} [RingHomInvPair τ τ'] [RingHomInvPair τ' τ]
  {ρ : K →+* K''} {ρ' : K'' →+* K} [RingHomInvPair ρ ρ'] [RingHomInvPair ρ' ρ]
  [RingHomCompTriple σ τ ρ] [RingHomCompTriple τ' σ' ρ']
  [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V'] [AddCommGroup V''] [Module K'' V'']

namespace LinearMap

/-- Lift a (semi)linear map to `WithLp`. -/
/-
**LinearMap.withLpMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：withLpMap (f : V ->ₛₗ[σ] V') : WithLp p V ->ₛₗ[σ] WithLp p V'
参数：f : V ->ₛₗ[σ] V'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a (semi)linear map to `WithLp`.
-/
def withLpMap (f : V →ₛₗ[σ] V') : WithLp p V →ₛₗ[σ] WithLp p V' :=
  (WithLp.linearEquiv p K' V').symm.toLinearMap ∘ₛₗ f ∘ₛₗ (WithLp.linearEquiv p K V).toLinearMap

@[simp]
/-
**LinearMap.coe_withLpMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_withLpMap (f : V ->ₛₗ[σ] V') : ⇑(withLpMap p f) = WithLp.map p f
参数：f : V ->ₛₗ[σ] V'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_withLpMap (f : V →ₛₗ[σ] V') : ⇑(withLpMap p f) = WithLp.map p f :=
  rfl

@[simp]
/-
**LinearMap.withLpMap_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：withLpMap_id : withLpMap p (LinearMap.id (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem withLpMap_id : withLpMap p (LinearMap.id (R := K) (M := V)) = LinearMap.id :=
  rfl

@[simp]
/-
**LinearMap.withLpMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：withLpMap_comp (f : V' ->ₛₗ[τ] V'') (g : V ->ₛₗ[σ] V') : withLpMap p (f ∘ₛ
ₗ g) = withLpMap p f ∘ₛₗ withLpMap p g
参数：f : V' ->ₛₗ[τ] V''；g : V ->ₛₗ[σ] V'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem withLpMap_comp (f : V' →ₛₗ[τ] V'') (g : V →ₛₗ[σ] V') :
    withLpMap p (f ∘ₛₗ g) = withLpMap p f ∘ₛₗ withLpMap p g :=
  rfl

end LinearMap

namespace LinearEquiv

/-- Lift a (semi)linear equivalence to `WithLp`. -/
/-
**LinearEquiv.withLpCongr** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：withLpCongr (f : V ≃ₛₗ[σ] V') : WithLp p V ≃ₛₗ[σ] WithLp p V'
参数：f : V ≃ₛₗ[σ] V'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a (semi)linear equivalence to `WithLp`.
-/
def withLpCongr (f : V ≃ₛₗ[σ] V') : WithLp p V ≃ₛₗ[σ] WithLp p V' :=
  (WithLp.linearEquiv p K V).trans <| f.trans <| (WithLp.linearEquiv p K' V').symm

@[simp]
/-
**LinearEquiv.coe_withLpCongr** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_withLpCongr (f : V ≃ₛₗ[σ] V') : ⇑(withLpCongr p f) = WithLp.map p f
参数：f : V ≃ₛₗ[σ] V'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_withLpCongr (f : V ≃ₛₗ[σ] V') : ⇑(withLpCongr p f) = WithLp.map p f :=
  rfl

@[simp]
/-
**LinearEquiv.withLpCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：withLpCongr_symm (f : V ≃ₛₗ[σ] V') : (withLpCongr p f).symm = withLpCongr 
p f.symm
参数：f : V ≃ₛₗ[σ] V'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem withLpCongr_symm (f : V ≃ₛₗ[σ] V') : (withLpCongr p f).symm = withLpCongr p f.symm :=
  rfl

@[simp]
/-
**LinearEquiv.withLpCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：withLpCongr_refl : withLpCongr p (LinearEquiv.refl K V) = LinearEquiv.refl
 K _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem withLpCongr_refl :
    withLpCongr p (LinearEquiv.refl K V) = LinearEquiv.refl K _ :=
  rfl
/-
**LinearEquiv.withLpCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：withLpCongr_trans (f : V ≃ₛₗ[σ] V') (g : V' ≃ₛₗ[τ] V'') : withLpCongr p (f
.trans g) = (withLpCongr p f).trans (withLpCongr p g)
参数：f : V ≃ₛₗ[σ] V'；g : V' ≃ₛₗ[τ] V''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem withLpCongr_trans (f : V ≃ₛₗ[σ] V') (g : V' ≃ₛₗ[τ] V'') :
    withLpCongr p (f.trans g) = (withLpCongr p f).trans (withLpCongr p g) :=
  rfl

end LinearEquiv

end

