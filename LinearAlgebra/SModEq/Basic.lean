/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# modular equivalence for submodule
-/

@[expose] public section


open Submodule

open Polynomial

variable {R : Type*} [Ring R]
variable {S : Type*} [Ring S]
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module S M] (U U₁ U₂ : Submodule R M)
variable {x x₁ x₂ y y₁ y₂ z z₁ z₂ : M}
variable {N : Type*} [AddCommGroup N] [Module R N] (V V₁ V₂ : Submodule R N)

/-- A predicate saying two elements of a module are equivalent modulo a submodule. -/
/-
**SModEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SModEq (x y : M) : Prop
参数：x y : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate saying two elements of a module are equivalent modulo a submodule.
-/
def SModEq (x y : M) : Prop :=
  (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y

@[inherit_doc] notation:50 x " ≡ " y " [SMOD " N "]" => SModEq N x y

variable {U U₁ U₂}
/-
**SModEq.def** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡ y [SMOD U] ↔ S
ubmodule.Quotient.mk x = Submodule.Quotient.mk y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem SModEq.def :
    x ≡ y [SMOD U] ↔ (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y :=
  Iff.rfl

namespace SModEq

/-
**SModEq.sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：sub_mem : x ≡ y [SMOD U] ↔ x - y in U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SModEq.def`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : Ad
dCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡ 
…
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sub_mem : x ≡ y [SMOD U] ↔ x - y ∈ U := by rw [SModEq.def, Submodule.Quotient.eq]

@[simp]
/-
**SModEq.top** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：top : x ≡ y [SMOD (⊤ : Submodule R M)]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
-/
theorem top : x ≡ y [SMOD (⊤ : Submodule R M)] :=
  (Submodule.Quotient.eq ⊤).2 mem_top

@[simp]
/-
**SModEq.bot** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：bot : x ≡ y [SMOD (⊥ : Submodule R M)] ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SModEq.def`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : Ad
dCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡ 
…
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bot : x ≡ y [SMOD (⊥ : Submodule R M)] ↔ x = y := by
  rw [SModEq.def, Submodule.Quotient.eq, mem_bot, sub_eq_zero]

@[gcongr, mono]
/-
**SModEq.mono** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：mono (HU : U₁ <= U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD U₂]
参数：HU : U₁ <= U₂；hxy : x ≡ y [SMOD U₁]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem mono (HU : U₁ ≤ U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD U₂] :=
  (Submodule.Quotient.eq U₂).2 <| HU <| (Submodule.Quotient.eq U₁).1 hxy
/-
**SModEq.of_toAddSubgroup_le** 是 Mathlib 中的一个引理，位于命名空间 `SModEq`。
形式化陈述：of_toAddSubgroup_le {U : Submodule R M} {V : Submodule S M} (h : U.toAddSu
bgroup <= V.toAddSubgroup) {x y : M} (hxy : x ≡ y [SMOD U]) : x ≡ y [SMOD V]
参数：h : U.toAddSubgroup <= V.toAddSubgroup；hxy : x ≡ y [SMOD U]。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_toAddSubgroup_le {U : Submodule R M} {V : Submodule S M}
    (h : U.toAddSubgroup ≤ V.toAddSubgroup) {x y : M} (hxy : x ≡ y [SMOD U]) : x ≡ y [SMOD V] := by
  simp only [SModEq, Submodule.Quotient.eq] at hxy ⊢
  exact h hxy

@[refl, simp]
/-
**SModEq.refl** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {U : Submodule R M} (x : M), x ≡ x [SMOD U]
参数：x : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem refl (x : M) : x ≡ x [SMOD U] :=
  @rfl _ _
/-
**SModEq.rfl** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {U : Submodule R M} {x : M}, x ≡ x [SMOD U]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SModEq.refl`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} (x : M), x ≡ x
 …
-/
protected theorem rfl : x ≡ x [SMOD U] :=
  SModEq.refl _
/-
**SModEq.** 是 Mathlib 中的一个实例，位于命名空间 `SModEq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Refl (SModEq U) :=
  ⟨SModEq.refl⟩

@[symm]
nonrec theorem symm (hxy : x ≡ y [SMOD U]) : y ≡ x [SMOD U] :=
  hxy.symm
/-
**SModEq.comm** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：comm : x ≡ y [SMOD U] ↔ y ≡ x [SMOD U]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SModEq.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡
 …
-/
theorem comm : x ≡ y [SMOD U] ↔ y ≡ x [SMOD U] := ⟨symm, symm⟩

@[trans]
nonrec theorem trans (hxy : x ≡ y [SMOD U]) (hyz : y ≡ z [SMOD U]) : x ≡ z [SMOD U] :=
  hxy.trans hyz
/-
**SModEq.instTrans** 是 Mathlib 中的一个实例，位于命名空间 `SModEq`。
形式化陈述：instTrans : Trans (SModEq U) (SModEq U) (SModEq U) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SModEq.trans`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : 
AddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y z : M}, 
x …
-/
instance instTrans : Trans (SModEq U) (SModEq U) (SModEq U) where
  trans := trans

@[gcongr]
/-
**SModEq.add** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：add (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ + x₂ ≡ y₁ + y
₂ [SMOD U]
参数：hxy₁ : x₁ ≡ y₁ [SMOD U]；hxy₂ : x₂ ≡ y₂ [SMOD U]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SModEq.def`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : Ad
dCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡ 
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ + x₂ ≡ y₁ + y₂ [SMOD U] := by
  rw [SModEq.def] at hxy₁ hxy₂ ⊢
  simp_rw [Quotient.mk_add, hxy₁, hxy₂]

@[gcongr]
/-
**SModEq.sum** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：sum {ι} {s : Finset ι} {x y : ι -> M} (hxy : forall i in s, x i ≡ y i [SMO
D U]) : ∑ i in s, x i ≡ ∑ i in s, y i [SMOD U]
参数：hxy : forall i in s, x i ≡ y i [SMOD U]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `SModEq.add`：add (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁
 + x₂ ≡ y₁ + y₂ [SMOD U]
· 使用定理 `Finset.mem_cons_self`：mem_cons_self (a : α) (s : Finset α) {h} : a in co
ns a s h
· 使用定理 `SModEq.refl`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} (x : M), x ≡ x
 …
· 使用定理 `Finset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Finset α} {hb : b
 ∉ s} (ha : a in s) : a in cons b s hb
-/
theorem sum {ι} {s : Finset ι} {x y : ι → M}
    (hxy : ∀ i ∈ s, x i ≡ y i [SMOD U]) : ∑ i ∈ s, x i ≡ ∑ i ∈ s, y i [SMOD U] := by
  induction s using Finset.cons_induction with
  | empty => simp [SModEq.rfl]
  | cons i s _ ih =>
    grw [Finset.sum_cons, Finset.sum_cons, hxy i (Finset.mem_cons_self i s),
      ih (fun j hj ↦ hxy j (Finset.mem_cons_of_mem hj))]

@[gcongr]
/-
**SModEq.smul** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：smul (hxy : x ≡ y [SMOD U]) (c : R) : c • x ≡ c • y [SMOD U]
参数：hxy : x ≡ y [SMOD U]；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SModEq.def`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : Ad
dCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡ 
…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul (hxy : x ≡ y [SMOD U]) (c : R) : c • x ≡ c • y [SMOD U] := by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]
/-
**SModEq.nsmul** 是 Mathlib 中的一个引理，位于命名空间 `SModEq`。
形式化陈述：nsmul (hxy : x ≡ y [SMOD U]) (n : Nat) : n • x ≡ n • y [SMOD U]
参数：hxy : x ≡ y [SMOD U]；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SModEq.def`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : Ad
dCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡ 
…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nsmul (hxy : x ≡ y [SMOD U]) (n : ℕ) : n • x ≡ n • y [SMOD U] := by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]
/-
**SModEq.zsmul** 是 Mathlib 中的一个引理，位于命名空间 `SModEq`。
形式化陈述：zsmul (hxy : x ≡ y [SMOD U]) (n : Int) : n • x ≡ n • y [SMOD U]
参数：hxy : x ≡ y [SMOD U]；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SModEq.def`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : Ad
dCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡ 
…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zsmul (hxy : x ≡ y [SMOD U]) (n : ℤ) : n • x ≡ n • y [SMOD U] := by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]
/-
**SModEq.mul** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：mul {I : Ideal A} {x₁ x₂ y₁ y₂ : A} (hxy₁ : x₁ ≡ y₁ [SMOD I]) (hxy₂ : x₂ ≡
 y₂ [SMOD I]) : x₁ * x₂ ≡ y₁ * y₂ [SMOD I]
参数：hxy₁ : x₁ ≡ y₁ [SMOD I]；hxy₂ : x₂ ≡ y₂ [SMOD I]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
theorem mul {I : Ideal A} {x₁ x₂ y₁ y₂ : A} (hxy₁ : x₁ ≡ y₁ [SMOD I])
    (hxy₂ : x₂ ≡ y₂ [SMOD I]) : x₁ * x₂ ≡ y₁ * y₂ [SMOD I] := by
  simp only [SModEq.def, Ideal.Quotient.mk_eq_mk, map_mul] at hxy₁ hxy₂ ⊢
  rw [hxy₁, hxy₂]

@[gcongr]
/-
**SModEq.prod** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：prod {I : Ideal A} {ι} {s : Finset ι} {x y : ι -> A} (hxy : forall i in s,
 x i ≡ y i [SMOD I]) : ∏ i in s, x i ≡ ∏ i in s, y i [SMOD I]
参数：hxy : forall i in s, x i ≡ y i [SMOD I]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `SModEq.mul`：mul {I : Ideal A} {x₁ x₂ y₁ y₂ : A} (hxy₁ : x₁ ≡ y₁ [SMOD I]
) (hxy₂ : x₂ ≡ y₂ [SMOD I]) : x₁ * x₂ ≡ y₁ * y₂ [SMOD I]
· 使用定理 `Finset.mem_cons_self`：mem_cons_self (a : α) (s : Finset α) {h} : a in co
ns a s h
· 使用定理 `SModEq.refl`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} (x : M), x ≡ x
 …
· 使用定理 `Finset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Finset α} {hb : b
 ∉ s} (ha : a in s) : a in cons b s hb
-/
theorem prod {I : Ideal A} {ι} {s : Finset ι} {x y : ι → A}
    (hxy : ∀ i ∈ s, x i ≡ y i [SMOD I]) : ∏ i ∈ s, x i ≡ ∏ i ∈ s, y i [SMOD I] := by
  induction s using Finset.cons_induction with
  | empty => simp [SModEq.rfl]
  | cons i s _ ih =>
    grw [Finset.prod_cons, Finset.prod_cons, hxy i (Finset.mem_cons_self i s),
      ih (fun j hj ↦ hxy j (Finset.mem_cons_of_mem hj))]

@[gcongr]
/-
**SModEq.pow** 是 Mathlib 中的一个引理，位于命名空间 `SModEq`。
形式化陈述：pow {I : Ideal A} {x y : A} (n : Nat) (hxy : x ≡ y [SMOD I]) : x ^ n ≡ y ^
 n [SMOD I]
参数：n : Nat；hxy : x ≡ y [SMOD I]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma pow {I : Ideal A} {x y : A} (n : ℕ) (hxy : x ≡ y [SMOD I]) :
    x ^ n ≡ y ^ n [SMOD I] := by
  simp only [SModEq.def, Ideal.Quotient.mk_eq_mk, map_pow] at hxy ⊢
  rw [hxy]

@[gcongr]
/-
**SModEq.neg** 是 Mathlib 中的一个引理，位于命名空间 `SModEq`。
形式化陈述：neg (hxy : x ≡ y [SMOD U]) : -x ≡ - y [SMOD U]
参数：hxy : x ≡ y [SMOD U]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma neg (hxy : x ≡ y [SMOD U]) : -x ≡ - y [SMOD U] := by
  simpa only [SModEq.def, Quotient.mk_neg, neg_inj]

@[gcongr]
/-
**SModEq.sub** 是 Mathlib 中的一个引理，位于命名空间 `SModEq`。
形式化陈述：sub (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ - x₂ ≡ y₁ - y
₂ [SMOD U]
参数：hxy₁ : x₁ ≡ y₁ [SMOD U]；hxy₂ : x₂ ≡ y₂ [SMOD U]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SModEq.def`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : Ad
dCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡ 
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sub (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ - x₂ ≡ y₁ - y₂ [SMOD U] := by
  rw [SModEq.def] at hxy₁ hxy₂ ⊢
  simp_rw [Quotient.mk_sub, hxy₁, hxy₂]
/-
**SModEq.zero** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：zero : x ≡ 0 [SMOD U] ↔ x in U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SModEq.def`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : Ad
dCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡ 
…
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zero : x ≡ 0 [SMOD U] ↔ x ∈ U := by rw [SModEq.def, Submodule.Quotient.eq, sub_zero]
/-
**SModEq._root_.sub_smodEq_zero** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.sub_smodEq_zero : x - y ≡ 0 [SMOD U] ↔ x ≡ y [SMOD U] := by
  simp only [SModEq.sub_mem, sub_zero]
/-
**SModEq.map** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：map (hxy : x ≡ y [SMOD U]) (f : M ->ₗ[R] N) : f x ≡ f y [SMOD U.map f]
参数：hxy : x ≡ y [SMOD U]；f : M ->ₗ[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `LinearMap.map_sub`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem map (hxy : x ≡ y [SMOD U]) (f : M →ₗ[R] N) : f x ≡ f y [SMOD U.map f] :=
  (Submodule.Quotient.eq _).2 <| f.map_sub x y ▸ mem_map_of_mem <| (Submodule.Quotient.eq _).1 hxy
/-
**SModEq.comap** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：comap {f : M ->ₗ[R] N} (hxy : f x ≡ f y [SMOD V]) : x ≡ y [SMOD V.comap f]
参数：hxy : f x ≡ f y [SMOD V]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.map_sub`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem comap {f : M →ₗ[R] N} (hxy : f x ≡ f y [SMOD V]) : x ≡ y [SMOD V.comap f] :=
  (Submodule.Quotient.eq _).2 <|
    show f (x - y) ∈ V from (f.map_sub x y).symm ▸ (Submodule.Quotient.eq _).1 hxy

@[gcongr]
/-
**SModEq.eval** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：eval {R : Type*} [CommRing R] {I : Ideal R} {x y : R} (h : x ≡ y [SMOD I])
 (f : R[X]) : f.eval x ≡ f.eval y [SMOD I]
参数：h : x ≡ y [SMOD I]；f : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_eq_sum`：eval_eq_sum : p.eval x = p.sum fun e a => a * x 
^ e
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SModEq.sum`：sum {ι} {s : Finset ι} {x y : ι -> M} (hxy : forall i in s, 
x i ≡ y i [SMOD U]) : ∑ i in s, x i ≡ ∑ i in s, y i [SMOD U]
· 使用定理 `SModEq.mul`：mul {I : Ideal A} {x₁ x₂ y₁ y₂ : A} (hxy₁ : x₁ ≡ y₁ [SMOD I]
) (hxy₂ : x₂ ≡ y₂ [SMOD I]) : x₁ * x₂ ≡ y₁ * y₂ [SMOD I]
· 使用定理 `SModEq.refl`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} (x : M), x ≡ x
 …
· 使用引理 `SModEq.pow`：pow {I : Ideal A} {x y : A} (n : Nat) (hxy : x ≡ y [SMOD I])
 : x ^ n ≡ y ^ n [SMOD I]
-/
theorem eval {R : Type*} [CommRing R] {I : Ideal R} {x y : R} (h : x ≡ y [SMOD I]) (f : R[X]) :
    f.eval x ≡ f.eval y [SMOD I] := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum]
  gcongr

variable (S) in
/-
**SModEq.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：restrictScalars [SMul S R] [IsScalarTower S R M] : x ≡ y [SMOD U.restrictS
calars S] ↔ x ≡ y [SMOD U]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem restrictScalars [SMul S R] [IsScalarTower S R M] : x ≡ y [SMOD U.restrictScalars S] ↔
    x ≡ y [SMOD U] := by simp [SModEq.sub_mem]
/-
**SModEq.idealQuotientMk** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：idealQuotientMk {R : Type*} [CommRing R] {I : Ideal R} {x y : R} : x ≡ y [
SMOD I] ↔ Ideal.Quotient.mk I x = Ideal.Quotient.mk I y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem idealQuotientMk {R : Type*} [CommRing R] {I : Ideal R} {x y : R} :
    x ≡ y [SMOD I] ↔ Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := Iff.rfl

section Pointwise

open scoped Pointwise

@[simp]
/-
**SModEq._root_.Submodule.vadd_set_subset_vadd_set_iff** 是 Mathlib 中的一个定理，位于命名空间
 `SModEq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Submodule.vadd_set_subset_vadd_set_iff :
    x +ᵥ (U : Set M) ⊆ y +ᵥ (U : Set M) ↔ x ≡ y [SMOD U] := by
  rw [SModEq.sub_mem]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Set.vadd_set_subset_iff_subset_neg_vadd_set, vadd_vadd, neg_add_eq_sub] at h
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using h U.zero_mem
  · rw [Set.vadd_set_subset_iff_subset_neg_vadd_set, vadd_vadd, neg_add_eq_sub]
    intro z hz
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using U.add_mem h hz

@[simp]
/-
**SModEq._root_.Submodule.vadd_set_eq_vadd_set_iff** 是 Mathlib 中的一个定理，位于命名空间 `SM
odEq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Submodule.vadd_set_eq_vadd_set_iff :
    x +ᵥ (U : Set M) = y +ᵥ (U : Set M) ↔ x ≡ y [SMOD U] :=
  ⟨fun h ↦ Submodule.vadd_set_subset_vadd_set_iff.mp h.subset,
    fun h ↦ Set.Subset.antisymm (Submodule.vadd_set_subset_vadd_set_iff.mpr h)
      (Submodule.vadd_set_subset_vadd_set_iff.mpr h.symm)⟩

end Pointwise

end SModEq

