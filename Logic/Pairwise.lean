/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Nat.Notation

/-!
# Relations holding pairwise

This file defines pairwise relations.

## Main declarations

* `Pairwise`: `Pairwise r` states that `r i j` for all `i ≠ j`.
* `Set.Pairwise`: `s.Pairwise r` states that `r i j` for all `i ≠ j` with `i, j ∈ s`.
-/

@[expose] public section

open Function

variable {α β ι : Type*} {r p : α → α → Prop}

section Pairwise

variable {f : ι → α} {s : Set α} {a b : α}

/-- A relation `r` holds pairwise if `r i j` for all `i ≠ j`. -/
/-
**Pairwise** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Pairwise (r : α -> α -> Prop)
参数：r : α -> α -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation `r` holds pairwise if `r i j` for all `i ≠ j`.
-/
def Pairwise (r : α → α → Prop) :=
  ∀ ⦃i j⦄, i ≠ j → r i j
/-
**Pairwise.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.Pairwise r
参数：h : t subseteq s；hs : s.Pairwise r。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pairwise.mono (hr : Pairwise r) (h : ∀ ⦃i j⦄, r i j → p i j) : Pairwise p :=
  fun _i _j hij => h <| hr hij
/-
**Pairwise.eq** 是 Mathlib 中的一个定理，位于命名空间 `Pairwise`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {a b : α}, Pairwise r → ¬r a b → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
-/
protected theorem Pairwise.eq (h : Pairwise r) : ¬r a b → a = b :=
  not_imp_comm.1 <| @h _ _

@[simp]
/-
**Subsingleton.pairwise** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} [Subsingleton α], Pairwise r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
protected lemma Subsingleton.pairwise [Subsingleton α] : Pairwise r :=
  fun _ _ h ↦ False.elim <| h.elim <| Subsingleton.elim _ _
/-
**Function.injective_iff_pairwise_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.injective_iff_pairwise_ne : Injective f ↔ Pairwise ((· != ·) on f
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
-/
theorem Function.injective_iff_pairwise_ne : Injective f ↔ Pairwise ((· ≠ ·) on f) :=
  forall₂_congr fun _i _j => not_imp_not.symm

alias ⟨Function.Injective.pairwise_ne, _⟩ := Function.injective_iff_pairwise_ne
/-
**Pairwise.comp_of_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pairwise.comp_of_injective (hr : Pairwise r) {f : β -> α} (hf : Injective 
f) : Pairwise (r on f)
参数：hr : Pairwise r；hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
-/
lemma Pairwise.comp_of_injective (hr : Pairwise r) {f : β → α} (hf : Injective f) :
    Pairwise (r on f) :=
  fun _ _ h ↦ hr <| hf.ne h
/-
**Pairwise.of_comp_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pairwise.of_comp_of_surjective {f : β -> α} (hr : Pairwise (r on f)) (hf :
 Surjective f) : Pairwise r
参数：hr : Pairwise (r on f)；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall₂`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}
,   Function.Surjective f → ∀ {p : β → β → Prop}, (∀ (y₁ y₂ : β), p y₁ y₂) ↔ ∀ (
x₁ x₂ : α), p (f …
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
lemma Pairwise.of_comp_of_surjective {f : β → α} (hr : Pairwise (r on f)) (hf : Surjective f) :
    Pairwise r := hf.forall₂.2 fun _ _ h ↦ hr <| ne_of_apply_ne f h
/-
**Function.Bijective.pairwise_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Bijective.pairwise_comp_iff {f : β -> α} (hf : Bijective f) : Pai
rwise (r on f) ↔ Pairwise r
参数：hf : Bijective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pairwise.of_comp_of_surjective`：Pairwise.of_comp_of_surjective {f : β ->
 α} (hr : Pairwise (r on f)) (hf : Surjective f) : Pairwise r
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用引理 `Pairwise.comp_of_injective`：Pairwise.comp_of_injective (hr : Pairwise r)
 {f : β -> α} (hf : Injective f) : Pairwise (r on f)
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
-/
lemma Function.Bijective.pairwise_comp_iff {f : β → α} (hf : Bijective f) :
    Pairwise (r on f) ↔ Pairwise r :=
  ⟨fun hr ↦ hr.of_comp_of_surjective hf.surjective, fun hr ↦ hr.comp_of_injective hf.injective⟩
/-
**pairwise_fin_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pairwise_fin_succ_iff {n : Nat} {R : Fin n.succ -> Fin n.succ -> Prop} : P
airwise R ↔ (forall i, R (Fin.succ i) 0) ∧ (forall j, R 0 (Fin.succ j)) ∧ Pairwi
se fun i j => R (Fin.succ i) (Fin.succ j) where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.succ_ne_zero`：∀ {n : ℕ} (k : Fin n), k.succ ≠ 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.succ_inj`：∀ {n : ℕ} {a b : Fin n}, a.succ = b.succ ↔ a = b
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
theorem pairwise_fin_succ_iff {n : ℕ} {R : Fin n.succ → Fin n.succ → Prop} :
    Pairwise R ↔
      (∀ i, R (Fin.succ i) 0) ∧ (∀ j, R 0 (Fin.succ j)) ∧
      Pairwise fun i j => R (Fin.succ i) (Fin.succ j) where
  mp h := ⟨
    fun _ => h (Fin.succ_ne_zero _), fun _ => h (Fin.succ_ne_zero _).symm,
    fun _i _j hij => h <| Fin.succ_inj.not.2 hij⟩
  mpr
  | ⟨hi, hj, h⟩ =>
    Fin.cases
      (Fin.cases nofun fun j _ => hj j)
      (fun i => Fin.cases (fun _ => hi i) fun _j hij => h (ne_of_apply_ne _ hij))
/-
**pairwise_fin_succ_iff_of_isSymm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pairwise_fin_succ_iff_of_isSymm {n : Nat} {R : Fin n.succ -> Fin n.succ ->
 Prop} [Std.Symm R] : Pairwise R ↔ (forall j, R 0 (Fin.succ j)) ∧ Pairwise fun i
 j => R (Fin.succ i) (Fin.succ j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `comm`：comm [Std.Symm r] {a b : α} : r a b ↔ r b a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwise_fin_succ_iff_of_isSymm {n : ℕ} {R : Fin n.succ → Fin n.succ → Prop} [Std.Symm R] :
    Pairwise R ↔ (∀ j, R 0 (Fin.succ j)) ∧ Pairwise fun i j => R (Fin.succ i) (Fin.succ j) := by
  simp only [pairwise_fin_succ_iff, comm (b := 0) (r := R), and_self_left]

namespace Set

/-- The relation `r` holds pairwise on the set `s` if `r x y` for all *distinct* `x y ∈ s`. -/
/-
**Set.Pairwise** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_1} → Set α → (α → α → Prop) → Prop
参数：α → α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation `r` holds pairwise on the set `s` if `r x y` for all *distinct* `x 
y ∈ s`.
-/
protected def Pairwise (s : Set α) (r : α → α → Prop) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → r x y
/-
**Set.pairwise_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_of_forall (s : Set α) (r : α -> α -> Prop) (h : forall a b, r a b
) : s.Pairwise r
参数：s : Set α；r : α -> α -> Prop；h : forall a b, r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pairwise_of_forall (s : Set α) (r : α → α → Prop) (h : ∀ a b, r a b) : s.Pairwise r :=
  fun a _ b _ _ => h a b
/-
**Set.Pairwise.imp_on** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, s.Pairwise r → (s.Pairw
ise fun ⦃a b⦄ => r a b → p a b) → s.Pairwise p
参数：s.Pairwise fun ⦃a b⦄ => r a b → p a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pairwise.imp_on (h : s.Pairwise r) (hrp : s.Pairwise fun ⦃a b : α⦄ => r a b → p a b) :
    s.Pairwise p :=
  fun _a ha _b hb hab => hrp ha hb hab <| h ha hb hab
/-
**Set.Pairwise.imp** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, s.Pairwise r → (∀ ⦃a b 
: α⦄, r a b → p a b) → s.Pairwise p
参数：∀ ⦃a b : α⦄, r a b → p a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.imp_on`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, 
s.Pairwise r → (s.Pairwise fun ⦃a b⦄ => r a b → p a b) → s.Pairwise p
· 使用定理 `Set.pairwise_of_forall`：pairwise_of_forall (s : Set α) (r : α -> α -> Pr
op) (h : forall a b, r a b) : s.Pairwise r
-/
theorem Pairwise.imp (h : s.Pairwise r) (hpq : ∀ ⦃a b : α⦄, r a b → p a b) : s.Pairwise p :=
  h.imp_on <| pairwise_of_forall s _ hpq
/-
**Set.Pairwise.eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a b : α}, s.Pairwise r → 
a ∈ s → b ∈ s → ¬r a b → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
-/
protected theorem Pairwise.eq (hs : s.Pairwise r) (ha : a ∈ s) (hb : b ∈ s) (h : ¬r a b) : a = b :=
  of_not_not fun hab => h <| hs ha hb hab
/-
**Set._root_.Std.Refl.set_pairwise_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Std.Refl.set_pairwise_iff [Std.Refl r] :
    s.Pairwise r ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b :=
  forall₄_congr fun a _ _ _ => or_iff_not_imp_left.symm.trans <| or_iff_right_of_imp <| Eq.ndrec <|
    refl a

@[deprecated (since := "2026-03-27")]
alias _root_.Reflexive.set_pairwise_iff := Std.Refl.set_pairwise_iff
/-
**Set.Pairwise.on_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pairwise`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} {r : α → α → Prop} {f : ι → α} {s : Set α}
,   s.Pairwise r → Function.Injective f → (∀ (x : ι), f x ∈ s) → Pairwise (Funct
ion.onFun r f)
参数：∀ (x : ι), f x ∈ s；Function.onFun r f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
-/
theorem Pairwise.on_injective (hs : s.Pairwise r) (hf : Function.Injective f) (hfs : ∀ x, f x ∈ s) :
    Pairwise (r on f) := fun i j hij => hs (hfs i) (hfs j) (hf.ne hij)

end Set

/-
**Pairwise.set_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：Pairwise.set_pairwise (hl : Pairwise R l) [Std.Symm R] : { x | x in l }.Pa
irwise R
参数：hl : Pairwise R l。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pairwise.set_pairwise (h : Pairwise r) (s : Set α) : s.Pairwise r := fun _ _ _ _ w => h w

end Pairwise

