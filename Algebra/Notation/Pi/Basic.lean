/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
module

public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Logic.Function.Basic

/-!
# Very basic algebraic operations on pi types

This file provides very basic algebraic operations on functions.
-/

@[expose] public section

assert_not_exists Monoid Preorder

open Function

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

namespace Pi
variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

/-- The function supported at `i`, with value `x` there, and `1` elsewhere. -/
@[to_additive /-- The function supported at `i`, with value `x` there, and `0` elsewhere. -/]
/-
**Pi.mulSingle** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
形式化陈述：mulSingle (i : ι) (x : M i) : forall j, M j
参数：i : ι；x : M i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function supported at `i`, with value `x` there, and `1` elsewhere.
-/
def mulSingle (i : ι) (x : M i) : ∀ j, M j := Function.update 1 i x

@[to_additive (attr := simp)]
/-
**Pi.mulSingle_eq_same** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i x i = x
参数：i : ι；x : M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
lemma mulSingle_eq_same (i : ι) (x : M i) : mulSingle i x i = x := Function.update_self i x _

@[to_additive (attr := simp)]
/-
**Pi.mulSingle_eq_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_eq_of_ne {i i' : ι} (h : i' != i) (x : M i) : mulSingle i x i' =
 1
参数：h : i' != i；x : M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
lemma mulSingle_eq_of_ne {i i' : ι} (h : i' ≠ i) (x : M i) : mulSingle i x i' = 1 :=
  Function.update_of_ne h x _

/-- Abbreviation for `mulSingle_eq_of_ne h.symm`, for ease of use by `simp`. -/
@[to_additive (attr := simp)
  /-- Abbreviation for `single_eq_of_ne h.symm`, for ease of use by `simp`. -/]
/-
**Pi.mulSingle_eq_of_ne'** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_eq_of_ne' {i i' : ι} (h : i != i') (x : M i) : mulSingle i x i' 
= 1
参数：h : i != i'；x : M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.mulSingle_eq_of_ne`：mulSingle_eq_of_ne {i i' : ι} (h : i' != i) (x : 
M i) : mulSingle i x i' = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma mulSingle_eq_of_ne' {i i' : ι} (h : i ≠ i') (x : M i) : mulSingle i x i' = 1 :=
  mulSingle_eq_of_ne h.symm x

@[to_additive (attr := simp)]
/-
**Pi.mulSingle_one** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_one (i : ι) : mulSingle i (1 : M i) = 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
-/
lemma mulSingle_one (i : ι) : mulSingle i (1 : M i) = 1 := Function.update_eq_self _ _

@[to_additive (attr := simp)]
/-
**Pi.mulSingle_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_eq_one_iff : mulSingle i x = 1 ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
· 使用引理 `Pi.mulSingle_one`：mulSingle_one (i : ι) : mulSingle i (1 : M i) = 1
-/
lemma mulSingle_eq_one_iff : mulSingle i x = 1 ↔ x = 1 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ mulSingle_one i⟩
  rw [← mulSingle_eq_same i x, h, one_apply]

@[to_additive]
/-
**Pi.mulSingle_ne_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_ne_one_iff : mulSingle i x != 1 ↔ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用引理 `Pi.mulSingle_eq_one_iff`：mulSingle_eq_one_iff : mulSingle i x = 1 ↔ x = 
1
-/
lemma mulSingle_ne_one_iff : mulSingle i x ≠ 1 ↔ x ≠ 1 :=
  mulSingle_eq_one_iff.ne

@[to_additive]
/-
**Pi.apply_mulSingle** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：apply_mulSingle (f' : forall i, M i -> N i) (hf' : forall i, f' i 1 = 1) (
i : ι) (x : M i) (j : ι) : f' j (mulSingle i x j) = mulSingle i (f' i x) j
参数：f' : forall i, M i -> N i；hf' : forall i, f' i 1 = 1；i : ι；x : M i；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update.congr_simp`：∀ {α : Sort u} {β : α → Sort v} {inst : Deci
dableEq α} [inst_1 : DecidableEq α] (f f_1 : (a : α) → β a),   f = f_1 → ∀ (a' :
 α) (v v_1 : β a…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.apply_update`：apply_update {ι : Sort*} [DecidableEq ι] {α β : ι
 -> Sort*} (f : forall i, α i -> β i) (g : forall i, α i) (i : ι) (v : α i) (j :
 ι) : f j (…
-/
lemma apply_mulSingle (f' : ∀ i, M i → N i) (hf' : ∀ i, f' i 1 = 1) (i : ι) (x : M i) (j : ι) :
    f' j (mulSingle i x j) = mulSingle i (f' i x) j := by
  simpa only [Pi.one_apply, hf', mulSingle] using! Function.apply_update f' 1 i x j

@[to_additive apply_single₂]
/-
**Pi.apply_mulSingle** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：apply_mulSingle (f' : forall i, M i -> N i) (hf' : forall i, f' i 1 = 1) (
i : ι) (x : M i) (j : ι) : f' j (mulSingle i x j) = mulSingle i (f' i x) j
参数：f' : forall i, M i -> N i；hf' : forall i, f' i 1 = 1；i : ι；x : M i；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update.congr_simp`：∀ {α : Sort u} {β : α → Sort v} {inst : Deci
dableEq α} [inst_1 : DecidableEq α] (f f_1 : (a : α) → β a),   f = f_1 → ∀ (a' :
 α) (v v_1 : β a…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.apply_update`：apply_update {ι : Sort*} [DecidableEq ι] {α β : ι
 -> Sort*} (f : forall i, α i -> β i) (g : forall i, α i) (i : ι) (v : α i) (j :
 ι) : f j (…
-/
lemma apply_mulSingle₂ (f' : ∀ i, M i → N i → O i) (hf' : ∀ i, f' i 1 1 = 1) (i : ι)
    (x : M i) (y : N i) (j : ι) :
    f' j (mulSingle i x j) (mulSingle i y j) = mulSingle i (f' i x y) j := by
  by_cases h : j = i
  · subst h
    simp only [mulSingle_eq_same]
  · simp only [mulSingle_eq_of_ne h, hf']

@[to_additive]
/-
**Pi.mulSingle_op** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_op (op : forall i, M i -> N i) (h : forall i, op i 1 = 1) (i : ι
) (x : M i) : mulSingle i (op i x) = fun j => op j (mulSingle i x j)
参数：op : forall i, M i -> N i；h : forall i, op i 1 = 1；i : ι；x : M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Pi.apply_mulSingle`：apply_mulSingle (f' : forall i, M i -> N i) (hf' : f
orall i, f' i 1 = 1) (i : ι) (x : M i) (j : ι) : f' j (mulSingle i x j) = mulSin
gle i (f…
-/
lemma mulSingle_op (op : ∀ i, M i → N i) (h : ∀ i, op i 1 = 1) (i : ι) (x : M i) :
    mulSingle i (op i x) = fun j => op j (mulSingle i x j) :=
  .symm <| funext <| apply_mulSingle op h i x

@[to_additive]
/-
**Pi.mulSingle_op** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_op (op : forall i, M i -> N i) (h : forall i, op i 1 = 1) (i : ι
) (x : M i) : mulSingle i (op i x) = fun j => op j (mulSingle i x j)
参数：op : forall i, M i -> N i；h : forall i, op i 1 = 1；i : ι；x : M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Pi.apply_mulSingle`：apply_mulSingle (f' : forall i, M i -> N i) (hf' : f
orall i, f' i 1 = 1) (i : ι) (x : M i) (j : ι) : f' j (mulSingle i x j) = mulSin
gle i (f…
-/
lemma mulSingle_op₂ (op : ∀ i, M i → N i → O i) (h : ∀ i, op i 1 1 = 1) (i : ι) (x : M i)
    (y : N i) : mulSingle i (op i x y) = fun j ↦ op j (mulSingle i x j) (mulSingle i y j) :=
  .symm <| funext <| apply_mulSingle₂ op h i x y

@[to_additive]
/-
**Pi.mulSingle_injective** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_injective (i : ι) : Function.Injective (mulSingle i : M i -> for
all i, M i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_injective`：update_injective (f : forall a, β a) (a' : α)
 : Injective (update f a')
-/
lemma mulSingle_injective (i : ι) : Function.Injective (mulSingle i : M i → ∀ i, M i) :=
  Function.update_injective _ i

@[to_additive (attr := simp)]
/-
**Pi.mulSingle_inj** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_inj (i : ι) {x y : M i} : mulSingle i x = mulSingle i y ↔ x = y
参数：i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Pi.mulSingle_injective`：mulSingle_injective (i : ι) : Function.Injective
 (mulSingle i : M i -> forall i, M i)
-/
lemma mulSingle_inj (i : ι) {x y : M i} : mulSingle i x = mulSingle i y ↔ x = y :=
  (mulSingle_injective _).eq_iff

variable {M : Type*} [One M]

/--
A congruence lemma for `Pi.mulSingle`, specialized for the non-dependent case. Without this,
`simp` can't rewrite in the first and third argument (`i` and `j`) because of dependence.
See also https://github.com/leanprover/lean4/issues/12478.
-/
@[to_additive (attr := congr) /--
A congruence lemma for `Pi.single`, specialized for the non-dependent case. Without this,
`simp` can't rewrite in the first and third argument (`i` and `j`) because of dependence.
See also https://github.com/leanprover/lean4/issues/12478.
-/]
/-
**Pi.mulSingle_congr** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_congr {i₁ i₂ : ι} (hi : i₁ = i₂) {x₁ x₂ : M} (hx : x₁ = x₂) {j₁ 
j₂ : ι} (hj : j₁ = j₂) : (mulSingle i₁ x₁ : ι -> M) j₁ = (mulSingle i₂ x₂ : ι ->
 M) j₂
参数：hi : i₁ = i₂；hx : x₁ = x₂；hj : j₁ = j₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.update_congr`：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f
₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (
ha : a₁ = a…
-/
lemma mulSingle_congr {i₁ i₂ : ι} (hi : i₁ = i₂)
    {x₁ x₂ : M} (hx : x₁ = x₂) {j₁ j₂ : ι} (hj : j₁ = j₂) :
    (mulSingle i₁ x₁ : ι → M) j₁ = (mulSingle i₂ x₂ : ι → M) j₂ :=
  update_congr rfl hi hx hj

/-- On non-dependent functions, `Pi.mulSingle` can be expressed as an `ite` -/
@[to_additive (attr := grind =)
  /-- On non-dependent functions, `Pi.single` can be expressed as an `ite` -/]
/-
**Pi.mulSingle_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_apply (i : ι) (x : M) (i' : ι) : (mulSingle i x : ι -> M) i' = i
f i' = i then x else 1
参数：i : ι；x : M；i' : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
-/
lemma mulSingle_apply (i : ι) (x : M) (i' : ι) :
    (mulSingle i x : ι → M) i' = if i' = i then x else 1 :=
  Function.update_apply (1 : ι → M) i x i'

-- Porting note: added type ascription (_ : ι → M)
/-- On non-dependent functions, `Pi.mulSingle` is symmetric in the two indices. -/
@[to_additive /-- On non-dependent functions, `Pi.single` is symmetric in the two indices. -/]
/-
**Pi.mulSingle_comm** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_comm (i : ι) (x : M) (j : ι) : (mulSingle i x : ι -> M) j = (mul
Single j x : ι -> M) i
参数：i : ι；x : M；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mulSingle_apply`：mulSingle_apply (i : ι) (x : M) (i' : ι) : (mulSingl
e i x : ι -> M) i' = if i' = i then x else 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
On non-dependent functions, `Pi.mulSingle` is symmetric in the two indices.
-/
lemma mulSingle_comm (i : ι) (x : M) (j : ι) :
    (mulSingle i x : ι → M) j = (mulSingle j x : ι → M) i := by simp [mulSingle_apply, eq_comm]

variable [DecidableEq ι']

@[to_additive (attr := simp)]
/-
**Pi.curry_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：curry_mulSingle (i : ι × ι') (b : M) : curry (Pi.mulSingle i b) = Pi.mulSi
ngle i.1 (Pi.mulSingle i.2 b)
参数：i : ι × ι'；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.curry_update`：curry_update {α α' β : Type*} [DecidableEq α] [De
cidableEq α'] (f : α × α' -> β) (aa' : α × α') (b : β) : curry (Function.update 
f aa' b) = …
-/
theorem curry_mulSingle (i : ι × ι') (b : M) :
    curry (Pi.mulSingle i b) = Pi.mulSingle i.1 (Pi.mulSingle i.2 b) :=
  curry_update _ _ _

@[to_additive (attr := simp)]
/-
**Pi.uncurry_mulSingle_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：uncurry_mulSingle_mulSingle (i : ι) (i' : ι') (b : M) : uncurry (Pi.mulSin
gle i (Pi.mulSingle i' b)) = Pi.mulSingle (i, i') b
参数：i : ι；i' : ι'；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.uncurry_update_update`：uncurry_update_update {α α' β : Type*} [
DecidableEq α] [DecidableEq α'] (f : α -> α' -> β) (a : α) (a' : α') (b : β) : u
ncurry (Function.upd…
-/
theorem uncurry_mulSingle_mulSingle (i : ι) (i' : ι') (b : M) :
    uncurry (Pi.mulSingle i (Pi.mulSingle i' b)) = Pi.mulSingle (i, i') b :=
  uncurry_update_update _ _ _ _

end Pi

