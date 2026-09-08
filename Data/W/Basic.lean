/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Logic.Encodable.Pi

/-!
# W types

Given `α : Type` and `β : α → Type`, the W type determined by this data, `WType β`, is the
inductively defined type of trees where the nodes are labeled by elements of `α` and the children of
a node labeled `a` are indexed by elements of `β a`.

This file is currently a stub, awaiting a full development of the theory. Currently, the main result
is that if `α` is an encodable fintype and `β a` is encodable for every `a : α`, then `WType β` is
encodable. This can be used to show the encodability of other inductive types, such as those that
are commonly used to formalize syntax, e.g. terms and expressions in a given language. The strategy
is illustrated in the example found in the file `prop_encodable` in the `archive/examples` folder of
mathlib.

## Implementation details

While the name `WType` is somewhat verbose, it is preferable to putting a single character
identifier `W` in the root namespace.
-/

@[expose] public section

-- For "W_type"

/--
Given `β : α → Type*`, `WType β` is the type of finitely branching trees where nodes are labeled by
elements of `α` and the children of a node labeled `a` are indexed by elements of `β a`.
-/
/-
**WType** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → (α → Type u_2) → Type (max u_1 u_2)
参数：α → Type u_2；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `β : α → Type*`, `WType β` is the type of finitely branching trees where n
odes are labeled by
elements of `α` and the children of a node labeled `a` are indexed by elements o
f `β a`.
-/
inductive WType {α : Type*} (β : α → Type*)
  | mk (a : α) (f : β a → WType β) : WType β
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (WType fun _ : Unit => Empty) :=
  ⟨WType.mk Unit.unit Empty.elim⟩

namespace WType

variable {α : Type*} {β : α → Type*}

/-- The canonical map to the corresponding sigma type, returning the label of a node as an
  element `a` of `α`, and the children of the node as a function `β a → WType β`. -/
/-
**WType.toSigma** 是 Mathlib 中的一个定义，位于命名空间 `WType`。
形式化陈述：{α : Type u_1} → {β : α → Type u_2} → WType β → (a : α) × (β a → WType β)
参数：a : α；β a → WType β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map to the corresponding sigma type, returning the label of a node
 as an
  element `a` of `α`, and the children of the node as a function `β a → WType β`
.
-/
def toSigma : WType β → Σ a : α, β a → WType β
  | ⟨a, f⟩ => ⟨a, f⟩

/-- The canonical map from the sigma type into a `WType`. Given a node `a : α`, and
  its children as a function `β a → WType β`, return the corresponding tree. -/
/-
**WType.ofSigma** 是 Mathlib 中的一个定义，位于命名空间 `WType`。
形式化陈述：{α : Type u_1} → {β : α → Type u_2} → (a : α) × (β a → WType β) → WType β
参数：a : α；β a → WType β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the sigma type into a `WType`. Given a node `a : α`, and
  its children as a function `β a → WType β`, return the corresponding tree.
-/
def ofSigma : (Σ a : α, β a → WType β) → WType β
  | ⟨a, f⟩ => WType.mk a f

@[simp]
/-
**WType.ofSigma_toSigma** 是 Mathlib 中的一个定理，位于命名空间 `WType`。
形式化陈述：∀ {α : Type u_1} {β : α → Type u_2} (w : WType β), WType.ofSigma w.toSigma
 = w
参数：w : WType β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSigma_toSigma : ∀ w : WType β, ofSigma (toSigma w) = w
  | ⟨_, _⟩ => rfl

@[simp]
/-
**WType.toSigma_ofSigma** 是 Mathlib 中的一个定理，位于命名空间 `WType`。
形式化陈述：∀ {α : Type u_1} {β : α → Type u_2} (s : (a : α) × (β a → WType β)), (WTyp
e.ofSigma s).toSigma = s
参数：s : (a : α) × (β a → WType β)；WType.ofSigma s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSigma_ofSigma : ∀ s : Σ a : α, β a → WType β, toSigma (ofSigma s) = s
  | ⟨_, _⟩ => rfl

variable (β) in
/-- The canonical bijection with the sigma type, showing that `WType` is a fixed point of
  the polynomial functor `X ↦ Σ a : α, β a → X`. -/
@[simps]
/-
**WType.equivSigma** 是 Mathlib 中的一个定义，位于命名空间 `WType`。
形式化陈述：equivSigma : WType β ≃ Σ a : α, β a -> WType β where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WType.ofSigma_toSigma`：∀ {α : Type u_1} {β : α → Type u_2} (w : WType β)
, WType.ofSigma w.toSigma = w
· 使用定理 `WType.toSigma_ofSigma`：∀ {α : Type u_1} {β : α → Type u_2} (s : (a : α) 
× (β a → WType β)), (WType.ofSigma s).toSigma = s

--- 原说明 ---
The canonical bijection with the sigma type, showing that `WType` is a fixed poi
nt of
  the polynomial functor `X ↦ Σ a : α, β a → X`.
-/
def equivSigma : WType β ≃ Σ a : α, β a → WType β where
  toFun := toSigma
  invFun := ofSigma
  left_inv := ofSigma_toSigma
  right_inv := toSigma_ofSigma

/-- The canonical map from `WType β` into any type `γ` given a map `(Σ a : α, β a → γ) → γ`. -/
/-
**WType.elim** 是 Mathlib 中的一个定义，位于命名空间 `WType`。
形式化陈述：{α : Type u_1} → {β : α → Type u_2} → (γ : Type u_3) → ((a : α) × (β a → γ
) → γ) → WType β → γ
参数：γ : Type u_3；(a : α) × (β a → γ) → γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `WType β` into any type `γ` given a map `(Σ a : α, β a → 
γ) → γ`.
-/
def elim (γ : Type*) (fγ : (Σ a : α, β a → γ) → γ) : WType β → γ
  | ⟨a, f⟩ => fγ ⟨a, fun b => elim γ fγ (f b)⟩
/-
**WType.elim_injective** 是 Mathlib 中的一个定理，位于命名空间 `WType`。
形式化陈述：elim_injective (γ : Type*) (fγ : (Σ a : α, β a -> γ) -> γ) (fγ_injective :
 Function.Injective fγ) : Function.Injective (elim γ fγ) | ⟨a₁, f₁⟩, ⟨a₂, f₂⟩, h
 => by obtain ⟨rfl, h⟩
参数：γ : Type*；fγ : (Σ a : α, β a -> γ) -> γ；fγ_injective : Function.Injective fγ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem elim_injective (γ : Type*) (fγ : (Σ a : α, β a → γ) → γ)
    (fγ_injective : Function.Injective fγ) : Function.Injective (elim γ fγ)
  | ⟨a₁, f₁⟩, ⟨a₂, f₂⟩, h => by
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp (fγ_injective h)
    congr with x
    exact elim_injective γ fγ fγ_injective (congr_fun (eq_of_heq h) x :)
/-
**WType.** 是 Mathlib 中的一个实例，位于命名空间 `WType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hα : IsEmpty α] : IsEmpty (WType β) :=
  ⟨fun w => WType.recOn w (IsEmpty.elim hα)⟩
/-
**WType.infinite_of_nonempty_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `WType`。
形式化陈述：infinite_of_nonempty_of_isEmpty (a b : α) [ha : Nonempty (β a)] [he : IsEm
pty (β b)] : Infinite (WType β)
参数：a b : α；β a；β b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `not_injective_infinite_finite`：not_injective_infinite_finite {α β} [Infi
nite α] [Finite β] (f : α -> β) : ¬Injective f
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WType.mk.injEq`：∀ {α : Type u_1} {β : α → Type u_2} (a : α) (f : β a → W
Type β) (a_1 : α) (f_1 : β a_1 → WType β),   (WType.mk a f = WType.mk a_1 f_1) =
 (a …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem infinite_of_nonempty_of_isEmpty (a b : α) [ha : Nonempty (β a)] [he : IsEmpty (β b)] :
    Infinite (WType β) :=
  ⟨by
    intro hf
    have hba : b ≠ a := fun h => ha.elim (IsEmpty.elim' (show IsEmpty (β a) from h ▸ he))
    refine
      not_injective_infinite_finite
        (fun n : ℕ =>
          show WType β from Nat.recOn n ⟨b, IsEmpty.elim' he⟩ fun _ ih => ⟨a, fun _ => ih⟩)
        ?_
    intro n m h
    induction n generalizing m with
    | zero => rcases m with - | m <;> simp_all
    | succ n ih =>
      rcases m with - | m
      · simp_all
      · refine congr_arg Nat.succ (ih ?_)
        simp_all [funext_iff]⟩

variable [∀ a : α, Fintype (β a)]

/-- The depth of a finitely branching tree. -/
/-
**WType.depth** 是 Mathlib 中的一个定义，位于命名空间 `WType`。
形式化陈述：{α : Type u_1} → {β : α → Type u_2} → [(a : α) → Fintype (β a)] → WType β 
→ ℕ
参数：a : α；β a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The depth of a finitely branching tree.
-/
def depth : WType β → ℕ
  | ⟨_, f⟩ => (Finset.sup Finset.univ fun n => depth (f n)) + 1
/-
**WType.depth_pos** 是 Mathlib 中的一个定理，位于命名空间 `WType`。
形式化陈述：depth_pos (t : WType β) : 0 < t.depth
参数：t : WType β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem depth_pos (t : WType β) : 0 < t.depth := by
  cases t
  apply Nat.succ_pos
/-
**WType.depth_lt_depth_mk** 是 Mathlib 中的一个定理，位于命名空间 `WType`。
形式化陈述：depth_lt_depth_mk (a : α) (f : β a -> WType β) (i : β a) : depth (f i) < d
epth ⟨a, f⟩
参数：a : α；f : β a -> WType β；i : β a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem depth_lt_depth_mk (a : α) (f : β a → WType β) (i : β a) : depth (f i) < depth ⟨a, f⟩ :=
  Nat.lt_succ_of_le (Finset.le_sup (f := (depth <| f ·)) (Finset.mem_univ i))

set_option backward.privateInPublic true in
/-
Show that W types are encodable when `α` is an encodable fintype and for every `a : α`, `β a` is
encodable.

We define an auxiliary type `WType' β n` of trees of depth at most `n`, and then we show by
induction on `n` that these are all encodable. These auxiliary constructions are not interesting in
and of themselves, so we mark them as `private`.
-/
/-
**WType.WType'** 是 Mathlib 中的一个缩写定义，位于命名空间 `WType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show that W types are encodable when `α` is an encodable fintype and for every `
a : α`, `β a` is
encodable.

We define an auxiliary type `WType' β n` of trees of depth at most `n`, and then
 we show by
induction on `n` that these are all encodable. These auxiliary constructions are
 not interesting in
and of themselves, so we mark them as `private`.
-/
private abbrev WType' {α : Type*} (β : α → Type*) [∀ a : α, Fintype (β a)] (n : ℕ) :=
  { t : WType β // t.depth ≤ n }

variable [∀ a : α, Encodable (β a)]

set_option backward.privateInPublic true in
@[instance_reducible]
/-
**WType.encodable_zero** 是 Mathlib 中的一个定义，位于命名空间 `WType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def encodable_zero : Encodable (WType' β 0) :=
  let f : WType' β 0 → Empty := fun ⟨_, h⟩ => False.elim <| not_lt_of_ge h (WType.depth_pos _)
  let finv : Empty → WType' β 0 := by
    intro x
    cases x
  have : ∀ x, finv (f x) = x := fun ⟨_, h⟩ => False.elim <| not_lt_of_ge h (WType.depth_pos _)
  Encodable.ofLeftInverse f finv this
/-
**WType.f** 是 Mathlib 中的一个定义，位于命名空间 `WType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def f (n : ℕ) : WType' β (n + 1) → Σ a : α, β a → WType' β n
  | ⟨t, h⟩ => by
    obtain ⟨a, f⟩ := t
    have h₀ : ∀ i : β a, WType.depth (f i) ≤ n := fun i =>
      Nat.le_of_lt_succ (lt_of_lt_of_le (WType.depth_lt_depth_mk a f i) h)
    exact ⟨a, fun i : β a => ⟨f i, h₀ i⟩⟩
/-
**WType.finv** 是 Mathlib 中的一个定义，位于命名空间 `WType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def finv (n : ℕ) : (Σ a : α, β a → WType' β n) → WType' β (n + 1)
  | ⟨a, f⟩ =>
    let f' := fun i : β a => (f i).val
    have : WType.depth ⟨a, f'⟩ ≤ n + 1 := Nat.add_le_add_right (Finset.sup_le fun b _ => (f b).2) 1
    ⟨⟨a, f'⟩, this⟩

variable [Encodable α]

set_option backward.privateInPublic true in
@[instance_reducible]
/-
**WType.encodable_succ** 是 Mathlib 中的一个定义，位于命名空间 `WType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def encodable_succ (n : Nat) (_ : Encodable (WType' β n)) : Encodable (WType' β (n + 1)) :=
  Encodable.ofLeftInverse (f n) (finv n)
    (by
      rintro ⟨⟨_, _⟩, _⟩
      rfl)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `WType` is encodable when `α` is an encodable fintype and for every `a : α`, `β a` is
encodable. -/
/-
**WType.** 是 Mathlib 中的一个实例，位于命名空间 `WType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WType` is encodable when `α` is an encodable fintype and for every `a : α`, `β 
a` is
encodable.
-/
instance : Encodable (WType β) := by
  haveI h' : ∀ n, Encodable (WType' β n) := fun n => Nat.rec encodable_zero encodable_succ n
  let f : WType β → Σ n, WType' β n := fun t => ⟨t.depth, ⟨t, le_rfl⟩⟩
  let finv : (Σ n, WType' β n) → WType β := fun p => p.2.1
  have : ∀ t, finv (f t) = t := fun t => rfl
  exact Encodable.ofLeftInverse f finv this

end WType

