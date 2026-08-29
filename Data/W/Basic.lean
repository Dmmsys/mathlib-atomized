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
Inductive type `WType` / 归纳类型 `WType`

English:
inductive WType
  parameters: {α : Type*} (β : α -> Type*)
  constructors (1):
    - mk: (a : α) (f : β a -> WType β) : WType β

中文:
归纳类型 WType
  参数: {α : 类型} (β : α -> 类型)
  构造子 (1 个):
    - mk: (a : α) (f : β a -> WType β) : WType β
-/
inductive WType {α : Type*} (β : α -> Type*)
  | mk (a : α) (f : β a -> WType β) : WType β

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (WType fun _ : Unit => Empty)
  body: ⟨WType.mk Unit.unit Empty.elim⟩

中文:
实例 :
  签名: 可居 (WType fun _ : 单元 => 空)
  定义体: ⟨WType.mk Unit.unit Empty.elim⟩

Depends on / 依赖: Empty.elim, Unit.unit, WType.mk
-/
instance : Inhabited (WType fun _ : Unit => Empty) :=
  ⟨WType.mk Unit.unit Empty.elim⟩

namespace WType

variable {α : Type*} {β : α -> Type*}

/--
Definition of `toSigma` / `toSigma` 的定义

English:
definition toSigma
  signature: : WType β -> Σ a : α, β a -> WType β

中文:
定义 toSigma
  签名: : WType β -> Σ a : α, β a -> WType β
-/
def toSigma : WType β -> Σ a : α, β a -> WType β
  | ⟨a, f⟩ => ⟨a, f⟩

/--
Definition of `ofSigma` / `ofSigma` 的定义

English:
definition ofSigma
  signature: : (Σ a : α, β a -> WType β) -> WType β

中文:
定义 ofSigma
  签名: : (Σ a : α, β a -> WType β) -> WType β
-/
def ofSigma : (Σ a : α, β a -> WType β) -> WType β
  | ⟨a, f⟩ => WType.mk a f

@[simp]
/--
theorem `ofSigma_toSigma` / 定理 `ofSigma_toSigma`

English:
theorem ofSigma_toSigma
  statement: forall w : WType β, ofSigma (toSigma w) = w

中文:
定理 ofSigma_toSigma
  结论: 对任意 w : WType β, ofSigma (toSigma w) = w
-/
theorem ofSigma_toSigma : forall w : WType β, ofSigma (toSigma w) = w
  | ⟨_, _⟩ => rfl

@[simp]
/--
theorem `toSigma_ofSigma` / 定理 `toSigma_ofSigma`

English:
theorem toSigma_ofSigma
  statement: forall s : Σ a : α, β a -> WType β, toSigma (ofSigma s) = s

中文:
定理 toSigma_ofSigma
  结论: 对任意 s : Σ a : α, β a -> WType β, toSigma (ofSigma s) = s
-/
theorem toSigma_ofSigma : forall s : Σ a : α, β a -> WType β, toSigma (ofSigma s) = s
  | ⟨_, _⟩ => rfl

variable (β) in
/-- The canonical bijection with the sigma type, showing that `WType` is a fixed point of
  the polynomial functor `X ↦ Σ a : α, β a → X`. -/
@[simps]
/--
Definition of `equivSigma` / `equivSigma` 的定义

English:
definition equivSigma
  signature: : WType β ≃ Σ a : α, β a -> WType β where
  body: toSigma
  invFun := ofSigma
  left_inv := ofSigma_toSigma
  right_inv := toSigma_ofSigma

中文:
定义 equivSigma
  签名: : WType β ≃ Σ a : α, β a -> WType β where
  定义体: toSigma
  invFun := ofSigma
  left_inv := ofSigma_toSigma
  right_inv := toSigma_ofSigma

Depends on / 依赖: toSigma
-/
def equivSigma : WType β ≃ Σ a : α, β a -> WType β where
  toFun := toSigma
  invFun := ofSigma
  left_inv := ofSigma_toSigma
  right_inv := toSigma_ofSigma

/--
Definition of `elim` / `elim` 的定义

English:
definition elim
  signature: (γ : Type*) (fγ : (Σ a : α, β a -> γ) -> γ)

中文:
定义 elim
  签名: (γ : 类型) (fγ : (Σ a : α, β a -> γ) -> γ)
-/
def elim (γ : Type*) (fγ : (Σ a : α, β a -> γ) -> γ) : WType β -> γ
  | ⟨a, f⟩ => fγ ⟨a, fun b => elim γ fγ (f b)⟩

/--
theorem `elim_injective` / 定理 `elim_injective`

English:
theorem elim_injective
  statement: (γ : Type*) (fγ : (Σ a : α, β a -> γ) -> γ)
  proof: Sigma.mk.inj_iff.mp (fγ_injective h)
    congr with x
    exact elim_injective γ fγ fγ_injective (congr_fun (eq_of_heq h) x :)

中文:
定理 elim_injective
  结论: (γ : 类型) (fγ : (Σ a : α, β a -> γ) -> γ)
  证明: Sigma.mk.inj_iff.mp (fγ_injective h)
    congr with x
    exact elim_injective γ fγ fγ_injective (congr_fun (eq_of_heq h) x :)

Depends on / 依赖: Sigma.mk.inj_iff.mp, inj_iff
-/
theorem elim_injective (γ : Type*) (fγ : (Σ a : α, β a -> γ) -> γ)
    (fγ_injective : Function.Injective fγ) : Function.Injective (elim γ fγ)
  | ⟨a₁, f₁⟩, ⟨a₂, f₂⟩, h => by
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp (fγ_injective h)
    congr with x
    exact elim_injective γ fγ fγ_injective (congr_fun (eq_of_heq h) x :)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hα
  signature: : IsEmpty α] : IsEmpty (WType β)
  body: ⟨fun w => WType.recOn w (IsEmpty.elim hα)⟩

中文:
实例 [hα
  签名: : 是空 α] : 是空 (WType β)
  定义体: ⟨fun w => WType.recOn w (IsEmpty.elim hα)⟩

Depends on / 依赖: IsEmpty, IsEmpty.elim, WType.recOn
-/
instance [hα : IsEmpty α] : IsEmpty (WType β) :=
  ⟨fun w => WType.recOn w (IsEmpty.elim hα)⟩

/--
theorem `infinite_of_nonempty_of_isEmpty` / 定理 `infinite_of_nonempty_of_isEmpty`

English:
theorem infinite_of_nonempty_of_isEmpty
  given: (a b : α) [ha : Nonempty (β a)] [he : IsEmpty (β b)]
  proof: ⟨by
    intro hf
    have hba : b != a := fun h => ha.elim (IsEmpty.elim' (show IsEmpty (β a) from h ▸ he))
    refine
      not_injective_infinite_finite
        (fun n : Nat =>
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

中文:
定理 infinite_of_nonempty_of_isEmpty
  条件: (a b : α) [ha : 非空 (β a)] [he : 是空 (β b)]
  证明: ⟨by
    intro hf
    have hba : b != a := fun h => ha.elim (IsEmpty.elim' (show IsEmpty (β a) from h ▸ he))
    refine
      not_injective_infinite_finite
        (fun n : Nat =>
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

Depends on / 依赖: IsEmpty, IsEmpty.elim, Nat.recOn, Nat.succ, congr_arg, funext_iff, generalizing, ha.elim, not_injective_infinite_finite
-/
theorem infinite_of_nonempty_of_isEmpty (a b : α) [ha : Nonempty (β a)] [he : IsEmpty (β b)] :
    Infinite (WType β) :=
  ⟨by
    intro hf
    have hba : b != a := fun h => ha.elim (IsEmpty.elim' (show IsEmpty (β a) from h ▸ he))
    refine
      not_injective_infinite_finite
        (fun n : Nat =>
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

variable [forall a : α, Fintype (β a)]

/--
Definition of `depth` / `depth` 的定义

English:
definition depth
  signature: : WType β -> Nat

中文:
定义 depth
  签名: : WType β -> 自然数
-/
def depth : WType β -> Nat
  | ⟨_, f⟩ => (Finset.sup Finset.univ fun n => depth (f n)) + 1

/--
theorem `depth_pos` / 定理 `depth_pos`

English:
theorem depth_pos
  given: (t : WType β)
  statement: 0 < t.depth
  proof: by
  cases t
  apply Nat.succ_pos

中文:
定理 depth_pos
  条件: (t : WType β)
  结论: 0 < t.depth
  证明: by
  cases t
  apply Nat.succ_pos

Depends on / 依赖: Nat.succ_pos, succ_pos
-/
theorem depth_pos (t : WType β) : 0 < t.depth := by
  cases t
  apply Nat.succ_pos

/--
theorem `depth_lt_depth_mk` / 定理 `depth_lt_depth_mk`

English:
theorem depth_lt_depth_mk
  given: (a : α) (f : β a -> WType β) (i : β a)
  statement: depth (f i) < depth ⟨a, f⟩
  proof: Nat.lt_succ_of_le (Finset.le_sup (f := (depth <| f ·)) (Finset.mem_univ i))

中文:
定理 depth_lt_depth_mk
  条件: (a : α) (f : β a -> WType β) (i : β a)
  结论: depth (f i) < depth ⟨a, f⟩
  证明: Nat.lt_succ_of_le (Finset.le_sup (f := (depth <| f ·)) (Finset.mem_univ i))

Depends on / 依赖: Finset, Finset.le_sup, Finset.mem_univ, Nat.lt_succ_of_le, le_sup, lt_succ_of_le, mem_univ
-/
theorem depth_lt_depth_mk (a : α) (f : β a -> WType β) (i : β a) : depth (f i) < depth ⟨a, f⟩ :=
  Nat.lt_succ_of_le (Finset.le_sup (f := (depth <| f ·)) (Finset.mem_univ i))

set_option backward.privateInPublic true in
/--
Definition of `WType'` / `WType'` 的定义

English:
abbreviation WType'
  signature: {α : Type*} (β : α -> Type*) [forall a : α, Fintype (β a)] (n : Nat)
  body: { t : WType β // t.depth <= n }

中文:
缩写 WType'
  签名: {α : 类型} (β : α -> 类型) [对任意 a : α, 有限类型 (β a)] (n : 自然数)
  定义体: { t : WType β // t.depth <= n }
-/
private abbrev WType' {α : Type*} (β : α -> Type*) [forall a : α, Fintype (β a)] (n : Nat) :=
  { t : WType β // t.depth <= n }

variable [forall a : α, Encodable (β a)]

set_option backward.privateInPublic true in
@[instance_reducible]
/--
Definition of `encodable_zero` / `encodable_zero` 的定义

English:
definition encodable_zero
  signature: : Encodable (WType' β 0)
  body: let f : WType' β 0 -> Empty := fun ⟨_, h⟩ => False.elim not_lt_of_ge h (WType.depth_pos _)
  let finv : Empty -> WType' β 0 := by
    intro x
    cases x
have : forall x, finv (f x) = x := fun ⟨_, h⟩ => False.elim not_lt_of_ge h (WType.depth_pos _)
  Encodable.ofLeftInverse f finv this

中文:
定义 encodable_zero
  签名: : 可编码 (WType' β 0)
  定义体: let f : WType' β 0 -> Empty := fun ⟨_, h⟩ => False.elim not_lt_of_ge h (WType.depth_pos _)
  let finv : Empty -> WType' β 0 := by
    intro x
    cases x
have : forall x, finv (f x) = x := fun ⟨_, h⟩ => False.elim not_lt_of_ge h (WType.depth_pos _)
  Encodable.ofLeftInverse f finv this
-/
private def encodable_zero : Encodable (WType' β 0) :=
let f : WType' β 0 -> Empty := fun ⟨_, h⟩ => False.elim not_lt_of_ge h (WType.depth_pos _)
  let finv : Empty -> WType' β 0 := by
    intro x
    cases x
have : forall x, finv (f x) = x := fun ⟨_, h⟩ => False.elim not_lt_of_ge h (WType.depth_pos _)
  Encodable.ofLeftInverse f finv this

/--
Definition of `f` / `f` 的定义

English:
definition f
  signature: (n : Nat)
  body: t
    have h₀ : forall i : β a, WType.depth (f i) <= n := fun i =>
      Nat.le_of_lt_succ (lt_of_lt_of_le (WType.depth_lt_depth_mk a f i) h)
    exact ⟨a, fun i : β a => ⟨f i, h₀ i⟩⟩

中文:
定义 f
  签名: (n : 自然数)
  定义体: t
    have h₀ : forall i : β a, WType.depth (f i) <= n := fun i =>
      Nat.le_of_lt_succ (lt_of_lt_of_le (WType.depth_lt_depth_mk a f i) h)
    exact ⟨a, fun i : β a => ⟨f i, h₀ i⟩⟩
-/
private def f (n : Nat) : WType' β (n + 1) -> Σ a : α, β a -> WType' β n
  | ⟨t, h⟩ => by
    obtain ⟨a, f⟩ := t
    have h₀ : forall i : β a, WType.depth (f i) <= n := fun i =>
      Nat.le_of_lt_succ (lt_of_lt_of_le (WType.depth_lt_depth_mk a f i) h)
    exact ⟨a, fun i : β a => ⟨f i, h₀ i⟩⟩

/--
Definition of `finv` / `finv` 的定义

English:
definition finv
  signature: (n : Nat)
  body: fun i : β a => (f i).val
    have : WType.depth ⟨a, f'⟩ <= n + 1 := Nat.add_le_add_right (Finset.sup_le fun b _ => (f b).2) 1
    ⟨⟨a, f'⟩, this⟩

中文:
定义 finv
  签名: (n : 自然数)
  定义体: fun i : β a => (f i).val
    have : WType.depth ⟨a, f'⟩ <= n + 1 := Nat.add_le_add_right (Finset.sup_le fun b _ => (f b).2) 1
    ⟨⟨a, f'⟩, this⟩
-/
private def finv (n : Nat) : (Σ a : α, β a -> WType' β n) -> WType' β (n + 1)
  | ⟨a, f⟩ =>
    let f' := fun i : β a => (f i).val
    have : WType.depth ⟨a, f'⟩ <= n + 1 := Nat.add_le_add_right (Finset.sup_le fun b _ => (f b).2) 1
    ⟨⟨a, f'⟩, this⟩

variable [Encodable α]

set_option backward.privateInPublic true in
@[instance_reducible]
/--
Definition of `encodable_succ` / `encodable_succ` 的定义

English:
definition encodable_succ
  signature: (n : Nat) (_ : Encodable (WType' β n))
  body: Encodable.ofLeftInverse (f n) (finv n)
    (by
      rintro ⟨⟨_, _⟩, _⟩
      rfl)

中文:
定义 encodable_succ
  签名: (n : 自然数) (_ : 可编码 (WType' β n))
  定义体: Encodable.ofLeftInverse (f n) (finv n)
    (by
      rintro ⟨⟨_, _⟩, _⟩
      rfl)
-/
private def encodable_succ (n : Nat) (_ : Encodable (WType' β n)) : Encodable (WType' β (n + 1)) :=
  Encodable.ofLeftInverse (f n) (finv n)
    (by
      rintro ⟨⟨_, _⟩, _⟩
      rfl)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Encodable (WType β)
  body: by
  haveI h' : forall n, Encodable (WType' β n) := fun n => Nat.rec encodable_zero encodable_succ n
  let f : WType β -> Σ n, WType' β n := fun t => ⟨t.depth, ⟨t, le_rfl⟩⟩
  let finv : (Σ n, WType' β n) -> WType β := fun p => p.2.1
  have : forall t, finv (f t) = t := fun t => rfl
  exact Encodable.ofLeftInverse f finv this

中文:
实例 :
  签名: 可编码 (WType β)
  定义体: by
  haveI h' : forall n, Encodable (WType' β n) := fun n => Nat.rec encodable_zero encodable_succ n
  let f : WType β -> Σ n, WType' β n := fun t => ⟨t.depth, ⟨t, le_rfl⟩⟩
  let finv : (Σ n, WType' β n) -> WType β := fun p => p.2.1
  have : forall t, finv (f t) = t := fun t => rfl
  exact Encodable.ofLeftInverse f finv this

Depends on / 依赖: Encodable, Encodable.ofLeftInverse, Nat.rec, encodable_succ, encodable_zero, le_rfl, ofLeftInverse, t.depth
-/
instance : Encodable (WType β) := by
  haveI h' : forall n, Encodable (WType' β n) := fun n => Nat.rec encodable_zero encodable_succ n
  let f : WType β -> Σ n, WType' β n := fun t => ⟨t.depth, ⟨t, le_rfl⟩⟩
  let finv : (Σ n, WType' β n) -> WType β := fun p => p.2.1
  have : forall t, finv (f t) = t := fun t => rfl
  exact Encodable.ofLeftInverse f finv this

end WType
