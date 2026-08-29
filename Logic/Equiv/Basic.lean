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
/--
Definition of `piOptionEquivProd` / `piOptionEquivProd` 的定义

English:
definition piOptionEquivProd
  signature: {α} {β : Option α -> Type*}
  body: (f none, fun a => f (some a))
  invFun x a := Option.casesOn a x.fst x.snd
  left_inv f := funext fun a => by cases a <;> rfl

中文:
定义 piOptionEquivProd
  签名: {α} {β : Option α -> 类型}
  定义体: (f none, fun a => f (some a))
  invFun x a := Option.casesOn a x.fst x.snd
  left_inv f := funext fun a => by cases a <;> rfl
-/
def piOptionEquivProd {α} {β : Option α -> Type*} :
    (forall a : Option α, β a) ≃ β none × forall a : α, β (some a) where
  toFun f := (f none, fun a => f (some a))
  invFun x a := Option.casesOn a x.fst x.snd
  left_inv f := funext fun a => by cases a <;> rfl

section subtypeCongr

/--
Definition of `subtypeCongr` / `subtypeCongr` 的定义

English:
definition subtypeCongr
  signature: {α} {p q : α -> Prop} [DecidablePred p] [DecidablePred q]
  body: (sumCompl p).symm.trans ((sumCongr e f).trans (sumCompl q))

中文:
定义 subtypeCongr
  签名: {α} {p q : α -> 命题} [DecidablePred p] [DecidablePred q]
  定义体: (sumCompl p).symm.trans ((sumCongr e f).trans (sumCompl q))

Depends on / 依赖: sumCompl, sumCongr, symm.trans
-/
def subtypeCongr {α} {p q : α -> Prop} [DecidablePred p] [DecidablePred q]
    (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x }) : Perm α :=
  (sumCompl p).symm.trans ((sumCongr e f).trans (sumCompl q))

variable {ε : Type*} {p : ε -> Prop} [DecidablePred p]
variable (ep ep' : Perm { a // p a }) (en en' : Perm { a // ¬p a })

/--
Definition of `Perm.subtypeCongr` / `Perm.subtypeCongr` 的定义

English:
definition Perm.subtypeCongr
  signature: : Equiv.Perm ε
  body: permCongr (sumCompl p) (sumCongr ep en)

中文:
定义 Perm.subtypeCongr
  签名: : Equiv.Perm ε
  定义体: permCongr (sumCompl p) (sumCongr ep en)

Depends on / 依赖: permCongr, sumCompl, sumCongr
-/
def Perm.subtypeCongr : Equiv.Perm ε :=
  permCongr (sumCompl p) (sumCongr ep en)

/--
theorem `Perm.subtypeCongr.apply` / 定理 `Perm.subtypeCongr.apply`

English:
theorem Perm.subtypeCongr.apply
  given: (a : ε)
  statement: ep.subtypeCongr en a =
  proof: by
  by_cases h : p a <;> simp [Perm.subtypeCongr, h]

@[simp]

中文:
定理 Perm.subtypeCongr.apply
  条件: (a : ε)
  结论: ep.subtypeCongr en a =
  证明: by
  by_cases h : p a <;> simp [Perm.subtypeCongr, h]

@[simp]

Depends on / 依赖: Perm.subtypeCongr, subtypeCongr
-/
theorem Perm.subtypeCongr.apply (a : ε) : ep.subtypeCongr en a =
    if h : p a then (ep ⟨a, h⟩ : ε) else en ⟨a, h⟩ := by
  by_cases h : p a <;> simp [Perm.subtypeCongr, h]

@[simp]
/--
theorem `Perm.subtypeCongr.left_apply` / 定理 `Perm.subtypeCongr.left_apply`

English:
theorem Perm.subtypeCongr.left_apply
  given: {a : ε} (h : p a)
  statement: ep.subtypeCongr en a = ep ⟨a, h⟩
  proof: by
  simp [Perm.subtypeCongr.apply, h]

@[simp]

中文:
定理 Perm.subtypeCongr.left_apply
  条件: {a : ε} (h : p a)
  结论: ep.subtypeCongr en a = ep ⟨a, h⟩
  证明: by
  simp [Perm.subtypeCongr.apply, h]

@[simp]

Depends on / 依赖: Perm.subtypeCongr.apply, subtypeCongr
-/
theorem Perm.subtypeCongr.left_apply {a : ε} (h : p a) : ep.subtypeCongr en a = ep ⟨a, h⟩ := by
  simp [Perm.subtypeCongr.apply, h]

@[simp]
/--
theorem `Perm.subtypeCongr.left_apply_subtype` / 定理 `Perm.subtypeCongr.left_apply_subtype`

English:
theorem Perm.subtypeCongr.left_apply_subtype
  given: (a : { a // p a })
  statement: ep.subtypeCongr en a = ep a
  proof: Perm.subtypeCongr.left_apply ep en a.property

@[simp]

中文:
定理 Perm.subtypeCongr.left_apply_subtype
  条件: (a : { a // p a })
  结论: ep.subtypeCongr en a = ep a
  证明: Perm.subtypeCongr.left_apply ep en a.property

@[simp]

Depends on / 依赖: Perm.subtypeCongr.left_apply, a.property, left_apply, property, subtypeCongr
-/
theorem Perm.subtypeCongr.left_apply_subtype (a : { a // p a }) : ep.subtypeCongr en a = ep a :=
    Perm.subtypeCongr.left_apply ep en a.property

@[simp]
/--
theorem `Perm.subtypeCongr.right_apply` / 定理 `Perm.subtypeCongr.right_apply`

English:
theorem Perm.subtypeCongr.right_apply
  given: {a : ε} (h : ¬p a)
  statement: ep.subtypeCongr en a = en ⟨a, h⟩
  proof: by
  simp [Perm.subtypeCongr.apply, h]

@[simp]

中文:
定理 Perm.subtypeCongr.right_apply
  条件: {a : ε} (h : ¬p a)
  结论: ep.subtypeCongr en a = en ⟨a, h⟩
  证明: by
  simp [Perm.subtypeCongr.apply, h]

@[simp]

Depends on / 依赖: Perm.subtypeCongr.apply, subtypeCongr
-/
theorem Perm.subtypeCongr.right_apply {a : ε} (h : ¬p a) : ep.subtypeCongr en a = en ⟨a, h⟩ := by
  simp [Perm.subtypeCongr.apply, h]

@[simp]
/--
theorem `Perm.subtypeCongr.right_apply_subtype` / 定理 `Perm.subtypeCongr.right_apply_subtype`

English:
theorem Perm.subtypeCongr.right_apply_subtype
  given: (a : { a // ¬p a })
  statement: ep.subtypeCongr en a = en a
  proof: Perm.subtypeCongr.right_apply ep en a.property

@[simp]

中文:
定理 Perm.subtypeCongr.right_apply_subtype
  条件: (a : { a // ¬p a })
  结论: ep.subtypeCongr en a = en a
  证明: Perm.subtypeCongr.right_apply ep en a.property

@[simp]

Depends on / 依赖: Perm.subtypeCongr.right_apply, a.property, property, right_apply, subtypeCongr
-/
theorem Perm.subtypeCongr.right_apply_subtype (a : { a // ¬p a }) : ep.subtypeCongr en a = en a :=
  Perm.subtypeCongr.right_apply ep en a.property

@[simp]
/--
theorem `Perm.subtypeCongr.refl` / 定理 `Perm.subtypeCongr.refl`

English:
theorem Perm.subtypeCongr.refl
  proof: by
  ext x
  by_cases h : p x <;> simp [h]

@[simp]

中文:
定理 Perm.subtypeCongr.refl
  证明: by
  ext x
  by_cases h : p x <;> simp [h]

@[simp]
-/
theorem Perm.subtypeCongr.refl :
    Perm.subtypeCongr (Equiv.refl { a // p a }) (Equiv.refl { a // ¬p a }) = Equiv.refl ε := by
  ext x
  by_cases h : p x <;> simp [h]

@[simp]
/--
theorem `Perm.subtypeCongr.symm` / 定理 `Perm.subtypeCongr.symm`

English:
theorem Perm.subtypeCongr.symm
  statement: (ep.subtypeCongr en).symm = Perm.subtypeCongr ep.symm en.symm
  proof: rfl

@[simp]

中文:
定理 Perm.subtypeCongr.symm
  结论: (ep.subtypeCongr en).symm = Perm.subtypeCongr ep.symm en.symm
  证明: rfl

@[simp]
-/
theorem Perm.subtypeCongr.symm : (ep.subtypeCongr en).symm = Perm.subtypeCongr ep.symm en.symm :=
  rfl

@[simp]
/--
theorem `Perm.subtypeCongr.trans` / 定理 `Perm.subtypeCongr.trans`

English:
theorem Perm.subtypeCongr.trans
  proof: by
  grind [eq_def, coe_trans]

中文:
定理 Perm.subtypeCongr.trans
  证明: by
  grind [eq_def, coe_trans]

Depends on / 依赖: coe_trans, eq_def
-/
theorem Perm.subtypeCongr.trans :
    (ep.subtypeCongr en).trans (ep'.subtypeCongr en')
    = Perm.subtypeCongr (ep.trans ep') (en.trans en') := by
  grind [eq_def, coe_trans]

end subtypeCongr

section subtypePreimage

variable (p : α -> Prop) [DecidablePred p] (x₀ : { a // p a } -> β)

/-- For a fixed function `x₀ : {a // p a} → β` defined on a subtype of `α`,
the subtype of functions `x : α → β` that agree with `x₀` on the subtype `{a // p a}`
is naturally equivalent to the type of functions `{a // ¬ p a} → β`. -/
@[simps]
/--
Definition of `subtypePreimage` / `subtypePreimage` 的定义

English:
definition subtypePreimage
  signature: : { x : α -> β // x ∘ Subtype.val = x₀ } ≃ ({ a // ¬p a } -> β) where
  body: (x : α -> β) a
  invFun x := ⟨fun a => if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩, funext fun ⟨_, h⟩ => dif_pos h⟩
  left_inv := fun ⟨x, hx⟩ =>
Subtype.val_injective
      funext fun a => by
        dsimp only
        split_ifs
        · rw [← hx]; rfl
        · rfl
  right_inv x :=
    funext fun ⟨a, 

中文:
定义 subtypePreimage
  签名: : { x : α -> β // x ∘ Subtype.val = x₀ } ≃ ({ a // ¬p a } -> β) where
  定义体: (x : α -> β) a
  invFun x := ⟨fun a => if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩, funext fun ⟨_, h⟩ => dif_pos h⟩
  left_inv := fun ⟨x, hx⟩ =>
Subtype.val_injective
      funext fun a => by
        dsimp only
        split_ifs
        · rw [← hx]; rfl
        · rfl
  right_inv x :=
    funext fun ⟨a, 
-/
def subtypePreimage : { x : α -> β // x ∘ Subtype.val = x₀ } ≃ ({ a // ¬p a } -> β) where
  toFun (x : { x : α -> β // x ∘ Subtype.val = x₀ }) a := (x : α -> β) a
  invFun x := ⟨fun a => if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩, funext fun ⟨_, h⟩ => dif_pos h⟩
  left_inv := fun ⟨x, hx⟩ =>
Subtype.val_injective
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

/--
theorem `subtypePreimage_symm_apply_coe_pos` / 定理 `subtypePreimage_symm_apply_coe_pos`

English:
theorem subtypePreimage_symm_apply_coe_pos
  given: (x : { a // ¬p a } -> β) (a : α) (h : p a)
  proof: dif_pos h

中文:
定理 subtypePreimage_symm_apply_coe_pos
  条件: (x : { a // ¬p a } -> β) (a : α) (h : p a)
  证明: dif_pos h

Depends on / 依赖: dif_pos
-/
theorem subtypePreimage_symm_apply_coe_pos (x : { a // ¬p a } -> β) (a : α) (h : p a) :
    ((subtypePreimage p x₀).symm x : α -> β) a = x₀ ⟨a, h⟩ :=
  dif_pos h

/--
theorem `subtypePreimage_symm_apply_coe_neg` / 定理 `subtypePreimage_symm_apply_coe_neg`

English:
theorem subtypePreimage_symm_apply_coe_neg
  given: (x : { a // ¬p a } -> β) (a : α) (h : ¬p a)
  proof: dif_neg h

中文:
定理 subtypePreimage_symm_apply_coe_neg
  条件: (x : { a // ¬p a } -> β) (a : α) (h : ¬p a)
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
theorem subtypePreimage_symm_apply_coe_neg (x : { a // ¬p a } -> β) (a : α) (h : ¬p a) :
    ((subtypePreimage p x₀).symm x : α -> β) a = x ⟨a, h⟩ :=
  dif_neg h

end subtypePreimage

section

/-- A family of equivalences `∀ a, β₁ a ≃ β₂ a` generates an equivalence between `∀ a, β₁ a` and
`∀ a, β₂ a`. -/
@[simps (attr := grind =)]
/--
Definition of `piCongrRight` / `piCongrRight` 的定义

English:
definition piCongrRight
  signature: {β₁ β₂ : α -> Sort*} (F : forall a, β₁ a ≃ β₂ a)
  body: ⟨Pi.map fun a => F a, Pi.map fun a => (F a).symm, fun H => funext by simp,
fun H => funext by simp⟩

@[simp]

中文:
定义 piCongrRight
  签名: {β₁ β₂ : α -> Sort*} (F : 对任意 a, β₁ a ≃ β₂ a)
  定义体: ⟨Pi.map fun a => F a, Pi.map fun a => (F a).symm, fun H => funext by simp,
fun H => funext by simp⟩

@[simp]

Depends on / 依赖: Or.inl, Or.inr, Pi.map
-/
def piCongrRight {β₁ β₂ : α -> Sort*} (F : forall a, β₁ a ≃ β₂ a) : (forall a, β₁ a) ≃ (forall a, β₂ a) :=
⟨Pi.map fun a => F a, Pi.map fun a => (F a).symm, fun H => funext by simp,
fun H => funext by simp⟩

@[simp]
/--
lemma `piCongrRight_refl` / 引理 `piCongrRight_refl`

English:
lemma piCongrRight_refl
  given: {β : α -> Sort*}
  statement: piCongrRight (fun a => .refl (β a)) = .refl (forall a, β a)
  proof: rfl

中文:
引理 piCongrRight_refl
  条件: {β : α -> Sort*}
  结论: piCongrRight (fun a => .refl (β a)) = .refl (对任意 a, β a)
  证明: rfl

Depends on / 依赖: Or.inr
-/
lemma piCongrRight_refl {β : α -> Sort*} : piCongrRight (fun a => .refl (β a)) = .refl (forall a, β a) :=
  rfl

/-- Given `φ : α → β → Sort*`, we have an equivalence between `∀ a b, φ a b` and `∀ b a, φ a b`.
This is `Function.swap` as an `Equiv`. -/
@[simps apply]
/--
Definition of `piComm` / `piComm` 的定义

English:
definition piComm
  signature: (φ : α -> β -> Sort*)
  body: ⟨swap, swap, fun _ => rfl, fun _ => rfl⟩

@[simp]

中文:
定义 piComm
  签名: (φ : α -> β -> Sort*)
  定义体: ⟨swap, swap, fun _ => rfl, fun _ => rfl⟩

@[simp]
-/
def piComm (φ : α -> β -> Sort*) : (forall a b, φ a b) ≃ forall b a, φ a b :=
  ⟨swap, swap, fun _ => rfl, fun _ => rfl⟩

@[simp]
/--
theorem `piComm_symm` / 定理 `piComm_symm`

English:
theorem piComm_symm
  given: {φ : α -> β -> Sort*}
  statement: (piComm φ).symm = (piComm <| swap φ)
  proof: rfl

中文:
定理 piComm_symm
  条件: {φ : α -> β -> Sort*}
  结论: (piComm φ).symm = (piComm <| swap φ)
  证明: rfl
-/
theorem piComm_symm {φ : α -> β -> Sort*} : (piComm φ).symm = (piComm <| swap φ) :=
  rfl

/--
Definition of `piCurry` / `piCurry` 的定义

English:
definition piCurry
  signature: {α} {β : α -> Type*} (γ : forall a, β a -> Type*)
  body: Sigma.curry
  invFun := Sigma.uncurry
  left_inv := Sigma.uncurry_curry
  right_inv := Sigma.curry_uncurry

中文:
定义 piCurry
  签名: {α} {β : α -> 类型} (γ : 对任意 a, β a -> 类型)
  定义体: Sigma.curry
  invFun := Sigma.uncurry
  left_inv := Sigma.uncurry_curry
  right_inv := Sigma.curry_uncurry

Depends on / 依赖: Sigma.curry
-/
def piCurry {α} {β : α -> Type*} (γ : forall a, β a -> Type*) :
    (forall x : Σ i, β i, γ x.1 x.2) ≃ forall a b, γ a b where
  toFun := Sigma.curry
  invFun := Sigma.uncurry
  left_inv := Sigma.uncurry_curry
  right_inv := Sigma.curry_uncurry

-- `simps` overapplies these but `simps -fullyApplied` under-applies them
/--
theorem `piCurry_apply` / 定理 `piCurry_apply`

English:
theorem piCurry_apply
  statement: {α} {β : α -> Type*} (γ : forall a, β a -> Type*)
  proof: rfl

中文:
定理 piCurry_apply
  结论: {α} {β : α -> 类型} (γ : 对任意 a, β a -> 类型)
  证明: rfl
-/
@[simp] theorem piCurry_apply {α} {β : α -> Type*} (γ : forall a, β a -> Type*)
    (f : forall x : Σ i, β i, γ x.1 x.2) :
    piCurry γ f = Sigma.curry f :=
  rfl

/--
theorem `piCurry_symm_apply` / 定理 `piCurry_symm_apply`

English:
theorem piCurry_symm_apply
  given: {α} {β : α -> Type*} (γ : forall a, β a -> Type*) (f : forall a b, γ a b)
  proof: rfl

中文:
定理 piCurry_symm_apply
  条件: {α} {β : α -> 类型} (γ : 对任意 a, β a -> 类型) (f : 对任意 a b, γ a b)
  证明: rfl
-/
@[simp] theorem piCurry_symm_apply {α} {β : α -> Type*} (γ : forall a, β a -> Type*) (f : forall a b, γ a b) :
    (piCurry γ).symm f = Sigma.uncurry f :=
  rfl

end

section prodCongr

variable {α₁ α₂ β₁ β₂ : Type*} (e : α₁ -> β₁ ≃ β₂)

-- See also `Equiv.ofPreimageEquiv`.
/-- A family of equivalences between fibers gives an equivalence between domains. -/
@[simps!]
/--
Definition of `ofFiberEquiv` / `ofFiberEquiv` 的定义

English:
definition ofFiberEquiv
  signature: {α β γ} {f : α -> γ} {g : β -> γ}
  body: (sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight e).trans (sigmaFiberEquiv g)

中文:
定义 ofFiberEquiv
  签名: {α β γ} {f : α -> γ} {g : β -> γ}
  定义体: (sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight e).trans (sigmaFiberEquiv g)

Depends on / 依赖: Equiv.sigmaCongrRight, sigmaCongrRight, sigmaFiberEquiv, symm.trans
-/
def ofFiberEquiv {α β γ} {f : α -> γ} {g : β -> γ}
    (e : forall c, { a // f a = c } ≃ { b // g b = c }) : α ≃ β :=
(sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight e).trans (sigmaFiberEquiv g)

/--
theorem `ofFiberEquiv_map` / 定理 `ofFiberEquiv_map`

English:
theorem ofFiberEquiv_map
  statement: {α β γ} {f : α -> γ} {g : β -> γ}
  proof: (_ : { b // g b = _ }).property

中文:
定理 ofFiberEquiv_map
  结论: {α β γ} {f : α -> γ} {g : β -> γ}
  证明: (_ : { b // g b = _ }).property

Depends on / 依赖: property
-/
theorem ofFiberEquiv_map {α β γ} {f : α -> γ} {g : β -> γ}
    (e : forall c, { a // f a = c } ≃ { b // g b = c }) (a : α) : g (ofFiberEquiv e a) = f a :=
  (_ : { b // g b = _ }).property

end prodCongr

section

open Sum

/--
Definition of `sigmaNatSucc` / `sigmaNatSucc` 的定义

English:
definition sigmaNatSucc
  signature: (f : Nat -> Type u)
  body: ⟨fun x =>
    @Sigma.casesOn Nat f (fun _ => f 0 oplus Σ n, f (n + 1)) x fun n =>
      @Nat.casesOn (fun i => f i -> f 0 oplus Σ n : Nat, f (n + 1)) n (fun x : f 0 => Sum.inl x)
        fun (n : Nat) (x : f n.succ) => Sum.inr ⟨n, x⟩,
    Sum.elim (Sigma.mk 0) (Sigma.map Nat.succ fun _ => id), by ri

中文:
定义 sigmaNatSucc
  签名: (f : 自然数 -> 类型u)
  定义体: ⟨fun x =>
    @Sigma.casesOn Nat f (fun _ => f 0 oplus Σ n, f (n + 1)) x fun n =>
      @Nat.casesOn (fun i => f i -> f 0 oplus Σ n : Nat, f (n + 1)) n (fun x : f 0 => Sum.inl x)
        fun (n : Nat) (x : f n.succ) => Sum.inr ⟨n, x⟩,
    Sum.elim (Sigma.mk 0) (Sigma.map Nat.succ fun _ => id), by ri

Depends on / 依赖: Nat.casesOn, Nat.succ, Sigma.casesOn, Sigma.map, Sigma.mk, Sum.elim, Sum.inl, Sum.inr, casesOn, n.succ
-/
def sigmaNatSucc (f : Nat -> Type u) : (Σ n, f n) ≃ f 0 oplus Σ n, f (n + 1) :=
  ⟨fun x =>
    @Sigma.casesOn Nat f (fun _ => f 0 oplus Σ n, f (n + 1)) x fun n =>
      @Nat.casesOn (fun i => f i -> f 0 oplus Σ n : Nat, f (n + 1)) n (fun x : f 0 => Sum.inl x)
        fun (n : Nat) (x : f n.succ) => Sum.inr ⟨n, x⟩,
    Sum.elim (Sigma.mk 0) (Sigma.map Nat.succ fun _ => id), by rintro ⟨n | n, x⟩ <;> rfl, by
    rintro (x | ⟨n, x⟩) <;> rfl⟩

end

section

open Sum Nat

/--
Definition of `natEquivNatSumPUnit` / `natEquivNatSumPUnit` 的定义

English:
definition natEquivNatSumPUnit
  signature: : Nat ≃ Nat oplus PUnit where
  body: Nat.casesOn n (inr PUnit.unit) inl
  invFun := Sum.elim Nat.succ fun _ => 0
  left_inv n := by cases n <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

中文:
定义 natEquivNatSumPUnit
  签名: : 自然数 ≃ 自然数 oplus PUnit where
  定义体: Nat.casesOn n (inr PUnit.unit) inl
  invFun := Sum.elim Nat.succ fun _ => 0
  left_inv n := by cases n <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

Depends on / 依赖: Nat.casesOn, PUnit.unit, casesOn
-/
def natEquivNatSumPUnit : Nat ≃ Nat oplus PUnit where
  toFun n := Nat.casesOn n (inr PUnit.unit) inl
  invFun := Sum.elim Nat.succ fun _ => 0
  left_inv n := by cases n <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

/--
Definition of `natSumPUnitEquivNat` / `natSumPUnitEquivNat` 的定义

English:
definition natSumPUnitEquivNat
  signature: : Nat oplus PUnit ≃ Nat
  body: natEquivNatSumPUnit.symm

中文:
定义 natSumPUnitEquivNat
  签名: : 自然数 oplus PUnit ≃ 自然数
  定义体: natEquivNatSumPUnit.symm

Depends on / 依赖: natEquivNatSumPUnit, natEquivNatSumPUnit.symm
-/
def natSumPUnitEquivNat : Nat oplus PUnit ≃ Nat :=
  natEquivNatSumPUnit.symm

/--
Definition of `intEquivNatSumNat` / `intEquivNatSumNat` 的定义

English:
definition intEquivNatSumNat
  signature: : Int ≃ Nat oplus Nat where
  body: Int.casesOn z inl inr
  invFun := Sum.elim Int.ofNat Int.negSucc
  left_inv := by rintro (m | n) <;> rfl
  right_inv := by rintro (m | n) <;> rfl

中文:
定义 intEquivNatSumNat
  签名: : 整数 ≃ 自然数 oplus 自然数 where
  定义体: Int.casesOn z inl inr
  invFun := Sum.elim Int.ofNat Int.negSucc
  left_inv := by rintro (m | n) <;> rfl
  right_inv := by rintro (m | n) <;> rfl

Depends on / 依赖: Int.casesOn, casesOn
-/
def intEquivNatSumNat : Int ≃ Nat oplus Nat where
  toFun z := Int.casesOn z inl inr
  invFun := Sum.elim Int.ofNat Int.negSucc
  left_inv := by rintro (m | n) <;> rfl
  right_inv := by rintro (m | n) <;> rfl

end

/--
Definition of `uniqueCongr` / `uniqueCongr` 的定义

English:
definition uniqueCongr
  signature: (e : α ≃ β)
  body: @Equiv.unique _ _ h e.symm
  invFun h := @Equiv.unique _ _ h e
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 uniqueCongr
  签名: (e : α ≃ β)
  定义体: @Equiv.unique _ _ h e.symm
  invFun h := @Equiv.unique _ _ h e
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

Depends on / 依赖: Equiv.unique, e.symm, unique
-/
def uniqueCongr (e : α ≃ β) : Unique α ≃ Unique β where
  toFun h := @Equiv.unique _ _ h e.symm
  invFun h := @Equiv.unique _ _ h e
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/--
theorem `isEmpty_congr` / 定理 `isEmpty_congr`

English:
theorem isEmpty_congr
  given: (e : α ≃ β)
  statement: IsEmpty α ↔ IsEmpty β
  proof: ⟨fun h => @Function.isEmpty _ _ h e.symm, fun h => @Function.isEmpty _ _ h e⟩

中文:
定理 isEmpty_congr
  条件: (e : α ≃ β)
  结论: IsEmpty α ↔ IsEmpty β
  证明: ⟨fun h => @Function.isEmpty _ _ h e.symm, fun h => @Function.isEmpty _ _ h e⟩

Depends on / 依赖: Function, Function.isEmpty, e.symm, isEmpty
-/
theorem isEmpty_congr (e : α ≃ β) : IsEmpty α ↔ IsEmpty β :=
  ⟨fun h => @Function.isEmpty _ _ h e.symm, fun h => @Function.isEmpty _ _ h e⟩

/--
theorem `isEmpty` / 定理 `isEmpty`

English:
theorem isEmpty
  given: (e : α ≃ β) [IsEmpty β]
  statement: IsEmpty α
  proof: e.isEmpty_congr.mpr ‹_›

中文:
定理 isEmpty
  条件: (e : α ≃ β) [IsEmpty β]
  结论: IsEmpty α
  证明: e.isEmpty_congr.mpr ‹_›
-/
protected theorem isEmpty (e : α ≃ β) [IsEmpty β] : IsEmpty α :=
  e.isEmpty_congr.mpr ‹_›

section

open Subtype

/-- If `α` is equivalent to `β` and the predicates `p : α → Prop` and `q : β → Prop` are equivalent
at corresponding points, then `{a // p a}` is equivalent to `{b // q b}`.
For the statement where `α = β`, that is, `e : perm α`, see `Perm.subtypePerm`. -/
@[simps apply]
/--
Definition of `subtypeEquiv` / `subtypeEquiv` 的定义

English:
definition subtypeEquiv
  signature: {p : α -> Prop} {q : β -> Prop} (e : α ≃ β) (h : forall a, p a ↔ q (e a))
  body: ⟨e a, (h _).mp a.property⟩
  invFun b := ⟨e.symm b, (h _).mpr ((e.apply_symm_apply b).symm ▸ b.property)⟩
left_inv a := Subtype.ext by simp
right_inv b := Subtype.ext by simp

中文:
定义 subtypeEquiv
  签名: {p : α -> 命题} {q : β -> 命题} (e : α ≃ β) (h : 对任意 a, p a ↔ q (e a))
  定义体: ⟨e a, (h _).mp a.property⟩
  invFun b := ⟨e.symm b, (h _).mpr ((e.apply_symm_apply b).symm ▸ b.property)⟩
left_inv a := Subtype.ext by simp
right_inv b := Subtype.ext by simp

Depends on / 依赖: a.property, property
-/
def subtypeEquiv {p : α -> Prop} {q : β -> Prop} (e : α ≃ β) (h : forall a, p a ↔ q (e a)) :
    { a : α // p a } ≃ { b : β // q b } where
  toFun a := ⟨e a, (h _).mp a.property⟩
  invFun b := ⟨e.symm b, (h _).mpr ((e.apply_symm_apply b).symm ▸ b.property)⟩
left_inv a := Subtype.ext by simp
right_inv b := Subtype.ext by simp

/--
lemma `coe_subtypeEquiv_eq_map` / 引理 `coe_subtypeEquiv_eq_map`

English:
lemma coe_subtypeEquiv_eq_map
  statement: {X Y} {p : X -> Prop} {q : Y -> Prop} (e : X ≃ Y)
  proof: rfl

@[simp]

中文:
引理 coe_subtypeEquiv_eq_map
  结论: {X Y} {p : X -> 命题} {q : Y -> 命题} (e : X ≃ Y)
  证明: rfl

@[simp]
-/
lemma coe_subtypeEquiv_eq_map {X Y} {p : X -> Prop} {q : Y -> Prop} (e : X ≃ Y)
    (h : forall x, p x ↔ q (e x)) : ⇑(e.subtypeEquiv h) = Subtype.map e (h · |>.mp) :=
  rfl

@[simp]
/--
theorem `subtypeEquiv_refl` / 定理 `subtypeEquiv_refl`

English:
theorem subtypeEquiv_refl
  given: {p : α -> Prop} (h : forall a, p a ↔ p (Equiv.refl _ a) := fun _ => Iff.rfl)
  proof: by
  ext
  rfl

中文:
定理 subtypeEquiv_refl
  条件: {p : α -> 命题} (h : 对任意 a, p a ↔ p (Equiv.refl _ a) := fun _ => Iff.rfl)
  证明: by
  ext
  rfl

Depends on / 依赖: Iff.rfl
-/
theorem subtypeEquiv_refl {p : α -> Prop} (h : forall a, p a ↔ p (Equiv.refl _ a) := fun _ => Iff.rfl) :
    (Equiv.refl α).subtypeEquiv h = Equiv.refl { a : α // p a } := by
  ext
  rfl

-- We use `as_aux_lemma` here to avoid creating large proof terms when using `simp`
@[simp]
/--
theorem `subtypeEquiv_symm` / 定理 `subtypeEquiv_symm`

English:
theorem subtypeEquiv_symm
  given: {p : α -> Prop} {q : β -> Prop} (e : α ≃ β) (h : forall a : α, p a ↔ q (e a))
  proof: rfl

@[simp]

中文:
定理 subtypeEquiv_symm
  条件: {p : α -> 命题} {q : β -> 命题} (e : α ≃ β) (h : 对任意 a : α, p a ↔ q (e a))
  证明: rfl

@[simp]
-/
theorem subtypeEquiv_symm {p : α -> Prop} {q : β -> Prop} (e : α ≃ β) (h : forall a : α, p a ↔ q (e a)) :
    (e.subtypeEquiv h).symm = e.symm.subtypeEquiv (by as_aux_lemma => grind) :=
  rfl

@[simp]
/--
theorem `subtypeEquiv_trans` / 定理 `subtypeEquiv_trans`

English:
theorem subtypeEquiv_trans
  statement: {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (e : α ≃ β) (f : β ≃ γ)
  proof: rfl

中文:
定理 subtypeEquiv_trans
  结论: {p : α -> 命题} {q : β -> 命题} {r : γ -> 命题} (e : α ≃ β) (f : β ≃ γ)
  证明: rfl
-/
theorem subtypeEquiv_trans {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (e : α ≃ β) (f : β ≃ γ)
    (h : forall a : α, p a ↔ q (e a)) (h' : forall b : β, q b ↔ r (f b)) :
    (e.subtypeEquiv h).trans (f.subtypeEquiv h')
    = (e.trans f).subtypeEquiv (by as_aux_lemma => exact fun a => (h a).trans (h' <| e a)) :=
  rfl

/-- If two predicates `p` and `q` are pointwise equivalent, then `{x // p x}` is equivalent to
`{x // q x}`. -/
@[simps!]
/--
Definition of `subtypeEquivRight` / `subtypeEquivRight` 的定义

English:
definition subtypeEquivRight
  signature: {p q : α -> Prop} (e : forall x, p x ↔ q x)
  body: subtypeEquiv (Equiv.refl _) e

中文:
定义 subtypeEquivRight
  签名: {p q : α -> 命题} (e : 对任意 x, p x ↔ q x)
  定义体: subtypeEquiv (Equiv.refl _) e

Depends on / 依赖: Equiv.refl, subtypeEquiv
-/
def subtypeEquivRight {p q : α -> Prop} (e : forall x, p x ↔ q x) : { x // p x } ≃ { x // q x } :=
  subtypeEquiv (Equiv.refl _) e

/--
lemma `subtypeEquivRight_apply` / 引理 `subtypeEquivRight_apply`

English:
lemma subtypeEquivRight_apply
  statement: {p q : α -> Prop} (e : forall x, p x ↔ q x)
  proof: rfl

中文:
引理 subtypeEquivRight_apply
  结论: {p q : α -> 命题} (e : 对任意 x, p x ↔ q x)
  证明: rfl
-/
lemma subtypeEquivRight_apply {p q : α -> Prop} (e : forall x, p x ↔ q x)
    (z : { x // p x }) : subtypeEquivRight e z = ⟨z, (e z.1).mp z.2⟩ := rfl

/--
lemma `subtypeEquivRight_symm_apply` / 引理 `subtypeEquivRight_symm_apply`

English:
lemma subtypeEquivRight_symm_apply
  statement: {p q : α -> Prop} (e : forall x, p x ↔ q x)
  proof: rfl

中文:
引理 subtypeEquivRight_symm_apply
  结论: {p q : α -> 命题} (e : 对任意 x, p x ↔ q x)
  证明: rfl
-/
lemma subtypeEquivRight_symm_apply {p q : α -> Prop} (e : forall x, p x ↔ q x)
    (z : { x // q x }) : (subtypeEquivRight e).symm z = ⟨z, (e z.1).mpr z.2⟩ := rfl

/--
Definition of `subtypeEquivOfSubtype` / `subtypeEquivOfSubtype` 的定义

English:
definition subtypeEquivOfSubtype
  signature: {p : β -> Prop} (e : α ≃ β)
  body: subtypeEquiv e by simp

中文:
定义 subtypeEquivOfSubtype
  签名: {p : β -> 命题} (e : α ≃ β)
  定义体: subtypeEquiv e by simp

Depends on / 依赖: subtypeEquiv
-/
def subtypeEquivOfSubtype {p : β -> Prop} (e : α ≃ β) : { a : α // p (e a) } ≃ { b : β // p b } :=
subtypeEquiv e by simp

/--
Definition of `subtypeEquivOfSubtype'` / `subtypeEquivOfSubtype'` 的定义

English:
definition subtypeEquivOfSubtype'
  signature: {p : α -> Prop} (e : α ≃ β)
  body: e.symm.subtypeEquivOfSubtype.symm

中文:
定义 subtypeEquivOfSubtype'
  签名: {p : α -> 命题} (e : α ≃ β)
  定义体: e.symm.subtypeEquivOfSubtype.symm

Depends on / 依赖: e.symm.subtypeEquivOfSubtype.symm, subtypeEquivOfSubtype
-/
def subtypeEquivOfSubtype' {p : α -> Prop} (e : α ≃ β) :
    { a : α // p a } ≃ { b : β // p (e.symm b) } :=
  e.symm.subtypeEquivOfSubtype.symm

/--
Definition of `subtypeEquivProp` / `subtypeEquivProp` 的定义

English:
definition subtypeEquivProp
  signature: {p q : α -> Prop} (h : p = q)
  body: subtypeEquiv (Equiv.refl α) fun _ => h ▸ Iff.rfl

中文:
定义 subtypeEquivProp
  签名: {p q : α -> 命题} (h : p = q)
  定义体: subtypeEquiv (Equiv.refl α) fun _ => h ▸ Iff.rfl

Depends on / 依赖: Equiv.refl, Iff.rfl, subtypeEquiv
-/
def subtypeEquivProp {p q : α -> Prop} (h : p = q) : Subtype p ≃ Subtype q :=
  subtypeEquiv (Equiv.refl α) fun _ => h ▸ Iff.rfl

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. This
version allows the “inner” predicate to depend on `h : p a`. -/
@[simps]
/--
Definition of `subtypeSubtypeEquivSubtypeExists` / `subtypeSubtypeEquivSubtypeExists` 的定义

English:
definition subtypeSubtypeEquivSubtypeExists
  signature: (p : α -> Prop) (q : Subtype p -> Prop)
  body: ⟨fun a =>
    ⟨a.1, a.1.2, by
      rcases a with ⟨⟨a, hap⟩, haq⟩
      exact haq⟩,
    fun a => ⟨⟨a, a.2.fst⟩, a.2.snd⟩, fun ⟨⟨_, _⟩, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩

中文:
定义 subtypeSubtypeEquivSubtypeExists
  签名: (p : α -> 命题) (q : Subtype p -> 命题)
  定义体: ⟨fun a =>
    ⟨a.1, a.1.2, by
      rcases a with ⟨⟨a, hap⟩, haq⟩
      exact haq⟩,
    fun a => ⟨⟨a, a.2.fst⟩, a.2.snd⟩, fun ⟨⟨_, _⟩, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩
-/
def subtypeSubtypeEquivSubtypeExists (p : α -> Prop) (q : Subtype p -> Prop) :
    Subtype q ≃ { a : α // exists h : p a, q ⟨a, h⟩ } :=
  ⟨fun a =>
    ⟨a.1, a.1.2, by
      rcases a with ⟨⟨a, hap⟩, haq⟩
      exact haq⟩,
    fun a => ⟨⟨a, a.2.fst⟩, a.2.snd⟩, fun ⟨⟨_, _⟩, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. -/
@[simps!]
/--
Definition of `subtypeSubtypeEquivSubtypeInter` / `subtypeSubtypeEquivSubtypeInter` 的定义

English:
definition subtypeSubtypeEquivSubtypeInter
  signature: {α : Type u} (p q : α -> Prop)
  body: (subtypeSubtypeEquivSubtypeExists p _).trans
    subtypeEquivRight fun x => @exists_prop (q x) (p x)

中文:
定义 subtypeSubtypeEquivSubtypeInter
  签名: {α : 类型u} (p q : α -> 命题)
  定义体: (subtypeSubtypeEquivSubtypeExists p _).trans
    subtypeEquivRight fun x => @exists_prop (q x) (p x)

Depends on / 依赖: exists_prop, subtypeEquivRight, subtypeSubtypeEquivSubtypeExists
-/
def subtypeSubtypeEquivSubtypeInter {α : Type u} (p q : α -> Prop) :
    { x : Subtype p // q x.1 } ≃ Subtype fun x => p x ∧ q x :=
(subtypeSubtypeEquivSubtypeExists p _).trans
    subtypeEquivRight fun x => @exists_prop (q x) (p x)

/-- If the outer subtype has more restrictive predicate than the inner one,
then we can drop the latter. -/
@[simps!]
/--
Definition of `subtypeSubtypeEquivSubtype` / `subtypeSubtypeEquivSubtype` 的定义

English:
definition subtypeSubtypeEquivSubtype
  signature: {α} {p q : α -> Prop} (h : forall {x}, q x -> p x)
  body: (subtypeSubtypeEquivSubtypeInter p _).trans subtypeEquivRight fun _ => and_iff_right_of_imp h

中文:
定义 subtypeSubtypeEquivSubtype
  签名: {α} {p q : α -> 命题} (h : 对任意 {x}, q x -> p x)
  定义体: (subtypeSubtypeEquivSubtypeInter p _).trans subtypeEquivRight fun _ => and_iff_right_of_imp h

Depends on / 依赖: and_iff_right_of_imp, subtypeEquivRight, subtypeSubtypeEquivSubtypeInter
-/
def subtypeSubtypeEquivSubtype {α} {p q : α -> Prop} (h : forall {x}, q x -> p x) :
    { x : Subtype p // q x.1 } ≃ Subtype q :=
(subtypeSubtypeEquivSubtypeInter p _).trans subtypeEquivRight fun _ => and_iff_right_of_imp h

/-- If a proposition holds for all elements, then the subtype is
equivalent to the original type. -/
@[simps apply symm_apply]
/--
Definition of `subtypeUnivEquiv` / `subtypeUnivEquiv` 的定义

English:
definition subtypeUnivEquiv
  signature: {α} {p : α -> Prop} (h : forall x, p x)
  body: ⟨fun x => x, fun x => ⟨x, h x⟩, fun _ => Subtype.ext rfl, fun _ => rfl⟩

中文:
定义 subtypeUnivEquiv
  签名: {α} {p : α -> 命题} (h : 对任意 x, p x)
  定义体: ⟨fun x => x, fun x => ⟨x, h x⟩, fun _ => Subtype.ext rfl, fun _ => rfl⟩

Depends on / 依赖: Subtype, Subtype.ext
-/
def subtypeUnivEquiv {α} {p : α -> Prop} (h : forall x, p x) : Subtype p ≃ α :=
  ⟨fun x => x, fun x => ⟨x, h x⟩, fun _ => Subtype.ext rfl, fun _ => rfl⟩

/--
Definition of `subtypeSigmaEquiv` / `subtypeSigmaEquiv` 的定义

English:
definition subtypeSigmaEquiv
  signature: {α} (p : α -> Type v) (q : α -> Prop)
  body: ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun _ => rfl,
    fun _ => rfl⟩

中文:
定义 subtypeSigmaEquiv
  签名: {α} (p : α -> 类型v) (q : α -> 命题)
  定义体: ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun _ => rfl,
    fun _ => rfl⟩
-/
def subtypeSigmaEquiv {α} (p : α -> Type v) (q : α -> Prop) : { y : Sigma p // q y.1 } ≃ Σ x :
    Subtype q, p x.1 :=
  ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun _ => rfl,
    fun _ => rfl⟩

/--
Definition of `sigmaSubtypeEquivOfSubset` / `sigmaSubtypeEquivOfSubset` 的定义

English:
definition sigmaSubtypeEquivOfSubset
  signature: {α} (p : α -> Type v) (q : α -> Prop) (h : forall x, p x -> q x)
  body: (subtypeSigmaEquiv p q).symm.trans subtypeUnivEquiv fun x => h x.1 x.2

中文:
定义 sigmaSubtypeEquivOfSubset
  签名: {α} (p : α -> 类型v) (q : α -> 命题) (h : 对任意 x, p x -> q x)
  定义体: (subtypeSigmaEquiv p q).symm.trans subtypeUnivEquiv fun x => h x.1 x.2

Depends on / 依赖: subtypeSigmaEquiv, subtypeUnivEquiv, symm.trans
-/
def sigmaSubtypeEquivOfSubset {α} (p : α -> Type v) (q : α -> Prop) (h : forall x, p x -> q x) :
    (Σ x : Subtype q, p x) ≃ Σ x : α, p x :=
(subtypeSigmaEquiv p q).symm.trans subtypeUnivEquiv fun x => h x.1 x.2

/--
Definition of `sigmaSubtypeFiberEquiv` / `sigmaSubtypeFiberEquiv` 的定义

English:
definition sigmaSubtypeFiberEquiv
  signature: {α β : Type*} (f : α -> β) (p : β -> Prop) (h : forall x, p (f x))
  body: calc
    _ ≃ Σ y : β, { x : α // f x = y } := sigmaSubtypeEquivOfSubset _ p fun _ ⟨x, h'⟩ => h' ▸ h x
    _ ≃ α := sigmaFiberEquiv f

中文:
定义 sigmaSubtypeFiberEquiv
  签名: {α β : 类型} (f : α -> β) (p : β -> 命题) (h : 对任意 x, p (f x))
  定义体: calc
    _ ≃ Σ y : β, { x : α // f x = y } := sigmaSubtypeEquivOfSubset _ p fun _ ⟨x, h'⟩ => h' ▸ h x
    _ ≃ α := sigmaFiberEquiv f

Depends on / 依赖: sigmaFiberEquiv, sigmaSubtypeEquivOfSubset
-/
def sigmaSubtypeFiberEquiv {α β : Type*} (f : α -> β) (p : β -> Prop) (h : forall x, p (f x)) :
    (Σ y : Subtype p, { x : α // f x = y }) ≃ α :=
  calc
    _ ≃ Σ y : β, { x : α // f x = y } := sigmaSubtypeEquivOfSubset _ p fun _ ⟨x, h'⟩ => h' ▸ h x
    _ ≃ α := sigmaFiberEquiv f

/--
Definition of `sigmaSubtypeFiberEquivSubtype` / `sigmaSubtypeFiberEquivSubtype` 的定义

English:
definition sigmaSubtypeFiberEquivSubtype
  signature: {α β : Type*} (f : α -> β) {p : α -> Prop} {q : β -> Prop}
  body: calc
    (Σ y : Subtype q, { x : α // f x = y }) ≃ Σ y :
        Subtype q, { x : Subtype p // Subtype.mk (f x) ((h x).1 x.2) = y } := by {
          apply sigmaCongrRight
          intro y
          apply Equiv.symm
          refine (subtypeSubtypeEquivSubtypeExists _ _).trans (subtypeEquivRight ?_

中文:
定义 sigmaSubtypeFiberEquivSubtype
  签名: {α β : 类型} (f : α -> β) {p : α -> 命题} {q : β -> 命题}
  定义体: calc
    (Σ y : Subtype q, { x : α // f x = y }) ≃ Σ y :
        Subtype q, { x : Subtype p // Subtype.mk (f x) ((h x).1 x.2) = y } := by {
          apply sigmaCongrRight
          intro y
          apply Equiv.symm
          refine (subtypeSubtypeEquivSubtypeExists _ _).trans (subtypeEquivRight ?_

Depends on / 依赖: Equiv.symm, Subtype, Subtype.ext, Subtype.mk, Subtype.val, congr_arg, property, sigmaCongrRight, sigmaFiberEquiv, subtypeEquivRight, subtypeSubtypeEquivSubtypeExists, x.property
-/
def sigmaSubtypeFiberEquivSubtype {α β : Type*} (f : α -> β) {p : α -> Prop} {q : β -> Prop}
    (h : forall x, p x ↔ q (f x)) : (Σ y : Subtype q, { x : α // f x = y }) ≃ Subtype p :=
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

/--
Definition of `sigmaOptionEquivOfSome` / `sigmaOptionEquivOfSome` 的定义

English:
definition sigmaOptionEquivOfSome
  signature: {α} (p : Option α -> Type v) (h : p none -> False)
  body: haveI h' : forall x, p x -> x.isSome := by
    intro x
    cases x
    · intro n
      exfalso
      exact h n
    · intro _
      exact rfl
  (sigmaSubtypeEquivOfSubset _ _ h').symm.trans (sigmaCongrLeft' (optionIsSomeEquiv α))

中文:
定义 sigmaOptionEquivOfSome
  签名: {α} (p : Option α -> 类型v) (h : p none -> False)
  定义体: haveI h' : forall x, p x -> x.isSome := by
    intro x
    cases x
    · intro n
      exfalso
      exact h n
    · intro _
      exact rfl
  (sigmaSubtypeEquivOfSubset _ _ h').symm.trans (sigmaCongrLeft' (optionIsSomeEquiv α))

Depends on / 依赖: isSome, optionIsSomeEquiv, sigmaCongrLeft, sigmaSubtypeEquivOfSubset, symm.trans, x.isSome
-/
def sigmaOptionEquivOfSome {α} (p : Option α -> Type v) (h : p none -> False) :
    (Σ x : Option α, p x) ≃ Σ x : α, p (some x) :=
  haveI h' : forall x, p x -> x.isSome := by
    intro x
    cases x
    · intro n
      exfalso
      exact h n
    · intro _
      exact rfl
  (sigmaSubtypeEquivOfSubset _ _ h').symm.trans (sigmaCongrLeft' (optionIsSomeEquiv α))

/--
Definition of `piEquivSubtypeSigma` / `piEquivSubtypeSigma` 的定义

English:
definition piEquivSubtypeSigma
  signature: (ι) (π : ι -> Type*)
  body: fun f => ⟨fun i => ⟨i, f i⟩, fun _ => rfl⟩
  invFun := fun f i => by rw [← f.2 i]; exact (f.1 i).2
  right_inv := fun ⟨f, hf⟩ =>
Subtype.ext funext fun i =>
Sigma.eq (hf i).symm eq_of_heq rec_heq_of_heq _ by simp

中文:
定义 piEquivSubtypeSigma
  签名: (ι) (π : ι -> 类型)
  定义体: fun f => ⟨fun i => ⟨i, f i⟩, fun _ => rfl⟩
  invFun := fun f i => by rw [← f.2 i]; exact (f.1 i).2
  right_inv := fun ⟨f, hf⟩ =>
Subtype.ext funext fun i =>
Sigma.eq (hf i).symm eq_of_heq rec_heq_of_heq _ by simp
-/
def piEquivSubtypeSigma (ι) (π : ι -> Type*) :
    (forall i, π i) ≃ { f : ι -> Σ i, π i // forall i, (f i).1 = i } where
  toFun := fun f => ⟨fun i => ⟨i, f i⟩, fun _ => rfl⟩
  invFun := fun f i => by rw [← f.2 i]; exact (f.1 i).2
  right_inv := fun ⟨f, hf⟩ =>
Subtype.ext funext fun i =>
Sigma.eq (hf i).symm eq_of_heq rec_heq_of_heq _ by simp

/--
Definition of `subtypePiEquivPi` / `subtypePiEquivPi` 的定义

English:
definition subtypePiEquivPi
  signature: {β : α -> Sort v} {p : forall a, β a -> Prop}
  body: fun f a => ⟨f.1 a, f.2 a⟩
  invFun := fun f => ⟨fun a => (f a).1, fun a => (f a).2⟩
  left_inv := by
    rintro ⟨f, h⟩
    rfl
  right_inv := by
    rintro f
    funext a
    exact Subtype.ext rfl

中文:
定义 subtypePiEquivPi
  签名: {β : α -> Sort v} {p : 对任意 a, β a -> 命题}
  定义体: fun f a => ⟨f.1 a, f.2 a⟩
  invFun := fun f => ⟨fun a => (f a).1, fun a => (f a).2⟩
  left_inv := by
    rintro ⟨f, h⟩
    rfl
  right_inv := by
    rintro f
    funext a
    exact Subtype.ext rfl
-/
def subtypePiEquivPi {β : α -> Sort v} {p : forall a, β a -> Prop} :
    { f : forall a, β a // forall a, p a (f a) } ≃ forall a, { b : β a // p a b } where
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
/--
Definition of `sigmaAssocProd` / `sigmaAssocProd` 的定义

English:
definition sigmaAssocProd
  signature: {α β : Type*} {γ : α -> β -> Type*}
  body: .trans sigmaAssoc γ sigmaCongrLeft' (sigmaEquivProd _ _).symm

中文:
定义 sigmaAssocProd
  签名: {α β : 类型} {γ : α -> β -> 类型}
  定义体: .trans sigmaAssoc γ sigmaCongrLeft' (sigmaEquivProd _ _).symm

Depends on / 依赖: sigmaAssoc, sigmaCongrLeft, sigmaEquivProd
-/
def sigmaAssocProd {α β : Type*} {γ : α -> β -> Type*} :
    (ab : α × β) × γ ab.1 ab.2 ≃ (a : α) × (b : β) × γ a b :=
.trans sigmaAssoc γ sigmaCongrLeft' (sigmaEquivProd _ _).symm

/-- A subtype of a sigma which pins down the base of the sigma is equivalent to
the respective fiber. -/
@[simps]
/--
Definition of `sigmaSubtype` / `sigmaSubtype` 的定义

English:
definition sigmaSubtype
  signature: {α : Type*} {β : α -> Type*} (a : α)
  body: fun ⟨⟨_, b⟩, h⟩ => h ▸ b
  invFun b := ⟨⟨a, b⟩, rfl⟩
  left_inv := fun ⟨a, h⟩ => by cases h; simp
  right_inv b := by simp

中文:
定义 sigmaSubtype
  签名: {α : 类型} {β : α -> 类型} (a : α)
  定义体: fun ⟨⟨_, b⟩, h⟩ => h ▸ b
  invFun b := ⟨⟨a, b⟩, rfl⟩
  left_inv := fun ⟨a, h⟩ => by cases h; simp
  right_inv b := by simp

Depends on / 依赖: bernoulli
-/
def sigmaSubtype {α : Type*} {β : α -> Type*} (a : α) :
    {s : Sigma β // s.1 = a} ≃ β a where
  toFun := fun ⟨⟨_, b⟩, h⟩ => h ▸ b
  invFun b := ⟨⟨a, b⟩, rfl⟩
  left_inv := fun ⟨a, h⟩ => by cases h; simp
  right_inv b := by simp


section
attribute [local simp] Trans.trans sigmaAssoc subtypeSigmaEquiv uniqueSigma eqRec_eq_cast

set_option backward.isDefEq.respectTransparency.types false in
/-- A subtype of a dependent triple which pins down both bases is equivalent to the
respective fiber. -/
@[simps! +simpRhs apply]
/--
Definition of `sigmaSigmaSubtype` / `sigmaSigmaSubtype` 的定义

English:
definition sigmaSigmaSubtype
  signature: {α : Type*} {β : α -> Type*} {γ : (a : α) -> β a -> Type*}
  body: calc {s : (a : α) × (b : β a) × γ a b // p ⟨s.1, s.2.1⟩}
  _ ≃ _ := subtypeEquiv (p := fun ⟨a, b, c⟩ => p ⟨a, b⟩) (q := (p ·.1))
    (sigmaAssoc γ).symm fun s => by simp [sigmaAssoc]
  _ ≃ _ := subtypeSigmaEquiv _ _
  _ ≃ _ := uniqueSigma (fun ab => γ (Sigma.fst <| Subtype.val ab) (Sigma.snd <| Subt

中文:
定义 sigmaSigmaSubtype
  签名: {α : 类型} {β : α -> 类型} {γ : (a : α) -> β a -> 类型}
  定义体: calc {s : (a : α) × (b : β a) × γ a b // p ⟨s.1, s.2.1⟩}
  _ ≃ _ := subtypeEquiv (p := fun ⟨a, b, c⟩ => p ⟨a, b⟩) (q := (p ·.1))
    (sigmaAssoc γ).symm fun s => by simp [sigmaAssoc]
  _ ≃ _ := subtypeSigmaEquiv _ _
  _ ≃ _ := uniqueSigma (fun ab => γ (Sigma.fst <| Subtype.val ab) (Sigma.snd <| Subt

Depends on / 依赖: Equiv.cast, Fin.sum_univ_eq_sum_range, Sigma.fst, Sigma.snd, Subtype, Subtype.val, _def, bernoulli, sigmaAssoc, subtypeEquiv, subtypeSigmaEquiv, sum_univ_eq_sum_range, uniq.default, uniq.uniq, uniqueSigma
-/
def sigmaSigmaSubtype {α : Type*} {β : α -> Type*} {γ : (a : α) -> β a -> Type*}
    (p : (a : α) × β a -> Prop) [uniq : Unique {ab // p ab}] {a : α} {b : β a} (h : p ⟨a, b⟩) :
    {s : (a : α) × (b : β a) × γ a b // p ⟨s.1, s.2.1⟩} ≃ γ a b :=
  calc {s : (a : α) × (b : β a) × γ a b // p ⟨s.1, s.2.1⟩}
  _ ≃ _ := subtypeEquiv (p := fun ⟨a, b, c⟩ => p ⟨a, b⟩) (q := (p ·.1))
    (sigmaAssoc γ).symm fun s => by simp [sigmaAssoc]
  _ ≃ _ := subtypeSigmaEquiv _ _
  _ ≃ _ := uniqueSigma (fun ab => γ (Sigma.fst <| Subtype.val ab) (Sigma.snd <| Subtype.val ab))
_ ≃ γ a b := Equiv.cast by rw [← show ⟨⟨a, b⟩, h⟩ = uniq.default from uniq.uniq _]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `sigmaSigmaSubtype_symm_apply` / 引理 `sigmaSigmaSubtype_symm_apply`

English:
lemma sigmaSigmaSubtype_symm_apply
  statement: {α : Type*} {β : α -> Type*} {γ : (a : α) -> β a -> Type*}
  proof: by
  rw [Equiv.symm_apply_eq]; simp

中文:
引理 sigmaSigmaSubtype_symm_apply
  结论: {α : 类型} {β : α -> 类型} {γ : (a : α) -> β a -> 类型}
  证明: by
  rw [Equiv.symm_apply_eq]; simp

Depends on / 依赖: Equiv.symm_apply_eq, Finset, Finset.sum_eq_zero, _def, bernoulli, cast_one, choose_symm, choose_zero_right, div_one, le_of_lt, mem_range, neg_eq_zero, one_mul, sub_add, sub_eq_zero, sub_self, sub_sub_cancel_left, sum_eq_zero, sum_range_succ_comm, sum_sub_distrib
-/
lemma sigmaSigmaSubtype_symm_apply {α : Type*} {β : α -> Type*} {γ : (a : α) -> β a -> Type*}
    (p : (a : α) × β a -> Prop) [uniq : Unique {ab // p ab}]
    {a : α} {b : β a} (c : γ a b) (h : p ⟨a, b⟩) :
    (sigmaSigmaSubtype p h).symm c = ⟨⟨a, ⟨b, c⟩⟩, h⟩ := by
  rw [Equiv.symm_apply_eq]; simp

/--
Definition of `sigmaSigmaSubtypeEq` / `sigmaSigmaSubtypeEq` 的定义

English:
definition sigmaSigmaSubtypeEq
  signature: {α β : Type*} {γ : α -> β -> Type*} (a : α) (b : β)
  body: have : Unique (@Subtype ((_ : α) × β) (fun ⟨a', b'⟩ => a' = a ∧ b' = b)) := {
    default := ⟨⟨a, b⟩, ⟨rfl, rfl⟩⟩
    uniq := by rintro ⟨⟨a', b'⟩, ⟨rfl, rfl⟩⟩; rfl }
  sigmaSigmaSubtype (fun ⟨a', b'⟩ => a' = a ∧ b' = b) ⟨rfl, rfl⟩

中文:
定义 sigmaSigmaSubtypeEq
  签名: {α β : 类型} {γ : α -> β -> 类型} (a : α) (b : β)
  定义体: have : Unique (@Subtype ((_ : α) × β) (fun ⟨a', b'⟩ => a' = a ∧ b' = b)) := {
    default := ⟨⟨a, b⟩, ⟨rfl, rfl⟩⟩
    uniq := by rintro ⟨⟨a', b'⟩, ⟨rfl, rfl⟩⟩; rfl }
  sigmaSigmaSubtype (fun ⟨a', b'⟩ => a' = a ∧ b' = b) ⟨rfl, rfl⟩

Depends on / 依赖: Subtype, Unique, _spec, add_tsub_cancel_of_le, bernoulli, cast_sub, mem_range_succ_iff, mem_range_succ_iff.mp, sigmaSigmaSubtype, sum_antidiagonal_eq_sum_range_succ_mk, sum_congr
-/
def sigmaSigmaSubtypeEq {α β : Type*} {γ : α -> β -> Type*} (a : α) (b : β) :
    {s : (a : α) × (b : β) × γ a b // s.1 = a ∧ s.2.1 = b} ≃ γ a b :=
  have : Unique (@Subtype ((_ : α) × β) (fun ⟨a', b'⟩ => a' = a ∧ b' = b)) := {
    default := ⟨⟨a, b⟩, ⟨rfl, rfl⟩⟩
    uniq := by rintro ⟨⟨a', b'⟩, ⟨rfl, rfl⟩⟩; rfl }
  sigmaSigmaSubtype (fun ⟨a', b'⟩ => a' = a ∧ b' = b) ⟨rfl, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `sigmaSigmaSubtypeEq_apply` / 引理 `sigmaSigmaSubtypeEq_apply`

English:
lemma sigmaSigmaSubtypeEq_apply
  statement: {α β : Type*} {γ : α -> β -> Type*} {a : α} {b : β}
  proof: by
  simp [sigmaSigmaSubtypeEq]

@[simp]

中文:
引理 sigmaSigmaSubtypeEq_apply
  结论: {α β : 类型} {γ : α -> β -> 类型} {a : α} {b : β}
  证明: by
  simp [sigmaSigmaSubtypeEq]

@[simp]

Depends on / 依赖: _def, bernoulli, sigmaSigmaSubtypeEq
-/
lemma sigmaSigmaSubtypeEq_apply {α β : Type*} {γ : α -> β -> Type*} {a : α} {b : β}
    (s : {s : (a : α) × (b : β) × γ a b // s.1 = a ∧ s.2.1 = b}) :
    sigmaSigmaSubtypeEq a b s = cast (congrArg₂ γ s.2.1 s.2.2) s.1.2.2 := by
  simp [sigmaSigmaSubtypeEq]

@[simp]
/--
lemma `sigmaSigmaSubtypeEq_symm_apply` / 引理 `sigmaSigmaSubtypeEq_symm_apply`

English:
lemma sigmaSigmaSubtypeEq_symm_apply
  given: {α β : Type*} {γ : α -> β -> Type*} {a : α} {b : β} (c : γ a b)
  proof: by
  simp [sigmaSigmaSubtypeEq]

中文:
引理 sigmaSigmaSubtypeEq_symm_apply
  条件: {α β : 类型} {γ : α -> β -> 类型} {a : α} {b : β} (c : γ a b)
  证明: by
  simp [sigmaSigmaSubtypeEq]

Depends on / 依赖: _def, bernoulli, sigmaSigmaSubtypeEq
-/
lemma sigmaSigmaSubtypeEq_symm_apply {α β : Type*} {γ : α -> β -> Type*} {a : α} {b : β} (c : γ a b) :
    (sigmaSigmaSubtypeEq a b).symm c = ⟨⟨a, ⟨b, c⟩⟩, ⟨rfl, rfl⟩⟩ := by
  simp [sigmaSigmaSubtypeEq]

end

end

section subtypeEquivCodomain

variable {X Y : Sort*} [DecidableEq X] {x : X}

/--
Definition of `subtypeEquivCodomain` / `subtypeEquivCodomain` 的定义

English:
definition subtypeEquivCodomain
  signature: (f : { x' // x' != x } -> Y)
  body: (subtypePreimage _ f).trans
@funUnique { x' // ¬x' != x } _
      show Unique { x' // ¬x' != x } from
        @Equiv.unique _ _
          (show Unique { x' // x' = x } from {
            default := ⟨x, rfl⟩, uniq := fun ⟨_, h⟩ => Subtype.val_injective h })
          (subtypeEquivRight fun _ => not_n

中文:
定义 subtypeEquivCodomain
  签名: (f : { x' // x' != x } -> Y)
  定义体: (subtypePreimage _ f).trans
@funUnique { x' // ¬x' != x } _
      show Unique { x' // ¬x' != x } from
        @Equiv.unique _ _
          (show Unique { x' // x' = x } from {
            default := ⟨x, rfl⟩, uniq := fun ⟨_, h⟩ => Subtype.val_injective h })
          (subtypeEquivRight fun _ => not_n

Depends on / 依赖: Equiv.unique, Subtype, Subtype.val_injective, Unique, _def, bernoulli, funUnique, not_not, subtypeEquivRight, subtypePreimage, sum_range_succ, sum_range_zero, unique, val_injective
-/
def subtypeEquivCodomain (f : { x' // x' != x } -> Y) :
    { g : X -> Y // g ∘ (↑) = f } ≃ Y :=
(subtypePreimage _ f).trans
@funUnique { x' // ¬x' != x } _
      show Unique { x' // ¬x' != x } from
        @Equiv.unique _ _
          (show Unique { x' // x' = x } from {
            default := ⟨x, rfl⟩, uniq := fun ⟨_, h⟩ => Subtype.val_injective h })
          (subtypeEquivRight fun _ => not_not)

@[simp]
/--
theorem `coe_subtypeEquivCodomain` / 定理 `coe_subtypeEquivCodomain`

English:
theorem coe_subtypeEquivCodomain
  given: (f : { x' // x' != x } -> Y)
  proof: rfl

@[simp]

中文:
定理 coe_subtypeEquivCodomain
  条件: (f : { x' // x' != x } -> Y)
  证明: rfl

@[simp]

Depends on / 依赖: _def, bernoulli, sum_range_succ, sum_range_zero
-/
theorem coe_subtypeEquivCodomain (f : { x' // x' != x } -> Y) :
    (subtypeEquivCodomain f : _ -> Y) =
      fun g : { g : X -> Y // g ∘ (↑) = f } => (g : X -> Y) x :=
  rfl

@[simp]
/--
theorem `subtypeEquivCodomain_apply` / 定理 `subtypeEquivCodomain_apply`

English:
theorem subtypeEquivCodomain_apply
  given: (f : { x' // x' != x } -> Y) (g)
  proof: rfl

中文:
定理 subtypeEquivCodomain_apply
  条件: (f : { x' // x' != x } -> Y) (g)
  证明: rfl

Depends on / 依赖: Nat.choose, _def, bernoulli, sum_range_succ, sum_range_zero
-/
theorem subtypeEquivCodomain_apply (f : { x' // x' != x } -> Y) (g) :
    subtypeEquivCodomain f g = (g : X -> Y) x :=
  rfl

/--
theorem `coe_subtypeEquivCodomain_symm` / 定理 `coe_subtypeEquivCodomain_symm`

English:
theorem coe_subtypeEquivCodomain_symm
  given: (f : { x' // x' != x } -> Y)
  proof: rfl

@[simp]

中文:
定理 coe_subtypeEquivCodomain_symm
  条件: (f : { x' // x' != x } -> Y)
  证明: rfl

@[simp]
-/
theorem coe_subtypeEquivCodomain_symm (f : { x' // x' != x } -> Y) :
    ((subtypeEquivCodomain f).symm : Y -> _) = fun y =>
      ⟨fun x' => if h : x' != x then f ⟨x', h⟩ else y, by grind⟩ :=
  rfl

@[simp]
/--
theorem `subtypeEquivCodomain_symm_apply` / 定理 `subtypeEquivCodomain_symm_apply`

English:
theorem subtypeEquivCodomain_symm_apply
  given: (f : { x' // x' != x } -> Y) (y : Y) (x' : X)
  proof: rfl

中文:
定理 subtypeEquivCodomain_symm_apply
  条件: (f : { x' // x' != x } -> Y) (y : Y) (x' : X)
  证明: rfl

Depends on / 依赖: algebraMap, bernoulli
-/
theorem subtypeEquivCodomain_symm_apply (f : { x' // x' != x } -> Y) (y : Y) (x' : X) :
    ((subtypeEquivCodomain f).symm y : X -> Y) x' = if h : x' != x then f ⟨x', h⟩ else y :=
  rfl

/--
theorem `subtypeEquivCodomain_symm_apply_eq` / 定理 `subtypeEquivCodomain_symm_apply_eq`

English:
theorem subtypeEquivCodomain_symm_apply_eq
  given: (f : { x' // x' != x } -> Y) (y : Y)
  proof: dif_neg (not_not.mpr rfl)

中文:
定理 subtypeEquivCodomain_symm_apply_eq
  条件: (f : { x' // x' != x } -> Y) (y : Y)
  证明: dif_neg (not_not.mpr rfl)

Depends on / 依赖: dif_neg, not_not, not_not.mpr
-/
theorem subtypeEquivCodomain_symm_apply_eq (f : { x' // x' != x } -> Y) (y : Y) :
    ((subtypeEquivCodomain f).symm y : X -> Y) x = y :=
  dif_neg (not_not.mpr rfl)

/--
theorem `subtypeEquivCodomain_symm_apply_ne` / 定理 `subtypeEquivCodomain_symm_apply_ne`

English:
theorem subtypeEquivCodomain_symm_apply_ne
  proof: dif_pos h

中文:
定理 subtypeEquivCodomain_symm_apply_ne
  证明: dif_pos h

Depends on / 依赖: Nat.factorial, PowerSeries, PowerSeries.ext_iff, PowerSeries_mul_exp_sub_one, bernoulli, coeff_X, dif_pos, eq_zero_of_neg_eq, evalNegHom, ext_iff, factorial, factorial_ne_zero, h_odd, h_odd.neg_one_pow, mul_eq_mul_right_iff, mul_eq_mul_right_iff.mp, neg_one_pow, specialize, split_ifs
-/
theorem subtypeEquivCodomain_symm_apply_ne
    (f : { x' // x' != x } -> Y) (y : Y) (x' : X) (h : x' != x) :
    ((subtypeEquivCodomain f).symm y : X -> Y) x' = f ⟨x', h⟩ :=
  dif_pos h

end subtypeEquivCodomain

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift (α -> β) (α ≃ β) (↑) Bijective
  body: ⟨ofBijective f hf, rfl⟩

中文:
实例 :
  签名: CanLift (α -> β) (α ≃ β) (↑) Bijective
  定义体: ⟨ofBijective f hf, rfl⟩

Depends on / 依赖: ofBijective
-/
instance : CanLift (α -> β) (α ≃ β) (↑) Bijective where prf f hf := ⟨ofBijective f hf, rfl⟩

section

variable {α' β' : Type*} (e : Perm α') {p : β' -> Prop} [DecidablePred p] (f : α' ≃ Subtype p)

/--
Definition of `Perm.extendDomain` / `Perm.extendDomain` 的定义

English:
definition Perm.extendDomain
  signature: : Perm β'
  body: (permCongr f e).subtypeCongr (Equiv.refl _)

@[simp]

中文:
定义 Perm.extendDomain
  签名: : Perm β'
  定义体: (permCongr f e).subtypeCongr (Equiv.refl _)

@[simp]

Depends on / 依赖: Equiv.refl, bernoulli, mul_assoc, mul_comm, permCongr, pow_mul, subtypeCongr
-/
def Perm.extendDomain : Perm β' :=
  (permCongr f e).subtypeCongr (Equiv.refl _)

@[simp]
/--
theorem `Perm.extendDomain_apply_image` / 定理 `Perm.extendDomain_apply_image`

English:
theorem Perm.extendDomain_apply_image
  given: (a : α')
  statement: e.extendDomain f (f a) = f (e a)
  proof: by
  simp [Perm.extendDomain]

中文:
定理 Perm.extendDomain_apply_image
  条件: (a : α')
  结论: e.extendDomain f (f a) = f (e a)
  证明: by
  simp [Perm.extendDomain]

Depends on / 依赖: Perm.extendDomain, extendDomain
-/
theorem Perm.extendDomain_apply_image (a : α') : e.extendDomain f (f a) = f (e a) := by
  simp [Perm.extendDomain]

/--
theorem `Perm.extendDomain_apply_subtype` / 定理 `Perm.extendDomain_apply_subtype`

English:
theorem Perm.extendDomain_apply_subtype
  given: {b : β'} (h : p b)
  proof: by
  simp [Perm.extendDomain, h]

中文:
定理 Perm.extendDomain_apply_subtype
  条件: {b : β'} (h : p b)
  证明: by
  simp [Perm.extendDomain, h]

Depends on / 依赖: Perm.extendDomain, extendDomain
-/
theorem Perm.extendDomain_apply_subtype {b : β'} (h : p b) :
    e.extendDomain f b = f (e (f.symm ⟨b, h⟩)) := by
  simp [Perm.extendDomain, h]

/--
theorem `Perm.extendDomain_apply_not_subtype` / 定理 `Perm.extendDomain_apply_not_subtype`

English:
theorem Perm.extendDomain_apply_not_subtype
  given: {b : β'} (h : ¬p b)
  statement: e.extendDomain f b = b
  proof: by
  simp [Perm.extendDomain, h]

@[simp]

中文:
定理 Perm.extendDomain_apply_not_subtype
  条件: {b : β'} (h : ¬p b)
  结论: e.extendDomain f b = b
  证明: by
  simp [Perm.extendDomain, h]

@[simp]

Depends on / 依赖: Perm.extendDomain, extendDomain
-/
theorem Perm.extendDomain_apply_not_subtype {b : β'} (h : ¬p b) : e.extendDomain f b = b := by
  simp [Perm.extendDomain, h]

@[simp]
/--
theorem `Perm.extendDomain_refl` / 定理 `Perm.extendDomain_refl`

English:
theorem Perm.extendDomain_refl
  statement: Perm.extendDomain (Equiv.refl _) f = Equiv.refl _
  proof: by
  simp [Perm.extendDomain]

@[simp]

中文:
定理 Perm.extendDomain_refl
  结论: Perm.extendDomain (Equiv.refl _) f = Equiv.refl _
  证明: by
  simp [Perm.extendDomain]

@[simp]

Depends on / 依赖: Perm.extendDomain, extendDomain
-/
theorem Perm.extendDomain_refl : Perm.extendDomain (Equiv.refl _) f = Equiv.refl _ := by
  simp [Perm.extendDomain]

@[simp]
/--
theorem `Perm.extendDomain_symm` / 定理 `Perm.extendDomain_symm`

English:
theorem Perm.extendDomain_symm
  statement: (e.extendDomain f).symm = Perm.extendDomain e.symm f
  proof: rfl

中文:
定理 Perm.extendDomain_symm
  结论: (e.extendDomain f).symm = Perm.extendDomain e.symm f
  证明: rfl
-/
theorem Perm.extendDomain_symm : (e.extendDomain f).symm = Perm.extendDomain e.symm f :=
  rfl

/--
theorem `Perm.extendDomain_trans` / 定理 `Perm.extendDomain_trans`

English:
theorem Perm.extendDomain_trans
  given: (e e' : Perm α')
  proof: by
  simp [Perm.extendDomain, permCongr_trans]

中文:
定理 Perm.extendDomain_trans
  条件: (e e' : Perm α')
  证明: by
  simp [Perm.extendDomain, permCongr_trans]

Depends on / 依赖: Perm.extendDomain, extendDomain, permCongr_trans
-/
theorem Perm.extendDomain_trans (e e' : Perm α') :
    (e.extendDomain f).trans (e'.extendDomain f) = Perm.extendDomain (e.trans e') f := by
  simp [Perm.extendDomain, permCongr_trans]

end

/--
Definition of `subtypeQuotientEquivQuotientSubtype` / `subtypeQuotientEquivQuotientSubtype` 的定义

English:
definition subtypeQuotientEquivQuotientSubtype
  signature: (p₁ : α -> Prop) {s₁ : Setoid α} {s₂ : Setoid (Subtype p₁)}
  body: Quotient.hrecOn a.1 (fun a h => ⟦⟨a, (hp₂ _).2 h⟩⟧)
      (fun a b hab => hfunext (by rw [Quotient.sound hab]) fun _ _ _ =>
        heq_of_eq (Quotient.sound ((h _ _).2 hab)))
      a.2
  invFun a :=
    Quotient.liftOn a (fun a => (⟨⟦a.1⟧, (hp₂ _).1 a.2⟩ : { x // p₂ x })) fun _ _ hab =>
      Subty

中文:
定义 subtypeQuotientEquivQuotientSubtype
  签名: (p₁ : α -> 命题) {s₁ : Setoid α} {s₂ : Setoid (Subtype p₁)}
  定义体: Quotient.hrecOn a.1 (fun a h => ⟦⟨a, (hp₂ _).2 h⟩⟧)
      (fun a b hab => hfunext (by rw [Quotient.sound hab]) fun _ _ _ =>
        heq_of_eq (Quotient.sound ((h _ _).2 hab)))
      a.2
  invFun a :=
    Quotient.liftOn a (fun a => (⟨⟦a.1⟧, (hp₂ _).1 a.2⟩ : { x // p₂ x })) fun _ _ hab =>
      Subty

Depends on / 依赖: Quotient, Quotient.hrecOn, Quotient.inductionOn, Quotient.liftOn, Quotient.sound, Subtype, Subtype.ext, heq_of_eq, hfunext, hrecOn, inductionOn, invFun, left_inv, liftOn, right_inv
-/
def subtypeQuotientEquivQuotientSubtype (p₁ : α -> Prop) {s₁ : Setoid α} {s₂ : Setoid (Subtype p₁)}
    (p₂ : Quotient s₁ -> Prop) (hp₂ : forall a, p₁ a ↔ p₂ ⟦a⟧)
    (h : forall x y : Subtype p₁, s₂.r x y ↔ s₁.r x y) : {x // p₂ x} ≃ Quotient s₂ where
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
/--
theorem `subtypeQuotientEquivQuotientSubtype_mk` / 定理 `subtypeQuotientEquivQuotientSubtype_mk`

English:
theorem subtypeQuotientEquivQuotientSubtype_mk
  statement: (p₁ : α -> Prop)
  proof: rfl

@[simp]

中文:
定理 subtypeQuotientEquivQuotientSubtype_mk
  结论: (p₁ : α -> 命题)
  证明: rfl

@[simp]
-/
theorem subtypeQuotientEquivQuotientSubtype_mk (p₁ : α -> Prop)
    [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)] (p₂ : Quotient s₁ -> Prop) (hp₂ : forall a, p₁ a ↔ p₂ ⟦a⟧)
    (h : forall x y : Subtype p₁, s₂ x y ↔ (x : α) ≈ y)
    (x hx) : subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h ⟨⟦x⟧, hx⟩ = ⟦⟨x, (hp₂ _).2 hx⟩⟧ :=
  rfl

@[simp]
/--
theorem `subtypeQuotientEquivQuotientSubtype_symm_mk` / 定理 `subtypeQuotientEquivQuotientSubtype_symm_mk`

English:
theorem subtypeQuotientEquivQuotientSubtype_symm_mk
  statement: (p₁ : α -> Prop)
  proof: rfl

中文:
定理 subtypeQuotientEquivQuotientSubtype_symm_mk
  结论: (p₁ : α -> 命题)
  证明: rfl
-/
theorem subtypeQuotientEquivQuotientSubtype_symm_mk (p₁ : α -> Prop)
    [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)] (p₂ : Quotient s₁ -> Prop) (hp₂ : forall a, p₁ a ↔ p₂ ⟦a⟧)
    (h : forall x y : Subtype p₁, s₂ x y ↔ (x : α) ≈ y) (x) :
    (subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h).symm ⟦x⟧ = ⟨⟦x⟧, (hp₂ _).1 x.property⟩ :=
  rfl

section Swap

variable [DecidableEq α]

/--
Definition of `swapCore` / `swapCore` 的定义

English:
definition swapCore
  signature: (a b r : α)
  body: if r = a then b else if r = b then a else r

中文:
定义 swapCore
  签名: (a b r : α)
  定义体: if r = a then b else if r = b then a else r
-/
def swapCore (a b r : α) : α :=
  if r = a then b else if r = b then a else r

/--
theorem `swapCore_self` / 定理 `swapCore_self`

English:
theorem swapCore_self
  given: (r a : α)
  statement: swapCore a a r = r
  proof: by
  unfold swapCore
  split_ifs <;> simp [*]

中文:
定理 swapCore_self
  条件: (r a : α)
  结论: swapCore a a r = r
  证明: by
  unfold swapCore
  split_ifs <;> simp [*]

Depends on / 依赖: split_ifs, swapCore
-/
theorem swapCore_self (r a : α) : swapCore a a r = r := by
  unfold swapCore
  split_ifs <;> simp [*]

/--
theorem `swapCore_swapCore` / 定理 `swapCore_swapCore`

English:
theorem swapCore_swapCore
  given: (r a b : α)
  statement: swapCore a b (swapCore a b r) = r
  proof: by
  unfold swapCore; split_ifs <;> grind

中文:
定理 swapCore_swapCore
  条件: (r a b : α)
  结论: swapCore a b (swapCore a b r) = r
  证明: by
  unfold swapCore; split_ifs <;> grind

Depends on / 依赖: split_ifs, swapCore
-/
theorem swapCore_swapCore (r a b : α) : swapCore a b (swapCore a b r) = r := by
  unfold swapCore; split_ifs <;> grind

/--
theorem `swapCore_comm` / 定理 `swapCore_comm`

English:
theorem swapCore_comm
  given: (r a b : α)
  statement: swapCore a b r = swapCore b a r
  proof: by
  unfold swapCore; split_ifs <;> grind

中文:
定理 swapCore_comm
  条件: (r a b : α)
  结论: swapCore a b r = swapCore b a r
  证明: by
  unfold swapCore; split_ifs <;> grind

Depends on / 依赖: split_ifs, swapCore
-/
theorem swapCore_comm (r a b : α) : swapCore a b r = swapCore b a r := by
  unfold swapCore; split_ifs <;> grind

/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: (a b : α)
  body: ⟨swapCore a b, swapCore a b, fun r => swapCore_swapCore r a b,
    fun r => swapCore_swapCore r a b⟩

@[simp]

中文:
定义 swap
  签名: (a b : α)
  定义体: ⟨swapCore a b, swapCore a b, fun r => swapCore_swapCore r a b,
    fun r => swapCore_swapCore r a b⟩

@[simp]

Depends on / 依赖: swapCore, swapCore_swapCore
-/
def swap (a b : α) : Perm α :=
  ⟨swapCore a b, swapCore a b, fun r => swapCore_swapCore r a b,
    fun r => swapCore_swapCore r a b⟩

@[simp]
/--
theorem `swap_self` / 定理 `swap_self`

English:
theorem swap_self
  given: (a : α)
  statement: swap a a = Equiv.refl _
  proof: ext fun r => swapCore_self r a

中文:
定理 swap_self
  条件: (a : α)
  结论: swap a a = Equiv.refl _
  证明: ext fun r => swapCore_self r a

Depends on / 依赖: swapCore_self
-/
theorem swap_self (a : α) : swap a a = Equiv.refl _ :=
  ext fun r => swapCore_self r a

/--
theorem `swap_comm` / 定理 `swap_comm`

English:
theorem swap_comm
  given: (a b : α)
  statement: swap a b = swap b a
  proof: ext fun r => swapCore_comm r _ _

@[aesop simp, grind =]

中文:
定理 swap_comm
  条件: (a b : α)
  结论: swap a b = swap b a
  证明: ext fun r => swapCore_comm r _ _

@[aesop simp, grind =]

Depends on / 依赖: swapCore_comm
-/
theorem swap_comm (a b : α) : swap a b = swap b a :=
  ext fun r => swapCore_comm r _ _

@[aesop simp, grind =]
/--
theorem `swap_apply_def` / 定理 `swap_apply_def`

English:
theorem swap_apply_def
  given: (a b x : α)
  statement: swap a b x = if x = a then b else if x = b then a else x
  proof: rfl

@[simp]

中文:
定理 swap_apply_def
  条件: (a b x : α)
  结论: swap a b x = if x = a then b else if x = b then a else x
  证明: rfl

@[simp]
-/
theorem swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b then a else x :=
  rfl

@[simp]
/--
theorem `swap_apply_left` / 定理 `swap_apply_left`

English:
theorem swap_apply_left
  given: (a b : α)
  statement: swap a b a = b
  proof: if_pos rfl

@[simp]

中文:
定理 swap_apply_left
  条件: (a b : α)
  结论: swap a b a = b
  证明: if_pos rfl

@[simp]

Depends on / 依赖: if_pos
-/
theorem swap_apply_left (a b : α) : swap a b a = b :=
  if_pos rfl

@[simp]
/--
theorem `swap_apply_right` / 定理 `swap_apply_right`

English:
theorem swap_apply_right
  given: (a b : α)
  statement: swap a b b = a
  proof: by
  grind

中文:
定理 swap_apply_right
  条件: (a b : α)
  结论: swap a b b = a
  证明: by
  grind
-/
theorem swap_apply_right (a b : α) : swap a b b = a := by
  grind

/--
theorem `swap_apply_of_ne_of_ne` / 定理 `swap_apply_of_ne_of_ne`

English:
theorem swap_apply_of_ne_of_ne
  given: {a b x : α}
  statement: x != a -> x != b -> swap a b x = x
  proof: by
  grind

中文:
定理 swap_apply_of_ne_of_ne
  条件: {a b x : α}
  结论: x != a -> x != b -> swap a b x = x
  证明: by
  grind
-/
theorem swap_apply_of_ne_of_ne {a b x : α} : x != a -> x != b -> swap a b x = x := by
  grind

/--
theorem `eq_or_eq_of_swap_apply_ne_self` / 定理 `eq_or_eq_of_swap_apply_ne_self`

English:
theorem eq_or_eq_of_swap_apply_ne_self
  given: {a b x : α} (h : swap a b x != x)
  statement: x = a ∨ x = b
  proof: by
  contrapose! h
  exact swap_apply_of_ne_of_ne h.1 h.2

@[simp]

中文:
定理 eq_or_eq_of_swap_apply_ne_self
  条件: {a b x : α} (h : swap a b x != x)
  结论: x = a ∨ x = b
  证明: by
  contrapose! h
  exact swap_apply_of_ne_of_ne h.1 h.2

@[simp]

Depends on / 依赖: contrapose, swap_apply_of_ne_of_ne
-/
theorem eq_or_eq_of_swap_apply_ne_self {a b x : α} (h : swap a b x != x) : x = a ∨ x = b := by
  contrapose! h
  exact swap_apply_of_ne_of_ne h.1 h.2

@[simp]
/--
theorem `swap_swap` / 定理 `swap_swap`

English:
theorem swap_swap
  given: (a b : α)
  statement: (swap a b).trans (swap a b) = Equiv.refl _
  proof: ext fun _ => swapCore_swapCore _ _ _

@[simp]

中文:
定理 swap_swap
  条件: (a b : α)
  结论: (swap a b).trans (swap a b) = Equiv.refl _
  证明: ext fun _ => swapCore_swapCore _ _ _

@[simp]

Depends on / 依赖: swapCore_swapCore
-/
theorem swap_swap (a b : α) : (swap a b).trans (swap a b) = Equiv.refl _ :=
  ext fun _ => swapCore_swapCore _ _ _

@[simp]
/--
theorem `symm_swap` / 定理 `symm_swap`

English:
theorem symm_swap
  given: (a b : α)
  statement: (swap a b).symm = swap a b
  proof: rfl

@[simp]

中文:
定理 symm_swap
  条件: (a b : α)
  结论: (swap a b).symm = swap a b
  证明: rfl

@[simp]
-/
theorem symm_swap (a b : α) : (swap a b).symm = swap a b :=
  rfl

@[simp]
/--
theorem `swap_eq_refl_iff` / 定理 `swap_eq_refl_iff`

English:
theorem swap_eq_refl_iff
  given: {x y : α}
  statement: swap x y = Equiv.refl _ ↔ x = y
  proof: ⟨fun h => (Equiv.refl _).injective (by grind), by grind⟩

中文:
定理 swap_eq_refl_iff
  条件: {x y : α}
  结论: swap x y = Equiv.refl _ ↔ x = y
  证明: ⟨fun h => (Equiv.refl _).injective (by grind), by grind⟩

Depends on / 依赖: Equiv.refl, injective
-/
theorem swap_eq_refl_iff {x y : α} : swap x y = Equiv.refl _ ↔ x = y :=
  ⟨fun h => (Equiv.refl _).injective (by grind), by grind⟩

/--
theorem `swap_comp_apply` / 定理 `swap_comp_apply`

English:
theorem swap_comp_apply
  given: {a b x : α} (π : Perm α)
  proof: by
  cases π
  rfl

中文:
定理 swap_comp_apply
  条件: {a b x : α} (π : Perm α)
  证明: by
  cases π
  rfl
-/
theorem swap_comp_apply {a b x : α} (π : Perm α) :
    π.trans (swap a b) x = if π x = a then b else if π x = b then a else π x := by
  cases π
  rfl

/--
theorem `swap_eq_update` / 定理 `swap_eq_update`

English:
theorem swap_eq_update
  given: (i j : α)
  statement: (Equiv.swap i j : α -> α) = update (update id j i) i j
  proof: by
  grind

中文:
定理 swap_eq_update
  条件: (i j : α)
  结论: (Equiv.swap i j : α -> α) = update (update id j i) i j
  证明: by
  grind
-/
theorem swap_eq_update (i j : α) : (Equiv.swap i j : α -> α) = update (update id j i) i j := by
  grind

/--
theorem `comp_swap_eq_update` / 定理 `comp_swap_eq_update`

English:
theorem comp_swap_eq_update
  given: (i j : α) (f : α -> β)
  proof: by
  grind

@[simp]

中文:
定理 comp_swap_eq_update
  条件: (i j : α) (f : α -> β)
  证明: by
  grind

@[simp]
-/
theorem comp_swap_eq_update (i j : α) (f : α -> β) :
    f ∘ Equiv.swap i j = update (update f j (f i)) i (f j) := by
  grind

@[simp]
/--
theorem `symm_trans_swap_trans` / 定理 `symm_trans_swap_trans`

English:
theorem symm_trans_swap_trans
  given: [DecidableEq β] (a b : α) (e : α ≃ β)
  proof: by
  grind

@[simp]

中文:
定理 symm_trans_swap_trans
  条件: [DecidableEq β] (a b : α) (e : α ≃ β)
  证明: by
  grind

@[simp]
-/
theorem symm_trans_swap_trans [DecidableEq β] (a b : α) (e : α ≃ β) :
    (e.symm.trans (swap a b)).trans e = swap (e a) (e b) := by
  grind

@[simp]
/--
theorem `trans_swap_trans_symm` / 定理 `trans_swap_trans_symm`

English:
theorem trans_swap_trans_symm
  given: [DecidableEq β] (a b : β) (e : α ≃ β)
  proof: symm_trans_swap_trans a b e.symm

@[simp]

中文:
定理 trans_swap_trans_symm
  条件: [DecidableEq β] (a b : β) (e : α ≃ β)
  证明: symm_trans_swap_trans a b e.symm

@[simp]

Depends on / 依赖: e.symm, symm_trans_swap_trans
-/
theorem trans_swap_trans_symm [DecidableEq β] (a b : β) (e : α ≃ β) :
    (e.trans (swap a b)).trans e.symm = swap (e.symm a) (e.symm b) :=
  symm_trans_swap_trans a b e.symm

@[simp]
/--
theorem `swap_apply_self` / 定理 `swap_apply_self`

English:
theorem swap_apply_self
  given: (i j a : α)
  statement: swap i j (swap i j a) = a
  proof: by
  grind

中文:
定理 swap_apply_self
  条件: (i j a : α)
  结论: swap i j (swap i j a) = a
  证明: by
  grind
-/
theorem swap_apply_self (i j a : α) : swap i j (swap i j a) = a := by
  grind

/--
theorem `apply_swap_eq_self` / 定理 `apply_swap_eq_self`

English:
theorem apply_swap_eq_self
  given: {v : α -> β} {i j : α} (hv : v i = v j) (k : α)
  proof: by
  grind

中文:
定理 apply_swap_eq_self
  条件: {v : α -> β} {i j : α} (hv : v i = v j) (k : α)
  证明: by
  grind
-/
theorem apply_swap_eq_self {v : α -> β} {i j : α} (hv : v i = v j) (k : α) :
    v (swap i j k) = v k := by
  grind

/--
theorem `swap_apply_eq_iff` / 定理 `swap_apply_eq_iff`

English:
theorem swap_apply_eq_iff
  given: {x y z w : α}
  statement: swap x y z = w ↔ z = swap x y w
  proof: by
  grind

中文:
定理 swap_apply_eq_iff
  条件: {x y z w : α}
  结论: swap x y z = w ↔ z = swap x y w
  证明: by
  grind
-/
theorem swap_apply_eq_iff {x y z w : α} : swap x y z = w ↔ z = swap x y w := by
  grind

/--
theorem `swap_apply_ne_self_iff` / 定理 `swap_apply_ne_self_iff`

English:
theorem swap_apply_ne_self_iff
  given: {a b x : α}
  statement: swap a b x != x ↔ a != b ∧ (x = a ∨ x = b)
  proof: by
  grind

中文:
定理 swap_apply_ne_self_iff
  条件: {a b x : α}
  结论: swap a b x != x ↔ a != b ∧ (x = a ∨ x = b)
  证明: by
  grind
-/
theorem swap_apply_ne_self_iff {a b x : α} : swap a b x != x ↔ a != b ∧ (x = a ∨ x = b) := by
  grind

/--
theorem `swap_injective_of_left` / 定理 `swap_injective_of_left`

English:
theorem swap_injective_of_left
  given: (a : α)
  proof: fun c d h => by
  simp only at h
  rw [← Equiv.swap_apply_left a c]; rw [h]; rw [Equiv.swap_apply_left]

中文:
定理 swap_injective_of_left
  条件: (a : α)
  证明: fun c d h => by
  simp only at h
  rw [← Equiv.swap_apply_left a c]; rw [h]; rw [Equiv.swap_apply_left]

Depends on / 依赖: Equiv.swap_apply_left, swap_apply_left
-/
theorem swap_injective_of_left (a : α) :
    Function.Injective (fun x => Equiv.swap a x) := fun c d h => by
  simp only at h
  rw [← Equiv.swap_apply_left a c]; rw [h]; rw [Equiv.swap_apply_left]

/--
theorem `swap_injective_of_right` / 定理 `swap_injective_of_right`

English:
theorem swap_injective_of_right
  given: (a : α)
  proof: by
  simp_rw [swap_comm _ a]
  exact swap_injective_of_left a

中文:
定理 swap_injective_of_right
  条件: (a : α)
  证明: by
  simp_rw [swap_comm _ a]
  exact swap_injective_of_left a

Depends on / 依赖: simp_rw, swap_comm, swap_injective_of_left
-/
theorem swap_injective_of_right (a : α) :
    Function.Injective (fun x => Equiv.swap x a) := by
  simp_rw [swap_comm _ a]
  exact swap_injective_of_left a

instance (α : Type*) [Nontrivial α] : Nontrivial (Equiv.Perm α) := by
  classical
  obtain ⟨a : α⟩ := Nontrivial.to_nonempty (α := α)
  exact Function.Injective.nontrivial (Equiv.swap_injective_of_left a)

/--
lemma `image_swap_of_mem_of_notMem` / 引理 `image_swap_of_mem_of_notMem`

English:
lemma image_swap_of_mem_of_notMem
  statement: {α : Type*} [DecidableEq α] {s : Set α} {i j : α}
  proof: Set.ext fun a => by
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain rfl | ne := eq_or_ne a i
      · rw [swap_apply_left]; exact ⟨.inl rfl, (ne_of_mem_of_not_mem hi hj).symm⟩
      · rw [swap_apply_of_ne_of_ne ne (ne_of_mem_of_not_mem ha hj)]; exact ⟨.inr ha, ne⟩
    · rintro ⟨rfl | has, hai⟩

中文:
引理 image_swap_of_mem_of_notMem
  结论: {α : 类型} [DecidableEq α] {s : Set α} {i j : α}
  证明: Set.ext fun a => by
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain rfl | ne := eq_or_ne a i
      · rw [swap_apply_left]; exact ⟨.inl rfl, (ne_of_mem_of_not_mem hi hj).symm⟩
      · rw [swap_apply_of_ne_of_ne ne (ne_of_mem_of_not_mem ha hj)]; exact ⟨.inr ha, ne⟩
    · rintro ⟨rfl | has, hai⟩

Depends on / 依赖: Set.ext, eq_or_ne, ne_of_mem_of_not_mem, swap_apply_left, swap_apply_of_ne_of_ne
-/
lemma image_swap_of_mem_of_notMem {α : Type*} [DecidableEq α] {s : Set α} {i j : α}
    (hi : i in s) (hj : j ∉ s) : s.image (swap i j) = insert j s \ {i} :=
  Set.ext fun a => by
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
/--
theorem `sumCongr_swap_refl` / 定理 `sumCongr_swap_refl`

English:
theorem sumCongr_swap_refl
  given: {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : α)
  proof: by
  aesop

@[simp]

中文:
定理 sumCongr_swap_refl
  条件: {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : α)
  证明: by
  aesop

@[simp]
-/
theorem sumCongr_swap_refl {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : α) :
    Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.refl β) = Equiv.swap (Sum.inl i) (Sum.inl j) := by
  aesop

@[simp]
/--
theorem `sumCongr_refl_swap` / 定理 `sumCongr_refl_swap`

English:
theorem sumCongr_refl_swap
  given: {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : β)
  proof: by
  aesop

中文:
定理 sumCongr_refl_swap
  条件: {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : β)
  证明: by
  aesop
-/
theorem sumCongr_refl_swap {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : β) :
    Equiv.Perm.sumCongr (Equiv.refl α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) := by
  aesop

end Perm

/--
Definition of `setValue` / `setValue` 的定义

English:
definition setValue
  signature: (f : α ≃ β) (a : α) (b : β)
  body: (swap a (f.symm b)).trans f

@[simp]

中文:
定义 setValue
  签名: (f : α ≃ β) (a : α) (b : β)
  定义体: (swap a (f.symm b)).trans f

@[simp]

Depends on / 依赖: f.symm
-/
def setValue (f : α ≃ β) (a : α) (b : β) : α ≃ β :=
  (swap a (f.symm b)).trans f

@[simp]
/--
theorem `setValue_eq` / 定理 `setValue_eq`

English:
theorem setValue_eq
  given: (f : α ≃ β) (a : α) (b : β)
  statement: setValue f a b a = b
  proof: by
  simp [setValue, swap_apply_left]

中文:
定理 setValue_eq
  条件: (f : α ≃ β) (a : α) (b : β)
  结论: setValue f a b a = b
  证明: by
  simp [setValue, swap_apply_left]

Depends on / 依赖: setValue, swap_apply_left
-/
theorem setValue_eq (f : α ≃ β) (a : α) (b : β) : setValue f a b a = b := by
  simp [setValue, swap_apply_left]

end Swap

end Equiv

namespace Function.Involutive

/--
Definition of `toPerm` / `toPerm` 的定义

English:
definition toPerm
  signature: (f : α -> α) (h : Involutive f)
  body: ⟨f, f, h.leftInverse, h.rightInverse⟩

@[simp]

中文:
定义 toPerm
  签名: (f : α -> α) (h : Involutive f)
  定义体: ⟨f, f, h.leftInverse, h.rightInverse⟩

@[simp]

Depends on / 依赖: h.leftInverse, h.rightInverse, leftInverse, rightInverse
-/
def toPerm (f : α -> α) (h : Involutive f) : Equiv.Perm α :=
  ⟨f, f, h.leftInverse, h.rightInverse⟩

@[simp]
/--
theorem `coe_toPerm` / 定理 `coe_toPerm`

English:
theorem coe_toPerm
  given: {f : α -> α} (h : Involutive f)
  statement: (h.toPerm f : α -> α) = f
  proof: rfl

@[simp]

中文:
定理 coe_toPerm
  条件: {f : α -> α} (h : Involutive f)
  结论: (h.toPerm f : α -> α) = f
  证明: rfl

@[simp]
-/
theorem coe_toPerm {f : α -> α} (h : Involutive f) : (h.toPerm f : α -> α) = f :=
  rfl

@[simp]
/--
theorem `toPerm_symm` / 定理 `toPerm_symm`

English:
theorem toPerm_symm
  given: {f : α -> α} (h : Involutive f)
  statement: (h.toPerm f).symm = h.toPerm f
  proof: rfl

中文:
定理 toPerm_symm
  条件: {f : α -> α} (h : Involutive f)
  结论: (h.toPerm f).symm = h.toPerm f
  证明: rfl
-/
theorem toPerm_symm {f : α -> α} (h : Involutive f) : (h.toPerm f).symm = h.toPerm f :=
  rfl

/--
theorem `toPerm_involutive` / 定理 `toPerm_involutive`

English:
theorem toPerm_involutive
  given: {f : α -> α} (h : Involutive f)
  statement: Involutive (h.toPerm f)
  proof: h

中文:
定理 toPerm_involutive
  条件: {f : α -> α} (h : Involutive f)
  结论: Involutive (h.toPerm f)
  证明: h
-/
theorem toPerm_involutive {f : α -> α} (h : Involutive f) : Involutive (h.toPerm f) :=
  h

/--
theorem `symm_eq_self_of_involutive` / 定理 `symm_eq_self_of_involutive`

English:
theorem symm_eq_self_of_involutive
  given: (f : Equiv.Perm α) (h : Involutive f)
  statement: f.symm = f
  proof: DFunLike.coe_injective (h.leftInverse_iff.mp f.left_inv)

中文:
定理 symm_eq_self_of_involutive
  条件: (f : Equiv.Perm α) (h : Involutive f)
  结论: f.symm = f
  证明: DFunLike.coe_injective (h.leftInverse_iff.mp f.left_inv)

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, f.left_inv, h.leftInverse_iff.mp, leftInverse_iff, left_inv
-/
theorem symm_eq_self_of_involutive (f : Equiv.Perm α) (h : Involutive f) : f.symm = f :=
  DFunLike.coe_injective (h.leftInverse_iff.mp f.left_inv)

end Function.Involutive

/--
theorem `PLift.eq_up_iff_down_eq` / 定理 `PLift.eq_up_iff_down_eq`

English:
theorem PLift.eq_up_iff_down_eq
  given: {x : PLift α} {y : α}
  statement: x = PLift.up y ↔ x.down = y
  proof: Equiv.plift.eq_symm_apply

中文:
定理 PLift.eq_up_iff_down_eq
  条件: {x : PLift α} {y : α}
  结论: x = PLift.up y ↔ x.down = y
  证明: Equiv.plift.eq_symm_apply

Depends on / 依赖: Equiv.plift.eq_symm_apply, eq_symm_apply
-/
theorem PLift.eq_up_iff_down_eq {x : PLift α} {y : α} : x = PLift.up y ↔ x.down = y :=
  Equiv.plift.eq_symm_apply

/--
theorem `Function.Injective.map_swap` / 定理 `Function.Injective.map_swap`

English:
theorem Function.Injective.map_swap
  statement: [DecidableEq α] [DecidableEq β] {f : α -> β}
  proof: by
  grind

中文:
定理 Function.Injective.map_swap
  结论: [DecidableEq α] [DecidableEq β] {f : α -> β}
  证明: by
  grind
-/
theorem Function.Injective.map_swap [DecidableEq α] [DecidableEq β] {f : α -> β}
    (hf : Function.Injective f) (x y z : α) :
    f (Equiv.swap x y z) = Equiv.swap (f x) (f y) (f z) := by
  grind

namespace Equiv

section

/-- Transport dependent functions through an equivalence of the base space.
-/
@[simps apply, simps -isSimp symm_apply]
/--
Definition of `piCongrLeft'` / `piCongrLeft'` 的定义

English:
definition piCongrLeft'
  signature: (P : α -> Sort*) (e : α ≃ β)
  body: f (e.symm x)
  invFun f x := (e.symm_apply_apply x).ndrec (f (e x))
  left_inv f := by grind
  right_inv f := by grind

中文:
定义 piCongrLeft'
  签名: (P : α -> Sort*) (e : α ≃ β)
  定义体: f (e.symm x)
  invFun f x := (e.symm_apply_apply x).ndrec (f (e x))
  left_inv f := by grind
  right_inv f := by grind

Depends on / 依赖: e.symm
-/
def piCongrLeft' (P : α -> Sort*) (e : α ≃ β) : (forall a, P a) ≃ forall b, P (e.symm b) where
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
/--
theorem `piCongrLeft'_symm` / 定理 `piCongrLeft'_symm`

English:
theorem piCongrLeft'_symm
  given: (P : Sort*) (e : α ≃ β)
  proof: by ext; simp [piCongrLeft']

中文:
定理 piCongrLeft'_symm
  条件: (P : Sort*) (e : α ≃ β)
  证明: by ext; simp [piCongrLeft']
-/
theorem piCongrLeft'_symm (P : Sort*) (e : α ≃ β) :
    (piCongrLeft' (fun _ => P) e).symm = piCongrLeft' _ e.symm := by ext; simp [piCongrLeft']

/-- Note: the "obvious" statement `(piCongrLeft' P e).symm g a = g (e a)` doesn't typecheck: the
LHS would have type `P a` while the RHS would have type `P (e.symm (e a))`. This lemma is a way
around it in the case where `a` is of the form `e.symm b`, so we can use `g b` instead of
`g (e (e.symm b))`. -/
@[simp]
/--
lemma `piCongrLeft'_symm_apply_apply` / 引理 `piCongrLeft'_symm_apply_apply`

English:
lemma piCongrLeft'_symm_apply_apply
  given: (P : α -> Sort*) (e : α ≃ β) (g : forall b, P (e.symm b)) (b : β)
  proof: by
  rw [piCongrLeft'_symm_apply]; rw [← heq_iff_eq]; rw [eqRec_heq_iff]
  exact congr_arg_heq _ (e.apply_symm_apply _)

@[simp]

中文:
引理 piCongrLeft'_symm_apply_apply
  条件: (P : α -> Sort*) (e : α ≃ β) (g : 对任意 b, P (e.symm b)) (b : β)
  证明: by
  rw [piCongrLeft'_symm_apply]; rw [← heq_iff_eq]; rw [eqRec_heq_iff]
  exact congr_arg_heq _ (e.apply_symm_apply _)

@[simp]
-/
lemma piCongrLeft'_symm_apply_apply (P : α -> Sort*) (e : α ≃ β) (g : forall b, P (e.symm b)) (b : β) :
    (piCongrLeft' P e).symm g (e.symm b) = g b := by
  rw [piCongrLeft'_symm_apply]; rw [← heq_iff_eq]; rw [eqRec_heq_iff]
  exact congr_arg_heq _ (e.apply_symm_apply _)

@[simp]
/--
lemma `piCongrLeft'_refl` / 引理 `piCongrLeft'_refl`

English:
lemma piCongrLeft'_refl
  given: (P : α -> Sort*)
  statement: piCongrLeft' P (.refl α) = .refl (forall a, P a)
  proof: rfl

中文:
引理 piCongrLeft'_refl
  条件: (P : α -> Sort*)
  结论: piCongrLeft' P (.refl α) = .refl (对任意 a, P a)
  证明: rfl
-/
lemma piCongrLeft'_refl (P : α -> Sort*) : piCongrLeft' P (.refl α) = .refl (forall a, P a) := rfl

end

section

variable (P : β -> Sort w) (e : α ≃ β)

/--
Definition of `piCongrLeft` / `piCongrLeft` 的定义

English:
definition piCongrLeft
  signature: : (forall a, P (e a)) ≃ forall b, P b
  body: (piCongrLeft' P e.symm).symm

中文:
定义 piCongrLeft
  签名: : (对任意 a, P (e a)) ≃ 对任意 b, P b
  定义体: (piCongrLeft' P e.symm).symm

Depends on / 依赖: e.symm, piCongrLeft
-/
def piCongrLeft : (forall a, P (e a)) ≃ forall b, P b :=
  (piCongrLeft' P e.symm).symm

/--
lemma `piCongrLeft_apply` / 引理 `piCongrLeft_apply`

English:
lemma piCongrLeft_apply
  given: (f : forall a, P (e a)) (b : β)
  proof: rfl

@[simp, grind =]

中文:
引理 piCongrLeft_apply
  条件: (f : 对任意 a, P (e a)) (b : β)
  证明: rfl

@[simp, grind =]
-/
lemma piCongrLeft_apply (f : forall a, P (e a)) (b : β) :
    (piCongrLeft P e) f b = e.apply_symm_apply b ▸ f (e.symm b) :=
  rfl

@[simp, grind =]
/--
lemma `piCongrLeft_symm_apply` / 引理 `piCongrLeft_symm_apply`

English:
lemma piCongrLeft_symm_apply
  given: (g : forall b, P b) (a : α)
  proof: piCongrLeft'_apply P e.symm g a

@[simp]

中文:
引理 piCongrLeft_symm_apply
  条件: (g : 对任意 b, P b) (a : α)
  证明: piCongrLeft'_apply P e.symm g a

@[simp]

Depends on / 依赖: _apply, e.symm, piCongrLeft
-/
lemma piCongrLeft_symm_apply (g : forall b, P b) (a : α) :
    (piCongrLeft P e).symm g a = g (e a) :=
  piCongrLeft'_apply P e.symm g a

@[simp]
/--
lemma `piCongrLeft_refl` / 引理 `piCongrLeft_refl`

English:
lemma piCongrLeft_refl
  given: (P : α -> Sort*)
  statement: piCongrLeft P (.refl α) = .refl (forall a, P a)
  proof: rfl

中文:
引理 piCongrLeft_refl
  条件: (P : α -> Sort*)
  结论: piCongrLeft P (.refl α) = .refl (对任意 a, P a)
  证明: rfl
-/
lemma piCongrLeft_refl (P : α -> Sort*) : piCongrLeft P (.refl α) = .refl (forall a, P a) :=
  rfl

/-- Note: the "obvious" statement `(piCongrLeft P e) f b = f (e.symm b)` doesn't typecheck: the
LHS would have type `P b` while the RHS would have type `P (e (e.symm b))`. This lemma is a way
around it in the case where `b` is of the form `e a`, so we can use `f a` instead of
`f (e.symm (e a))`. -/
@[simp, grind =]
/--
lemma `piCongrLeft_apply_apply` / 引理 `piCongrLeft_apply_apply`

English:
lemma piCongrLeft_apply_apply
  given: (f : forall a, P (e a)) (a : α)
  proof: piCongrLeft'_symm_apply_apply P e.symm f a

中文:
引理 piCongrLeft_apply_apply
  条件: (f : 对任意 a, P (e a)) (a : α)
  证明: piCongrLeft'_symm_apply_apply P e.symm f a

Depends on / 依赖: _symm_apply_apply, e.symm, piCongrLeft
-/
lemma piCongrLeft_apply_apply (f : forall a, P (e a)) (a : α) :
    (piCongrLeft P e) f (e a) = f a :=
  piCongrLeft'_symm_apply_apply P e.symm f a

open Sum

/--
lemma `piCongrLeft_apply_eq_cast` / 引理 `piCongrLeft_apply_eq_cast`

English:
lemma piCongrLeft_apply_eq_cast
  statement: {P : β -> Sort v} {e : α ≃ β}
  proof: eqRec_eq_cast _ _

中文:
引理 piCongrLeft_apply_eq_cast
  结论: {P : β -> Sort v} {e : α ≃ β}
  证明: eqRec_eq_cast _ _

Depends on / 依赖: eqRec_eq_cast
-/
lemma piCongrLeft_apply_eq_cast {P : β -> Sort v} {e : α ≃ β}
    (f : (a : α) -> P (e a)) (b : β) :
    piCongrLeft P e f b = cast (congr_arg P (e.apply_symm_apply b)) (f (e.symm b)) :=
  eqRec_eq_cast _ _

/--
theorem `piCongrLeft_sumInl` / 定理 `piCongrLeft_sumInl`

English:
theorem piCongrLeft_sumInl
  statement: {ι ι' ι''} (π : ι'' -> Type*) (e : ι oplus ι' ≃ ι'') (f : forall i, π (e (inl i)))
  proof: by
  grind

中文:
定理 piCongrLeft_sumInl
  结论: {ι ι' ι''} (π : ι'' -> 类型) (e : ι oplus ι' ≃ ι'') (f : 对任意 i, π (e (inl i)))
  证明: by
  grind
-/
theorem piCongrLeft_sumInl {ι ι' ι''} (π : ι'' -> Type*) (e : ι oplus ι' ≃ ι'') (f : forall i, π (e (inl i)))
    (g : forall i, π (e (inr i))) (i : ι) :
    piCongrLeft π e (sumPiEquivProdPi (fun x => π (e x)) |>.symm (f, g)) (e (inl i)) = f i := by
  grind

/--
theorem `piCongrLeft_sumInr` / 定理 `piCongrLeft_sumInr`

English:
theorem piCongrLeft_sumInr
  statement: {ι ι' ι''} (π : ι'' -> Type*) (e : ι oplus ι' ≃ ι'') (f : forall i, π (e (inl i)))
  proof: by
  grind

中文:
定理 piCongrLeft_sumInr
  结论: {ι ι' ι''} (π : ι'' -> 类型) (e : ι oplus ι' ≃ ι'') (f : 对任意 i, π (e (inl i)))
  证明: by
  grind
-/
theorem piCongrLeft_sumInr {ι ι' ι''} (π : ι'' -> Type*) (e : ι oplus ι' ≃ ι'') (f : forall i, π (e (inl i)))
    (g : forall i, π (e (inr i))) (j : ι') :
    piCongrLeft π e (sumPiEquivProdPi (fun x => π (e x)) |>.symm (f, g)) (e (inr j)) = g j := by
  grind

end

section

variable {W : α -> Sort w} {Z : β -> Sort z} (h₁ : α ≃ β) (h₂ : forall a : α, W a ≃ Z (h₁ a))

/--
Definition of `piCongr` / `piCongr` 的定义

English:
definition piCongr
  signature: : (forall a, W a) ≃ forall b, Z b
  body: (Equiv.piCongrRight h₂).trans (Equiv.piCongrLeft _ h₁)

@[simp]

中文:
定义 piCongr
  签名: : (对任意 a, W a) ≃ 对任意 b, Z b
  定义体: (Equiv.piCongrRight h₂).trans (Equiv.piCongrLeft _ h₁)

@[simp]

Depends on / 依赖: Equiv.piCongrLeft, Equiv.piCongrRight, piCongrLeft, piCongrRight
-/
def piCongr : (forall a, W a) ≃ forall b, Z b :=
  (Equiv.piCongrRight h₂).trans (Equiv.piCongrLeft _ h₁)

@[simp]
/--
theorem `coe_piCongr_symm` / 定理 `coe_piCongr_symm`

English:
theorem coe_piCongr_symm
  proof: rfl

@[simp, grind =]

中文:
定理 coe_piCongr_symm
  证明: rfl

@[simp, grind =]
-/
theorem coe_piCongr_symm :
    ((h₁.piCongr h₂).symm : (forall b, Z b) -> forall a, W a) = fun f a => (h₂ a).symm (f (h₁ a)) :=
  rfl

@[simp, grind =]
/--
theorem `piCongr_symm_apply` / 定理 `piCongr_symm_apply`

English:
theorem piCongr_symm_apply
  given: (f : forall b, Z b)
  proof: rfl

@[simp, grind =]

中文:
定理 piCongr_symm_apply
  条件: (f : 对任意 b, Z b)
  证明: rfl

@[simp, grind =]
-/
theorem piCongr_symm_apply (f : forall b, Z b) :
    (h₁.piCongr h₂).symm f = fun a => (h₂ a).symm (f (h₁ a)) :=
  rfl

@[simp, grind =]
/--
theorem `piCongr_apply_apply` / 定理 `piCongr_apply_apply`

English:
theorem piCongr_apply_apply
  given: (f : forall a, W a) (a : α)
  statement: h₁.piCongr h₂ f (h₁ a) = h₂ a (f a)
  proof: by
  rw [piCongr]; rw [trans_apply]; rw [piCongrLeft_apply_apply]; rw [piCongrRight_apply]; rw [Pi.map_apply]

中文:
定理 piCongr_apply_apply
  条件: (f : 对任意 a, W a) (a : α)
  结论: h₁.piCongr h₂ f (h₁ a) = h₂ a (f a)
  证明: by
  rw [piCongr]; rw [trans_apply]; rw [piCongrLeft_apply_apply]; rw [piCongrRight_apply]; rw [Pi.map_apply]

Depends on / 依赖: Pi.map_apply, map_apply, piCongr, piCongrLeft_apply_apply, piCongrRight_apply, trans_apply
-/
theorem piCongr_apply_apply (f : forall a, W a) (a : α) : h₁.piCongr h₂ f (h₁ a) = h₂ a (f a) := by
  rw [piCongr]; rw [trans_apply]; rw [piCongrLeft_apply_apply]; rw [piCongrRight_apply]; rw [Pi.map_apply]

end

section

variable {W : α -> Sort w} {Z : β -> Sort z} (h₁ : α ≃ β) (h₂ : forall b : β, W (h₁.symm b) ≃ Z b)

/--
Definition of `piCongr'` / `piCongr'` 的定义

English:
definition piCongr'
  signature: : (forall a, W a) ≃ forall b, Z b
  body: (piCongr h₁.symm fun b => (h₂ b).symm).symm

@[simp]

中文:
定义 piCongr'
  签名: : (对任意 a, W a) ≃ 对任意 b, Z b
  定义体: (piCongr h₁.symm fun b => (h₂ b).symm).symm

@[simp]

Depends on / 依赖: piCongr
-/
def piCongr' : (forall a, W a) ≃ forall b, Z b :=
  (piCongr h₁.symm fun b => (h₂ b).symm).symm

@[simp]
/--
theorem `coe_piCongr'` / 定理 `coe_piCongr'`

English:
theorem coe_piCongr'
  proof: rfl

中文:
定理 coe_piCongr'
  证明: rfl
-/
theorem coe_piCongr' :
(h₁.piCongr' h₂ : (forall a, W a) -> forall b, Z b) = fun f b => h₂ b f h₁.symm b :=
  rfl

/--
theorem `piCongr'_apply` / 定理 `piCongr'_apply`

English:
theorem piCongr'_apply
  given: (f : forall a, W a)
  statement: h₁.piCongr' h₂ f = fun b => h₂ b f h₁.symm b
  proof: rfl

@[simp]

中文:
定理 piCongr'_apply
  条件: (f : 对任意 a, W a)
  结论: h₁.piCongr' h₂ f = fun b => h₂ b f h₁.symm b
  证明: rfl

@[simp]
-/
theorem piCongr'_apply (f : forall a, W a) : h₁.piCongr' h₂ f = fun b => h₂ b f h₁.symm b :=
  rfl

@[simp]
/--
theorem `piCongr'_symm_apply_symm_apply` / 定理 `piCongr'_symm_apply_symm_apply`

English:
theorem piCongr'_symm_apply_symm_apply
  given: (f : forall b, Z b) (b : β)
  proof: by
  simp [piCongr', piCongr_apply_apply]

中文:
定理 piCongr'_symm_apply_symm_apply
  条件: (f : 对任意 b, Z b) (b : β)
  证明: by
  simp [piCongr', piCongr_apply_apply]
-/
theorem piCongr'_symm_apply_symm_apply (f : forall b, Z b) (b : β) :
    (h₁.piCongr' h₂).symm f (h₁.symm b) = (h₂ b).symm (f b) := by
  simp [piCongr', piCongr_apply_apply]

end

variable {α : Type*} {β : Type*} {f : α -> β}

/--
Definition of `piCongrSigmaFiber` / `piCongrSigmaFiber` 的定义

English:
definition piCongrSigmaFiber
  signature: {γ₁ γ₂ : α -> Sort*} (e : (a : α) -> γ₁ a ≃ γ₂ a)
  body: .trans (piCongrRight e) piCongrLeft γ₁ (sigmaFiberEquiv f)

@[simp]

中文:
定义 piCongrSigmaFiber
  签名: {γ₁ γ₂ : α -> Sort*} (e : (a : α) -> γ₁ a ≃ γ₂ a)
  定义体: .trans (piCongrRight e) piCongrLeft γ₁ (sigmaFiberEquiv f)

@[simp]

Depends on / 依赖: piCongrLeft, piCongrRight, sigmaFiberEquiv
-/
def piCongrSigmaFiber {γ₁ γ₂ : α -> Sort*} (e : (a : α) -> γ₁ a ≃ γ₂ a) :
    ((σ : (y : β) × { x : α // f x = y }) -> γ₁ σ.2.1) ≃ ((a : α) -> γ₂ a) :=
.trans (piCongrRight e) piCongrLeft γ₁ (sigmaFiberEquiv f)

@[simp]
/--
theorem `piCongrSigmaFiber_apply` / 定理 `piCongrSigmaFiber_apply`

English:
theorem piCongrSigmaFiber_apply
  statement: {γ₁ γ₂ : α -> Sort*} (e : (a : α) -> γ₁ a ≃ γ₂ a)
  proof: rfl

@[simp]

中文:
定理 piCongrSigmaFiber_apply
  结论: {γ₁ γ₂ : α -> Sort*} (e : (a : α) -> γ₁ a ≃ γ₂ a)
  证明: rfl

@[simp]
-/
theorem piCongrSigmaFiber_apply {γ₁ γ₂ : α -> Sort*} (e : (a : α) -> γ₁ a ≃ γ₂ a)
    (g : (σ : (y : β) × { x : α // f x = y }) -> γ₁ σ.2.1) (a : α) :
    piCongrSigmaFiber e g a = e a (g ⟨f a, ⟨a, rfl⟩⟩) := rfl

@[simp]
/--
theorem `piCongrSigmaFiber_symm_apply` / 定理 `piCongrSigmaFiber_symm_apply`

English:
theorem piCongrSigmaFiber_symm_apply
  statement: {γ₁ γ₂ : α -> Sort*} (e : (a : α) -> γ₁ a ≃ γ₂ a)
  proof: rfl

中文:
定理 piCongrSigmaFiber_symm_apply
  结论: {γ₁ γ₂ : α -> Sort*} (e : (a : α) -> γ₁ a ≃ γ₂ a)
  证明: rfl
-/
theorem piCongrSigmaFiber_symm_apply {γ₁ γ₂ : α -> Sort*} (e : (a : α) -> γ₁ a ≃ γ₂ a)
    (g : (a : α) -> γ₂ a) (σ : (y : β) × { x : α // f x = y }) :
    (piCongrSigmaFiber e).symm g σ = (e σ.2.1).symm (g σ.2.1) := rfl

/--
Definition of `piCongrFiberwise` / `piCongrFiberwise` 的定义

English:
definition piCongrFiberwise
  signature: {γ₁ : α -> Type*} {γ₂ : β -> Type*} {f : α -> β}
  body: ((piCongrSigmaFiber (fun _ => Equiv.refl _)).symm.trans
    (piCurry fun b (x : { x : α // f x = b }) => γ₁ x.1)).trans
      (piCongrRight e)

@[simp]

中文:
定义 piCongrFiberwise
  签名: {γ₁ : α -> 类型} {γ₂ : β -> 类型} {f : α -> β}
  定义体: ((piCongrSigmaFiber (fun _ => Equiv.refl _)).symm.trans
    (piCurry fun b (x : { x : α // f x = b }) => γ₁ x.1)).trans
      (piCongrRight e)

@[simp]

Depends on / 依赖: Equiv.refl, piCongrRight, piCongrSigmaFiber, piCurry, symm.trans
-/
def piCongrFiberwise {γ₁ : α -> Type*} {γ₂ : β -> Type*} {f : α -> β}
    (e : (b : β) -> ((σ : { a : α // f a = b }) -> γ₁ σ.1) ≃ γ₂ b) :
    ((a : α) -> γ₁ a) ≃ ((b : β) -> γ₂ b) :=
  ((piCongrSigmaFiber (fun _ => Equiv.refl _)).symm.trans
    (piCurry fun b (x : { x : α // f x = b }) => γ₁ x.1)).trans
      (piCongrRight e)

@[simp]
/--
theorem `piCongrFiberwise_apply` / 定理 `piCongrFiberwise_apply`

English:
theorem piCongrFiberwise_apply
  statement: {γ₁ : α -> Type*} {γ₂ : β -> Type*} {f : α -> β}
  proof: rfl

@[simp]

中文:
定理 piCongrFiberwise_apply
  结论: {γ₁ : α -> 类型} {γ₂ : β -> 类型} {f : α -> β}
  证明: rfl

@[simp]
-/
theorem piCongrFiberwise_apply {γ₁ : α -> Type*} {γ₂ : β -> Type*} {f : α -> β}
    (e : (b : β) -> ((σ : { a : α // f a = b }) -> γ₁ σ.1) ≃ γ₂ b) (g : (a : α) -> γ₁ a) (b : β) :
    piCongrFiberwise e g b = e b fun σ => g σ.1 := rfl

@[simp]
/--
theorem `piCongrFiberwise_symm_apply` / 定理 `piCongrFiberwise_symm_apply`

English:
theorem piCongrFiberwise_symm_apply
  statement: {γ₁ : α -> Type*} {γ₂ : β -> Type*} {f : α -> β}
  proof: rfl

中文:
定理 piCongrFiberwise_symm_apply
  结论: {γ₁ : α -> 类型} {γ₂ : β -> 类型} {f : α -> β}
  证明: rfl
-/
theorem piCongrFiberwise_symm_apply {γ₁ : α -> Type*} {γ₂ : β -> Type*} {f : α -> β}
    (e : (b : β) -> ((σ : { a : α // f a = b }) -> γ₁ σ.1) ≃ γ₂ b) (g : (b : β) -> γ₂ b) (a : α) :
    (piCongrFiberwise e).symm g a = (e (f a)).symm (g (f a)) ⟨a, rfl⟩ := rfl

/--
Definition of `piCongrSet` / `piCongrSet` 的定义

English:
definition piCongrSet
  signature: {α} {W : α -> Sort w} {s t : Set α} (h : s = t)
  body: f ⟨i, h ▸ i.2⟩
  invFun f i := f ⟨i, h.symm ▸ i.2⟩

中文:
定义 piCongrSet
  签名: {α} {W : α -> Sort w} {s t : Set α} (h : s = t)
  定义体: f ⟨i, h ▸ i.2⟩
  invFun f i := f ⟨i, h.symm ▸ i.2⟩
-/
@[simps!] def piCongrSet {α} {W : α -> Sort w} {s t : Set α} (h : s = t) :
    (forall i : {i // i in s}, W i) ≃ (forall i : {i // i in t}, W i) where
  toFun f i := f ⟨i, h ▸ i.2⟩
  invFun f i := f ⟨i, h.symm ▸ i.2⟩

/--
lemma `eq_conj` / 引理 `eq_conj`

English:
lemma eq_conj
  statement: {α α' β β' : Sort*} (ε₁ : α ≃ α') (ε₂ : β' ≃ β)
  proof: by
  rw [Equiv.symm_comp_eq]; rw [Equiv.comp_symm_eq]; rw [Function.comp_assoc]

中文:
引理 eq_conj
  结论: {α α' β β' : Sort*} (ε₁ : α ≃ α') (ε₂ : β' ≃ β)
  证明: by
  rw [Equiv.symm_comp_eq]; rw [Equiv.comp_symm_eq]; rw [Function.comp_assoc]

Depends on / 依赖: Equiv.comp_symm_eq, Equiv.symm_comp_eq, Function, Function.comp_assoc, comp_assoc, comp_symm_eq, symm_comp_eq
-/
lemma eq_conj {α α' β β' : Sort*} (ε₁ : α ≃ α') (ε₂ : β' ≃ β)
    (f : α -> β) (f' : α' -> β') : ε₂.symm ∘ f ∘ ε₁.symm = f' ↔ f = ε₂ ∘ f' ∘ ε₁ := by
  rw [Equiv.symm_comp_eq]; rw [Equiv.comp_symm_eq]; rw [Function.comp_assoc]

section BinaryOp

variable {α₁ β₁ : Type*} (e : α₁ ≃ β₁) (f : α₁ -> α₁ -> α₁)

/--
theorem `semiconj_conj` / 定理 `semiconj_conj`

English:
theorem semiconj_conj
  given: (f : α₁ -> α₁)
  statement: Semiconj e f (e.conj f)
  proof: fun x => by simp

中文:
定理 semiconj_conj
  条件: (f : α₁ -> α₁)
  结论: Semiconj e f (e.conj f)
  证明: fun x => by simp
-/
theorem semiconj_conj (f : α₁ -> α₁) : Semiconj e f (e.conj f) := fun x => by simp

/--
theorem `semiconj₂_conj` / 定理 `semiconj₂_conj`

English:
theorem semiconj₂_conj
  statement: Semiconj₂ e f (e.arrowCongr e.conj f)
  proof: fun x y => by simp [arrowCongr]

中文:
定理 semiconj₂_conj
  结论: Semiconj₂ e f (e.arrowCongr e.conj f)
  证明: fun x y => by simp [arrowCongr]

Depends on / 依赖: arrowCongr
-/
theorem semiconj₂_conj : Semiconj₂ e f (e.arrowCongr e.conj f) := fun x y => by simp [arrowCongr]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Associative
  signature: f] : Std.Associative (e.arrowCongr (e.arrowCongr e) f)
  body: (e.semiconj₂_conj f).isAssociative_right e.surjective

中文:
实例 [Std.Associative
  签名: f] : Std.Associative (e.arrowCongr (e.arrowCongr e) f)
  定义体: (e.semiconj₂_conj f).isAssociative_right e.surjective

Depends on / 依赖: e.semiconj, e.surjective, isAssociative_right, surjective
-/
instance [Std.Associative f] : Std.Associative (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).isAssociative_right e.surjective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.IdempotentOp
  signature: f] : Std.IdempotentOp (e.arrowCongr (e.arrowCongr e) f)
  body: (e.semiconj₂_conj f).isIdempotent_right e.surjective

中文:
实例 [Std.IdempotentOp
  签名: f] : Std.IdempotentOp (e.arrowCongr (e.arrowCongr e) f)
  定义体: (e.semiconj₂_conj f).isIdempotent_right e.surjective

Depends on / 依赖: e.semiconj, e.surjective, isIdempotent_right, surjective
-/
instance [Std.IdempotentOp f] : Std.IdempotentOp (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).isIdempotent_right e.surjective

end BinaryOp

section ULift

@[simp]
/--
theorem `ulift_symm_down` / 定理 `ulift_symm_down`

English:
theorem ulift_symm_down
  given: {α} (x : α)
  statement: (Equiv.ulift.{u, v}.symm x).down = x
  proof: rfl

中文:
定理 ulift_symm_down
  条件: {α} (x : α)
  结论: (Equiv.ulift.{u, v}.symm x).down = x
  证明: rfl
-/
theorem ulift_symm_down {α} (x : α) : (Equiv.ulift.{u, v}.symm x).down = x :=
  rfl

end ULift

end Equiv

/--
theorem `Function.Injective.swap_apply` / 定理 `Function.Injective.swap_apply`

English:
theorem Function.Injective.swap_apply
  proof: Eq.symm (map_swap hf x y z)

中文:
定理 Function.Injective.swap_apply
  证明: Eq.symm (map_swap hf x y z)

Depends on / 依赖: Eq.symm, map_swap
-/
theorem Function.Injective.swap_apply
    [DecidableEq α] [DecidableEq β] {f : α -> β} (hf : Function.Injective f) (x y z : α) :
    Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z) :=
  Eq.symm (map_swap hf x y z)

/--
theorem `Function.Injective.swap_comp` / 定理 `Function.Injective.swap_comp`

English:
theorem Function.Injective.swap_comp
  proof: funext fun _ => hf.swap_apply _ _ _

中文:
定理 Function.Injective.swap_comp
  证明: funext fun _ => hf.swap_apply _ _ _

Depends on / 依赖: hf.swap_apply, swap_apply
-/
theorem Function.Injective.swap_comp
    [DecidableEq α] [DecidableEq β] {f : α -> β} (hf : Function.Injective f) (x y : α) :
    Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y :=
  funext fun _ => hf.swap_apply _ _ _

/--
Definition of `equivOfSubsingletonOfSubsingleton` / `equivOfSubsingletonOfSubsingleton` 的定义

English:
definition equivOfSubsingletonOfSubsingleton
  signature: [Subsingleton α] [Subsingleton β] (f : α -> β) (g : β -> α)
  body: f
  invFun := g
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 equivOfSubsingletonOfSubsingleton
  签名: [Subsingleton α] [Subsingleton β] (f : α -> β) (g : β -> α)
  定义体: f
  invFun := g
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
-/
def equivOfSubsingletonOfSubsingleton [Subsingleton α] [Subsingleton β] (f : α -> β) (g : β -> α) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/--
Definition of `Equiv.punitOfNonemptyOfSubsingleton` / `Equiv.punitOfNonemptyOfSubsingleton` 的定义

English:
definition Equiv.punitOfNonemptyOfSubsingleton
  signature: [h : Nonempty α] [Subsingleton α]
  body: equivOfSubsingletonOfSubsingleton (fun _ => PUnit.unit) fun _ => h.some

中文:
定义 Equiv.punitOfNonemptyOfSubsingleton
  签名: [h : Nonempty α] [Subsingleton α]
  定义体: equivOfSubsingletonOfSubsingleton (fun _ => PUnit.unit) fun _ => h.some

Depends on / 依赖: PUnit.unit, equivOfSubsingletonOfSubsingleton, h.some
-/
noncomputable def Equiv.punitOfNonemptyOfSubsingleton [h : Nonempty α] [Subsingleton α] :
    α ≃ PUnit :=
  equivOfSubsingletonOfSubsingleton (fun _ => PUnit.unit) fun _ => h.some

/--
Definition of `uniqueUniqueEquiv` / `uniqueUniqueEquiv` 的定义

English:
definition uniqueUniqueEquiv
  signature: : Unique (Unique α) ≃ Unique α
  body: equivOfSubsingletonOfSubsingleton (fun h => h.default) fun h =>
    { default := h, uniq := fun _ => Subsingleton.elim _ _ }

中文:
定义 uniqueUniqueEquiv
  签名: : Unique (Unique α) ≃ Unique α
  定义体: equivOfSubsingletonOfSubsingleton (fun h => h.default) fun h =>
    { default := h, uniq := fun _ => Subsingleton.elim _ _ }

Depends on / 依赖: Subsingleton, Subsingleton.elim, equivOfSubsingletonOfSubsingleton, h.default
-/
def uniqueUniqueEquiv : Unique (Unique α) ≃ Unique α :=
  equivOfSubsingletonOfSubsingleton (fun h => h.default) fun h =>
    { default := h, uniq := fun _ => Subsingleton.elim _ _ }

/--
Definition of `uniqueEquivEquivUnique` / `uniqueEquivEquivUnique` 的定义

English:
definition uniqueEquivEquivUnique
  signature: (α : Sort u) (β : Sort v) [Unique β]
  body: equivOfSubsingletonOfSubsingleton (fun _ => Equiv.ofUnique _ _) Equiv.unique

中文:
定义 uniqueEquivEquivUnique
  签名: (α : Sort u) (β : Sort v) [Unique β]
  定义体: equivOfSubsingletonOfSubsingleton (fun _ => Equiv.ofUnique _ _) Equiv.unique

Depends on / 依赖: Equiv.ofUnique, Equiv.unique, equivOfSubsingletonOfSubsingleton, ofUnique, unique
-/
def uniqueEquivEquivUnique (α : Sort u) (β : Sort v) [Unique β] : Unique α ≃ (α ≃ β) :=
  equivOfSubsingletonOfSubsingleton (fun _ => Equiv.ofUnique _ _) Equiv.unique

namespace Function

variable {α' : Sort*}

/--
theorem `update_comp_equiv` / 定理 `update_comp_equiv`

English:
theorem update_comp_equiv
  statement: [DecidableEq α'] [DecidableEq α] (f : α -> β)
  proof: by
  rw [← update_comp_eq_of_injective _ g.injective]; rw [g.apply_symm_apply]

中文:
定理 update_comp_equiv
  结论: [DecidableEq α'] [DecidableEq α] (f : α -> β)
  证明: by
  rw [← update_comp_eq_of_injective _ g.injective]; rw [g.apply_symm_apply]

Depends on / 依赖: apply_symm_apply, g.apply_symm_apply, g.injective, injective, update_comp_eq_of_injective
-/
theorem update_comp_equiv [DecidableEq α'] [DecidableEq α] (f : α -> β)
    (g : α' ≃ α) (a : α) (v : β) :
    update f a v ∘ g = update (f ∘ g) (g.symm a) v := by
  rw [← update_comp_eq_of_injective _ g.injective]; rw [g.apply_symm_apply]

/--
theorem `update_apply_equiv_apply` / 定理 `update_apply_equiv_apply`

English:
theorem update_apply_equiv_apply
  statement: [DecidableEq α'] [DecidableEq α] (f : α -> β)
  proof: congr_fun (update_comp_equiv f g a v) a'

中文:
定理 update_apply_equiv_apply
  结论: [DecidableEq α'] [DecidableEq α] (f : α -> β)
  证明: congr_fun (update_comp_equiv f g a v) a'

Depends on / 依赖: congr_fun, update_comp_equiv
-/
theorem update_apply_equiv_apply [DecidableEq α'] [DecidableEq α] (f : α -> β)
    (g : α' ≃ α) (a : α) (v : β) (a' : α') : update f a v (g a') = update (f ∘ g) (g.symm a) v a' :=
  congr_fun (update_comp_equiv f g a v) a'

/--
theorem `piCongrLeft'_update` / 定理 `piCongrLeft'_update`

English:
theorem piCongrLeft'_update
  statement: [DecidableEq α] [DecidableEq β] (P : α -> Sort*) (e : α ≃ β)
  proof: by
  ext b'
  rcases eq_or_ne b' b with (rfl | h) <;> simp_all

中文:
定理 piCongrLeft'_update
  结论: [DecidableEq α] [DecidableEq β] (P : α -> Sort*) (e : α ≃ β)
  证明: by
  ext b'
  rcases eq_or_ne b' b with (rfl | h) <;> simp_all

Depends on / 依赖: eq_or_ne
-/
theorem piCongrLeft'_update [DecidableEq α] [DecidableEq β] (P : α -> Sort*) (e : α ≃ β)
    (f : forall a, P a) (b : β) (x : P (e.symm b)) :
    e.piCongrLeft' P (update f (e.symm b) x) = update (e.piCongrLeft' P f) b x := by
  ext b'
  rcases eq_or_ne b' b with (rfl | h) <;> simp_all

/--
theorem `piCongrLeft'_symm_update` / 定理 `piCongrLeft'_symm_update`

English:
theorem piCongrLeft'_symm_update
  statement: [DecidableEq α] [DecidableEq β] (P : α -> Sort*) (e : α ≃ β)
  proof: by
  simp [(e.piCongrLeft' P).symm_apply_eq, piCongrLeft'_update]

中文:
定理 piCongrLeft'_symm_update
  结论: [DecidableEq α] [DecidableEq β] (P : α -> Sort*) (e : α ≃ β)
  证明: by
  simp [(e.piCongrLeft' P).symm_apply_eq, piCongrLeft'_update]
-/
theorem piCongrLeft'_symm_update [DecidableEq α] [DecidableEq β] (P : α -> Sort*) (e : α ≃ β)
    (f : forall b, P (e.symm b)) (b : β) (x : P (e.symm b)) :
    (e.piCongrLeft' P).symm (update f b x) = update ((e.piCongrLeft' P).symm f) (e.symm b) x := by
  simp [(e.piCongrLeft' P).symm_apply_eq, piCongrLeft'_update]

end Function
