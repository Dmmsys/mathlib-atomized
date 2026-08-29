/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Data.Option.Defs
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic.Coe

/-!
# Equivalence between sum types

In this file we continue the work on equivalences begun in `Mathlib/Logic/Equiv/Defs.lean`, defining

* canonical isomorphisms between various types: e.g.,

  - `Equiv.sumEquivSigmaBool` is the canonical equivalence between the sum of two types `α ⊕ β`
    and the sigma-type `Σ b, bif b then β else α`;

  - `Equiv.prodSumDistrib : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)` shows that type product and type sum
    satisfy the distributive law up to a canonical equivalence;

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

section

open Sum

/--
Definition of `psumEquivSum` / `psumEquivSum` 的定义

English:
definition psumEquivSum
  signature: (α β)
  body: PSum.casesOn s inl inr
  invFun := Sum.elim PSum.inl PSum.inr
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

中文:
定义 psumEquivSum
  签名: (α β)
  定义体: PSum.casesOn s inl inr
  invFun := Sum.elim PSum.inl PSum.inr
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

Depends on / 依赖: PSum.casesOn, casesOn
-/
def psumEquivSum (α β) : α oplus' β ≃ α oplus β where
  toFun s := PSum.casesOn s inl inr
  invFun := Sum.elim PSum.inl PSum.inr
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

/-- If `α ≃ α'` and `β ≃ β'`, then `α ⊕ β ≃ α' ⊕ β'`. This is `Sum.map` as an equivalence. -/
@[simps (attr := grind =) apply]
/--
Definition of `sumCongr` / `sumCongr` 的定义

English:
definition sumCongr
  signature: {α₁ α₂ β₁ β₂} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
  body: ⟨Sum.map ea eb, Sum.map ea.symm eb.symm, fun x => by simp, fun x => by simp⟩

@[simp, grind =]

中文:
定义 sumCongr
  签名: {α₁ α₂ β₁ β₂} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
  定义体: ⟨Sum.map ea eb, Sum.map ea.symm eb.symm, fun x => by simp, fun x => by simp⟩

@[simp, grind =]

Depends on / 依赖: Sum.map, ea.symm, eb.symm
-/
def sumCongr {α₁ α₂ β₁ β₂} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : α₁ oplus β₁ ≃ α₂ oplus β₂ :=
  ⟨Sum.map ea eb, Sum.map ea.symm eb.symm, fun x => by simp, fun x => by simp⟩

@[simp, grind =]
/--
theorem `sumCongr_trans` / 定理 `sumCongr_trans`

English:
theorem sumCongr_trans
  given: {α₁ α₂ β₁ β₂ γ₁ γ₂} (e : α₁ ≃ β₁) (f : α₂ ≃ β₂) (g : β₁ ≃ γ₁) (h : β₂ ≃ γ₂)
  proof: by
  ext i
  cases i <;> rfl

@[simp]

中文:
定理 sumCongr_trans
  条件: {α₁ α₂ β₁ β₂ γ₁ γ₂} (e : α₁ ≃ β₁) (f : α₂ ≃ β₂) (g : β₁ ≃ γ₁) (h : β₂ ≃ γ₂)
  证明: by
  ext i
  cases i <;> rfl

@[simp]
-/
theorem sumCongr_trans {α₁ α₂ β₁ β₂ γ₁ γ₂} (e : α₁ ≃ β₁) (f : α₂ ≃ β₂) (g : β₁ ≃ γ₁) (h : β₂ ≃ γ₂) :
    (Equiv.sumCongr e f).trans (Equiv.sumCongr g h) = Equiv.sumCongr (e.trans g) (f.trans h) := by
  ext i
  cases i <;> rfl

@[simp]
/--
theorem `sumCongr_symm` / 定理 `sumCongr_symm`

English:
theorem sumCongr_symm
  given: {α β γ δ} (e : α ≃ β) (f : γ ≃ δ)
  proof: rfl

@[simp]

中文:
定理 sumCongr_symm
  条件: {α β γ δ} (e : α ≃ β) (f : γ ≃ δ)
  证明: rfl

@[simp]
-/
theorem sumCongr_symm {α β γ δ} (e : α ≃ β) (f : γ ≃ δ) :
    (Equiv.sumCongr e f).symm = Equiv.sumCongr e.symm f.symm :=
  rfl

@[simp]
/--
theorem `sumCongr_refl` / 定理 `sumCongr_refl`

English:
theorem sumCongr_refl
  given: {α β}
  proof: by
  ext i
  cases i <;> rfl

中文:
定理 sumCongr_refl
  条件: {α β}
  证明: by
  ext i
  cases i <;> rfl
-/
theorem sumCongr_refl {α β} :
    Equiv.sumCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α oplus β) := by
  ext i
  cases i <;> rfl

/--
Definition of `psumCongr` / `psumCongr` 的定义

English:
definition psumCongr
  signature: (e₁ : α ≃ β) (e₂ : γ ≃ δ)
  body: PSum.casesOn x (PSum.inl ∘ e₁) (PSum.inr ∘ e₂)
  invFun x := PSum.casesOn x (PSum.inl ∘ e₁.symm) (PSum.inr ∘ e₂.symm)
  left_inv := by rintro (x | x) <;> simp
  right_inv := by rintro (x | x) <;> simp

中文:
定义 psumCongr
  签名: (e₁ : α ≃ β) (e₂ : γ ≃ δ)
  定义体: PSum.casesOn x (PSum.inl ∘ e₁) (PSum.inr ∘ e₂)
  invFun x := PSum.casesOn x (PSum.inl ∘ e₁.symm) (PSum.inr ∘ e₂.symm)
  left_inv := by rintro (x | x) <;> simp
  right_inv := by rintro (x | x) <;> simp

Depends on / 依赖: PSum.casesOn, PSum.inl, PSum.inr, casesOn
-/
def psumCongr (e₁ : α ≃ β) (e₂ : γ ≃ δ) : α oplus' γ ≃ β oplus' δ where
  toFun x := PSum.casesOn x (PSum.inl ∘ e₁) (PSum.inr ∘ e₂)
  invFun x := PSum.casesOn x (PSum.inl ∘ e₁.symm) (PSum.inr ∘ e₂.symm)
  left_inv := by rintro (x | x) <;> simp
  right_inv := by rintro (x | x) <;> simp

/--
Definition of `psumSum` / `psumSum` 的定义

English:
definition psumSum
  signature: {α₂ β₂} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
  body: (ea.psumCongr eb).trans (psumEquivSum _ _)

中文:
定义 psumSum
  签名: {α₂ β₂} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
  定义体: (ea.psumCongr eb).trans (psumEquivSum _ _)

Depends on / 依赖: ea.psumCongr, psumCongr, psumEquivSum
-/
def psumSum {α₂ β₂} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    α₁ oplus' β₁ ≃ α₂ oplus β₂ :=
  (ea.psumCongr eb).trans (psumEquivSum _ _)

/--
Definition of `sumPSum` / `sumPSum` 的定义

English:
definition sumPSum
  signature: {α₁ β₁} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
  body: (ea.symm.psumSum eb.symm).symm

中文:
定义 sumPSum
  签名: {α₁ β₁} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
  定义体: (ea.symm.psumSum eb.symm).symm

Depends on / 依赖: ea.symm.psumSum, eb.symm, psumSum
-/
def sumPSum {α₁ β₁} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    α₁ oplus β₁ ≃ α₂ oplus' β₂ :=
  (ea.symm.psumSum eb.symm).symm

/--
Definition of `subtypeSum` / `subtypeSum` 的定义

English:
definition subtypeSum
  signature: {α β} {p : α oplus β -> Prop}
  body: by rintro ⟨a | b, h⟩ <;> rfl
  right_inv := by rintro (a | b) <;> rfl

中文:
定义 subtypeSum
  签名: {α β} {p : α oplus β -> 命题}
  定义体: by rintro ⟨a | b, h⟩ <;> rfl
  right_inv := by rintro (a | b) <;> rfl

Depends on / 依赖: right_inv
-/
def subtypeSum {α β} {p : α oplus β -> Prop} :
    {c // p c} ≃ {a // p (Sum.inl a)} oplus {b // p (Sum.inr b)} where
  toFun
    | ⟨.inl a, h⟩ => .inl ⟨a, h⟩
    | ⟨.inr b, h⟩ => .inr ⟨b, h⟩
  invFun
    | .inl a => ⟨.inl a, a.2⟩
    | .inr b => ⟨.inr b, b.2⟩
  left_inv := by rintro ⟨a | b, h⟩ <;> rfl
  right_inv := by rintro (a | b) <;> rfl

namespace Perm

/--
Definition of `sumCongr` / `sumCongr` 的定义

English:
abbreviation sumCongr
  signature: {α β} (ea : Equiv.Perm α) (eb : Equiv.Perm β)
  body: Equiv.sumCongr ea eb

@[simp]

中文:
缩写 sumCongr
  签名: {α β} (ea : Equiv.Perm α) (eb : Equiv.Perm β)
  定义体: Equiv.sumCongr ea eb

@[simp]

Depends on / 依赖: Equiv.sumCongr, sumCongr
-/
abbrev sumCongr {α β} (ea : Equiv.Perm α) (eb : Equiv.Perm β) : Equiv.Perm (α oplus β) :=
  Equiv.sumCongr ea eb

@[simp]
/--
theorem `sumCongr_apply` / 定理 `sumCongr_apply`

English:
theorem sumCongr_apply
  given: {α β} (ea : Equiv.Perm α) (eb : Equiv.Perm β) (x : α oplus β)
  proof: rfl

中文:
定理 sumCongr_apply
  条件: {α β} (ea : Equiv.Perm α) (eb : Equiv.Perm β) (x : α oplus β)
  证明: rfl
-/
theorem sumCongr_apply {α β} (ea : Equiv.Perm α) (eb : Equiv.Perm β) (x : α oplus β) :
    sumCongr ea eb x = Sum.map (⇑ea) (⇑eb) x := rfl

/--
theorem `sumCongr_trans` / 定理 `sumCongr_trans`

English:
theorem sumCongr_trans
  statement: {α β} (e : Equiv.Perm α) (f : Equiv.Perm β) (g : Equiv.Perm α)
  proof: Equiv.sumCongr_trans e f g h

中文:
定理 sumCongr_trans
  结论: {α β} (e : Equiv.Perm α) (f : Equiv.Perm β) (g : Equiv.Perm α)
  证明: Equiv.sumCongr_trans e f g h

Depends on / 依赖: Equiv.sumCongr_trans, sumCongr_trans
-/
theorem sumCongr_trans {α β} (e : Equiv.Perm α) (f : Equiv.Perm β) (g : Equiv.Perm α)
    (h : Equiv.Perm β) : (sumCongr e f).trans (sumCongr g h) = sumCongr (e.trans g) (f.trans h) :=
  Equiv.sumCongr_trans e f g h

/--
theorem `sumCongr_symm` / 定理 `sumCongr_symm`

English:
theorem sumCongr_symm
  given: {α β} (e : Equiv.Perm α) (f : Equiv.Perm β)
  proof: Equiv.sumCongr_symm e f

中文:
定理 sumCongr_symm
  条件: {α β} (e : Equiv.Perm α) (f : Equiv.Perm β)
  证明: Equiv.sumCongr_symm e f

Depends on / 依赖: Equiv.sumCongr_symm, sumCongr_symm
-/
theorem sumCongr_symm {α β} (e : Equiv.Perm α) (f : Equiv.Perm β) :
    (sumCongr e f).symm = sumCongr e.symm f.symm :=
  Equiv.sumCongr_symm e f

/--
theorem `sumCongr_refl` / 定理 `sumCongr_refl`

English:
theorem sumCongr_refl
  given: {α β}
  statement: sumCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α oplus β)
  proof: Equiv.sumCongr_refl

中文:
定理 sumCongr_refl
  条件: {α β}
  结论: sumCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α oplus β)
  证明: Equiv.sumCongr_refl

Depends on / 依赖: Equiv.sumCongr_refl, sumCongr_refl
-/
theorem sumCongr_refl {α β} : sumCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α oplus β) :=
  Equiv.sumCongr_refl

end Perm

/--
Definition of `boolEquivPUnitSumPUnit` / `boolEquivPUnitSumPUnit` 的定义

English:
definition boolEquivPUnitSumPUnit
  signature: : Bool ≃ PUnit.{u + 1} oplus PUnit.{v + 1}
  body: ⟨fun b => b.casesOn (inl PUnit.unit) (inr PUnit.unit), Sum.elim (fun _ => false) fun _ => true,
    fun b => by cases b <;> rfl, fun s => by rcases s with (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> rfl⟩

中文:
定义 boolEquivPUnitSumPUnit
  签名: : 布尔 ≃ PUnit.{u + 1} oplus PUnit.{v + 1}
  定义体: ⟨fun b => b.casesOn (inl PUnit.unit) (inr PUnit.unit), Sum.elim (fun _ => false) fun _ => true,
    fun b => by cases b <;> rfl, fun s => by rcases s with (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> rfl⟩

Depends on / 依赖: PUnit.unit, Sum.elim, b.casesOn, casesOn
-/
def boolEquivPUnitSumPUnit : Bool ≃ PUnit.{u + 1} oplus PUnit.{v + 1} :=
  ⟨fun b => b.casesOn (inl PUnit.unit) (inr PUnit.unit), Sum.elim (fun _ => false) fun _ => true,
    fun b => by cases b <;> rfl, fun s => by rcases s with (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> rfl⟩

/-- Sum of types is commutative up to an equivalence. This is `Sum.swap` as an equivalence. -/
@[simps -fullyApplied apply]
/--
Definition of `sumComm` / `sumComm` 的定义

English:
definition sumComm
  signature: (α β)
  body: ⟨Sum.swap, Sum.swap, Sum.swap_swap, Sum.swap_swap⟩

@[simp]

中文:
定义 sumComm
  签名: (α β)
  定义体: ⟨Sum.swap, Sum.swap, Sum.swap_swap, Sum.swap_swap⟩

@[simp]

Depends on / 依赖: Sum.swap, Sum.swap_swap, swap_swap
-/
def sumComm (α β) : α oplus β ≃ β oplus α :=
  ⟨Sum.swap, Sum.swap, Sum.swap_swap, Sum.swap_swap⟩

@[simp]
/--
theorem `sumComm_symm` / 定理 `sumComm_symm`

English:
theorem sumComm_symm
  given: (α β)
  statement: (sumComm α β).symm = sumComm β α
  proof: rfl

中文:
定理 sumComm_symm
  条件: (α β)
  结论: (sumComm α β).symm = sumComm β α
  证明: rfl
-/
theorem sumComm_symm (α β) : (sumComm α β).symm = sumComm β α :=
  rfl

/--
Definition of `sumAssoc` / `sumAssoc` 的定义

English:
definition sumAssoc
  signature: (α β γ)
  body: ⟨Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr),
Sum.elim (Sum.inl ∘ Sum.inl) Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr,
      by rintro (⟨_ | _⟩ | _) <;> rfl, by
    rintro (_ | ⟨_ | _⟩) <;> rfl⟩

@[simp]

中文:
定义 sumAssoc
  签名: (α β γ)
  定义体: ⟨Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr),
Sum.elim (Sum.inl ∘ Sum.inl) Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr,
      by rintro (⟨_ | _⟩ | _) <;> rfl, by
    rintro (_ | ⟨_ | _⟩) <;> rfl⟩

@[simp]

Depends on / 依赖: Sum.elim, Sum.inl, Sum.inr
-/
def sumAssoc (α β γ) : (α oplus β) oplus γ ≃ α oplus (β oplus γ) :=
  ⟨Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr),
Sum.elim (Sum.inl ∘ Sum.inl) Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr,
      by rintro (⟨_ | _⟩ | _) <;> rfl, by
    rintro (_ | ⟨_ | _⟩) <;> rfl⟩

@[simp]
/--
theorem `sumAssoc_apply_inl_inl` / 定理 `sumAssoc_apply_inl_inl`

English:
theorem sumAssoc_apply_inl_inl
  given: {α β γ} (a)
  statement: sumAssoc α β γ (inl (inl a)) = inl a
  proof: rfl

@[simp]

中文:
定理 sumAssoc_apply_inl_inl
  条件: {α β γ} (a)
  结论: sumAssoc α β γ (inl (inl a)) = inl a
  证明: rfl

@[simp]
-/
theorem sumAssoc_apply_inl_inl {α β γ} (a) : sumAssoc α β γ (inl (inl a)) = inl a :=
  rfl

@[simp]
/--
theorem `sumAssoc_apply_inl_inr` / 定理 `sumAssoc_apply_inl_inr`

English:
theorem sumAssoc_apply_inl_inr
  given: {α β γ} (b)
  statement: sumAssoc α β γ (inl (inr b)) = inr (inl b)
  proof: rfl

@[simp]

中文:
定理 sumAssoc_apply_inl_inr
  条件: {α β γ} (b)
  结论: sumAssoc α β γ (inl (inr b)) = inr (inl b)
  证明: rfl

@[simp]
-/
theorem sumAssoc_apply_inl_inr {α β γ} (b) : sumAssoc α β γ (inl (inr b)) = inr (inl b) :=
  rfl

@[simp]
/--
theorem `sumAssoc_apply_inr` / 定理 `sumAssoc_apply_inr`

English:
theorem sumAssoc_apply_inr
  given: {α β γ} (c)
  statement: sumAssoc α β γ (inr c) = inr (inr c)
  proof: rfl

@[simp]

中文:
定理 sumAssoc_apply_inr
  条件: {α β γ} (c)
  结论: sumAssoc α β γ (inr c) = inr (inr c)
  证明: rfl

@[simp]
-/
theorem sumAssoc_apply_inr {α β γ} (c) : sumAssoc α β γ (inr c) = inr (inr c) :=
  rfl

@[simp]
/--
theorem `sumAssoc_symm_apply_inl` / 定理 `sumAssoc_symm_apply_inl`

English:
theorem sumAssoc_symm_apply_inl
  given: {α β γ} (a)
  statement: (sumAssoc α β γ).symm (inl a) = inl (inl a)
  proof: rfl

@[simp]

中文:
定理 sumAssoc_symm_apply_inl
  条件: {α β γ} (a)
  结论: (sumAssoc α β γ).symm (inl a) = inl (inl a)
  证明: rfl

@[simp]
-/
theorem sumAssoc_symm_apply_inl {α β γ} (a) : (sumAssoc α β γ).symm (inl a) = inl (inl a) :=
  rfl

@[simp]
/--
theorem `sumAssoc_symm_apply_inr_inl` / 定理 `sumAssoc_symm_apply_inr_inl`

English:
theorem sumAssoc_symm_apply_inr_inl
  given: {α β γ} (b)
  proof: rfl

@[simp]

中文:
定理 sumAssoc_symm_apply_inr_inl
  条件: {α β γ} (b)
  证明: rfl

@[simp]
-/
theorem sumAssoc_symm_apply_inr_inl {α β γ} (b) :
    (sumAssoc α β γ).symm (inr (inl b)) = inl (inr b) :=
  rfl

@[simp]
/--
theorem `sumAssoc_symm_apply_inr_inr` / 定理 `sumAssoc_symm_apply_inr_inr`

English:
theorem sumAssoc_symm_apply_inr_inr
  given: {α β γ} (c)
  statement: (sumAssoc α β γ).symm (inr (inr c)) = inr c
  proof: rfl

中文:
定理 sumAssoc_symm_apply_inr_inr
  条件: {α β γ} (c)
  结论: (sumAssoc α β γ).symm (inr (inr c)) = inr c
  证明: rfl
-/
theorem sumAssoc_symm_apply_inr_inr {α β γ} (c) : (sumAssoc α β γ).symm (inr (inr c)) = inr c :=
  rfl

/-- Four-way commutativity of `sum`. The name matches `add_add_add_comm`. -/
@[simps apply]
/--
Definition of `sumSumSumComm` / `sumSumSumComm` 的定义

English:
definition sumSumSumComm
  signature: (α β γ δ)
  body: (sumAssoc (α oplus γ) β δ) ∘ (Sum.map (sumAssoc α γ β).symm (@id δ))
      ∘ (Sum.map (Sum.map (@id α) (sumComm β γ)) (@id δ))
      ∘ (Sum.map (sumAssoc α β γ) (@id δ))
      ∘ (sumAssoc (α oplus β) γ δ).symm
  invFun :=
    (sumAssoc (α oplus β) γ δ) ∘ (Sum.map (sumAssoc α β γ).symm (@id δ))
     

中文:
定义 sumSumSumComm
  签名: (α β γ δ)
  定义体: (sumAssoc (α oplus γ) β δ) ∘ (Sum.map (sumAssoc α γ β).symm (@id δ))
      ∘ (Sum.map (Sum.map (@id α) (sumComm β γ)) (@id δ))
      ∘ (Sum.map (sumAssoc α β γ) (@id δ))
      ∘ (sumAssoc (α oplus β) γ δ).symm
  invFun :=
    (sumAssoc (α oplus β) γ δ) ∘ (Sum.map (sumAssoc α β γ).symm (@id δ))
     

Depends on / 依赖: Sum.map, invFun, left_inv, right_inv, sumAssoc, sumComm
-/
def sumSumSumComm (α β γ δ) : (α oplus β) oplus γ oplus δ ≃ (α oplus γ) oplus β oplus δ where
  toFun :=
    (sumAssoc (α oplus γ) β δ) ∘ (Sum.map (sumAssoc α γ β).symm (@id δ))
      ∘ (Sum.map (Sum.map (@id α) (sumComm β γ)) (@id δ))
      ∘ (Sum.map (sumAssoc α β γ) (@id δ))
      ∘ (sumAssoc (α oplus β) γ δ).symm
  invFun :=
    (sumAssoc (α oplus β) γ δ) ∘ (Sum.map (sumAssoc α β γ).symm (@id δ))
      ∘ (Sum.map (Sum.map (@id α) (sumComm β γ).symm) (@id δ))
      ∘ (Sum.map (sumAssoc α γ β) (@id δ))
      ∘ (sumAssoc (α oplus γ) β δ).symm
  left_inv x := by rcases x with ((a | b) | (c | d)) <;> simp
  right_inv x := by rcases x with ((a | c) | (b | d)) <;> simp

@[simp]
/--
theorem `sumSumSumComm_symm` / 定理 `sumSumSumComm_symm`

English:
theorem sumSumSumComm_symm
  given: (α β γ δ)
  statement: (sumSumSumComm α β γ δ).symm = sumSumSumComm α γ β δ
  proof: rfl

中文:
定理 sumSumSumComm_symm
  条件: (α β γ δ)
  结论: (sumSumSumComm α β γ δ).symm = sumSumSumComm α γ β δ
  证明: rfl
-/
theorem sumSumSumComm_symm (α β γ δ) : (sumSumSumComm α β γ δ).symm = sumSumSumComm α γ β δ :=
  rfl

/-- Sum with `IsEmpty` is equivalent to the original type. -/
@[simps symm_apply]
/--
Definition of `sumEmpty` / `sumEmpty` 的定义

English:
definition sumEmpty
  signature: (α β) [IsEmpty β]
  body: Sum.elim id isEmptyElim
  invFun := inl
  left_inv s := by
    rcases s with (_ | x)
    · rfl
    · exact isEmptyElim x

@[simp]

中文:
定义 sumEmpty
  签名: (α β) [IsEmpty β]
  定义体: Sum.elim id isEmptyElim
  invFun := inl
  left_inv s := by
    rcases s with (_ | x)
    · rfl
    · exact isEmptyElim x

@[simp]

Depends on / 依赖: Sum.elim, isEmptyElim
-/
def sumEmpty (α β) [IsEmpty β] : α oplus β ≃ α where
  toFun := Sum.elim id isEmptyElim
  invFun := inl
  left_inv s := by
    rcases s with (_ | x)
    · rfl
    · exact isEmptyElim x

@[simp]
/--
theorem `sumEmpty_apply_inl` / 定理 `sumEmpty_apply_inl`

English:
theorem sumEmpty_apply_inl
  given: {α β} [IsEmpty β] (a : α)
  statement: sumEmpty α β (Sum.inl a) = a
  proof: rfl

中文:
定理 sumEmpty_apply_inl
  条件: {α β} [IsEmpty β] (a : α)
  结论: sumEmpty α β (Sum.inl a) = a
  证明: rfl
-/
theorem sumEmpty_apply_inl {α β} [IsEmpty β] (a : α) : sumEmpty α β (Sum.inl a) = a :=
  rfl

/-- The sum of `IsEmpty` with any type is equivalent to that type. -/
@[simps! symm_apply]
/--
Definition of `emptySum` / `emptySum` 的定义

English:
definition emptySum
  signature: (α β) [IsEmpty α]
  body: (sumComm _ _).trans sumEmpty _ _

@[simp]

中文:
定义 emptySum
  签名: (α β) [IsEmpty α]
  定义体: (sumComm _ _).trans sumEmpty _ _

@[simp]

Depends on / 依赖: sumComm, sumEmpty
-/
def emptySum (α β) [IsEmpty α] : α oplus β ≃ β :=
(sumComm _ _).trans sumEmpty _ _

@[simp]
/--
theorem `emptySum_apply_inr` / 定理 `emptySum_apply_inr`

English:
theorem emptySum_apply_inr
  given: {α β} [IsEmpty α] (b : β)
  statement: emptySum α β (Sum.inr b) = b
  proof: rfl

中文:
定理 emptySum_apply_inr
  条件: {α β} [IsEmpty α] (b : β)
  结论: emptySum α β (Sum.inr b) = b
  证明: rfl

Depends on / 依赖: count_nth_of_infinite, infinite_setOfPred_prime
-/
theorem emptySum_apply_inr {α β} [IsEmpty α] (b : β) : emptySum α β (Sum.inr b) = b :=
  rfl

/--
Definition of `sumEquivSigmaBool` / `sumEquivSigmaBool` 的定义

English:
definition sumEquivSigmaBool
  signature: (α β)
  body: ⟨fun s => s.elim (fun x => ⟨false, x⟩) fun x => ⟨true, x⟩, fun s =>
    match s with
    | ⟨false, a⟩ => inl a
    | ⟨true, b⟩ => inr b,
    fun s => by cases s <;> rfl, fun s => by rcases s with ⟨_ | _, _⟩ <;> rfl⟩

中文:
定义 sumEquivSigmaBool
  签名: (α β)
  定义体: ⟨fun s => s.elim (fun x => ⟨false, x⟩) fun x => ⟨true, x⟩, fun s =>
    match s with
    | ⟨false, a⟩ => inl a
    | ⟨true, b⟩ => inr b,
    fun s => by cases s <;> rfl, fun s => by rcases s with ⟨_ | _, _⟩ <;> rfl⟩

Depends on / 依赖: s.elim
-/
def sumEquivSigmaBool (α β) : α oplus β ≃ Σ b, bif b then β else α :=
  ⟨fun s => s.elim (fun x => ⟨false, x⟩) fun x => ⟨true, x⟩, fun s =>
    match s with
    | ⟨false, a⟩ => inl a
    | ⟨true, b⟩ => inr b,
    fun s => by cases s <;> rfl, fun s => by rcases s with ⟨_ | _, _⟩ <;> rfl⟩

-- See also `Equiv.sigmaPreimageEquiv`.
/-- `sigmaFiberEquiv f` for `f : α → β` is the natural equivalence between
the type of all fibres of `f` and the total space `α`. -/
@[simps]
/--
Definition of `sigmaFiberEquiv` / `sigmaFiberEquiv` 的定义

English:
definition sigmaFiberEquiv
  signature: {α β : Type*} (f : α -> β)
  body: ⟨fun x => ↑x.2, fun x => ⟨f x, x, rfl⟩, fun ⟨_, _, rfl⟩ => rfl, fun _ => rfl⟩

中文:
定义 sigmaFiberEquiv
  签名: {α β : 类型} (f : α -> β)
  定义体: ⟨fun x => ↑x.2, fun x => ⟨f x, x, rfl⟩, fun ⟨_, _, rfl⟩ => rfl, fun _ => rfl⟩
-/
def sigmaFiberEquiv {α β : Type*} (f : α -> β) : (Σ y : β, { x // f x = y }) ≃ α :=
  ⟨fun x => ↑x.2, fun x => ⟨f x, x, rfl⟩, fun ⟨_, _, rfl⟩ => rfl, fun _ => rfl⟩

/--
Definition of `sigmaEquivOptionOfInhabited` / `sigmaEquivOptionOfInhabited` 的定义

English:
definition sigmaEquivOptionOfInhabited
  signature: (α : Type u) [Inhabited α] [DecidableEq α]
  body: {a // a != default}
  snd.toFun a := if h : a = default then none else some ⟨a, h⟩
  snd.invFun := Option.elim' default (↑)
  snd.left_inv a := by dsimp only; split_ifs <;> simp [*]
  snd.right_inv
    | none => by simp
    | some ⟨_, ha⟩ => dif_neg ha

中文:
定义 sigmaEquivOptionOfInhabited
  签名: (α : 类型u) [Inhabited α] [DecidableEq α]
  定义体: {a // a != default}
  snd.toFun a := if h : a = default then none else some ⟨a, h⟩
  snd.invFun := Option.elim' default (↑)
  snd.left_inv a := by dsimp only; split_ifs <;> simp [*]
  snd.right_inv
    | none => by simp
    | some ⟨_, ha⟩ => dif_neg ha
-/
def sigmaEquivOptionOfInhabited (α : Type u) [Inhabited α] [DecidableEq α] :
    Σ β : Type u, α ≃ Option β where
  fst := {a // a != default}
  snd.toFun a := if h : a = default then none else some ⟨a, h⟩
  snd.invFun := Option.elim' default (↑)
  snd.left_inv a := by dsimp only; split_ifs <;> simp [*]
  snd.right_inv
    | none => by simp
    | some ⟨_, ha⟩ => dif_neg ha

end

section sumCompl

/--
Definition of `sumCompl` / `sumCompl` 的定义

English:
definition sumCompl
  signature: {α : Type*} (p : α -> Prop) [DecidablePred p]
  body: Sum.elim Subtype.val Subtype.val
  invFun a := if h : p a then Sum.inl ⟨a, h⟩ else Sum.inr ⟨a, h⟩
  left_inv := by
    rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> dsimp
    · rw [dif_pos]
    · rw [dif_neg]
  right_inv a := by
    dsimp
    split_ifs <;> rfl

@[simp]

中文:
定义 sumCompl
  签名: {α : 类型} (p : α -> 命题) [DecidablePred p]
  定义体: Sum.elim Subtype.val Subtype.val
  invFun a := if h : p a then Sum.inl ⟨a, h⟩ else Sum.inr ⟨a, h⟩
  left_inv := by
    rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> dsimp
    · rw [dif_pos]
    · rw [dif_neg]
  right_inv a := by
    dsimp
    split_ifs <;> rfl

@[simp]

Depends on / 依赖: Subtype, Subtype.val, Sum.elim
-/
def sumCompl {α : Type*} (p : α -> Prop) [DecidablePred p] :
    { a // p a } oplus { a // ¬p a } ≃ α where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun a := if h : p a then Sum.inl ⟨a, h⟩ else Sum.inr ⟨a, h⟩
  left_inv := by
    rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> dsimp
    · rw [dif_pos]
    · rw [dif_neg]
  right_inv a := by
    dsimp
    split_ifs <;> rfl

@[simp]
/--
theorem `sumCompl_apply_inl` / 定理 `sumCompl_apply_inl`

English:
theorem sumCompl_apply_inl
  given: {α} {p : α -> Prop} [DecidablePred p] (x : { a // p a })
  proof: rfl

@[simp]

中文:
定理 sumCompl_apply_inl
  条件: {α} {p : α -> 命题} [DecidablePred p] (x : { a // p a })
  证明: rfl

@[simp]
-/
theorem sumCompl_apply_inl {α} {p : α -> Prop} [DecidablePred p] (x : { a // p a }) :
    sumCompl p (Sum.inl x) = x :=
  rfl

@[simp]
/--
theorem `sumCompl_apply_inr` / 定理 `sumCompl_apply_inr`

English:
theorem sumCompl_apply_inr
  given: {α} {p : α -> Prop} [DecidablePred p] (x : { a // ¬p a })
  proof: rfl

@[simp]

中文:
定理 sumCompl_apply_inr
  条件: {α} {p : α -> 命题} [DecidablePred p] (x : { a // ¬p a })
  证明: rfl

@[simp]
-/
theorem sumCompl_apply_inr {α} {p : α -> Prop} [DecidablePred p] (x : { a // ¬p a }) :
    sumCompl p (Sum.inr x) = x :=
  rfl

@[simp]
/--
theorem `sumCompl_symm_apply_of_pos` / 定理 `sumCompl_symm_apply_of_pos`

English:
theorem sumCompl_symm_apply_of_pos
  given: {α} {p : α -> Prop} [DecidablePred p] {a : α} (h : p a)
  proof: dif_pos h

@[simp]

中文:
定理 sumCompl_symm_apply_of_pos
  条件: {α} {p : α -> 命题} [DecidablePred p] {a : α} (h : p a)
  证明: dif_pos h

@[simp]

Depends on / 依赖: Nat.count_eq_zero, Nat.nth_prime_zero_eq_two, Nat.prime_two, count_eq_zero, dif_pos, nth_prime_zero_eq_two, primeCounting, prime_two
-/
theorem sumCompl_symm_apply_of_pos {α} {p : α -> Prop} [DecidablePred p] {a : α} (h : p a) :
    (sumCompl p).symm a = Sum.inl ⟨a, h⟩ :=
  dif_pos h

@[simp]
/--
theorem `sumCompl_symm_apply_of_neg` / 定理 `sumCompl_symm_apply_of_neg`

English:
theorem sumCompl_symm_apply_of_neg
  given: {α} {p : α -> Prop} [DecidablePred p] {a : α} (h : ¬p a)
  proof: dif_neg h

@[simp]

中文:
定理 sumCompl_symm_apply_of_neg
  条件: {α} {p : α -> 命题} [DecidablePred p] {a : α} (h : ¬p a)
  证明: dif_neg h

@[simp]

Depends on / 依赖: dif_neg
-/
theorem sumCompl_symm_apply_of_neg {α} {p : α -> Prop} [DecidablePred p] {a : α} (h : ¬p a) :
    (sumCompl p).symm a = Sum.inr ⟨a, h⟩ :=
  dif_neg h

@[simp]
/--
theorem `sumCompl_symm_apply_pos` / 定理 `sumCompl_symm_apply_pos`

English:
theorem sumCompl_symm_apply_pos
  given: {α} {p : α -> Prop} [DecidablePred p] (x : {x // p x})
  proof: sumCompl_symm_apply_of_pos x.2

@[simp]

中文:
定理 sumCompl_symm_apply_pos
  条件: {α} {p : α -> 命题} [DecidablePred p] (x : {x // p x})
  证明: sumCompl_symm_apply_of_pos x.2

@[simp]

Depends on / 依赖: sumCompl_symm_apply_of_pos
-/
theorem sumCompl_symm_apply_pos {α} {p : α -> Prop} [DecidablePred p] (x : {x // p x}) :
    (sumCompl p).symm x = Sum.inl x :=
  sumCompl_symm_apply_of_pos x.2

@[simp]
/--
theorem `sumCompl_symm_apply_neg` / 定理 `sumCompl_symm_apply_neg`

English:
theorem sumCompl_symm_apply_neg
  given: {α} {p : α -> Prop} [DecidablePred p] (x : {x // ¬ p x})
  proof: sumCompl_symm_apply_of_neg x.2

中文:
定理 sumCompl_symm_apply_neg
  条件: {α} {p : α -> 命题} [DecidablePred p] (x : {x // ¬ p x})
  证明: sumCompl_symm_apply_of_neg x.2

Depends on / 依赖: sumCompl_symm_apply_of_neg
-/
theorem sumCompl_symm_apply_neg {α} {p : α -> Prop} [DecidablePred p] (x : {x // ¬ p x}) :
    (sumCompl p).symm x = Sum.inr x :=
  sumCompl_symm_apply_of_neg x.2

end sumCompl

section

open Sum

/--
Definition of `prodSumDistrib` / `prodSumDistrib` 的定义

English:
definition prodSumDistrib
  signature: (α β γ)
  body: calc
    α × (β oplus γ) ≃ (β oplus γ) × α := prodComm _ _
    _ ≃ (β × α) oplus (γ × α) := sumProdDistrib _ _ _
    _ ≃ (α × β) oplus (α × γ) := sumCongr (prodComm _ _) (prodComm _ _)

@[simp]

中文:
定义 prodSumDistrib
  签名: (α β γ)
  定义体: calc
    α × (β oplus γ) ≃ (β oplus γ) × α := prodComm _ _
    _ ≃ (β × α) oplus (γ × α) := sumProdDistrib _ _ _
    _ ≃ (α × β) oplus (α × γ) := sumCongr (prodComm _ _) (prodComm _ _)

@[simp]

Depends on / 依赖: prodComm, sumCongr, sumProdDistrib
-/
def prodSumDistrib (α β γ) : α × (β oplus γ) ≃ (α × β) oplus (α × γ) :=
  calc
    α × (β oplus γ) ≃ (β oplus γ) × α := prodComm _ _
    _ ≃ (β × α) oplus (γ × α) := sumProdDistrib _ _ _
    _ ≃ (α × β) oplus (α × γ) := sumCongr (prodComm _ _) (prodComm _ _)

@[simp]
/--
theorem `prodSumDistrib_apply_left` / 定理 `prodSumDistrib_apply_left`

English:
theorem prodSumDistrib_apply_left
  given: {α β γ} (a : α) (b : β)
  proof: rfl

@[simp]

中文:
定理 prodSumDistrib_apply_left
  条件: {α β γ} (a : α) (b : β)
  证明: rfl

@[simp]
-/
theorem prodSumDistrib_apply_left {α β γ} (a : α) (b : β) :
    prodSumDistrib α β γ (a, Sum.inl b) = Sum.inl (a, b) :=
  rfl

@[simp]
/--
theorem `prodSumDistrib_apply_right` / 定理 `prodSumDistrib_apply_right`

English:
theorem prodSumDistrib_apply_right
  given: {α β γ} (a : α) (c : γ)
  proof: rfl

@[simp]

中文:
定理 prodSumDistrib_apply_right
  条件: {α β γ} (a : α) (c : γ)
  证明: rfl

@[simp]
-/
theorem prodSumDistrib_apply_right {α β γ} (a : α) (c : γ) :
    prodSumDistrib α β γ (a, Sum.inr c) = Sum.inr (a, c) :=
  rfl

@[simp]
/--
theorem `prodSumDistrib_symm_apply_left` / 定理 `prodSumDistrib_symm_apply_left`

English:
theorem prodSumDistrib_symm_apply_left
  given: {α β γ} (a : α × β)
  proof: rfl

@[simp]

中文:
定理 prodSumDistrib_symm_apply_left
  条件: {α β γ} (a : α × β)
  证明: rfl

@[simp]
-/
theorem prodSumDistrib_symm_apply_left {α β γ} (a : α × β) :
    (prodSumDistrib α β γ).symm (inl a) = (a.1, inl a.2) :=
  rfl

@[simp]
/--
theorem `prodSumDistrib_symm_apply_right` / 定理 `prodSumDistrib_symm_apply_right`

English:
theorem prodSumDistrib_symm_apply_right
  given: {α β γ} (a : α × γ)
  proof: rfl

中文:
定理 prodSumDistrib_symm_apply_right
  条件: {α β γ} (a : α × γ)
  证明: rfl
-/
theorem prodSumDistrib_symm_apply_right {α β γ} (a : α × γ) :
    (prodSumDistrib α β γ).symm (inr a) = (a.1, inr a.2) :=
  rfl

/-- An indexed sum of disjoint sums of types is equivalent to the sum of the indexed sums. Compare
with `Equiv.sumSigmaDistrib` which is indexed by sums. -/
@[simps]
/--
Definition of `sigmaSumDistrib` / `sigmaSumDistrib` 的定义

English:
definition sigmaSumDistrib
  signature: {ι} (α β : ι -> Type*)
  body: ⟨fun p => p.2.map (Sigma.mk p.1) (Sigma.mk p.1),
    Sum.elim (Sigma.map id fun _ => Sum.inl) (Sigma.map id fun _ => Sum.inr), fun p => by
    rcases p with ⟨i, a | b⟩ <;> rfl, fun p => by rcases p with (⟨i, a⟩ | ⟨i, b⟩) <;> rfl⟩

中文:
定义 sigmaSumDistrib
  签名: {ι} (α β : ι -> 类型)
  定义体: ⟨fun p => p.2.map (Sigma.mk p.1) (Sigma.mk p.1),
    Sum.elim (Sigma.map id fun _ => Sum.inl) (Sigma.map id fun _ => Sum.inr), fun p => by
    rcases p with ⟨i, a | b⟩ <;> rfl, fun p => by rcases p with (⟨i, a⟩ | ⟨i, b⟩) <;> rfl⟩

Depends on / 依赖: Sigma.map, Sigma.mk, Sum.elim, Sum.inl, Sum.inr
-/
def sigmaSumDistrib {ι} (α β : ι -> Type*) :
    (Σ i, α i oplus β i) ≃ (Σ i, α i) oplus (Σ i, β i) :=
  ⟨fun p => p.2.map (Sigma.mk p.1) (Sigma.mk p.1),
    Sum.elim (Sigma.map id fun _ => Sum.inl) (Sigma.map id fun _ => Sum.inr), fun p => by
    rcases p with ⟨i, a | b⟩ <;> rfl, fun p => by rcases p with (⟨i, a⟩ | ⟨i, b⟩) <;> rfl⟩

/-- A type indexed by disjoint sums of types is equivalent to the sum of the sums. Compare with
`Equiv.sigmaSumDistrib` which has the sums as the output type. -/
@[simps]
/--
Definition of `sumSigmaDistrib` / `sumSigmaDistrib` 的定义

English:
definition sumSigmaDistrib
  signature: {α β} (t : α oplus β -> Type*)
  body: ⟨(match · with
    | .mk (.inl x) y => .inl ⟨x, y⟩
    | .mk (.inr x) y => .inr ⟨x, y⟩),
  Sum.elim (fun a => ⟨.inl a.1, a.2⟩) (fun b => ⟨.inr b.1, b.2⟩),
  by rintro ⟨x|x,y⟩ <;> simp,
  by rintro (⟨x,y⟩|⟨x,y⟩) <;> simp⟩

中文:
定义 sumSigmaDistrib
  签名: {α β} (t : α oplus β -> 类型)
  定义体: ⟨(match · with
    | .mk (.inl x) y => .inl ⟨x, y⟩
    | .mk (.inr x) y => .inr ⟨x, y⟩),
  Sum.elim (fun a => ⟨.inl a.1, a.2⟩) (fun b => ⟨.inr b.1, b.2⟩),
  by rintro ⟨x|x,y⟩ <;> simp,
  by rintro (⟨x,y⟩|⟨x,y⟩) <;> simp⟩

Depends on / 依赖: Sum.elim
-/
def sumSigmaDistrib {α β} (t : α oplus β -> Type*) :
    (Σ i, t i) ≃ (Σ i, t (.inl i)) oplus (Σ i, t (.inr i)) :=
  ⟨(match · with
    | .mk (.inl x) y => .inl ⟨x, y⟩
    | .mk (.inr x) y => .inr ⟨x, y⟩),
  Sum.elim (fun a => ⟨.inl a.1, a.2⟩) (fun b => ⟨.inr b.1, b.2⟩),
  by rintro ⟨x|x,y⟩ <;> simp,
  by rintro (⟨x,y⟩|⟨x,y⟩) <;> simp⟩

end

end Equiv
