/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Attr.Register

/-!
# Monoids of endomorphisms, groups of automorphisms

This file defines
* the endomorphism monoid structure on `Function.End α := α → α`
* the endomorphism monoid structure on `Monoid.End M := M →* M` and `AddMonoid.End M := M →+ M`
* the automorphism group structure on `Equiv.Perm α := α ≃ α`
* the automorphism group structure on `MulAut M := M ≃* M` and `AddAut M := M ≃+ M`.

## Implementation notes

The definition of multiplication in the endomorphism monoids and automorphism groups agrees with
function composition, and multiplication in `CategoryTheory.End`, but not with
`CategoryTheory.comp`.

## Tags

end monoid, aut group
-/

@[expose] public section

assert_not_exists HeytingAlgebra MonoidWithZero MulAction RelIso

variable {A M G α β γ : Type*}

/-! ### Type endomorphisms -/

variable (α) in
/--
Definition of `Function.End` / `Function.End` 的定义

English:
definition Function.End
  body: α -> α

中文:
定义 Function.End
  定义体: α -> α
-/
protected def Function.End := α -> α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (Function.End α)
  body: id
  mul := (· ∘ ·)
  mul_assoc _ _ _ := rfl
  mul_one _ := rfl
  one_mul _ := rfl
  npow n f := f^[n]
  npow_succ _ _ := Function.iterate_succ _ _

中文:
实例 :
  签名: Monoid (Function.End α)
  定义体: id
  mul := (· ∘ ·)
  mul_assoc _ _ _ := rfl
  mul_one _ := rfl
  one_mul _ := rfl
  npow n f := f^[n]
  npow_succ _ _ := Function.iterate_succ _ _
-/
instance : Monoid (Function.End α) where
  one := id
  mul := (· ∘ ·)
  mul_assoc _ _ _ := rfl
  mul_one _ := rfl
  one_mul _ := rfl
  npow n f := f^[n]
  npow_succ _ _ := Function.iterate_succ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Function.End α)
  body: ⟨1⟩

中文:
实例 :
  签名: Inhabited (Function.End α)
  定义体: ⟨1⟩
-/
instance : Inhabited (Function.End α) := ⟨1⟩

/-! ### Monoid endomorphisms -/

namespace Equiv.Perm

attribute [to_additive_dont_translate] Perm Equiv

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (Perm α) where one
  body: Equiv.refl _

中文:
实例 instOne
  签名: : One (Perm α) where one
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
instance instOne : One (Perm α) where one := Equiv.refl _
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (Perm α) where mul f g
  body: Equiv.trans g f

中文:
实例 instMul
  签名: : Mul (Perm α) where mul f g
  定义体: Equiv.trans g f

Depends on / 依赖: Equiv.trans
-/
instance instMul : Mul (Perm α) where mul f g := Equiv.trans g f
/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: : Inv (Perm α) where inv
  body: Equiv.symm

中文:
实例 instInv
  签名: : Inv (Perm α) where inv
  定义体: Equiv.symm

Depends on / 依赖: Equiv.symm
-/
instance instInv : Inv (Perm α) where inv := Equiv.symm
/--
Instance `instPowNat` / 实例 `instPowNat`

English:
instance instPowNat
  signature: : Pow (Perm α) Nat where
  body: ⟨f^[n], f.symm^[n], f.left_inv.iterate _, f.right_inv.iterate _⟩

中文:
实例 instPowNat
  签名: : Pow (Perm α) 自然数 where
  定义体: ⟨f^[n], f.symm^[n], f.left_inv.iterate _, f.right_inv.iterate _⟩

Depends on / 依赖: f.left_inv.iterate, f.right_inv.iterate, f.symm, iterate, left_inv, right_inv
-/
instance instPowNat : Pow (Perm α) Nat where
  pow f n := ⟨f^[n], f.symm^[n], f.left_inv.iterate _, f.right_inv.iterate _⟩

/--
Instance `permGroup` / 实例 `permGroup`

English:
instance permGroup
  signature: : Group (Perm α) where
  body: (trans_assoc _ _ _).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm
  npow n f := f ^ n
npow_succ _ _ := coe_fn_injective Function.iterate_succ _ _
  zpow := zpowRec fun n f => f ^ n
zpow_succ' _ _ := coe_fn_injective Function.iterate_succ _ _

@[simp]

中文:
实例 permGroup
  签名: : Group (Perm α) where
  定义体: (trans_assoc _ _ _).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm
  npow n f := f ^ n
npow_succ _ _ := coe_fn_injective Function.iterate_succ _ _
  zpow := zpowRec fun n f => f ^ n
zpow_succ' _ _ := coe_fn_injective Function.iterate_succ _ _

@[simp]

Depends on / 依赖: trans_assoc
-/
instance permGroup : Group (Perm α) where
  mul_assoc _ _ _ := (trans_assoc _ _ _).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm
  npow n f := f ^ n
npow_succ _ _ := coe_fn_injective Function.iterate_succ _ _
  zpow := zpowRec fun n f => f ^ n
zpow_succ' _ _ := coe_fn_injective Function.iterate_succ _ _

@[simp]
/--
theorem `default_eq` / 定理 `default_eq`

English:
theorem default_eq
  statement: (default : Perm α) = 1
  proof: rfl

中文:
定理 default_eq
  结论: (default : Perm α) = 1
  证明: rfl
-/
theorem default_eq : (default : Perm α) = 1 :=
  rfl

/-- The permutation of a type is equivalent to the units group of the endomorphisms monoid of this
type. -/
@[simps]
/--
Definition of `equivUnitsEnd` / `equivUnitsEnd` 的定义

English:
definition equivUnitsEnd
  signature: : Perm α ≃* Units (Function.End α) where
  body: ⟨⇑e, ⇑e.symm, e.self_comp_symm, e.symm_comp_self⟩
  invFun u :=
    ⟨(u : Function.End α), (↑u⁻¹ : Function.End α), congr_fun u.inv_val, congr_fun u.val_inv⟩
  map_mul' _ _ := rfl

中文:
定义 equivUnitsEnd
  签名: : Perm α ≃* Units (Function.End α) where
  定义体: ⟨⇑e, ⇑e.symm, e.self_comp_symm, e.symm_comp_self⟩
  invFun u :=
    ⟨(u : Function.End α), (↑u⁻¹ : Function.End α), congr_fun u.inv_val, congr_fun u.val_inv⟩
  map_mul' _ _ := rfl

Depends on / 依赖: e.self_comp_symm, e.symm, e.symm_comp_self, self_comp_symm, symm_comp_self
-/
def equivUnitsEnd : Perm α ≃* Units (Function.End α) where
  toFun e := ⟨⇑e, ⇑e.symm, e.self_comp_symm, e.symm_comp_self⟩
  invFun u :=
    ⟨(u : Function.End α), (↑u⁻¹ : Function.End α), congr_fun u.inv_val, congr_fun u.val_inv⟩
  map_mul' _ _ := rfl

/-- Lift a monoid homomorphism `f : G →* Function.End α` to a monoid homomorphism
`f : G →* Equiv.Perm α`. -/
@[simps!]
/--
Definition of `_root_.MonoidHom.toHomPerm` / `_root_.MonoidHom.toHomPerm` 的定义

English:
definition _root_.MonoidHom.toHomPerm
  signature: {G : Type*} [Group G] (f : G ->* Function.End α)
  body: equivUnitsEnd.symm.toMonoidHom.comp f.toHomUnits

中文:
定义 _root_.MonoidHom.toHomPerm
  签名: {G : 类型} [Group G] (f : G ->* Function.End α)
  定义体: equivUnitsEnd.symm.toMonoidHom.comp f.toHomUnits

Depends on / 依赖: equivUnitsEnd, equivUnitsEnd.symm.toMonoidHom.comp, f.toHomUnits, toHomUnits, toMonoidHom
-/
def _root_.MonoidHom.toHomPerm {G : Type*} [Group G] (f : G ->* Function.End α) : G ->* Perm α :=
  equivUnitsEnd.symm.toMonoidHom.comp f.toHomUnits

/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (f g : Perm α) (x)
  statement: (f * g) x = f (g x)
  proof: rfl

中文:
定理 mul_apply
  条件: (f g : Perm α) (x)
  结论: (f * g) x = f (g x)
  证明: rfl
-/
theorem mul_apply (f g : Perm α) (x) : (f * g) x = f (g x) :=
  rfl

/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (x)
  statement: (1 : Perm α) x = x
  proof: rfl

@[pull_end, push_end← ]

中文:
定理 one_apply
  条件: (x)
  结论: (1 : Perm α) x = x
  证明: rfl

@[pull_end, push_end← ]
-/
theorem one_apply (x) : (1 : Perm α) x = x :=
  rfl

@[pull_end, push_end← ]
/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : Perm α) = Equiv.refl α
  proof: rfl

@[pull_end, push_end← ]

中文:
定理 one_def
  结论: (1 : Perm α) = Equiv.refl α
  证明: rfl

@[pull_end, push_end← ]
-/
theorem one_def : (1 : Perm α) = Equiv.refl α :=
  rfl

@[pull_end, push_end← ]
/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (f g : Perm α)
  statement: f * g = g.trans f
  proof: rfl

@[pull_end, push_end← ]

中文:
定理 mul_def
  条件: (f g : Perm α)
  结论: f * g = g.trans f
  证明: rfl

@[pull_end, push_end← ]
-/
theorem mul_def (f g : Perm α) : f * g = g.trans f :=
  rfl

@[pull_end, push_end← ]
/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  given: (f : Perm α)
  statement: f⁻¹ = f.symm
  proof: rfl

中文:
定理 inv_def
  条件: (f : Perm α)
  结论: f⁻¹ = f.symm
  证明: rfl
-/
theorem inv_def (f : Perm α) : f⁻¹ = f.symm :=
  rfl

/--
lemma `coe_inv` / 引理 `coe_inv`

English:
lemma coe_inv
  given: (f : Perm α)
  statement: ⇑f⁻¹ = ⇑f.symm
  proof: rfl

中文:
引理 coe_inv
  条件: (f : Perm α)
  结论: ⇑f⁻¹ = ⇑f.symm
  证明: rfl
-/
@[simp] lemma coe_inv (f : Perm α) : ⇑f⁻¹ = ⇑f.symm := rfl

/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ⇑(1 : Perm α) = id
  proof: rfl

中文:
引理 coe_one
  结论: ⇑(1 : Perm α) = id
  证明: rfl
-/
@[simp, norm_cast] lemma coe_one : ⇑(1 : Perm α) = id := rfl

/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (f g : Perm α)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

中文:
引理 coe_mul
  条件: (f g : Perm α)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mul (f g : Perm α) : ⇑(f * g) = f ∘ g := rfl

/--
lemma `coe_pow` / 引理 `coe_pow`

English:
lemma coe_pow
  given: (f : Perm α) (n : Nat)
  statement: ⇑(f ^ n) = f^[n]
  proof: rfl

@[pull_end← , push_end]

中文:
引理 coe_pow
  条件: (f : Perm α) (n : 自然数)
  结论: ⇑(f ^ n) = f^[n]
  证明: rfl

@[pull_end← , push_end]
-/
@[norm_cast] lemma coe_pow (f : Perm α) (n : Nat) : ⇑(f ^ n) = f^[n] := rfl

@[pull_end← , push_end]
/--
lemma `iterate_eq_pow` / 引理 `iterate_eq_pow`

English:
lemma iterate_eq_pow
  given: (f : Perm α) (n : Nat)
  statement: f^[n] = ⇑(f ^ n)
  proof: rfl

中文:
引理 iterate_eq_pow
  条件: (f : Perm α) (n : 自然数)
  结论: f^[n] = ⇑(f ^ n)
  证明: rfl
-/
lemma iterate_eq_pow (f : Perm α) (n : Nat) : f^[n] = ⇑(f ^ n) := rfl

/--
theorem `eq_inv_iff_eq` / 定理 `eq_inv_iff_eq`

English:
theorem eq_inv_iff_eq
  given: {f : Perm α} {x y : α}
  statement: x = f⁻¹ y ↔ f x = y
  proof: f.eq_symm_apply

中文:
定理 eq_inv_iff_eq
  条件: {f : Perm α} {x y : α}
  结论: x = f⁻¹ y ↔ f x = y
  证明: f.eq_symm_apply

Depends on / 依赖: eq_symm_apply, f.eq_symm_apply
-/
theorem eq_inv_iff_eq {f : Perm α} {x y : α} : x = f⁻¹ y ↔ f x = y :=
  f.eq_symm_apply

/--
theorem `inv_eq_iff_eq` / 定理 `inv_eq_iff_eq`

English:
theorem inv_eq_iff_eq
  given: {f : Perm α} {x y : α}
  statement: f⁻¹ x = y ↔ x = f y
  proof: f.symm_apply_eq

中文:
定理 inv_eq_iff_eq
  条件: {f : Perm α} {x y : α}
  结论: f⁻¹ x = y ↔ x = f y
  证明: f.symm_apply_eq

Depends on / 依赖: f.symm_apply_eq, symm_apply_eq
-/
theorem inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x = y ↔ x = f y :=
  f.symm_apply_eq

/--
theorem `zpow_apply_comm` / 定理 `zpow_apply_comm`

English:
theorem zpow_apply_comm
  given: {α : Type*} (σ : Perm α) (m n : Int) {x : α}
  proof: by
  rw [← Equiv.Perm.mul_apply]; rw [← Equiv.Perm.mul_apply]; rw [zpow_mul_comm]

中文:
定理 zpow_apply_comm
  条件: {α : 类型} (σ : Perm α) (m n : 整数) {x : α}
  证明: by
  rw [← Equiv.Perm.mul_apply]; rw [← Equiv.Perm.mul_apply]; rw [zpow_mul_comm]

Depends on / 依赖: Equiv.Perm.mul_apply, mul_apply, zpow_mul_comm
-/
theorem zpow_apply_comm {α : Type*} (σ : Perm α) (m n : Int) {x : α} :
    (σ ^ m) ((σ ^ n) x) = (σ ^ n) ((σ ^ m) x) := by
  rw [← Equiv.Perm.mul_apply]; rw [← Equiv.Perm.mul_apply]; rw [zpow_mul_comm]

/-! Lemmas about mixing `Perm` with `Equiv`. Because we have multiple ways to express
`Equiv.refl`, `Equiv.symm`, and `Equiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it after
simp. -/

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/--
theorem `trans_one` / 定理 `trans_one`

English:
theorem trans_one
  given: {α : Sort*} {β : Type*} (e : α ≃ β)
  statement: e.trans (1 : Perm β) = e
  proof: Equiv.trans_refl e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]

中文:
定理 trans_one
  条件: {α : Sort*} {β : 类型} (e : α ≃ β)
  结论: e.trans (1 : Perm β) = e
  证明: Equiv.trans_refl e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]

Depends on / 依赖: Equiv.trans_refl, trans_refl
-/
theorem trans_one {α : Sort*} {β : Type*} (e : α ≃ β) : e.trans (1 : Perm β) = e :=
  Equiv.trans_refl e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/--
theorem `mul_refl` / 定理 `mul_refl`

English:
theorem mul_refl
  given: (e : Perm α)
  statement: e * Equiv.refl α = e
  proof: Equiv.trans_refl e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]

中文:
定理 mul_refl
  条件: (e : Perm α)
  结论: e * Equiv.refl α = e
  证明: Equiv.trans_refl e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]

Depends on / 依赖: Equiv.trans_refl, trans_refl
-/
theorem mul_refl (e : Perm α) : e * Equiv.refl α = e :=
  Equiv.trans_refl e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/--
theorem `one_symm` / 定理 `one_symm`

English:
theorem one_symm
  statement: (1 : Perm α).symm = 1
  proof: rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]

中文:
定理 one_symm
  结论: (1 : Perm α).symm = 1
  证明: rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
-/
theorem one_symm : (1 : Perm α).symm = 1 :=
  rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/--
theorem `refl_inv` / 定理 `refl_inv`

English:
theorem refl_inv
  statement: (Equiv.refl α : Perm α)⁻¹ = 1
  proof: rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]

中文:
定理 refl_inv
  结论: (Equiv.refl α : Perm α)⁻¹ = 1
  证明: rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
-/
theorem refl_inv : (Equiv.refl α : Perm α)⁻¹ = 1 :=
  rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/--
theorem `one_trans` / 定理 `one_trans`

English:
theorem one_trans
  given: {α : Type*} {β : Sort*} (e : α ≃ β)
  statement: (1 : Perm α).trans e = e
  proof: rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]

中文:
定理 one_trans
  条件: {α : 类型} {β : Sort*} (e : α ≃ β)
  结论: (1 : Perm α).trans e = e
  证明: rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
-/
theorem one_trans {α : Type*} {β : Sort*} (e : α ≃ β) : (1 : Perm α).trans e = e :=
  rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/--
theorem `refl_mul` / 定理 `refl_mul`

English:
theorem refl_mul
  given: (e : Perm α)
  statement: Equiv.refl α * e = e
  proof: rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]

中文:
定理 refl_mul
  条件: (e : Perm α)
  结论: Equiv.refl α * e = e
  证明: rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
-/
theorem refl_mul (e : Perm α) : Equiv.refl α * e = e :=
  rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/--
theorem `inv_trans_self` / 定理 `inv_trans_self`

English:
theorem inv_trans_self
  given: (e : Perm α)
  statement: e⁻¹.trans e = 1
  proof: Equiv.symm_trans_self e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]

中文:
定理 inv_trans_self
  条件: (e : Perm α)
  结论: e⁻¹.trans e = 1
  证明: Equiv.symm_trans_self e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]

Depends on / 依赖: Equiv.symm_trans_self, symm_trans_self
-/
theorem inv_trans_self (e : Perm α) : e⁻¹.trans e = 1 :=
  Equiv.symm_trans_self e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/--
theorem `mul_symm` / 定理 `mul_symm`

English:
theorem mul_symm
  given: (e : Perm α)
  statement: e * e.symm = 1
  proof: Equiv.symm_trans_self e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]

中文:
定理 mul_symm
  条件: (e : Perm α)
  结论: e * e.symm = 1
  证明: Equiv.symm_trans_self e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]

Depends on / 依赖: Equiv.symm_trans_self, symm_trans_self
-/
theorem mul_symm (e : Perm α) : e * e.symm = 1 :=
  Equiv.symm_trans_self e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/--
theorem `self_trans_inv` / 定理 `self_trans_inv`

English:
theorem self_trans_inv
  given: (e : Perm α)
  statement: e.trans e⁻¹ = 1
  proof: Equiv.self_trans_symm e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]

中文:
定理 self_trans_inv
  条件: (e : Perm α)
  结论: e.trans e⁻¹ = 1
  证明: Equiv.self_trans_symm e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]

Depends on / 依赖: Equiv.self_trans_symm, self_trans_symm
-/
theorem self_trans_inv (e : Perm α) : e.trans e⁻¹ = 1 :=
  Equiv.self_trans_symm e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/--
theorem `symm_mul` / 定理 `symm_mul`

English:
theorem symm_mul
  given: (e : Perm α)
  statement: e.symm * e = 1
  proof: Equiv.self_trans_symm e

中文:
定理 symm_mul
  条件: (e : Perm α)
  结论: e.symm * e = 1
  证明: Equiv.self_trans_symm e

Depends on / 依赖: Equiv.self_trans_symm, self_trans_symm
-/
theorem symm_mul (e : Perm α) : e.symm * e = 1 :=
  Equiv.self_trans_symm e

/-! Lemmas about `Equiv.Perm.sumCongr` re-expressed via the group structure. -/


@[simp]
/--
theorem `sumCongr_mul` / 定理 `sumCongr_mul`

English:
theorem sumCongr_mul
  given: {α β : Type*} (e : Perm α) (f : Perm β) (g : Perm α) (h : Perm β)
  proof: sumCongr_trans g h e f

@[simp]

中文:
定理 sumCongr_mul
  条件: {α β : 类型} (e : Perm α) (f : Perm β) (g : Perm α) (h : Perm β)
  证明: sumCongr_trans g h e f

@[simp]

Depends on / 依赖: sumCongr_trans
-/
theorem sumCongr_mul {α β : Type*} (e : Perm α) (f : Perm β) (g : Perm α) (h : Perm β) :
    sumCongr e f * sumCongr g h = sumCongr (e * g) (f * h) :=
  sumCongr_trans g h e f

@[simp]
/--
theorem `sumCongr_inv` / 定理 `sumCongr_inv`

English:
theorem sumCongr_inv
  given: {α β : Type*} (e : Perm α) (f : Perm β)
  proof: rfl

@[simp]

中文:
定理 sumCongr_inv
  条件: {α β : 类型} (e : Perm α) (f : Perm β)
  证明: rfl

@[simp]
-/
theorem sumCongr_inv {α β : Type*} (e : Perm α) (f : Perm β) :
    (sumCongr e f)⁻¹ = sumCongr e⁻¹ f⁻¹ :=
  rfl

@[simp]
/--
theorem `sumCongr_one` / 定理 `sumCongr_one`

English:
theorem sumCongr_one
  given: {α β : Type*}
  statement: sumCongr (1 : Perm α) (1 : Perm β) = 1
  proof: sumCongr_refl

中文:
定理 sumCongr_one
  条件: {α β : 类型}
  结论: sumCongr (1 : Perm α) (1 : Perm β) = 1
  证明: sumCongr_refl

Depends on / 依赖: sumCongr_refl
-/
theorem sumCongr_one {α β : Type*} : sumCongr (1 : Perm α) (1 : Perm β) = 1 :=
  sumCongr_refl

/-- `Equiv.Perm.sumCongr` as a `MonoidHom`, with its two arguments bundled into a single `Prod`.

This is particularly useful for its `MonoidHom.range` projection, which is the subgroup of
permutations which do not exchange elements between `α` and `β`. -/
@[simps]
/--
Definition of `sumCongrHom` / `sumCongrHom` 的定义

English:
definition sumCongrHom
  signature: (α β : Type*)
  body: sumCongr a.1 a.2
  map_one' := sumCongr_one
  map_mul' _ _ := (sumCongr_mul _ _ _ _).symm

中文:
定义 sumCongrHom
  签名: (α β : 类型)
  定义体: sumCongr a.1 a.2
  map_one' := sumCongr_one
  map_mul' _ _ := (sumCongr_mul _ _ _ _).symm

Depends on / 依赖: sumCongr
-/
def sumCongrHom (α β : Type*) : Perm α × Perm β ->* Perm (α oplus β) where
  toFun a := sumCongr a.1 a.2
  map_one' := sumCongr_one
  map_mul' _ _ := (sumCongr_mul _ _ _ _).symm

/--
theorem `sumCongrHom_injective` / 定理 `sumCongrHom_injective`

English:
theorem sumCongrHom_injective
  given: {α β : Type*}
  statement: Function.Injective (sumCongrHom α β)
  proof: by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk_inj]
  constructor <;> ext i
  · simpa using Equiv.congr_fun h (Sum.inl i)
  · simpa using Equiv.congr_fun h (Sum.inr i)

@[simp]

中文:
定理 sumCongrHom_injective
  条件: {α β : 类型}
  结论: Function.Injective (sumCongrHom α β)
  证明: by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk_inj]
  constructor <;> ext i
  · simpa using Equiv.congr_fun h (Sum.inl i)
  · simpa using Equiv.congr_fun h (Sum.inr i)

@[simp]

Depends on / 依赖: Equiv.congr_fun, Prod.mk_inj, Sum.inl, Sum.inr, congr_fun, mk_inj
-/
theorem sumCongrHom_injective {α β : Type*} : Function.Injective (sumCongrHom α β) := by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk_inj]
  constructor <;> ext i
  · simpa using Equiv.congr_fun h (Sum.inl i)
  · simpa using Equiv.congr_fun h (Sum.inr i)

@[simp]
/--
theorem `sumCongr_swap_one` / 定理 `sumCongr_swap_one`

English:
theorem sumCongr_swap_one
  given: {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : α)
  proof: sumCongr_swap_refl i j

@[simp]

中文:
定理 sumCongr_swap_one
  条件: {α β : 类型} [DecidableEq α] [DecidableEq β] (i j : α)
  证明: sumCongr_swap_refl i j

@[simp]

Depends on / 依赖: sumCongr_swap_refl
-/
theorem sumCongr_swap_one {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : α) :
    sumCongr (Equiv.swap i j) (1 : Perm β) = Equiv.swap (Sum.inl i) (Sum.inl j) :=
  sumCongr_swap_refl i j

@[simp]
/--
theorem `sumCongr_one_swap` / 定理 `sumCongr_one_swap`

English:
theorem sumCongr_one_swap
  given: {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : β)
  proof: sumCongr_refl_swap i j

中文:
定理 sumCongr_one_swap
  条件: {α β : 类型} [DecidableEq α] [DecidableEq β] (i j : β)
  证明: sumCongr_refl_swap i j

Depends on / 依赖: sumCongr_refl_swap
-/
theorem sumCongr_one_swap {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : β) :
    sumCongr (1 : Perm α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) :=
  sumCongr_refl_swap i j

/-! Lemmas about `Equiv.Perm.sigmaCongrRight` re-expressed via the group structure. -/


@[simp]
/--
theorem `sigmaCongrRight_mul` / 定理 `sigmaCongrRight_mul`

English:
theorem sigmaCongrRight_mul
  statement: {α : Type*} {β : α -> Type*} (F : forall a, Perm (β a))
  proof: rfl

@[simp]

中文:
定理 sigmaCongrRight_mul
  结论: {α : 类型} {β : α -> 类型} (F : 对任意 a, Perm (β a))
  证明: rfl

@[simp]
-/
theorem sigmaCongrRight_mul {α : Type*} {β : α -> Type*} (F : forall a, Perm (β a))
    (G : forall a, Perm (β a)) : sigmaCongrRight F * sigmaCongrRight G = sigmaCongrRight (F * G) :=
  rfl

@[simp]
/--
theorem `sigmaCongrRight_inv` / 定理 `sigmaCongrRight_inv`

English:
theorem sigmaCongrRight_inv
  given: {α : Type*} {β : α -> Type*} (F : forall a, Perm (β a))
  proof: rfl

@[simp]

中文:
定理 sigmaCongrRight_inv
  条件: {α : 类型} {β : α -> 类型} (F : 对任意 a, Perm (β a))
  证明: rfl

@[simp]
-/
theorem sigmaCongrRight_inv {α : Type*} {β : α -> Type*} (F : forall a, Perm (β a)) :
    (sigmaCongrRight F)⁻¹ = sigmaCongrRight fun a => (F a)⁻¹ :=
  rfl

@[simp]
/--
theorem `sigmaCongrRight_one` / 定理 `sigmaCongrRight_one`

English:
theorem sigmaCongrRight_one
  given: {α : Type*} {β : α -> Type*}
  proof: rfl

中文:
定理 sigmaCongrRight_one
  条件: {α : 类型} {β : α -> 类型}
  证明: rfl
-/
theorem sigmaCongrRight_one {α : Type*} {β : α -> Type*} :
    sigmaCongrRight (1 : forall a, Equiv.Perm <| β a) = 1 :=
  rfl

/-- `Equiv.Perm.sigmaCongrRight` as a `MonoidHom`.

This is particularly useful for its `MonoidHom.range` projection, which is the subgroup of
permutations which do not exchange elements between fibers. -/
@[simps]
/--
Definition of `sigmaCongrRightHom` / `sigmaCongrRightHom` 的定义

English:
definition sigmaCongrRightHom
  signature: {α : Type*} (β : α -> Type*)
  body: sigmaCongrRight
  map_one' := sigmaCongrRight_one
  map_mul' _ _ := (sigmaCongrRight_mul _ _).symm

中文:
定义 sigmaCongrRightHom
  签名: {α : 类型} (β : α -> 类型)
  定义体: sigmaCongrRight
  map_one' := sigmaCongrRight_one
  map_mul' _ _ := (sigmaCongrRight_mul _ _).symm

Depends on / 依赖: sigmaCongrRight
-/
def sigmaCongrRightHom {α : Type*} (β : α -> Type*) : (forall a, Perm (β a)) ->* Perm (Σ a, β a) where
  toFun := sigmaCongrRight
  map_one' := sigmaCongrRight_one
  map_mul' _ _ := (sigmaCongrRight_mul _ _).symm

/--
theorem `sigmaCongrRightHom_injective` / 定理 `sigmaCongrRightHom_injective`

English:
theorem sigmaCongrRightHom_injective
  given: {α : Type*} {β : α -> Type*}
  proof: by
  intro x y h
  ext a b
  simpa using Equiv.congr_fun h ⟨a, b⟩

中文:
定理 sigmaCongrRightHom_injective
  条件: {α : 类型} {β : α -> 类型}
  证明: by
  intro x y h
  ext a b
  simpa using Equiv.congr_fun h ⟨a, b⟩

Depends on / 依赖: Equiv.congr_fun, congr_fun
-/
theorem sigmaCongrRightHom_injective {α : Type*} {β : α -> Type*} :
    Function.Injective (sigmaCongrRightHom β) := by
  intro x y h
  ext a b
  simpa using Equiv.congr_fun h ⟨a, b⟩

/-- `Equiv.Perm.subtypeCongr` as a `MonoidHom`. -/
@[simps]
/--
Definition of `subtypeCongrHom` / `subtypeCongrHom` 的定义

English:
definition subtypeCongrHom
  signature: (p : α -> Prop) [DecidablePred p]
  body: Perm.subtypeCongr pair.fst pair.snd
  map_one' := Perm.subtypeCongr.refl
  map_mul' _ _ := (Perm.subtypeCongr.trans _ _ _ _).symm

中文:
定义 subtypeCongrHom
  签名: (p : α -> 命题) [DecidablePred p]
  定义体: Perm.subtypeCongr pair.fst pair.snd
  map_one' := Perm.subtypeCongr.refl
  map_mul' _ _ := (Perm.subtypeCongr.trans _ _ _ _).symm

Depends on / 依赖: Perm.subtypeCongr, pair.fst, pair.snd, subtypeCongr
-/
def subtypeCongrHom (p : α -> Prop) [DecidablePred p] :
    Perm { a // p a } × Perm { a // ¬p a } ->* Perm α where
  toFun pair := Perm.subtypeCongr pair.fst pair.snd
  map_one' := Perm.subtypeCongr.refl
  map_mul' _ _ := (Perm.subtypeCongr.trans _ _ _ _).symm

/--
theorem `subtypeCongrHom_injective` / 定理 `subtypeCongrHom_injective`

English:
theorem subtypeCongrHom_injective
  given: (p : α -> Prop) [DecidablePred p]
  proof: by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk_inj]
  constructor <;> ext i <;> simpa using Equiv.congr_fun h i

中文:
定理 subtypeCongrHom_injective
  条件: (p : α -> 命题) [DecidablePred p]
  证明: by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk_inj]
  constructor <;> ext i <;> simpa using Equiv.congr_fun h i

Depends on / 依赖: Equiv.congr_fun, Prod.mk_inj, congr_fun, mk_inj
-/
theorem subtypeCongrHom_injective (p : α -> Prop) [DecidablePred p] :
    Function.Injective (subtypeCongrHom p) := by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk_inj]
  constructor <;> ext i <;> simpa using Equiv.congr_fun h i

/-- If `e` is also a permutation, we can write `permCongr`
completely in terms of the group structure. -/
@[simp]
/--
theorem `_root_.Equiv.permCongr_eq_mul` / 定理 `_root_.Equiv.permCongr_eq_mul`

English:
theorem _root_.Equiv.permCongr_eq_mul
  given: (e p : Perm α)
  statement: e.permCongr p = e * p * e⁻¹
  proof: rfl

@[simp]

中文:
定理 _root_.Equiv.permCongr_eq_mul
  条件: (e p : Perm α)
  结论: e.permCongr p = e * p * e⁻¹
  证明: rfl

@[simp]
-/
theorem _root_.Equiv.permCongr_eq_mul (e p : Perm α) : e.permCongr p = e * p * e⁻¹ :=
  rfl

@[simp]
/--
lemma `_root_.Equiv.permCongr_mul` / 引理 `_root_.Equiv.permCongr_mul`

English:
lemma _root_.Equiv.permCongr_mul
  given: (e : α ≃ β) (p q : Perm α)
  proof: .symm permCongr_trans e q p

中文:
引理 _root_.Equiv.permCongr_mul
  条件: (e : α ≃ β) (p q : Perm α)
  证明: .symm permCongr_trans e q p

Depends on / 依赖: permCongr_trans
-/
lemma _root_.Equiv.permCongr_mul (e : α ≃ β) (p q : Perm α) :
    e.permCongr (p * q) = e.permCongr p * e.permCongr q :=
.symm permCongr_trans e q p

/--
Definition of `_root_.Equiv.permCongrHom` / `_root_.Equiv.permCongrHom` 的定义

English:
definition _root_.Equiv.permCongrHom
  signature: (e : α ≃ β)
  body: e.permCongr
  map_mul' p q := e.permCongr_mul p q

中文:
定义 _root_.Equiv.permCongrHom
  签名: (e : α ≃ β)
  定义体: e.permCongr
  map_mul' p q := e.permCongr_mul p q

Depends on / 依赖: e.permCongr, mul_smul, one_smul, permCongr, smul_mk
-/
def _root_.Equiv.permCongrHom (e : α ≃ β) : Perm α ≃* Perm β where
  toEquiv := e.permCongr
  map_mul' p q := e.permCongr_mul p q

attribute [inherit_doc Equiv.permCongr] Equiv.permCongrHom
extend_docs Equiv.permCongrHom after "This is `Equiv.permCongr` as a `MulEquiv`."

@[simp]
/--
theorem `_root_.Equiv.permCongrHom_symm` / 定理 `_root_.Equiv.permCongrHom_symm`

English:
theorem _root_.Equiv.permCongrHom_symm
  given: (e : α ≃ β)
  proof: rfl

@[simp]

中文:
定理 _root_.Equiv.permCongrHom_symm
  条件: (e : α ≃ β)
  证明: rfl

@[simp]
-/
theorem _root_.Equiv.permCongrHom_symm (e : α ≃ β) :
    e.permCongrHom.symm = e.symm.permCongrHom :=
  rfl

@[simp]
/--
theorem `_root_.Equiv.permCongrHom_trans` / 定理 `_root_.Equiv.permCongrHom_trans`

English:
theorem _root_.Equiv.permCongrHom_trans
  given: (e : α ≃ β) (e' : β ≃ γ)
  proof: rfl

@[simp]

中文:
定理 _root_.Equiv.permCongrHom_trans
  条件: (e : α ≃ β) (e' : β ≃ γ)
  证明: rfl

@[simp]
-/
theorem _root_.Equiv.permCongrHom_trans (e : α ≃ β) (e' : β ≃ γ) :
    e.permCongrHom.trans e'.permCongrHom = (e.trans e').permCongrHom :=
  rfl

@[simp]
/--
lemma `_root_.Equiv.permCongrHom_coe_equiv` / 引理 `_root_.Equiv.permCongrHom_coe_equiv`

English:
lemma _root_.Equiv.permCongrHom_coe_equiv
  given: (e : α ≃ β)
  proof: rfl

@[simp]

中文:
引理 _root_.Equiv.permCongrHom_coe_equiv
  条件: (e : α ≃ β)
  证明: rfl

@[simp]
-/
lemma _root_.Equiv.permCongrHom_coe_equiv (e : α ≃ β) :
    (↑e.permCongrHom : Perm α ≃ Perm β) = e.permCongr :=
  rfl

@[simp]
/--
lemma `_root_.Equiv.permCongrHom_coe` / 引理 `_root_.Equiv.permCongrHom_coe`

English:
lemma _root_.Equiv.permCongrHom_coe
  given: (e : α ≃ β)
  statement: ⇑e.permCongrHom = ⇑e.permCongr
  proof: rfl

中文:
引理 _root_.Equiv.permCongrHom_coe
  条件: (e : α ≃ β)
  结论: ⇑e.permCongrHom = ⇑e.permCongr
  证明: rfl
-/
lemma _root_.Equiv.permCongrHom_coe (e : α ≃ β) : ⇑e.permCongrHom = ⇑e.permCongr :=
  rfl

section ExtendDomain

/-! Lemmas about `Equiv.Perm.extendDomain` re-expressed via the group structure. -/


variable (e : Perm α) {p : β -> Prop} [DecidablePred p] (f : α ≃ Subtype p)

@[simp]
/--
theorem `extendDomain_one` / 定理 `extendDomain_one`

English:
theorem extendDomain_one
  statement: extendDomain 1 f = 1
  proof: extendDomain_refl f

@[simp]

中文:
定理 extendDomain_one
  结论: extendDomain 1 f = 1
  证明: extendDomain_refl f

@[simp]

Depends on / 依赖: extendDomain_refl
-/
theorem extendDomain_one : extendDomain 1 f = 1 :=
  extendDomain_refl f

@[simp]
/--
theorem `extendDomain_inv` / 定理 `extendDomain_inv`

English:
theorem extendDomain_inv
  statement: (e.extendDomain f)⁻¹ = e⁻¹.extendDomain f
  proof: rfl

@[simp]

中文:
定理 extendDomain_inv
  结论: (e.extendDomain f)⁻¹ = e⁻¹.extendDomain f
  证明: rfl

@[simp]
-/
theorem extendDomain_inv : (e.extendDomain f)⁻¹ = e⁻¹.extendDomain f :=
  rfl

@[simp]
/--
theorem `extendDomain_mul` / 定理 `extendDomain_mul`

English:
theorem extendDomain_mul
  given: (e e' : Perm α)
  proof: extendDomain_trans _ _ _

中文:
定理 extendDomain_mul
  条件: (e e' : Perm α)
  证明: extendDomain_trans _ _ _

Depends on / 依赖: extendDomain_trans
-/
theorem extendDomain_mul (e e' : Perm α) :
    e.extendDomain f * e'.extendDomain f = (e * e').extendDomain f :=
  extendDomain_trans _ _ _

/-- `extendDomain` as a group homomorphism -/
@[simps]
/--
Definition of `extendDomainHom` / `extendDomainHom` 的定义

English:
definition extendDomainHom
  signature: : Perm α ->* Perm β where
  body: extendDomain e f
  map_one' := extendDomain_one f
  map_mul' e e' := (extendDomain_mul f e e').symm

中文:
定义 extendDomainHom
  签名: : Perm α ->* Perm β where
  定义体: extendDomain e f
  map_one' := extendDomain_one f
  map_mul' e e' := (extendDomain_mul f e e').symm

Depends on / 依赖: extendDomain
-/
def extendDomainHom : Perm α ->* Perm β where
  toFun e := extendDomain e f
  map_one' := extendDomain_one f
  map_mul' e e' := (extendDomain_mul f e e').symm

/--
theorem `extendDomainHom_injective` / 定理 `extendDomainHom_injective`

English:
theorem extendDomainHom_injective
  statement: Function.Injective (extendDomainHom f)
  proof: (injective_iff_map_eq_one (extendDomainHom f)).mpr fun e he =>
ext fun x => f.injective
      Subtype.ext ((extendDomain_apply_image e f x).symm.trans (Perm.ext_iff.mp he (f x)))

@[simp]

中文:
定理 extendDomainHom_injective
  结论: Function.Injective (extendDomainHom f)
  证明: (injective_iff_map_eq_one (extendDomainHom f)).mpr fun e he =>
ext fun x => f.injective
      Subtype.ext ((extendDomain_apply_image e f x).symm.trans (Perm.ext_iff.mp he (f x)))

@[simp]

Depends on / 依赖: Perm.ext_iff.mp, Subtype, Subtype.ext, ext_iff, extendDomainHom, extendDomain_apply_image, f.injective, injective, injective_iff_map_eq_one, symm.trans
-/
theorem extendDomainHom_injective : Function.Injective (extendDomainHom f) :=
  (injective_iff_map_eq_one (extendDomainHom f)).mpr fun e he =>
ext fun x => f.injective
      Subtype.ext ((extendDomain_apply_image e f x).symm.trans (Perm.ext_iff.mp he (f x)))

@[simp]
/--
theorem `extendDomain_eq_one_iff` / 定理 `extendDomain_eq_one_iff`

English:
theorem extendDomain_eq_one_iff
  given: {e : Perm α} {f : α ≃ Subtype p}
  statement: e.extendDomain f = 1 ↔ e = 1
  proof: (injective_iff_map_eq_one' (extendDomainHom f)).mp (extendDomainHom_injective f) e

@[simp]

中文:
定理 extendDomain_eq_one_iff
  条件: {e : Perm α} {f : α ≃ Subtype p}
  结论: e.extendDomain f = 1 ↔ e = 1
  证明: (injective_iff_map_eq_one' (extendDomainHom f)).mp (extendDomainHom_injective f) e

@[simp]

Depends on / 依赖: extendDomainHom, extendDomainHom_injective, injective_iff_map_eq_one
-/
theorem extendDomain_eq_one_iff {e : Perm α} {f : α ≃ Subtype p} : e.extendDomain f = 1 ↔ e = 1 :=
  (injective_iff_map_eq_one' (extendDomainHom f)).mp (extendDomainHom_injective f) e

@[simp]
/--
lemma `extendDomain_pow` / 引理 `extendDomain_pow`

English:
lemma extendDomain_pow
  given: (n : Nat)
  statement: (e ^ n).extendDomain f = e.extendDomain f ^ n
  proof: map_pow (extendDomainHom f) _ _

@[simp]

中文:
引理 extendDomain_pow
  条件: (n : 自然数)
  结论: (e ^ n).extendDomain f = e.extendDomain f ^ n
  证明: map_pow (extendDomainHom f) _ _

@[simp]

Depends on / 依赖: congr_arg, exacts, extendDomainHom, map_pow, mul_smul, one_smul
-/
lemma extendDomain_pow (n : Nat) : (e ^ n).extendDomain f = e.extendDomain f ^ n :=
  map_pow (extendDomainHom f) _ _

@[simp]
/--
lemma `extendDomain_zpow` / 引理 `extendDomain_zpow`

English:
lemma extendDomain_zpow
  given: (n : Int)
  statement: (e ^ n).extendDomain f = e.extendDomain f ^ n
  proof: map_zpow (extendDomainHom f) _ _

中文:
引理 extendDomain_zpow
  条件: (n : 整数)
  结论: (e ^ n).extendDomain f = e.extendDomain f ^ n
  证明: map_zpow (extendDomainHom f) _ _

Depends on / 依赖: extendDomainHom, map_zpow
-/
lemma extendDomain_zpow (n : Int) : (e ^ n).extendDomain f = e.extendDomain f ^ n :=
  map_zpow (extendDomainHom f) _ _

end ExtendDomain

section Subtype

variable {p : α -> Prop} {f : Perm α}

/--
Definition of `subtypePerm` / `subtypePerm` 的定义

English:
definition subtypePerm
  signature: (f : Perm α) (h : forall x, p (f x) ↔ p x)
  body: fun x => ⟨f x, (h _).2 x.2⟩
invFun := fun x => ⟨f⁻¹ x, (h (f⁻¹ x)).1 by simpa using x.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

@[simp]

中文:
定义 subtypePerm
  签名: (f : Perm α) (h : 对任意 x, p (f x) ↔ p x)
  定义体: fun x => ⟨f x, (h _).2 x.2⟩
invFun := fun x => ⟨f⁻¹ x, (h (f⁻¹ x)).1 by simpa using x.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

@[simp]
-/
def subtypePerm (f : Perm α) (h : forall x, p (f x) ↔ p x) : Perm { x // p x } where
  toFun := fun x => ⟨f x, (h _).2 x.2⟩
invFun := fun x => ⟨f⁻¹ x, (h (f⁻¹ x)).1 by simpa using x.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

@[simp]
/--
theorem `subtypePerm_apply` / 定理 `subtypePerm_apply`

English:
theorem subtypePerm_apply
  given: (f : Perm α) (h : forall x, p (f x) ↔ p x) (x : { x // p x })
  proof: rfl

@[simp]

中文:
定理 subtypePerm_apply
  条件: (f : Perm α) (h : 对任意 x, p (f x) ↔ p x) (x : { x // p x })
  证明: rfl

@[simp]
-/
theorem subtypePerm_apply (f : Perm α) (h : forall x, p (f x) ↔ p x) (x : { x // p x }) :
    subtypePerm f h x = ⟨f x, (h _).2 x.2⟩ :=
  rfl

@[simp]
/--
theorem `subtypePerm_one` / 定理 `subtypePerm_one`

English:
theorem subtypePerm_one
  given: (p : α -> Prop) (h := fun _ => Iff.rfl)
  statement: @subtypePerm α p 1 h = 1
  proof: rfl

@[simp]

中文:
定理 subtypePerm_one
  条件: (p : α -> 命题) (h := fun _ => Iff.rfl)
  结论: @subtypePerm α p 1 h = 1
  证明: rfl

@[simp]

Depends on / 依赖: Iff.rfl, subtypePerm
-/
theorem subtypePerm_one (p : α -> Prop) (h := fun _ => Iff.rfl) : @subtypePerm α p 1 h = 1 :=
  rfl

@[simp]
/--
theorem `subtypePerm_mul` / 定理 `subtypePerm_mul`

English:
theorem subtypePerm_mul
  given: (f g : Perm α) (hf hg)
  proof: rfl

中文:
定理 subtypePerm_mul
  条件: (f g : Perm α) (hf hg)
  证明: rfl
-/
theorem subtypePerm_mul (f g : Perm α) (hf hg) :
    (f.subtypePerm hf * g.subtypePerm hg : Perm { x // p x }) =
(f * g).subtypePerm fun _ => (hf _).trans hg _ :=
  rfl

set_option backward.privateInPublic true in
/--
theorem `inv_aux` / 定理 `inv_aux`

English:
theorem inv_aux
  statement: (forall x, p (f x) ↔ p x) ↔ forall x, p (f⁻¹ x) ↔ p x
  proof: f⁻¹.surjective.forall.trans by simp [Iff.comm]

中文:
定理 inv_aux
  结论: (对任意 x, p (f x) ↔ p x) ↔ 对任意 x, p (f⁻¹ x) ↔ p x
  证明: f⁻¹.surjective.forall.trans by simp [Iff.comm]
-/
private theorem inv_aux : (forall x, p (f x) ↔ p x) ↔ forall x, p (f⁻¹ x) ↔ p x :=
f⁻¹.surjective.forall.trans by simp [Iff.comm]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `subtypePerm_inv` / 定理 `subtypePerm_inv`

English:
theorem subtypePerm_inv
  given: (f : Perm α) (hf)
  proof: rfl

中文:
定理 subtypePerm_inv
  条件: (f : Perm α) (hf)
  证明: rfl
-/
theorem subtypePerm_inv (f : Perm α) (hf) :
    f⁻¹.subtypePerm hf = (f.subtypePerm <| inv_aux.2 hf : Perm { x // p x })⁻¹ :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- See `Equiv.Perm.subtypePerm_inv`. -/
@[simp]
/--
theorem `inv_subtypePerm` / 定理 `inv_subtypePerm`

English:
theorem inv_subtypePerm
  given: (f : Perm α) (hf)
  proof: rfl

中文:
定理 inv_subtypePerm
  条件: (f : Perm α) (hf)
  证明: rfl
-/
theorem inv_subtypePerm (f : Perm α) (hf) :
    (f.subtypePerm hf : Perm { x // p x })⁻¹ = f⁻¹.subtypePerm (inv_aux.1 hf) :=
  rfl

set_option backward.privateInPublic true in
/--
theorem `pow_aux` / 定理 `pow_aux`

English:
theorem pow_aux
  given: (hf : forall x, p (f x) ↔ p x)
  statement: forall {n : Nat} (x), p ((f ^ n) x) ↔ p x

中文:
定理 pow_aux
  条件: (hf : 对任意 x, p (f x) ↔ p x)
  结论: 对任意 {n : 自然数} (x), p ((f ^ n) x) ↔ p x
-/
private theorem pow_aux (hf : forall x, p (f x) ↔ p x) : forall {n : Nat} (x), p ((f ^ n) x) ↔ p x
  | 0, _ => Iff.rfl
  | _ + 1, _ => (pow_aux hf (f _)).trans (hf _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/--
theorem `subtypePerm_pow` / 定理 `subtypePerm_pow`

English:
theorem subtypePerm_pow
  given: (f : Perm α) (n : Nat) (hf)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [pow_succ', ih, subtypePerm_mul]

中文:
定理 subtypePerm_pow
  条件: (f : Perm α) (n : 自然数) (hf)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [pow_succ', ih, subtypePerm_mul]

Depends on / 依赖: pow_succ, simp_rw, subtypePerm_mul
-/
theorem subtypePerm_pow (f : Perm α) (n : Nat) (hf) :
    (f.subtypePerm hf : Perm { x // p x }) ^ n = (f ^ n).subtypePerm (pow_aux hf) := by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [pow_succ', ih, subtypePerm_mul]

set_option backward.privateInPublic true in
/--
theorem `zpow_aux` / 定理 `zpow_aux`

English:
theorem zpow_aux
  given: (hf : forall x, p (f x) ↔ p x)
  statement: forall {n : Int} (x), p ((f ^ n) x) ↔ p x

中文:
定理 zpow_aux
  条件: (hf : 对任意 x, p (f x) ↔ p x)
  结论: 对任意 {n : 整数} (x), p ((f ^ n) x) ↔ p x
-/
private theorem zpow_aux (hf : forall x, p (f x) ↔ p x) : forall {n : Int} (x), p ((f ^ n) x) ↔ p x
  | Int.ofNat _ => pow_aux hf
  | Int.negSucc n => by
    rw [zpow_negSucc]
    exact pow_aux (inv_aux.1 hf)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/--
theorem `subtypePerm_zpow` / 定理 `subtypePerm_zpow`

English:
theorem subtypePerm_zpow
  given: (f : Perm α) (n : Int) (hf)
  proof: by
  cases n with
  | ofNat n => exact subtypePerm_pow _ _ _
  | negSucc n => simp only [zpow_negSucc, subtypePerm_pow, subtypePerm_inv]

中文:
定理 subtypePerm_zpow
  条件: (f : Perm α) (n : 整数) (hf)
  证明: by
  cases n with
  | ofNat n => exact subtypePerm_pow _ _ _
  | negSucc n => simp only [zpow_negSucc, subtypePerm_pow, subtypePerm_inv]

Depends on / 依赖: negSucc, subtypePerm_inv, subtypePerm_pow, zpow_negSucc
-/
theorem subtypePerm_zpow (f : Perm α) (n : Int) (hf) :
    (f.subtypePerm hf ^ n : Perm { x // p x }) = (f ^ n).subtypePerm (zpow_aux hf) := by
  cases n with
  | ofNat n => exact subtypePerm_pow _ _ _
  | negSucc n => simp only [zpow_negSucc, subtypePerm_pow, subtypePerm_inv]

variable [DecidablePred p] {a : α}

/--
Definition of `ofSubtype` / `ofSubtype` 的定义

English:
definition ofSubtype
  signature: : Perm (Subtype p) ->* Perm α where
  body: extendDomain f (Equiv.refl (Subtype p))
  map_one' := Equiv.Perm.extendDomain_one _
  map_mul' f g := (Equiv.Perm.extendDomain_mul _ f g).symm

中文:
定义 ofSubtype
  签名: : Perm (Subtype p) ->* Perm α where
  定义体: extendDomain f (Equiv.refl (Subtype p))
  map_one' := Equiv.Perm.extendDomain_one _
  map_mul' f g := (Equiv.Perm.extendDomain_mul _ f g).symm

Depends on / 依赖: Equiv.refl, Subtype, extendDomain
-/
def ofSubtype : Perm (Subtype p) ->* Perm α where
  toFun f := extendDomain f (Equiv.refl (Subtype p))
  map_one' := Equiv.Perm.extendDomain_one _
  map_mul' f g := (Equiv.Perm.extendDomain_mul _ f g).symm

/--
theorem `ofSubtype_subtypePerm` / 定理 `ofSubtype_subtypePerm`

English:
theorem ofSubtype_subtypePerm
  given: {f : Perm α} (h₁ : forall x, p (f x) ↔ p x) (h₂ : forall x, f x != x -> p x)
  proof: Equiv.ext fun x => by
    by_cases hx : p x
    · exact (subtypePerm f h₁).extendDomain_apply_subtype _ hx
    · rw [ofSubtype, MonoidHom.coe_mk, OneHom.coe_mk,
        Equiv.Perm.extendDomain_apply_not_subtype _ _ hx]
      exact not_not.mp fun h => hx (h₂ x (Ne.symm h))

中文:
定理 ofSubtype_subtypePerm
  条件: {f : Perm α} (h₁ : 对任意 x, p (f x) ↔ p x) (h₂ : 对任意 x, f x != x -> p x)
  证明: Equiv.ext fun x => by
    by_cases hx : p x
    · exact (subtypePerm f h₁).extendDomain_apply_subtype _ hx
    · rw [ofSubtype, MonoidHom.coe_mk, OneHom.coe_mk,
        Equiv.Perm.extendDomain_apply_not_subtype _ _ hx]
      exact not_not.mp fun h => hx (h₂ x (Ne.symm h))

Depends on / 依赖: Equiv.Perm.extendDomain_apply_not_subtype, Equiv.ext, MonoidHom, MonoidHom.coe_mk, Ne.symm, OneHom, OneHom.coe_mk, coe_mk, extendDomain_apply_not_subtype, extendDomain_apply_subtype, not_not, not_not.mp, ofSubtype, subtypePerm
-/
theorem ofSubtype_subtypePerm {f : Perm α} (h₁ : forall x, p (f x) ↔ p x) (h₂ : forall x, f x != x -> p x) :
    ofSubtype (subtypePerm f h₁) = f :=
  Equiv.ext fun x => by
    by_cases hx : p x
    · exact (subtypePerm f h₁).extendDomain_apply_subtype _ hx
    · rw [ofSubtype, MonoidHom.coe_mk, OneHom.coe_mk,
        Equiv.Perm.extendDomain_apply_not_subtype _ _ hx]
      exact not_not.mp fun h => hx (h₂ x (Ne.symm h))

/--
theorem `ofSubtype_apply_of_mem` / 定理 `ofSubtype_apply_of_mem`

English:
theorem ofSubtype_apply_of_mem
  given: (f : Perm (Subtype p)) (ha : p a)
  statement: ofSubtype f a = f ⟨a, ha⟩
  proof: extendDomain_apply_subtype _ _ ha

@[simp]

中文:
定理 ofSubtype_apply_of_mem
  条件: (f : Perm (Subtype p)) (ha : p a)
  结论: ofSubtype f a = f ⟨a, ha⟩
  证明: extendDomain_apply_subtype _ _ ha

@[simp]

Depends on / 依赖: extendDomain_apply_subtype
-/
theorem ofSubtype_apply_of_mem (f : Perm (Subtype p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩ :=
  extendDomain_apply_subtype _ _ ha

@[simp]
/--
theorem `ofSubtype_apply_coe` / 定理 `ofSubtype_apply_coe`

English:
theorem ofSubtype_apply_coe
  given: (f : Perm (Subtype p)) (x : Subtype p)
  statement: ofSubtype f x = f x
  proof: Subtype.casesOn x fun _ => ofSubtype_apply_of_mem f

中文:
定理 ofSubtype_apply_coe
  条件: (f : Perm (Subtype p)) (x : Subtype p)
  结论: ofSubtype f x = f x
  证明: Subtype.casesOn x fun _ => ofSubtype_apply_of_mem f

Depends on / 依赖: Subtype, Subtype.casesOn, casesOn, ofSubtype_apply_of_mem
-/
theorem ofSubtype_apply_coe (f : Perm (Subtype p)) (x : Subtype p) : ofSubtype f x = f x :=
  Subtype.casesOn x fun _ => ofSubtype_apply_of_mem f

/--
theorem `ofSubtype_apply_of_not_mem` / 定理 `ofSubtype_apply_of_not_mem`

English:
theorem ofSubtype_apply_of_not_mem
  given: (f : Perm (Subtype p)) (ha : ¬p a)
  statement: ofSubtype f a = a
  proof: extendDomain_apply_not_subtype _ _ ha

中文:
定理 ofSubtype_apply_of_not_mem
  条件: (f : Perm (Subtype p)) (ha : ¬p a)
  结论: ofSubtype f a = a
  证明: extendDomain_apply_not_subtype _ _ ha

Depends on / 依赖: extendDomain_apply_not_subtype
-/
theorem ofSubtype_apply_of_not_mem (f : Perm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a :=
  extendDomain_apply_not_subtype _ _ ha

/--
theorem `ofSubtype_apply_mem_iff_mem` / 定理 `ofSubtype_apply_mem_iff_mem`

English:
theorem ofSubtype_apply_mem_iff_mem
  given: (f : Perm (Subtype p)) (x : α)
  proof: if h : p x then by
    simpa only [h, iff_true, MonoidHom.coe_mk, ofSubtype_apply_of_mem f h] using (f ⟨x, h⟩).2
  else by simp [h, ofSubtype_apply_of_not_mem f h]

中文:
定理 ofSubtype_apply_mem_iff_mem
  条件: (f : Perm (Subtype p)) (x : α)
  证明: if h : p x then by
    simpa only [h, iff_true, MonoidHom.coe_mk, ofSubtype_apply_of_mem f h] using (f ⟨x, h⟩).2
  else by simp [h, ofSubtype_apply_of_not_mem f h]

Depends on / 依赖: MonoidHom, MonoidHom.coe_mk, coe_mk, iff_true, ofSubtype_apply_of_mem, ofSubtype_apply_of_not_mem
-/
theorem ofSubtype_apply_mem_iff_mem (f : Perm (Subtype p)) (x : α) :
    p ((ofSubtype f : α -> α) x) ↔ p x :=
  if h : p x then by
    simpa only [h, iff_true, MonoidHom.coe_mk, ofSubtype_apply_of_mem f h] using (f ⟨x, h⟩).2
  else by simp [h, ofSubtype_apply_of_not_mem f h]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ofSubtype_injective` / 定理 `ofSubtype_injective`

English:
theorem ofSubtype_injective
  statement: Function.Injective (ofSubtype : Perm (Subtype p) -> Perm α)
  proof: by
  intro x y h
  rw [Perm.ext_iff] at h ⊢
  intro a
  specialize h a
  rwa [ofSubtype_apply_coe, ofSubtype_apply_coe, SetCoe.ext_iff] at h

@[simp]

中文:
定理 ofSubtype_injective
  结论: Function.Injective (ofSubtype : Perm (Subtype p) -> Perm α)
  证明: by
  intro x y h
  rw [Perm.ext_iff] at h ⊢
  intro a
  specialize h a
  rwa [ofSubtype_apply_coe, ofSubtype_apply_coe, SetCoe.ext_iff] at h

@[simp]

Depends on / 依赖: Perm.ext_iff, SetCoe, SetCoe.ext_iff, ext_iff, ofSubtype_apply_coe, specialize
-/
theorem ofSubtype_injective : Function.Injective (ofSubtype : Perm (Subtype p) -> Perm α) := by
  intro x y h
  rw [Perm.ext_iff] at h ⊢
  intro a
  specialize h a
  rwa [ofSubtype_apply_coe, ofSubtype_apply_coe, SetCoe.ext_iff] at h

@[simp]
/--
theorem `subtypePerm_ofSubtype` / 定理 `subtypePerm_ofSubtype`

English:
theorem subtypePerm_ofSubtype
  given: (f : Perm (Subtype p))
  proof: Equiv.ext fun x => Subtype.coe_injective (ofSubtype_apply_coe f x)

中文:
定理 subtypePerm_ofSubtype
  条件: (f : Perm (Subtype p))
  证明: Equiv.ext fun x => Subtype.coe_injective (ofSubtype_apply_coe f x)

Depends on / 依赖: Equiv.ext, Subtype, Subtype.coe_injective, coe_injective, ofSubtype_apply_coe
-/
theorem subtypePerm_ofSubtype (f : Perm (Subtype p)) :
    subtypePerm (ofSubtype f) (ofSubtype_apply_mem_iff_mem f) = f :=
  Equiv.ext fun x => Subtype.coe_injective (ofSubtype_apply_coe f x)

/--
theorem `ofSubtype_subtypePerm_of_mem` / 定理 `ofSubtype_subtypePerm_of_mem`

English:
theorem ofSubtype_subtypePerm_of_mem
  statement: {p : α -> Prop} [DecidablePred p]
  proof: ofSubtype_apply_of_mem (g.subtypePerm hg) ha

中文:
定理 ofSubtype_subtypePerm_of_mem
  结论: {p : α -> 命题} [DecidablePred p]
  证明: ofSubtype_apply_of_mem (g.subtypePerm hg) ha

Depends on / 依赖: g.subtypePerm, ofSubtype_apply_of_mem, smul_assoc, subtypePerm
-/
theorem ofSubtype_subtypePerm_of_mem {p : α -> Prop} [DecidablePred p]
    {g : Perm α} (hg : forall (x : α), p (g x) ↔ p x)
    {a : α} (ha : p a) : (ofSubtype (g.subtypePerm hg)) a = g a :=
  ofSubtype_apply_of_mem (g.subtypePerm hg) ha

/--
theorem `ofSubtype_subtypePerm_of_not_mem` / 定理 `ofSubtype_subtypePerm_of_not_mem`

English:
theorem ofSubtype_subtypePerm_of_not_mem
  statement: {p : α -> Prop} [DecidablePred p]
  proof: ofSubtype_apply_of_not_mem (g.subtypePerm hg) ha

中文:
定理 ofSubtype_subtypePerm_of_not_mem
  结论: {p : α -> 命题} [DecidablePred p]
  证明: ofSubtype_apply_of_not_mem (g.subtypePerm hg) ha

Depends on / 依赖: g.subtypePerm, ofSubtype_apply_of_not_mem, subtypePerm
-/
theorem ofSubtype_subtypePerm_of_not_mem {p : α -> Prop} [DecidablePred p]
    {g : Perm α} (hg : forall (x : α), p (g x) ↔ p x)
    {a : α} (ha : ¬ p a) : (ofSubtype (g.subtypePerm hg)) a = a :=
  ofSubtype_apply_of_not_mem (g.subtypePerm hg) ha

/-- Permutations on a subtype are equivalent to permutations on the original type that fix pointwise
the rest. -/
@[simps]
/--
Definition of `subtypeEquivSubtypePerm` / `subtypeEquivSubtypePerm` 的定义

English:
definition subtypeEquivSubtypePerm
  signature: (p : α -> Prop) [DecidablePred p]
  body: ⟨ofSubtype f, fun _ => f.ofSubtype_apply_of_not_mem⟩
  invFun f :=
    (f : Perm α).subtypePerm fun _ =>
      ⟨Decidable.not_imp_not.1 fun hfa => (f.prop _ hfa).symm ▸ hfa,
Decidable.not_imp_not.1 fun hfa ha => hfa f.val.injective (f.prop _ hfa).symm ▸ ha⟩
  left_inv := Equiv.Perm.subtypePerm_ofSub

中文:
定义 subtypeEquivSubtypePerm
  签名: (p : α -> 命题) [DecidablePred p]
  定义体: ⟨ofSubtype f, fun _ => f.ofSubtype_apply_of_not_mem⟩
  invFun f :=
    (f : Perm α).subtypePerm fun _ =>
      ⟨Decidable.not_imp_not.1 fun hfa => (f.prop _ hfa).symm ▸ hfa,
Decidable.not_imp_not.1 fun hfa ha => hfa f.val.injective (f.prop _ hfa).symm ▸ ha⟩
  left_inv := Equiv.Perm.subtypePerm_ofSub
-/
protected def subtypeEquivSubtypePerm (p : α -> Prop) [DecidablePred p] :
    Perm (Subtype p) ≃ { f : Perm α // forall a, ¬p a -> f a = a } where
  toFun f := ⟨ofSubtype f, fun _ => f.ofSubtype_apply_of_not_mem⟩
  invFun f :=
    (f : Perm α).subtypePerm fun _ =>
      ⟨Decidable.not_imp_not.1 fun hfa => (f.prop _ hfa).symm ▸ hfa,
Decidable.not_imp_not.1 fun hfa ha => hfa f.val.injective (f.prop _ hfa).symm ▸ ha⟩
  left_inv := Equiv.Perm.subtypePerm_ofSubtype
  right_inv f :=
    Subtype.ext ((Equiv.Perm.ofSubtype_subtypePerm _) fun a => Not.decidable_imp_symm <| f.prop a)

/--
theorem `subtypeEquivSubtypePerm_apply_of_mem` / 定理 `subtypeEquivSubtypePerm_apply_of_mem`

English:
theorem subtypeEquivSubtypePerm_apply_of_mem
  given: (f : Perm (Subtype p)) (h : p a)
  proof: f.ofSubtype_apply_of_mem h

中文:
定理 subtypeEquivSubtypePerm_apply_of_mem
  条件: (f : Perm (Subtype p)) (h : p a)
  证明: f.ofSubtype_apply_of_mem h

Depends on / 依赖: f.ofSubtype_apply_of_mem, ofSubtype_apply_of_mem
-/
theorem subtypeEquivSubtypePerm_apply_of_mem (f : Perm (Subtype p)) (h : p a) :
    (Perm.subtypeEquivSubtypePerm p f).1 a = f ⟨a, h⟩ :=
  f.ofSubtype_apply_of_mem h

/--
theorem `subtypeEquivSubtypePerm_apply_of_not_mem` / 定理 `subtypeEquivSubtypePerm_apply_of_not_mem`

English:
theorem subtypeEquivSubtypePerm_apply_of_not_mem
  given: (f : Perm (Subtype p)) (h : ¬p a)
  proof: f.ofSubtype_apply_of_not_mem h

中文:
定理 subtypeEquivSubtypePerm_apply_of_not_mem
  条件: (f : Perm (Subtype p)) (h : ¬p a)
  证明: f.ofSubtype_apply_of_not_mem h

Depends on / 依赖: f.ofSubtype_apply_of_not_mem, ofSubtype_apply_of_not_mem
-/
theorem subtypeEquivSubtypePerm_apply_of_not_mem (f : Perm (Subtype p)) (h : ¬p a) :
    ((Perm.subtypeEquivSubtypePerm p) f).1 a = a :=
  f.ofSubtype_apply_of_not_mem h

end Subtype

end Perm

section Swap

variable [DecidableEq α]

@[simp]
/--
theorem `swap_inv` / 定理 `swap_inv`

English:
theorem swap_inv
  given: (x y : α)
  statement: (swap x y)⁻¹ = swap x y
  proof: rfl

@[simp]

中文:
定理 swap_inv
  条件: (x y : α)
  结论: (swap x y)⁻¹ = swap x y
  证明: rfl

@[simp]
-/
theorem swap_inv (x y : α) : (swap x y)⁻¹ = swap x y :=
  rfl

@[simp]
/--
theorem `swap_mul_self` / 定理 `swap_mul_self`

English:
theorem swap_mul_self
  given: (i j : α)
  statement: swap i j * swap i j = 1
  proof: swap_swap i j

中文:
定理 swap_mul_self
  条件: (i j : α)
  结论: swap i j * swap i j = 1
  证明: swap_swap i j

Depends on / 依赖: swap_swap
-/
theorem swap_mul_self (i j : α) : swap i j * swap i j = 1 :=
  swap_swap i j

/--
theorem `swap_mul_eq_mul_swap` / 定理 `swap_mul_eq_mul_swap`

English:
theorem swap_mul_eq_mul_swap
  given: (f : Perm α) (x y : α)
  statement: swap x y * f = f * swap (f⁻¹ x) (f⁻¹ y)
  proof: Equiv.ext fun z => by
    simp only [Perm.mul_apply, swap_apply_def]; split_ifs <;> simp_all [eq_symm_apply]

中文:
定理 swap_mul_eq_mul_swap
  条件: (f : Perm α) (x y : α)
  结论: swap x y * f = f * swap (f⁻¹ x) (f⁻¹ y)
  证明: Equiv.ext fun z => by
    simp only [Perm.mul_apply, swap_apply_def]; split_ifs <;> simp_all [eq_symm_apply]

Depends on / 依赖: Equiv.ext, Perm.mul_apply, eq_symm_apply, mul_apply, split_ifs, swap_apply_def
-/
theorem swap_mul_eq_mul_swap (f : Perm α) (x y : α) : swap x y * f = f * swap (f⁻¹ x) (f⁻¹ y) :=
  Equiv.ext fun z => by
    simp only [Perm.mul_apply, swap_apply_def]; split_ifs <;> simp_all [eq_symm_apply]

/--
theorem `mul_swap_eq_swap_mul` / 定理 `mul_swap_eq_swap_mul`

English:
theorem mul_swap_eq_swap_mul
  given: (f : Perm α) (x y : α)
  statement: f * swap x y = swap (f x) (f y) * f
  proof: by
  simp [swap_mul_eq_mul_swap]

中文:
定理 mul_swap_eq_swap_mul
  条件: (f : Perm α) (x y : α)
  结论: f * swap x y = swap (f x) (f y) * f
  证明: by
  simp [swap_mul_eq_mul_swap]

Depends on / 依赖: swap_mul_eq_mul_swap
-/
theorem mul_swap_eq_swap_mul (f : Perm α) (x y : α) : f * swap x y = swap (f x) (f y) * f := by
  simp [swap_mul_eq_mul_swap]

/--
theorem `swap_apply_apply` / 定理 `swap_apply_apply`

English:
theorem swap_apply_apply
  given: (f : Perm α) (x y : α)
  statement: swap (f x) (f y) = f * swap x y * f⁻¹
  proof: by
  rw [mul_swap_eq_swap_mul]; rw [mul_inv_cancel_right]

中文:
定理 swap_apply_apply
  条件: (f : Perm α) (x y : α)
  结论: swap (f x) (f y) = f * swap x y * f⁻¹
  证明: by
  rw [mul_swap_eq_swap_mul]; rw [mul_inv_cancel_right]

Depends on / 依赖: mul_inv_cancel_right, mul_swap_eq_swap_mul
-/
theorem swap_apply_apply (f : Perm α) (x y : α) : swap (f x) (f y) = f * swap x y * f⁻¹ := by
  rw [mul_swap_eq_swap_mul]; rw [mul_inv_cancel_right]

/-- Left-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
/--
theorem `swap_mul_self_mul` / 定理 `swap_mul_self_mul`

English:
theorem swap_mul_self_mul
  given: (i j : α) (σ : Perm α)
  statement: Equiv.swap i j * (Equiv.swap i j * σ) = σ
  proof: by
  simp [← mul_assoc]

中文:
定理 swap_mul_self_mul
  条件: (i j : α) (σ : Perm α)
  结论: Equiv.swap i j * (Equiv.swap i j * σ) = σ
  证明: by
  simp [← mul_assoc]

Depends on / 依赖: mul_assoc
-/
theorem swap_mul_self_mul (i j : α) (σ : Perm α) : Equiv.swap i j * (Equiv.swap i j * σ) = σ := by
  simp [← mul_assoc]

/-- Right-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
/--
theorem `mul_swap_mul_self` / 定理 `mul_swap_mul_self`

English:
theorem mul_swap_mul_self
  given: (i j : α) (σ : Perm α)
  statement: σ * Equiv.swap i j * Equiv.swap i j = σ
  proof: by
  rw [mul_assoc]; rw [swap_mul_self]; rw [mul_one]

中文:
定理 mul_swap_mul_self
  条件: (i j : α) (σ : Perm α)
  结论: σ * Equiv.swap i j * Equiv.swap i j = σ
  证明: by
  rw [mul_assoc]; rw [swap_mul_self]; rw [mul_one]

Depends on / 依赖: mul_assoc, mul_one, swap_mul_self
-/
theorem mul_swap_mul_self (i j : α) (σ : Perm α) : σ * Equiv.swap i j * Equiv.swap i j = σ := by
  rw [mul_assoc]; rw [swap_mul_self]; rw [mul_one]

/-- A stronger version of `mul_right_injective` -/
@[simp]
/--
theorem `swap_mul_involutive` / 定理 `swap_mul_involutive`

English:
theorem swap_mul_involutive
  given: (i j : α)
  statement: Function.Involutive (Equiv.swap i j * ·)
  proof: swap_mul_self_mul i j

中文:
定理 swap_mul_involutive
  条件: (i j : α)
  结论: Function.Involutive (Equiv.swap i j * ·)
  证明: swap_mul_self_mul i j

Depends on / 依赖: swap_mul_self_mul
-/
theorem swap_mul_involutive (i j : α) : Function.Involutive (Equiv.swap i j * ·) :=
  swap_mul_self_mul i j

/-- A stronger version of `mul_left_injective` -/
@[simp]
/--
theorem `mul_swap_involutive` / 定理 `mul_swap_involutive`

English:
theorem mul_swap_involutive
  given: (i j : α)
  statement: Function.Involutive (· * Equiv.swap i j)
  proof: mul_swap_mul_self i j

@[simp]

中文:
定理 mul_swap_involutive
  条件: (i j : α)
  结论: Function.Involutive (· * Equiv.swap i j)
  证明: mul_swap_mul_self i j

@[simp]

Depends on / 依赖: mul_swap_mul_self
-/
theorem mul_swap_involutive (i j : α) : Function.Involutive (· * Equiv.swap i j) :=
  mul_swap_mul_self i j

@[simp]
/--
theorem `swap_eq_one_iff` / 定理 `swap_eq_one_iff`

English:
theorem swap_eq_one_iff
  given: {i j : α}
  statement: swap i j = (1 : Perm α) ↔ i = j
  proof: swap_eq_refl_iff

中文:
定理 swap_eq_one_iff
  条件: {i j : α}
  结论: swap i j = (1 : Perm α) ↔ i = j
  证明: swap_eq_refl_iff

Depends on / 依赖: swap_eq_refl_iff
-/
theorem swap_eq_one_iff {i j : α} : swap i j = (1 : Perm α) ↔ i = j :=
  swap_eq_refl_iff

/--
theorem `swap_mul_eq_iff` / 定理 `swap_mul_eq_iff`

English:
theorem swap_mul_eq_iff
  given: {i j : α} {σ : Perm α}
  statement: swap i j * σ = σ ↔ i = j
  proof: by
  rw [mul_eq_right]; rw [swap_eq_one_iff]

中文:
定理 swap_mul_eq_iff
  条件: {i j : α} {σ : Perm α}
  结论: swap i j * σ = σ ↔ i = j
  证明: by
  rw [mul_eq_right]; rw [swap_eq_one_iff]

Depends on / 依赖: mul_eq_right, swap_eq_one_iff
-/
theorem swap_mul_eq_iff {i j : α} {σ : Perm α} : swap i j * σ = σ ↔ i = j := by
  rw [mul_eq_right]; rw [swap_eq_one_iff]

/--
theorem `mul_swap_eq_iff` / 定理 `mul_swap_eq_iff`

English:
theorem mul_swap_eq_iff
  given: {i j : α} {σ : Perm α}
  statement: σ * swap i j = σ ↔ i = j
  proof: by
  rw [mul_eq_left]; rw [swap_eq_one_iff]

中文:
定理 mul_swap_eq_iff
  条件: {i j : α} {σ : Perm α}
  结论: σ * swap i j = σ ↔ i = j
  证明: by
  rw [mul_eq_left]; rw [swap_eq_one_iff]

Depends on / 依赖: mul_eq_left, swap_eq_one_iff
-/
theorem mul_swap_eq_iff {i j : α} {σ : Perm α} : σ * swap i j = σ ↔ i = j := by
  rw [mul_eq_left]; rw [swap_eq_one_iff]

/--
theorem `swap_mul_swap_mul_swap` / 定理 `swap_mul_swap_mul_swap`

English:
theorem swap_mul_swap_mul_swap
  given: {x y z : α} (hxy : x != y) (hxz : x != z)
  proof: by
  nth_rewrite 3 [← swap_inv]
  rw [← swap_apply_apply]; rw [swap_apply_left]; rw [swap_apply_of_ne_of_ne hxy hxz]; rw [swap_comm]

中文:
定理 swap_mul_swap_mul_swap
  条件: {x y z : α} (hxy : x != y) (hxz : x != z)
  证明: by
  nth_rewrite 3 [← swap_inv]
  rw [← swap_apply_apply]; rw [swap_apply_left]; rw [swap_apply_of_ne_of_ne hxy hxz]; rw [swap_comm]

Depends on / 依赖: nth_rewrite, swap_apply_apply, swap_apply_left, swap_apply_of_ne_of_ne, swap_comm, swap_inv
-/
theorem swap_mul_swap_mul_swap {x y z : α} (hxy : x != y) (hxz : x != z) :
    swap y z * swap x y * swap y z = swap z x := by
  nth_rewrite 3 [← swap_inv]
  rw [← swap_apply_apply]; rw [swap_apply_left]; rw [swap_apply_of_ne_of_ne hxy hxz]; rw [swap_comm]

end Swap

section Group
variable [Group α] (a b : α)

@[to_additive (attr := simp)]
/--
lemma `mulLeft_one` / 引理 `mulLeft_one`

English:
lemma mulLeft_one
  statement: Equiv.mulLeft (1 : α) = 1
  proof: ext one_mul

@[to_additive (attr := simp)]

中文:
引理 mulLeft_one
  结论: Equiv.mulLeft (1 : α) = 1
  证明: ext one_mul

@[to_additive (attr := simp)]

Depends on / 依赖: one_mul
-/
lemma mulLeft_one : Equiv.mulLeft (1 : α) = 1 := ext one_mul

@[to_additive (attr := simp)]
/--
lemma `mulRight_one` / 引理 `mulRight_one`

English:
lemma mulRight_one
  statement: Equiv.mulRight (1 : α) = 1
  proof: ext mul_one

@[to_additive (attr := simp)]

中文:
引理 mulRight_one
  结论: Equiv.mulRight (1 : α) = 1
  证明: ext mul_one

@[to_additive (attr := simp)]

Depends on / 依赖: mul_one
-/
lemma mulRight_one : Equiv.mulRight (1 : α) = 1 := ext mul_one

@[to_additive (attr := simp)]
/--
lemma `mulLeft_mul` / 引理 `mulLeft_mul`

English:
lemma mulLeft_mul
  statement: Equiv.mulLeft (a * b) = Equiv.mulLeft a * Equiv.mulLeft b
  proof: ext mul_assoc _ _

@[to_additive (attr := simp)]

中文:
引理 mulLeft_mul
  结论: Equiv.mulLeft (a * b) = Equiv.mulLeft a * Equiv.mulLeft b
  证明: ext mul_assoc _ _

@[to_additive (attr := simp)]

Depends on / 依赖: mul_assoc
-/
lemma mulLeft_mul : Equiv.mulLeft (a * b) = Equiv.mulLeft a * Equiv.mulLeft b :=
ext mul_assoc _ _

@[to_additive (attr := simp)]
/--
lemma `mulRight_mul` / 引理 `mulRight_mul`

English:
lemma mulRight_mul
  statement: Equiv.mulRight (a * b) = Equiv.mulRight b * Equiv.mulRight a
  proof: ext fun _ => (mul_assoc _ _ _).symm

@[to_additive (attr := simp)]

中文:
引理 mulRight_mul
  结论: Equiv.mulRight (a * b) = Equiv.mulRight b * Equiv.mulRight a
  证明: ext fun _ => (mul_assoc _ _ _).symm

@[to_additive (attr := simp)]

Depends on / 依赖: mul_assoc
-/
lemma mulRight_mul : Equiv.mulRight (a * b) = Equiv.mulRight b * Equiv.mulRight a :=
  ext fun _ => (mul_assoc _ _ _).symm

@[to_additive (attr := simp)]
/--
lemma `inv_mulLeft` / 引理 `inv_mulLeft`

English:
lemma inv_mulLeft
  statement: (Equiv.mulLeft a)⁻¹ = Equiv.mulLeft a⁻¹
  proof: Equiv.coe_inj.1 rfl

@[to_additive (attr := simp)]

中文:
引理 inv_mulLeft
  结论: (Equiv.mulLeft a)⁻¹ = Equiv.mulLeft a⁻¹
  证明: Equiv.coe_inj.1 rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.coe_inj, coe_inj
-/
lemma inv_mulLeft : (Equiv.mulLeft a)⁻¹ = Equiv.mulLeft a⁻¹ := Equiv.coe_inj.1 rfl

@[to_additive (attr := simp)]
/--
lemma `inv_mulRight` / 引理 `inv_mulRight`

English:
lemma inv_mulRight
  statement: (Equiv.mulRight a)⁻¹ = Equiv.mulRight a⁻¹
  proof: Equiv.coe_inj.1 rfl

@[to_additive (attr := simp)]

中文:
引理 inv_mulRight
  结论: (Equiv.mulRight a)⁻¹ = Equiv.mulRight a⁻¹
  证明: Equiv.coe_inj.1 rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.coe_inj, coe_inj
-/
lemma inv_mulRight : (Equiv.mulRight a)⁻¹ = Equiv.mulRight a⁻¹ := Equiv.coe_inj.1 rfl

@[to_additive (attr := simp)]
/--
lemma `pow_mulLeft` / 引理 `pow_mulLeft`

English:
lemma pow_mulLeft
  given: (n : Nat)
  statement: Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n)
  proof: by
  ext; simp [Perm.coe_pow]

@[to_additive (attr := simp)]

中文:
引理 pow_mulLeft
  条件: (n : 自然数)
  结论: Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n)
  证明: by
  ext; simp [Perm.coe_pow]

@[to_additive (attr := simp)]

Depends on / 依赖: Perm.coe_pow, coe_pow
-/
lemma pow_mulLeft (n : Nat) : Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n) := by
  ext; simp [Perm.coe_pow]

@[to_additive (attr := simp)]
/--
lemma `pow_mulRight` / 引理 `pow_mulRight`

English:
lemma pow_mulRight
  given: (n : Nat)
  statement: Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n)
  proof: by
  ext; simp [Perm.coe_pow]

@[to_additive (attr := simp)]

中文:
引理 pow_mulRight
  条件: (n : 自然数)
  结论: Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n)
  证明: by
  ext; simp [Perm.coe_pow]

@[to_additive (attr := simp)]

Depends on / 依赖: Perm.coe_pow, coe_pow
-/
lemma pow_mulRight (n : Nat) : Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n) := by
  ext; simp [Perm.coe_pow]

@[to_additive (attr := simp)]
/--
lemma `zpow_mulLeft` / 引理 `zpow_mulLeft`

English:
lemma zpow_mulLeft
  statement: forall n : Int, Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n)

中文:
引理 zpow_mulLeft
  结论: 对任意 n : 整数, Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n)
-/
lemma zpow_mulLeft : forall n : Int, Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n)
  | Int.ofNat n => by simp
  | Int.negSucc n => by simp

@[to_additive (attr := simp)]
/--
lemma `zpow_mulRight` / 引理 `zpow_mulRight`

English:
lemma zpow_mulRight
  statement: forall n : Int, Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n)

中文:
引理 zpow_mulRight
  结论: 对任意 n : 整数, Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n)
-/
lemma zpow_mulRight : forall n : Int, Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n)
  | Int.ofNat n => by simp
  | Int.negSucc n => by simp

end Group
end Equiv

/-- The group of multiplicative automorphisms. -/
@[to_additive /-- The group of additive automorphisms. -/]
/--
Definition of `MulAut` / `MulAut` 的定义

English:
abbreviation MulAut
  signature: (M : Type*) [Mul M]
  body: M ≃* M

中文:
缩写 MulAut
  签名: (M : 类型) [Mul M]
  定义体: M ≃* M
-/
abbrev MulAut (M : Type*) [Mul M] :=
  M ≃* M

namespace MulAut

variable (M) [Mul M]

/-- If `M` is a type with multiplicative, then multiplicative automorphisms of `M` have the
structure of a group. -/
@[to_additive /-- If `M` is a type with addition, then additive automorphisms of `M` have the
/--
Definition of `of` / `of` 的定义

English:
structure of
  parameters: a group.
  (no additional axioms)

中文:
结构 of
  参数: a group.
  (无附加公理)
-/
structure of a group.

We give `AddAut M` the structure of an additive group rather than a multiplicative group to help
with `to_additive` translation. Without this, any proof in group theory making use of the
conjugation action `G →* MulAut G` would be impossible to `to_additive`-ize because a correct
additivization would require inserting `Additive` around `AddAut G` and dealing with these extra
`Additive`s in the proof, but `to_additive` is unable to do this automatically. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (MulAut M)
  body: MulEquiv.trans h g
  one := MulEquiv.refl _
  inv := MulEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := MulEquiv.self_trans_symm

@[to_additive]

中文:
实例 :
  签名: Group (MulAut M)
  定义体: MulEquiv.trans h g
  one := MulEquiv.refl _
  inv := MulEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := MulEquiv.self_trans_symm

@[to_additive]

Depends on / 依赖: MulEquiv, MulEquiv.trans
-/
instance : Group (MulAut M) where
  mul g h := MulEquiv.trans h g
  one := MulEquiv.refl _
  inv := MulEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := MulEquiv.self_trans_symm

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (MulAut M)
  body: ⟨1⟩

@[to_additive (attr := simp)]

中文:
实例 :
  签名: Inhabited (MulAut M)
  定义体: ⟨1⟩

@[to_additive (attr := simp)]
-/
instance : Inhabited (MulAut M) :=
  ⟨1⟩

@[to_additive (attr := simp)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (e₁ e₂ : MulAut M)
  statement: ⇑(e₁ * e₂) = e₁ ∘ e₂
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mul
  条件: (e₁ e₂ : MulAut M)
  结论: ⇑(e₁ * e₂) = e₁ ∘ e₂
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mul (e₁ e₂ : MulAut M) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : MulAut M) = id
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_one
  结论: ⇑(1 : MulAut M) = id
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_one : ⇑(1 : MulAut M) = id :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (e : MulAut M)
  statement: ⇑e⁻¹ = e.symm
  proof: rfl

@[to_additive]

中文:
定理 coe_inv
  条件: (e : MulAut M)
  结论: ⇑e⁻¹ = e.symm
  证明: rfl

@[to_additive]
-/
theorem coe_inv (e : MulAut M) : ⇑e⁻¹ = e.symm := rfl

@[to_additive]
/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (e₁ e₂ : MulAut M)
  statement: e₁ * e₂ = e₂.trans e₁
  proof: rfl

@[to_additive]

中文:
定理 mul_def
  条件: (e₁ e₂ : MulAut M)
  结论: e₁ * e₂ = e₂.trans e₁
  证明: rfl

@[to_additive]
-/
theorem mul_def (e₁ e₂ : MulAut M) : e₁ * e₂ = e₂.trans e₁ :=
  rfl

@[to_additive]
/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : MulAut M) = MulEquiv.refl _
  proof: rfl

@[to_additive]

中文:
定理 one_def
  结论: (1 : MulAut M) = MulEquiv.refl _
  证明: rfl

@[to_additive]
-/
theorem one_def : (1 : MulAut M) = MulEquiv.refl _ :=
  rfl

@[to_additive]
/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  given: (e₁ : MulAut M)
  statement: e₁⁻¹ = e₁.symm
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inv_def
  条件: (e₁ : MulAut M)
  结论: e₁⁻¹ = e₁.symm
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inv_def (e₁ : MulAut M) : e₁⁻¹ = e₁.symm :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `inv_symm` / 定理 `inv_symm`

English:
theorem inv_symm
  given: (e : MulAut M)
  statement: e⁻¹.symm = e
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inv_symm
  条件: (e : MulAut M)
  结论: e⁻¹.symm = e
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inv_symm (e : MulAut M) : e⁻¹.symm = e := rfl

@[to_additive (attr := simp)]
/--
theorem `symm_inv` / 定理 `symm_inv`

English:
theorem symm_inv
  given: (e : MulAut M)
  statement: (e.symm)⁻¹ = e
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 symm_inv
  条件: (e : MulAut M)
  结论: (e.symm)⁻¹ = e
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem symm_inv (e : MulAut M) : (e.symm)⁻¹ = e := rfl

@[to_additive (attr := simp)]
/--
theorem `inv_apply` / 定理 `inv_apply`

English:
theorem inv_apply
  given: (e : MulAut M) (m : M)
  statement: e⁻¹ m = e.symm m
  proof: by
  rw [inv_def]

@[to_additive (attr := simp)]

中文:
定理 inv_apply
  条件: (e : MulAut M) (m : M)
  结论: e⁻¹ m = e.symm m
  证明: by
  rw [inv_def]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_def
-/
theorem inv_apply (e : MulAut M) (m : M) : e⁻¹ m = e.symm m := by
  rw [inv_def]

@[to_additive (attr := simp)]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (e₁ e₂ : MulAut M) (m : M)
  statement: (e₁ * e₂) m = e₁ (e₂ m)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 mul_apply
  条件: (e₁ e₂ : MulAut M) (m : M)
  结论: (e₁ * e₂) m = e₁ (e₂ m)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem mul_apply (e₁ e₂ : MulAut M) (m : M) : (e₁ * e₂) m = e₁ (e₂ m) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (m : M)
  statement: (1 : MulAut M) m = m
  proof: rfl

@[to_additive]

中文:
定理 one_apply
  条件: (m : M)
  结论: (1 : MulAut M) m = m
  证明: rfl

@[to_additive]
-/
theorem one_apply (m : M) : (1 : MulAut M) m = m :=
  rfl

@[to_additive]
/--
theorem `apply_inv_self` / 定理 `apply_inv_self`

English:
theorem apply_inv_self
  given: (e : MulAut M) (m : M)
  statement: e (e⁻¹ m) = m
  proof: MulEquiv.apply_symm_apply _ _

@[to_additive]

中文:
定理 apply_inv_self
  条件: (e : MulAut M) (m : M)
  结论: e (e⁻¹ m) = m
  证明: MulEquiv.apply_symm_apply _ _

@[to_additive]

Depends on / 依赖: MulEquiv, MulEquiv.apply_symm_apply, apply_symm_apply
-/
theorem apply_inv_self (e : MulAut M) (m : M) : e (e⁻¹ m) = m :=
  MulEquiv.apply_symm_apply _ _

@[to_additive]
/--
theorem `inv_apply_self` / 定理 `inv_apply_self`

English:
theorem inv_apply_self
  given: (e : MulAut M) (m : M)
  statement: e⁻¹ (e m) = m
  proof: MulEquiv.apply_symm_apply _ _

中文:
定理 inv_apply_self
  条件: (e : MulAut M) (m : M)
  结论: e⁻¹ (e m) = m
  证明: MulEquiv.apply_symm_apply _ _

Depends on / 依赖: MulEquiv, MulEquiv.apply_symm_apply, apply_symm_apply
-/
theorem inv_apply_self (e : MulAut M) (m : M) : e⁻¹ (e m) = m :=
  MulEquiv.apply_symm_apply _ _

/--
Definition of `toPerm` / `toPerm` 的定义

English:
definition toPerm
  signature: : MulAut M ->* Equiv.Perm M where
  body: MulEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 toPerm
  签名: : MulAut M ->* Equiv.Perm M where
  定义体: MulEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: MulEquiv, MulEquiv.toEquiv, toEquiv
-/
def toPerm : MulAut M ->* Equiv.Perm M where
  toFun := MulEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Group conjugation, `MulAut.conj g h = g * h * g⁻¹`, as a monoid homomorphism
mapping multiplication in `G` into multiplication in the automorphism group `MulAut G`.
See also the type `ConjAct G` for any group `G`, which has a `MulAction (ConjAct G) G` instance
where `conj G` acts on `G` by conjugation. -/
@[to_additive /-- Group conjugation, `AddAut.addConj g h = g + h + -g`, as an additive homomorphism
mapping addition in `G` into addition in the additive automorphism group `AddAut G`. -/]
/--
Definition of `conj` / `conj` 的定义

English:
definition conj
  signature: [Group G]
  body: { toFun h := g * h * g⁻¹
      invFun h := g⁻¹ * h * g
      left_inv _ := by simp [mul_assoc]
      right_inv _ := by simp [mul_assoc]
      map_mul' := by simp [mul_assoc] }
  map_mul' _ _ := by ext; simp [mul_assoc]
  map_one' := by ext; simp

@[to_additive (attr := simp)]

中文:
定义 conj
  签名: [Group G]
  定义体: { toFun h := g * h * g⁻¹
      invFun h := g⁻¹ * h * g
      left_inv _ := by simp [mul_assoc]
      right_inv _ := by simp [mul_assoc]
      map_mul' := by simp [mul_assoc] }
  map_mul' _ _ := by ext; simp [mul_assoc]
  map_one' := by ext; simp

@[to_additive (attr := simp)]

Depends on / 依赖: invFun, left_inv, map_mul, map_one, mul_assoc, right_inv
-/
def conj [Group G] : G ->* MulAut G where
  toFun g :=
    { toFun h := g * h * g⁻¹
      invFun h := g⁻¹ * h * g
      left_inv _ := by simp [mul_assoc]
      right_inv _ := by simp [mul_assoc]
      map_mul' := by simp [mul_assoc] }
  map_mul' _ _ := by ext; simp [mul_assoc]
  map_one' := by ext; simp

@[to_additive (attr := simp)]
/--
theorem `conj_apply` / 定理 `conj_apply`

English:
theorem conj_apply
  given: [Group G] (g h : G)
  statement: conj g h = g * h * g⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 conj_apply
  条件: [Group G] (g h : G)
  结论: conj g h = g * h * g⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem conj_apply [Group G] (g h : G) : conj g h = g * h * g⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `conj_symm_apply` / 定理 `conj_symm_apply`

English:
theorem conj_symm_apply
  given: [Group G] (g h : G)
  statement: (conj g).symm h = g⁻¹ * h * g
  proof: rfl

@[to_additive]

中文:
定理 conj_symm_apply
  条件: [Group G] (g h : G)
  结论: (conj g).symm h = g⁻¹ * h * g
  证明: rfl

@[to_additive]
-/
theorem conj_symm_apply [Group G] (g h : G) : (conj g).symm h = g⁻¹ * h * g :=
  rfl

@[to_additive]
/--
theorem `conj_inv_apply` / 定理 `conj_inv_apply`

English:
theorem conj_inv_apply
  given: [Group G] (g h : G)
  statement: (conj g)⁻¹ h = g⁻¹ * h * g
  proof: rfl

中文:
定理 conj_inv_apply
  条件: [Group G] (g h : G)
  结论: (conj g)⁻¹ h = g⁻¹ * h * g
  证明: rfl
-/
theorem conj_inv_apply [Group G] (g h : G) : (conj g)⁻¹ h = g⁻¹ * h * g :=
  rfl

/-- Isomorphic groups have isomorphic automorphism groups. -/
@[to_additive (attr := simps) /-- Isomorphic groups have isomorphic automorphism groups. -/]
/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: [Group G] {H : Type*} [Group H] (ϕ : G ≃* H)
  body: ϕ.symm.trans (f.trans ϕ)
  invFun f := ϕ.trans (f.trans ϕ.symm)
  left_inv _ := by simp [DFunLike.ext_iff]
  right_inv _ := by simp [DFunLike.ext_iff]
  map_mul' := by simp [DFunLike.ext_iff]

中文:
定义 congr
  签名: [Group G] {H : 类型} [Group H] (ϕ : G ≃* H)
  定义体: ϕ.symm.trans (f.trans ϕ)
  invFun f := ϕ.trans (f.trans ϕ.symm)
  left_inv _ := by simp [DFunLike.ext_iff]
  right_inv _ := by simp [DFunLike.ext_iff]
  map_mul' := by simp [DFunLike.ext_iff]

Depends on / 依赖: f.trans, symm.trans
-/
def congr [Group G] {H : Type*} [Group H] (ϕ : G ≃* H) :
    MulAut G ≃* MulAut H where
  toFun f := ϕ.symm.trans (f.trans ϕ)
  invFun f := ϕ.trans (f.trans ϕ.symm)
  left_inv _ := by simp [DFunLike.ext_iff]
  right_inv _ := by simp [DFunLike.ext_iff]
  map_mul' := by simp [DFunLike.ext_iff]

end MulAut

namespace AddAut

variable (A) [Add A]

@[deprecated (since := "2026-05-26")] alias coe_mul := coe_add
@[deprecated (since := "2026-05-26")] alias coe_one := coe_zero
@[deprecated (since := "2026-05-26")] alias coe_inv := coe_neg
@[deprecated (since := "2026-05-26")] alias mul_def := add_def
@[deprecated (since := "2026-05-26")] alias one_def := zero_def
@[deprecated (since := "2026-05-26")] alias inv_def := neg_def
@[deprecated (since := "2026-05-26")] alias mul_apply := add_apply
@[deprecated (since := "2026-05-26")] alias one_apply := zero_apply
@[deprecated (since := "2026-05-26")] alias inv_symm := neg_symm
@[deprecated (since := "2026-05-26")] alias symm_inv := symm_neg
@[deprecated (since := "2026-05-26")] alias inv_apply := neg_apply
@[deprecated (since := "2026-05-26")] alias inv_apply_self := neg_apply_self
@[deprecated (since := "2026-05-26")] alias apply_inv_self := apply_neg_self

/--
Definition of `toPerm` / `toPerm` 的定义

English:
definition toPerm
  signature: : AddAut A ->+ Additive (Equiv.Perm A) where
  body: AddEquiv.toEquiv
  map_zero' := rfl
  map_add' _ _ := rfl

@[deprecated (since := "2026-05-26")] alias conj := addConj
@[deprecated (since := "2026-05-26")] alias conj_apply := addConj_apply
@[deprecated (since := "2026-05-26")] alias conj_symm_apply := addConj_symm_apply
@[deprecated (since := "202

中文:
定义 toPerm
  签名: : AddAut A ->+ Additive (Equiv.Perm A) where
  定义体: AddEquiv.toEquiv
  map_zero' := rfl
  map_add' _ _ := rfl

@[deprecated (since := "2026-05-26")] alias conj := addConj
@[deprecated (since := "2026-05-26")] alias conj_apply := addConj_apply
@[deprecated (since := "2026-05-26")] alias conj_symm_apply := addConj_symm_apply
@[deprecated (since := "202

Depends on / 依赖: AddEquiv, AddEquiv.toEquiv, toEquiv
-/
def toPerm : AddAut A ->+ Additive (Equiv.Perm A) where
  toFun := AddEquiv.toEquiv
  map_zero' := rfl
  map_add' _ _ := rfl

@[deprecated (since := "2026-05-26")] alias conj := addConj
@[deprecated (since := "2026-05-26")] alias conj_apply := addConj_apply
@[deprecated (since := "2026-05-26")] alias conj_symm_apply := addConj_symm_apply
@[deprecated (since := "2026-05-26")] alias conj_inv_apply := addConj_neg_apply

@[deprecated "use `addConj_neg_apply` instead" (since := "2026-05-26")]
/--
theorem `neg_conj_apply` / 定理 `neg_conj_apply`

English:
theorem neg_conj_apply
  given: [AddGroup G] (g h : G)
  statement: (-addConj g) h = -g + h + g
  proof: by
  simp

中文:
定理 neg_conj_apply
  条件: [AddGroup G] (g h : G)
  结论: (-addConj g) h = -g + h + g
  证明: by
  simp
-/
theorem neg_conj_apply [AddGroup G] (g h : G) : (-addConj g) h = -g + h + g := by
  simp

end AddAut

variable (G)

/-- `Multiplicative G` and `G` have isomorphic automorphism groups. -/
@[simps!]
/--
Definition of `MulAutMultiplicative` / `MulAutMultiplicative` 的定义

English:
definition MulAutMultiplicative
  signature: [AddGroup G]
  body: { AddEquiv.toMultiplicative.symm with map_mul' := fun _ _ => rfl }

中文:
定义 MulAutMultiplicative
  签名: [AddGroup G]
  定义体: { AddEquiv.toMultiplicative.symm with map_mul' := fun _ _ => rfl }

Depends on / 依赖: AddEquiv, AddEquiv.toMultiplicative.symm, map_mul, toMultiplicative
-/
def MulAutMultiplicative [AddGroup G] : MulAut (Multiplicative G) ≃* Multiplicative (AddAut G) :=
  { AddEquiv.toMultiplicative.symm with map_mul' := fun _ _ => rfl }

/-- `Additive G` and `G` have isomorphic automorphism groups. -/
@[simps!]
/--
Definition of `AddAutAdditive` / `AddAutAdditive` 的定义

English:
definition AddAutAdditive
  signature: [Group G]
  body: { MulEquiv.toAdditive.symm with map_add' := fun _ _ => rfl }

中文:
定义 AddAutAdditive
  签名: [Group G]
  定义体: { MulEquiv.toAdditive.symm with map_add' := fun _ _ => rfl }

Depends on / 依赖: MulEquiv, MulEquiv.toAdditive.symm, map_add, toAdditive
-/
def AddAutAdditive [Group G] : AddAut (Additive G) ≃+ Additive (MulAut G) :=
  { MulEquiv.toAdditive.symm with map_add' := fun _ _ => rfl }
