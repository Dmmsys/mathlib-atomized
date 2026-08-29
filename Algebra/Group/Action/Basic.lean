/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# More lemmas about group actions

This file contains lemmas about group actions that require more imports than
`Mathlib/Algebra/Group/Action/Defs.lean` offers.
-/

@[expose] public section

assert_not_exists MonoidWithZero Equiv.Perm.permGroup

variable {G M A B α β : Type*}

section MulAction

section Group

variable [Group α] [MulAction α β]

/-- Given an action of a group `α` on `β`, each `g : α` defines a permutation of `β`. -/
@[to_additive (attr := simps)]
/--
Definition of `MulAction.toPerm` / `MulAction.toPerm` 的定义

English:
definition MulAction.toPerm
  signature: (a : α)
  body: ⟨fun x => a • x, fun x => a⁻¹ • x, inv_smul_smul a, smul_inv_smul a⟩

中文:
定义 MulAction.toPerm
  签名: (a : α)
  定义体: ⟨fun x => a • x, fun x => a⁻¹ • x, inv_smul_smul a, smul_inv_smul a⟩

Depends on / 依赖: inv_smul_smul, smul_inv_smul
-/
def MulAction.toPerm (a : α) : Equiv.Perm β :=
  ⟨fun x => a • x, fun x => a⁻¹ • x, inv_smul_smul a, smul_inv_smul a⟩

/-- Given an action of an additive group `α` on `β`, each `g : α` defines a permutation of `β`. -/
add_decl_doc AddAction.toPerm

/-- `MulAction.toPerm` is injective on faithful actions. -/
@[to_additive /-- `AddAction.toPerm` is injective on faithful actions. -/]
/--
lemma `MulAction.toPerm_injective` / 引理 `MulAction.toPerm_injective`

English:
lemma MulAction.toPerm_injective
  given: [FaithfulSMul α β]
  proof: (show Function.Injective (Equiv.toFun ∘ MulAction.toPerm) from smul_left_injective').of_comp

@[to_additive]

中文:
引理 MulAction.toPerm_injective
  条件: [FaithfulSMul α β]
  证明: (show Function.Injective (Equiv.toFun ∘ MulAction.toPerm) from smul_left_injective').of_comp

@[to_additive]

Depends on / 依赖: Equiv.toFun, Function, Function.Injective, Injective, MulAction, MulAction.toPerm, of_comp, smul_left_injective, toPerm
-/
lemma MulAction.toPerm_injective [FaithfulSMul α β] :
    Function.Injective (MulAction.toPerm : α -> Equiv.Perm β) :=
  (show Function.Injective (Equiv.toFun ∘ MulAction.toPerm) from smul_left_injective').of_comp

@[to_additive]
/--
lemma `MulAction.bijective` / 引理 `MulAction.bijective`

English:
lemma MulAction.bijective
  given: (g : α)
  statement: Function.Bijective (g • · : β -> β)
  proof: (MulAction.toPerm g).bijective

@[to_additive]

中文:
引理 MulAction.bijective
  条件: (g : α)
  结论: Function.Bijective (g • · : β -> β)
  证明: (MulAction.toPerm g).bijective

@[to_additive]
-/
protected lemma MulAction.bijective (g : α) : Function.Bijective (g • · : β -> β) :=
  (MulAction.toPerm g).bijective

@[to_additive]
/--
lemma `MulAction.injective` / 引理 `MulAction.injective`

English:
lemma MulAction.injective
  given: (g : α)
  statement: Function.Injective (g • · : β -> β)
  proof: (MulAction.bijective g).injective

@[to_additive]

中文:
引理 MulAction.injective
  条件: (g : α)
  结论: Function.Injective (g • · : β -> β)
  证明: (MulAction.bijective g).injective

@[to_additive]
-/
protected lemma MulAction.injective (g : α) : Function.Injective (g • · : β -> β) :=
  (MulAction.bijective g).injective

@[to_additive]
/--
lemma `MulAction.surjective` / 引理 `MulAction.surjective`

English:
lemma MulAction.surjective
  given: (g : α)
  statement: Function.Surjective (g • · : β -> β)
  proof: (MulAction.bijective g).surjective

@[to_additive]

中文:
引理 MulAction.surjective
  条件: (g : α)
  结论: Function.Surjective (g • · : β -> β)
  证明: (MulAction.bijective g).surjective

@[to_additive]
-/
protected lemma MulAction.surjective (g : α) : Function.Surjective (g • · : β -> β) :=
  (MulAction.bijective g).surjective

@[to_additive]
/--
lemma `smul_left_cancel` / 引理 `smul_left_cancel`

English:
lemma smul_left_cancel
  given: (g : α) {x y : β} (h : g • x = g • y)
  statement: x = y
  proof: MulAction.injective g h

@[to_additive (attr := simp)]

中文:
引理 smul_left_cancel
  条件: (g : α) {x y : β} (h : g • x = g • y)
  结论: x = y
  证明: MulAction.injective g h

@[to_additive (attr := simp)]

Depends on / 依赖: MulAction, MulAction.injective, injective
-/
lemma smul_left_cancel (g : α) {x y : β} (h : g • x = g • y) : x = y := MulAction.injective g h

@[to_additive (attr := simp)]
/--
lemma `smul_left_cancel_iff` / 引理 `smul_left_cancel_iff`

English:
lemma smul_left_cancel_iff
  given: (g : α) {x y : β}
  statement: g • x = g • y ↔ x = y
  proof: (MulAction.injective g).eq_iff

@[to_additive]

中文:
引理 smul_left_cancel_iff
  条件: (g : α) {x y : β}
  结论: g • x = g • y ↔ x = y
  证明: (MulAction.injective g).eq_iff

@[to_additive]

Depends on / 依赖: MulAction, MulAction.injective, eq_iff, injective
-/
lemma smul_left_cancel_iff (g : α) {x y : β} : g • x = g • y ↔ x = y :=
  (MulAction.injective g).eq_iff

@[to_additive]
/--
lemma `smul_eq_iff_eq_inv_smul` / 引理 `smul_eq_iff_eq_inv_smul`

English:
lemma smul_eq_iff_eq_inv_smul
  given: (g : α) {x y : β}
  statement: g • x = y ↔ x = g⁻¹ • y
  proof: eq_inv_smul_iff.symm

@[to_additive]

中文:
引理 smul_eq_iff_eq_inv_smul
  条件: (g : α) {x y : β}
  结论: g • x = y ↔ x = g⁻¹ • y
  证明: eq_inv_smul_iff.symm

@[to_additive]

Depends on / 依赖: eq_inv_smul_iff, eq_inv_smul_iff.symm
-/
lemma smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g • x = y ↔ x = g⁻¹ • y :=
  eq_inv_smul_iff.symm

@[to_additive]
/--
lemma `isCancelSMul_iff_eq_one_of_smul_eq` / 引理 `isCancelSMul_iff_eq_one_of_smul_eq`

English:
lemma isCancelSMul_iff_eq_one_of_smul_eq
  proof: by
  refine ⟨fun H _ _ => IsCancelSMul.eq_one_of_smul, fun H => ⟨fun g h x => ?_⟩⟩
  rw [smul_eq_iff_eq_inv_smul]; rw [eq_comm]; rw [← mul_smul]; rw [← inv_mul_eq_one (G := α)]
  exact H (g⁻¹ * h) x

中文:
引理 isCancelSMul_iff_eq_one_of_smul_eq
  证明: by
  refine ⟨fun H _ _ => IsCancelSMul.eq_one_of_smul, fun H => ⟨fun g h x => ?_⟩⟩
  rw [smul_eq_iff_eq_inv_smul]; rw [eq_comm]; rw [← mul_smul]; rw [← inv_mul_eq_one (G := α)]
  exact H (g⁻¹ * h) x

Depends on / 依赖: IsCancelSMul, IsCancelSMul.eq_one_of_smul, eq_comm, eq_one_of_smul, inv_mul_eq_one, mul_smul, smul_eq_iff_eq_inv_smul
-/
lemma isCancelSMul_iff_eq_one_of_smul_eq :
    IsCancelSMul α β ↔ (forall (g : α) (x : β), g • x = x -> g = 1) := by
  refine ⟨fun H _ _ => IsCancelSMul.eq_one_of_smul, fun H => ⟨fun g h x => ?_⟩⟩
  rw [smul_eq_iff_eq_inv_smul]; rw [eq_comm]; rw [← mul_smul]; rw [← inv_mul_eq_one (G := α)]
  exact H (g⁻¹ * h) x

end Group

section Monoid
variable [Monoid α] [MulAction α β] (c : α) (x y : β) [Invertible c]

/--
lemma `invOf_smul_smul` / 引理 `invOf_smul_smul`

English:
lemma invOf_smul_smul
  statement: ⅟c • c • x = x
  proof: inv_smul_smul (unitOfInvertible c) _

中文:
引理 invOf_smul_smul
  结论: ⅟c • c • x = x
  证明: inv_smul_smul (unitOfInvertible c) _
-/
@[simp] lemma invOf_smul_smul : ⅟c • c • x = x := inv_smul_smul (unitOfInvertible c) _
/--
lemma `smul_invOf_smul` / 引理 `smul_invOf_smul`

English:
lemma smul_invOf_smul
  statement: c • (⅟c • x) = x
  proof: smul_inv_smul (unitOfInvertible c) _

中文:
引理 smul_invOf_smul
  结论: c • (⅟c • x) = x
  证明: smul_inv_smul (unitOfInvertible c) _
-/
@[simp] lemma smul_invOf_smul : c • (⅟c • x) = x := smul_inv_smul (unitOfInvertible c) _

variable {c x y}

/--
lemma `invOf_smul_eq_iff` / 引理 `invOf_smul_eq_iff`

English:
lemma invOf_smul_eq_iff
  statement: ⅟c • x = y ↔ x = c • y
  proof: inv_smul_eq_iff (g := unitOfInvertible c)

中文:
引理 invOf_smul_eq_iff
  结论: ⅟c • x = y ↔ x = c • y
  证明: inv_smul_eq_iff (g := unitOfInvertible c)

Depends on / 依赖: inv_smul_eq_iff, unitOfInvertible
-/
lemma invOf_smul_eq_iff : ⅟c • x = y ↔ x = c • y := inv_smul_eq_iff (g := unitOfInvertible c)

/--
lemma `smul_eq_iff_eq_invOf_smul` / 引理 `smul_eq_iff_eq_invOf_smul`

English:
lemma smul_eq_iff_eq_invOf_smul
  statement: c • x = y ↔ x = ⅟c • y
  proof: smul_eq_iff_eq_inv_smul (g := unitOfInvertible c)

中文:
引理 smul_eq_iff_eq_invOf_smul
  结论: c • x = y ↔ x = ⅟c • y
  证明: smul_eq_iff_eq_inv_smul (g := unitOfInvertible c)

Depends on / 依赖: smul_eq_iff_eq_inv_smul, unitOfInvertible
-/
lemma smul_eq_iff_eq_invOf_smul : c • x = y ↔ x = ⅟c • y :=
  smul_eq_iff_eq_inv_smul (g := unitOfInvertible c)

end Monoid
end MulAction

section Arrow
variable {G A B : Type*} [DivisionMonoid G] [MulAction G A]

/-- If `G` acts on `A`, then it acts also on `A → B`, by `(g • F) a = F (g⁻¹ • a)`. -/
@[to_additive (attr := instance_reducible, simps) arrowAddAction
/-- If `G` acts on `A`, then it acts also on `A → B`, by `(g +ᵥ F) a = F (g⁻¹ +ᵥ a)` -/]
/--
Definition of `arrowAction` / `arrowAction` 的定义

English:
definition arrowAction
  signature: : MulAction G (A -> B) where
  body: F (g⁻¹ • a)
  one_smul f := by
    change (fun x => f ((1 : G)⁻¹ • x)) = f
    simp only [inv_one, one_smul]
  mul_smul x y f := by
    change (fun a => f ((x * y)⁻¹ • a)) = (fun a => f (y⁻¹ • x⁻¹ • a))
    simp only [mul_smul, mul_inv_rev]

中文:
定义 arrowAction
  签名: : MulAction G (A -> B) where
  定义体: F (g⁻¹ • a)
  one_smul f := by
    change (fun x => f ((1 : G)⁻¹ • x)) = f
    simp only [inv_one, one_smul]
  mul_smul x y f := by
    change (fun a => f ((x * y)⁻¹ • a)) = (fun a => f (y⁻¹ • x⁻¹ • a))
    simp only [mul_smul, mul_inv_rev]
-/
def arrowAction : MulAction G (A -> B) where
  smul g F a := F (g⁻¹ • a)
  one_smul f := by
    change (fun x => f ((1 : G)⁻¹ • x)) = f
    simp only [inv_one, one_smul]
  mul_smul x y f := by
    change (fun a => f ((x * y)⁻¹ • a)) = (fun a => f (y⁻¹ • x⁻¹ • a))
    simp only [mul_smul, mul_inv_rev]

attribute [local instance] arrowAction

variable [Monoid M]

/-- When `M` is a monoid, `ArrowAction` is additionally a `MulDistribMulAction`. -/
@[instance_reducible]
/--
Definition of `arrowMulDistribMulAction` / `arrowMulDistribMulAction` 的定义

English:
definition arrowMulDistribMulAction
  signature: : MulDistribMulAction G (A -> M) where
  body: rfl
  smul_mul _ _ _ := rfl

中文:
定义 arrowMulDistribMulAction
  签名: : MulDistribMulAction G (A -> M) where
  定义体: rfl
  smul_mul _ _ _ := rfl
-/
def arrowMulDistribMulAction : MulDistribMulAction G (A -> M) where
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

end Arrow

namespace IsUnit
variable [Monoid α] [MulAction α β]

@[to_additive]
/--
theorem `smul_bijective` / 定理 `smul_bijective`

English:
theorem smul_bijective
  given: {m : α} (hm : IsUnit m)
  proof: by
  lift m to αˣ using hm
  exact MulAction.bijective m

@[to_additive]

中文:
定理 smul_bijective
  条件: {m : α} (hm : IsUnit m)
  证明: by
  lift m to αˣ using hm
  exact MulAction.bijective m

@[to_additive]

Depends on / 依赖: MulAction, MulAction.bijective, bijective
-/
theorem smul_bijective {m : α} (hm : IsUnit m) :
    Function.Bijective (fun (a : β) => m • a) := by
  lift m to αˣ using hm
  exact MulAction.bijective m

@[to_additive]
/--
lemma `smul_left_cancel` / 引理 `smul_left_cancel`

English:
lemma smul_left_cancel
  given: {a : α} (ha : IsUnit a) {x y : β}
  statement: a • x = a • y ↔ x = y
  proof: let ⟨u, hu⟩ := ha
  hu ▸ smul_left_cancel_iff u

中文:
引理 smul_left_cancel
  条件: {a : α} (ha : IsUnit a) {x y : β}
  结论: a • x = a • y ↔ x = y
  证明: let ⟨u, hu⟩ := ha
  hu ▸ smul_left_cancel_iff u

Depends on / 依赖: smul_left_cancel_iff
-/
lemma smul_left_cancel {a : α} (ha : IsUnit a) {x y : β} : a • x = a • y ↔ x = y :=
  let ⟨u, hu⟩ := ha
  hu ▸ smul_left_cancel_iff u

end IsUnit

section SMul
variable [Group α] [Monoid β] [MulAction α β] [SMulCommClass α β β] [IsScalarTower α β β]

/--
lemma `isUnit_smul_iff` / 引理 `isUnit_smul_iff`

English:
lemma isUnit_smul_iff
  given: (g : α) (m : β)
  statement: IsUnit (g • m) ↔ IsUnit m
  proof: ⟨fun h => inv_smul_smul g m ▸ h.smul g⁻¹, IsUnit.smul g⟩

中文:
引理 isUnit_smul_iff
  条件: (g : α) (m : β)
  结论: IsUnit (g • m) ↔ IsUnit m
  证明: ⟨fun h => inv_smul_smul g m ▸ h.smul g⁻¹, IsUnit.smul g⟩
-/
@[simp] lemma isUnit_smul_iff (g : α) (m : β) : IsUnit (g • m) ↔ IsUnit m :=
  ⟨fun h => inv_smul_smul g m ▸ h.smul g⁻¹, IsUnit.smul g⟩

end SMul

namespace MulAction
variable [Monoid M] [MulAction M α]

variable (M α) in
/-- Embedding of `α` into functions `M → α` induced by a multiplicative action of `M` on `α`. -/
@[to_additive
/-- Embedding of `α` into functions `M → α` induced by an additive action of `M` on `α`. -/]
/--
Definition of `toFun` / `toFun` 的定义

English:
definition toFun
  signature: : α ↪ M -> α
  body: ⟨fun y x => x • y, fun y₁ y₂ H => one_smul M y₁ ▸ one_smul M y₂ ▸ by convert! congr_fun H 1⟩

@[to_additive (attr := simp)]

中文:
定义 toFun
  签名: : α ↪ M -> α
  定义体: ⟨fun y x => x • y, fun y₁ y₂ H => one_smul M y₁ ▸ one_smul M y₂ ▸ by convert! congr_fun H 1⟩

@[to_additive (attr := simp)]

Depends on / 依赖: congr_fun, convert, one_smul
-/
def toFun : α ↪ M -> α :=
  ⟨fun y x => x • y, fun y₁ y₂ H => one_smul M y₁ ▸ one_smul M y₂ ▸ by convert! congr_fun H 1⟩

@[to_additive (attr := simp)]
/--
lemma `toFun_apply` / 引理 `toFun_apply`

English:
lemma toFun_apply
  given: (x : M) (y : α)
  statement: MulAction.toFun M α y x = x • y
  proof: rfl

中文:
引理 toFun_apply
  条件: (x : M) (y : α)
  结论: MulAction.toFun M α y x = x • y
  证明: rfl
-/
lemma toFun_apply (x : M) (y : α) : MulAction.toFun M α y x = x • y := rfl

end MulAction

section MulDistribMulAction
variable [Monoid M] [Monoid A] [MulDistribMulAction M A]

-- See note [reducible non-instances]
/--
Definition of `Function.Injective.mulDistribMulAction` / `Function.Injective.mulDistribMulAction` 的定义

English:
abbreviation Function.Injective.mulDistribMulAction
  signature: [Monoid B] [SMul M B] (f : B ->* A)
  body: hf.mulAction f smul
smul_mul c x y := hf by simp only [smul, f.map_mul, smul_mul']
smul_one c := hf by simp only [smul, f.map_one, smul_one]

中文:
缩写 Function.Injective.mulDistribMulAction
  签名: [Monoid B] [SMul M B] (f : B ->* A)
  定义体: hf.mulAction f smul
smul_mul c x y := hf by simp only [smul, f.map_mul, smul_mul']
smul_one c := hf by simp only [smul, f.map_one, smul_one]
-/
protected abbrev Function.Injective.mulDistribMulAction [Monoid B] [SMul M B] (f : B ->* A)
    (hf : Injective f) (smul : forall (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B where
  __ := hf.mulAction f smul
smul_mul c x y := hf by simp only [smul, f.map_mul, smul_mul']
smul_one c := hf by simp only [smul, f.map_one, smul_one]

-- See note [reducible non-instances]
/--
Definition of `Function.Surjective.mulDistribMulAction` / `Function.Surjective.mulDistribMulAction` 的定义

English:
abbreviation Function.Surjective.mulDistribMulAction
  signature: [Monoid B] [SMul M B] (f : A ->* B)
  body: hf.mulAction f smul
  smul_mul c := by simp only [hf.forall, smul_mul', ← smul, ← f.map_mul, implies_true]
  smul_one c := by rw [← f.map_one, ← smul, smul_one]

中文:
缩写 Function.Surjective.mulDistribMulAction
  签名: [Monoid B] [SMul M B] (f : A ->* B)
  定义体: hf.mulAction f smul
  smul_mul c := by simp only [hf.forall, smul_mul', ← smul, ← f.map_mul, implies_true]
  smul_one c := by rw [← f.map_one, ← smul, smul_one]
-/
protected abbrev Function.Surjective.mulDistribMulAction [Monoid B] [SMul M B] (f : A ->* B)
    (hf : Surjective f) (smul : forall (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B where
  __ := hf.mulAction f smul
  smul_mul c := by simp only [hf.forall, smul_mul', ← smul, ← f.map_mul, implies_true]
  smul_one c := by rw [← f.map_one, ← smul, smul_one]

variable (A) in
/--
Definition of `MulDistribMulAction.toMonoidHom` / `MulDistribMulAction.toMonoidHom` 的定义

English:
definition MulDistribMulAction.toMonoidHom
  signature: (r : M)
  body: (r • ·)
  map_one' := smul_one r
  map_mul' := smul_mul' r

中文:
定义 MulDistribMulAction.toMonoidHom
  签名: (r : M)
  定义体: (r • ·)
  map_one' := smul_one r
  map_mul' := smul_mul' r
-/
@[simps] def MulDistribMulAction.toMonoidHom (r : M) : A ->* A where
  toFun := (r • ·)
  map_one' := smul_one r
  map_mul' := smul_mul' r

/--
lemma `smul_pow'` / 引理 `smul_pow'`

English:
lemma smul_pow'
  given: (r : M) (x : A) (n : Nat)
  statement: r • x ^ n = (r • x) ^ n
  proof: (MulDistribMulAction.toMonoidHom _ _).map_pow _ _

中文:
引理 smul_pow'
  条件: (r : M) (x : A) (n : 自然数)
  结论: r • x ^ n = (r • x) ^ n
  证明: (MulDistribMulAction.toMonoidHom _ _).map_pow _ _
-/
@[simp] lemma smul_pow' (r : M) (x : A) (n : Nat) : r • x ^ n = (r • x) ^ n :=
  (MulDistribMulAction.toMonoidHom _ _).map_pow _ _

variable (M A) in
/-- Each element of the monoid defines a monoid homomorphism. -/
@[simps]
/--
Definition of `MulDistribMulAction.toMonoidEnd` / `MulDistribMulAction.toMonoidEnd` 的定义

English:
definition MulDistribMulAction.toMonoidEnd
  signature: : M ->* Monoid.End A where
  body: MulDistribMulAction.toMonoidHom A
map_one' := MonoidHom.ext one_smul M
map_mul' x y := MonoidHom.ext mul_smul x y

中文:
定义 MulDistribMulAction.toMonoidEnd
  签名: : M ->* Monoid.End A where
  定义体: MulDistribMulAction.toMonoidHom A
map_one' := MonoidHom.ext one_smul M
map_mul' x y := MonoidHom.ext mul_smul x y

Depends on / 依赖: MulDistribMulAction, MulDistribMulAction.toMonoidHom, toMonoidHom
-/
def MulDistribMulAction.toMonoidEnd : M ->* Monoid.End A where
  toFun := MulDistribMulAction.toMonoidHom A
map_one' := MonoidHom.ext one_smul M
map_mul' x y := MonoidHom.ext mul_smul x y

end MulDistribMulAction

section MulDistribMulAction
variable [Monoid M] [Group A] [MulDistribMulAction M A]

/--
lemma `smul_inv'` / 引理 `smul_inv'`

English:
lemma smul_inv'
  given: (r : M) (x : A)
  statement: r • x⁻¹ = (r • x)⁻¹
  proof: (MulDistribMulAction.toMonoidHom A r).map_inv x

中文:
引理 smul_inv'
  条件: (r : M) (x : A)
  结论: r • x⁻¹ = (r • x)⁻¹
  证明: (MulDistribMulAction.toMonoidHom A r).map_inv x
-/
@[simp] lemma smul_inv' (r : M) (x : A) : r • x⁻¹ = (r • x)⁻¹ :=
  (MulDistribMulAction.toMonoidHom A r).map_inv x

/--
lemma `smul_div'` / 引理 `smul_div'`

English:
lemma smul_div'
  given: (r : M) (x y : A)
  statement: r • (x / y) = r • x / r • y
  proof: map_div (MulDistribMulAction.toMonoidHom A r) x y

中文:
引理 smul_div'
  条件: (r : M) (x y : A)
  结论: r • (x / y) = r • x / r • y
  证明: map_div (MulDistribMulAction.toMonoidHom A r) x y

Depends on / 依赖: MulDistribMulAction, MulDistribMulAction.toMonoidHom, map_div, toMonoidHom
-/
lemma smul_div' (r : M) (x y : A) : r • (x / y) = r • x / r • y :=
  map_div (MulDistribMulAction.toMonoidHom A r) x y

/--
lemma `smul_zpow'` / 引理 `smul_zpow'`

English:
lemma smul_zpow'
  given: (r : M) (x : A) (z : Int)
  statement: r • (x ^ z) = (r • x) ^ z
  proof: map_zpow (MulDistribMulAction.toMonoidHom A r) x z

中文:
引理 smul_zpow'
  条件: (r : M) (x : A) (z : 整数)
  结论: r • (x ^ z) = (r • x) ^ z
  证明: map_zpow (MulDistribMulAction.toMonoidHom A r) x z

Depends on / 依赖: MulDistribMulAction, MulDistribMulAction.toMonoidHom, map_zpow, toMonoidHom
-/
lemma smul_zpow' (r : M) (x : A) (z : Int) : r • (x ^ z) = (r • x) ^ z :=
  map_zpow (MulDistribMulAction.toMonoidHom A r) x z

end MulDistribMulAction
