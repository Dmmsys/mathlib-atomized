/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Properties of `fixedPoints` and `fixedBy`

This module contains some useful properties of `MulAction.fixedPoints` and `MulAction.fixedBy`
that don't directly belong to `Mathlib/GroupTheory/GroupAction/Basic.lean`,
as well as their interaction with `MulActionHom`.

## Main theorems

* `MulAction.fixedBy_mul`: `fixedBy α (g * h) ⊆ fixedBy α g ∪ fixedBy α h`
* `MulAction.fixedBy_conj` and `MulAction.smul_fixedBy`: the pointwise group action of `h` on
  `fixedBy α g` is equal to the `fixedBy` set of the conjugation of `h` with `g`
  (`fixedBy α (h * g * h⁻¹)`).
* `MulAction.set_mem_fixedBy_of_movedBy_subset` shows that if a set `s` is a superset of
  `(fixedBy α g)ᶜ`, then the group action of `g` cannot send elements of `s` outside of `s`.
  This is expressed as `s ∈ fixedBy (Set α) g`, and `MulAction.set_mem_fixedBy_iff` allows one
  to convert the relationship back to `g • x ∈ s ↔ x ∈ s`.
* `MulAction.not_commute_of_disjoint_smul_movedBy` allows one to prove that `g` and `h`
  do not commute from the disjointness of the `(fixedBy α g)ᶜ` set and `h • (fixedBy α g)ᶜ`,
  which is a property used in the proof of Rubin's theorem.

The theorems above are also available for `AddAction`.

## Pointwise group action and `fixedBy (Set α) g`

Since `fixedBy α g = { x | g • x = x }` by definition, properties about the pointwise action of
a set `s : Set α` can be expressed using `fixedBy (Set α) g`.
To properly use theorems using `fixedBy (Set α) g`, you should `open Pointwise` in your file.

`s ∈ fixedBy (Set α) g` means that `g • s = s`, which is equivalent to say that
`∀ x, g • x ∈ s ↔ x ∈ s` (the translation can be done using `MulAction.set_mem_fixedBy_iff`).

`s ∈ fixedBy (Set α) g` is a weaker statement than `s ⊆ fixedBy α g`: the latter requires that
all points in `s` are fixed by `g`, whereas the former only requires that `g • x ∈ s`.
-/

public section

namespace MulAction
open scoped Pointwise

variable {α : Type*}
variable {G : Type*} [Group G] [MulAction G α]
variable {M : Type*} [Monoid M] [MulAction M α]


section FixedPoints

variable (α) in
/-- In a multiplicative group action, the points fixed by `g` are also fixed by `g⁻¹` -/
@[to_additive (attr := simp)
  /-- In an additive group action, the points fixed by `g` are also fixed by `g⁻¹` -/]
/-
**MulAction.fixedBy_inv** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：fixedBy_inv (g : G) : fixedBy α g⁻¹ = fixedBy α g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_fixedBy`：mem_fixedBy {m : M} {a : α} : a in fixedBy α m ↔ 
m • a = a
· 使用定理 `inv_smul_eq_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, g⁻¹ • a = b ↔ a = g • b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem fixedBy_inv (g : G) : fixedBy α g⁻¹ = fixedBy α g := by
  ext
  rw [mem_fixedBy, mem_fixedBy, inv_smul_eq_iff, eq_comm]

@[to_additive]
/-
**MulAction.smul_mem_fixedBy_iff_mem_fixedBy** 是 Mathlib 中的一个定理，位于命名空间 `MulActio
n`。
形式化陈述：smul_mem_fixedBy_iff_mem_fixedBy {a : α} {g : G} : g • a in fixedBy α g ↔ 
a in fixedBy α g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_fixedBy`：mem_fixedBy {m : M} {a : α} : a in fixedBy α m ↔ 
m • a = a
· 使用引理 `smul_left_cancel_iff`：smul_left_cancel_iff (g : α) {x y : β} : g • x = g
 • y ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem smul_mem_fixedBy_iff_mem_fixedBy {a : α} {g : G} :
    g • a ∈ fixedBy α g ↔ a ∈ fixedBy α g := by
  rw [mem_fixedBy, smul_left_cancel_iff]
  rfl

@[to_additive]
/-
**MulAction.smul_inv_mem_fixedBy_iff_mem_fixedBy** 是 Mathlib 中的一个定理，位于命名空间 `MulA
ction`。
形式化陈述：smul_inv_mem_fixedBy_iff_mem_fixedBy {a : α} {g : G} : g⁻¹ • a in fixedBy 
α g ↔ a in fixedBy α g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.fixedBy_inv`：fixedBy_inv (g : G) : fixedBy α g⁻¹ = fixedBy α g
· 使用定理 `MulAction.smul_mem_fixedBy_iff_mem_fixedBy`：smul_mem_fixedBy_iff_mem_fix
edBy {a : α} {g : G} : g • a in fixedBy α g ↔ a in fixedBy α g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem smul_inv_mem_fixedBy_iff_mem_fixedBy {a : α} {g : G} :
    g⁻¹ • a ∈ fixedBy α g ↔ a ∈ fixedBy α g := by
  rw [← fixedBy_inv, smul_mem_fixedBy_iff_mem_fixedBy, fixedBy_inv]

@[to_additive minimalPeriod_eq_one_iff_fixedBy]
/-
**MulAction.minimalPeriod_eq_one_iff_fixedBy** 是 Mathlib 中的一个定理，位于命名空间 `MulActio
n`。
形式化陈述：minimalPeriod_eq_one_iff_fixedBy {a : α} {g : G} : Function.minimalPeriod 
(fun x => g • x) a = 1 ↔ a in fixedBy α g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.minimalPeriod_eq_one_iff_isFixedPt`：minimalPeriod_eq_one_iff_is
FixedPt : minimalPeriod f x = 1 ↔ IsFixedPt f x
-/
theorem minimalPeriod_eq_one_iff_fixedBy {a : α} {g : G} :
    Function.minimalPeriod (fun x => g • x) a = 1 ↔ a ∈ fixedBy α g :=
  Function.minimalPeriod_eq_one_iff_isFixedPt

@[to_additive]
/-
**MulAction.mem_fixedBy_zpow** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：mem_fixedBy_zpow {g : G} {a : α} (h : a in fixedBy α g) (j : Int) : a in f
ixedBy α (g ^ j)
参数：h : a in fixedBy α g；j : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_fixedBy`：mem_fixedBy {m : M} {a : α} : a in fixedBy α m ↔ 
m • a = a
· 使用定理 `MulAction.zpow_smul_eq_iff_minimalPeriod_dvd`：∀ {α : Type v} {G : Type u
} [inst : Group G] [inst_1 : MulAction G α] {a : G} {b : α} {n : ℤ},   a ^ n • b
 = b ↔ ↑(Function.minimalPeriod (f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulAction.minimalPeriod_eq_one_iff_fixedBy`：minimalPeriod_eq_one_iff_fix
edBy {a : α} {g : G} : Function.minimalPeriod (fun x => g • x) a = 1 ↔ a in fixe
dBy α g
· 使用定理 `Int.natCast_one`：↑1 = 1
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
-/
theorem mem_fixedBy_zpow {g : G} {a : α} (h : a ∈ fixedBy α g) (j : ℤ) :
    a ∈ fixedBy α (g ^ j) := by
  rw [mem_fixedBy, zpow_smul_eq_iff_minimalPeriod_dvd, minimalPeriod_eq_one_iff_fixedBy.mpr h,
    Int.natCast_one]
  exact one_dvd j

@[to_additive]
/-
**MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy** 是 Mathlib 中的一个定理，位于命名空间 `MulAc
tion`。
形式化陈述：mem_fixedBy_zpowers_iff_mem_fixedBy {g : G} {a : α} : (forall j : Int, a i
n fixedBy α (g ^ j)) ↔ a in fixedBy α g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `MulAction.mem_fixedBy_zpow`：mem_fixedBy_zpow {g : G} {a : α} (h : a in f
ixedBy α g) (j : Int) : a in fixedBy α (g ^ j)
-/
theorem mem_fixedBy_zpowers_iff_mem_fixedBy {g : G} {a : α} :
    (∀ j : ℤ, a ∈ fixedBy α (g ^ j)) ↔ a ∈ fixedBy α g :=
  ⟨fun h ↦ by simpa using h 1, fun h j ↦ mem_fixedBy_zpow h j⟩

variable (α) in
@[to_additive]
/-
**MulAction.fixedBy_subset_fixedBy_zpow** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：fixedBy_subset_fixedBy_zpow (g : G) (j : Int) : fixedBy α g subseteq fixed
By α (g ^ j)
参数：g : G；j : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.mem_fixedBy_zpow`：mem_fixedBy_zpow {g : G} {a : α} (h : a in f
ixedBy α g) (j : Int) : a in fixedBy α (g ^ j)
-/
theorem fixedBy_subset_fixedBy_zpow (g : G) (j : ℤ) :
    fixedBy α g ⊆ fixedBy α (g ^ j) :=
  fun _ h ↦ mem_fixedBy_zpow h j

variable (M α) in
@[to_additive (attr := simp)]
/-
**MulAction.fixedBy_one_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：fixedBy_one_eq_univ : fixedBy α (1 : M) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem fixedBy_one_eq_univ : fixedBy α (1 : M) = Set.univ :=
  Set.eq_univ_iff_forall.mpr <| one_smul M

variable (α) in
@[to_additive]
/-
**MulAction.fixedBy_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：fixedBy_mul (m₁ m₂ : M) : fixedBy α m₁ inter fixedBy α m₂ subseteq fixedBy
 α (m₁ * m₂)
参数：m₁ m₂ : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_fixedBy`：mem_fixedBy {m : M} {a : α} : a in fixedBy α m ↔ 
m • a = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem fixedBy_mul (m₁ m₂ : M) : fixedBy α m₁ ∩ fixedBy α m₂ ⊆ fixedBy α (m₁ * m₂) := by
  intro a ⟨h₁, h₂⟩
  rw [mem_fixedBy, mul_smul, h₂, h₁]

variable (α) in
@[to_additive]
/-
**MulAction.smul_fixedBy** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：smul_fixedBy (g h : G) : h • fixedBy α g = fixedBy α (h * g * h⁻¹)
参数：g h : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `smul_eq_iff_eq_inv_smul`：smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g •
 x = y ↔ x = g⁻¹ • y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem smul_fixedBy (g h : G) :
    h • fixedBy α g = fixedBy α (h * g * h⁻¹) := by
  ext a
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem, mem_fixedBy, mul_smul, smul_eq_iff_eq_inv_smul h]
/-
**MulAction.fixedBy_mul_eq_empty_iff** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：fixedBy_mul_eq_empty_iff [IsRightCancelMul M] {m : M} : fixedBy M m = ∅ ↔ 
m != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma fixedBy_mul_eq_empty_iff [IsRightCancelMul M] {m : M} :
    fixedBy M m = ∅ ↔ m ≠ 1 := by
  simp [MulAction.fixedBy, Set.eq_empty_iff_forall_notMem]
/-
**MulAction.fixedBy_mul_op_eq_empty_iff** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：fixedBy_mul_op_eq_empty_iff [IsLeftCancelMul M] {m : M} : fixedBy M (MulOp
posite.op m) = ∅ ↔ m != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma fixedBy_mul_op_eq_empty_iff [IsLeftCancelMul M] {m : M} :
    fixedBy M (MulOpposite.op m) = ∅ ↔ m ≠ 1 := by
  simp [MulAction.fixedBy, Set.eq_empty_iff_forall_notMem]

end FixedPoints

section Pointwise

/-!
### `fixedBy` sets of the pointwise group action

The theorems below need the `Pointwise` scoped to be opened (using `open Pointwise`)
to be used effectively.
-/

/--
If a set `s : Set α` is in `fixedBy (Set α) g`, then all points of `s` will stay in `s` after being
moved by `g`.
-/
@[to_additive /-- If a set `s : Set α` is in `fixedBy (Set α) g`, then all points of `s` will stay
in `s` after being moved by `g`. -/]
/-
**MulAction.set_mem_fixedBy_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：set_mem_fixedBy_iff (s : Set α) (g : G) : s in fixedBy (Set α) g ↔ forall 
x, g • x in s ↔ x in s
参数：s : Set α；g : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem set_mem_fixedBy_iff (s : Set α) (g : G) :
    s ∈ fixedBy (Set α) g ↔ ∀ x, g • x ∈ s ↔ x ∈ s := by
  simp_rw [mem_fixedBy, ← eq_inv_smul_iff, Set.ext_iff, Set.mem_inv_smul_set_iff, Iff.comm]

@[to_additive]
/-
**MulAction.smul_mem_of_set_mem_fixedBy** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：smul_mem_of_set_mem_fixedBy {s : Set α} {g : G} (s_in_fixedBy : s in fixed
By (Set α) g) {x : α} : g • x in s ↔ x in s
参数：s_in_fixedBy : s in fixedBy (Set α) g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulAction.set_mem_fixedBy_iff`：set_mem_fixedBy_iff (s : Set α) (g : G) :
 s in fixedBy (Set α) g ↔ forall x, g • x in s ↔ x in s
-/
theorem smul_mem_of_set_mem_fixedBy {s : Set α} {g : G} (s_in_fixedBy : s ∈ fixedBy (Set α) g)
    {x : α} : g • x ∈ s ↔ x ∈ s := (set_mem_fixedBy_iff s g).mp s_in_fixedBy x

/--
If `s ⊆ fixedBy α g`, then `g • s = s`, which means that `s ∈ fixedBy (Set α) g`.

Note that the reverse implication is in general not true, as `s ∈ fixedBy (Set α) g` is a
weaker statement (it allows for points `x ∈ s` for which `g • x ≠ x` and `g • x ∈ s`).
-/
@[to_additive /-- If `s ⊆ fixedBy α g`, then `g +ᵥ s = s`, which means that `s ∈ fixedBy (Set α) g`.

Note that the reverse implication is in general not true, as `s ∈ fixedBy (Set α) g` is a
weaker statement (it allows for points `x ∈ s` for which `g +ᵥ x ≠ x` and `g +ᵥ x ∈ s`). -/]
/-
**MulAction.set_mem_fixedBy_of_subset_fixedBy** 是 Mathlib 中的一个定理，位于命名空间 `MulActi
on`。
形式化陈述：set_mem_fixedBy_of_subset_fixedBy {s : Set α} {g : G} (s_ss_fixedBy : s su
bseteq fixedBy α g) : s in fixedBy (Set α) g
参数：s_ss_fixedBy : s subseteq fixedBy α g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.fixedBy_inv`：fixedBy_inv (g : G) : fixedBy α g⁻¹ = fixedBy α g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_inv_smul_set_iff`：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in
 A
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
theorem set_mem_fixedBy_of_subset_fixedBy {s : Set α} {g : G} (s_ss_fixedBy : s ⊆ fixedBy α g) :
    s ∈ fixedBy (Set α) g := by
  rw [← fixedBy_inv]
  ext x
  rw [Set.mem_inv_smul_set_iff]
  refine ⟨fun gxs => ?xs, fun xs => (s_ss_fixedBy xs).symm ▸ xs⟩
  rw [← fixedBy_inv] at s_ss_fixedBy
  rwa [← s_ss_fixedBy gxs, inv_smul_smul] at gxs
/-
**MulAction.smul_subset_of_set_mem_fixedBy** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`
。
形式化陈述：smul_subset_of_set_mem_fixedBy {s t : Set α} {g : G} (t_ss_s : t subseteq 
s) (s_in_fixedBy : s in fixedBy (Set α) g) : g • t subseteq s
参数：t_ss_s : t subseteq s；s_in_fixedBy : s in fixedBy (Set α) g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.smul_set_subset_smul_set_iff`：smul_set_subset_smul_set_iff : a • A s
ubseteq a • B ↔ A subseteq B
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
theorem smul_subset_of_set_mem_fixedBy {s t : Set α} {g : G} (t_ss_s : t ⊆ s)
    (s_in_fixedBy : s ∈ fixedBy (Set α) g) : g • t ⊆ s :=
  (Set.smul_set_subset_smul_set_iff.mpr t_ss_s).trans s_in_fixedBy.subset

/-!
If a set `s : Set α` is a superset of `(MulAction.fixedBy α g)ᶜ` (resp. `(AddAction.fixedBy α g)ᶜ`),
then no point or subset of `s` can be moved outside of `s` by the group action of `g`.
-/

/-- If `(fixedBy α g)ᶜ ⊆ s`, then `g` cannot move a point of `s` outside of `s`. -/
@[to_additive /-- If `(fixedBy α g)ᶜ ⊆ s`, then `g` cannot move a point of `s` outside of `s`. -/]
/-
**MulAction.set_mem_fixedBy_of_movedBy_subset** 是 Mathlib 中的一个定理，位于命名空间 `MulActi
on`。
形式化陈述：set_mem_fixedBy_of_movedBy_subset {s : Set α} {g : G} (s_subset : (fixedBy
 α g)ᶜ subseteq s) : s in fixedBy (Set α) g
参数：s_subset : (fixedBy α g)ᶜ subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.fixedBy_inv`：fixedBy_inv (g : G) : fixedBy α g⁻¹ = fixedBy α g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_inv_smul_set_iff`：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in
 A
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `MulAction.smul_mem_fixedBy_iff_mem_fixedBy`：smul_mem_fixedBy_iff_mem_fix
edBy {a : α} {g : G} : g • a in fixedBy α g ↔ a in fixedBy α g

--- 原说明 ---
If `(fixedBy α g)ᶜ ⊆ s`, then `g` cannot move a point of `s` outside of `s`.
-/
theorem set_mem_fixedBy_of_movedBy_subset {s : Set α} {g : G} (s_subset : (fixedBy α g)ᶜ ⊆ s) :
    s ∈ fixedBy (Set α) g := by
  rw [← fixedBy_inv]
  ext a
  rw [Set.mem_inv_smul_set_iff]
  by_cases a ∈ fixedBy α g
  case pos a_fixed =>
    rw [a_fixed]
  case neg a_moved =>
    constructor <;> (intro; apply s_subset)
    · exact a_moved
    · rwa [Set.mem_compl_iff, smul_mem_fixedBy_iff_mem_fixedBy]

end Pointwise

section Commute

/-!
## Pointwise image of the `fixedBy` set by a commuting group element

If two group elements `g` and `h` commute, then `g` fixes `h • x` (resp. `h +ᵥ x`)
if and only if `g` fixes `x`.

This is equivalent to say that if `Commute g h`, then `fixedBy α g ∈ fixedBy (Set α) h` and
`(fixedBy α g)ᶜ ∈ fixedBy (Set α) h`.
-/

/--
If `g` and `h` commute, then `g` fixes `h • x` iff `g` fixes `x`.
This is equivalent to say that the set `fixedBy α g` is fixed by `h`.
-/
@[to_additive /-- If `g` and `h` commute, then `g` fixes `h +ᵥ x` iff `g` fixes `x`.
This is equivalent to say that the set `fixedBy α g` is fixed by `h`. -/]
/-
**MulAction.fixedBy_mem_fixedBy_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`
。
形式化陈述：fixedBy_mem_fixedBy_of_commute {g h : G} (comm : Commute g h) : (fixedBy α
 g) in fixedBy (Set α) h
参数：comm : Commute g h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
· 使用定理 `MulAction.mem_fixedBy`：mem_fixedBy {m : M} {a : α} : a in fixedBy α m ↔ 
m • a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Commute.inv_right`：∀ {G : Type u_1} [inst : Group G] {a b : G}, Commute 
a b → Commute a b⁻¹
· 使用引理 `smul_left_cancel_iff`：smul_left_cancel_iff (g : α) {x y : β} : g • x = g
 • y ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem fixedBy_mem_fixedBy_of_commute {g h : G} (comm : Commute g h) :
    (fixedBy α g) ∈ fixedBy (Set α) h := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_fixedBy, ← mul_smul, comm.inv_right, mul_smul,
    smul_left_cancel_iff, mem_fixedBy]

/--
If `g` and `h` commute, then `g` fixes `(h ^ j) • x` iff `g` fixes `x`.
-/
@[to_additive /-- If `g` and `h` commute, then `g` fixes `(j • h) +ᵥ x` iff `g` fixes `x`. -/]
/-
**MulAction.smul_zpow_fixedBy_eq_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `MulAction
`。
形式化陈述：smul_zpow_fixedBy_eq_of_commute {g h : G} (comm : Commute g h) (j : Int) :
 h ^ j • fixedBy α g = fixedBy α g
参数：comm : Commute g h；j : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.fixedBy_subset_fixedBy_zpow`：fixedBy_subset_fixedBy_zpow (g : 
G) (j : Int) : fixedBy α g subseteq fixedBy α (g ^ j)
· 使用定理 `MulAction.fixedBy_mem_fixedBy_of_commute`：fixedBy_mem_fixedBy_of_commute
 {g h : G} (comm : Commute g h) : (fixedBy α g) in fixedBy (Set α) h

--- 原说明 ---
If `g` and `h` commute, then `g` fixes `(h ^ j) • x` iff `g` fixes `x`.
-/
theorem smul_zpow_fixedBy_eq_of_commute {g h : G} (comm : Commute g h) (j : ℤ) :
    h ^ j • fixedBy α g = fixedBy α g :=
  fixedBy_subset_fixedBy_zpow (Set α) h j (fixedBy_mem_fixedBy_of_commute comm)

/--
If `g` and `h` commute, then `g` moves `h • x` iff `g` moves `x`.
This is equivalent to say that the set `(fixedBy α g)ᶜ` is fixed by `h`.
-/
@[to_additive /-- If `g` and `h` commute, then `g` moves `h +ᵥ x` iff `g` moves `x`.
This is equivalent to say that the set `(fixedBy α g)ᶜ` is fixed by `h`. -/]
/-
**MulAction.movedBy_mem_fixedBy_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`
。
形式化陈述：movedBy_mem_fixedBy_of_commute {g h : G} (comm : Commute g h) : (fixedBy α
 g)ᶜ in fixedBy (Set α) h
参数：comm : Commute g h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_fixedBy`：mem_fixedBy {m : M} {a : α} : a in fixedBy α m ↔ 
m • a = a
· 使用定理 `Set.smul_set_compl`：smul_set_compl : a • sᶜ = (a • s)ᶜ
· 使用定理 `MulAction.fixedBy_mem_fixedBy_of_commute`：fixedBy_mem_fixedBy_of_commute
 {g h : G} (comm : Commute g h) : (fixedBy α g) in fixedBy (Set α) h
-/
theorem movedBy_mem_fixedBy_of_commute {g h : G} (comm : Commute g h) :
    (fixedBy α g)ᶜ ∈ fixedBy (Set α) h := by
  rw [mem_fixedBy, Set.smul_set_compl, fixedBy_mem_fixedBy_of_commute comm]

/--
If `g` and `h` commute, then `g` moves `h ^ j • x` iff `g` moves `x`.
-/
@[to_additive /-- If `g` and `h` commute, then `g` moves `(j • h) +ᵥ x` iff `g` moves `x`. -/]
/-
**MulAction.smul_zpow_movedBy_eq_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `MulAction
`。
形式化陈述：smul_zpow_movedBy_eq_of_commute {g h : G} (comm : Commute g h) (j : Int) :
 h ^ j • (fixedBy α g)ᶜ = (fixedBy α g)ᶜ
参数：comm : Commute g h；j : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.fixedBy_subset_fixedBy_zpow`：fixedBy_subset_fixedBy_zpow (g : 
G) (j : Int) : fixedBy α g subseteq fixedBy α (g ^ j)
· 使用定理 `MulAction.movedBy_mem_fixedBy_of_commute`：movedBy_mem_fixedBy_of_commute
 {g h : G} (comm : Commute g h) : (fixedBy α g)ᶜ in fixedBy (Set α) h

--- 原说明 ---
If `g` and `h` commute, then `g` moves `h ^ j • x` iff `g` moves `x`.
-/
theorem smul_zpow_movedBy_eq_of_commute {g h : G} (comm : Commute g h) (j : ℤ) :
    h ^ j • (fixedBy α g)ᶜ = (fixedBy α g)ᶜ :=
  fixedBy_subset_fixedBy_zpow (Set α) h j (movedBy_mem_fixedBy_of_commute comm)

end Commute

section Faithful

variable [FaithfulSMul G α]
variable [FaithfulSMul M α]

/-- If the multiplicative action of `M` on `α` is faithful,
then `fixedBy α m = Set.univ` implies that `m = 1`. -/
@[to_additive /-- If the additive action of `M` on `α` is faithful,
then `fixedBy α m = Set.univ` implies that `m = 1`. -/]
/-
**MulAction.fixedBy_eq_univ_iff_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：fixedBy_eq_univ_iff_eq_one {m : M} : fixedBy α m = Set.univ ↔ m = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `smul_left_injective'`：smul_left_injective' [SMul M α] [FaithfulSMul M α]
 : Injective ((· • ·) : M -> α -> α)
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fixedBy_eq_univ_iff_eq_one {m : M} : fixedBy α m = Set.univ ↔ m = 1 := by
  rw [← (smul_left_injective' (M := M) (α := α)).eq_iff, Set.eq_univ_iff_forall]
  simp_rw [funext_iff, one_smul, mem_fixedBy]

/--
If the image of the `(fixedBy α g)ᶜ` set by the pointwise action of `h: G`
is disjoint from `(fixedBy α g)ᶜ`, then `g` and `h` cannot commute.
-/
@[to_additive /-- If the image of the `(fixedBy α g)ᶜ` set by the pointwise action of `h: G`
is disjoint from `(fixedBy α g)ᶜ`, then `g` and `h` cannot commute. -/]
/-
**MulAction.not_commute_of_disjoint_movedBy_preimage** 是 Mathlib 中的一个定理，位于命名空间 `
MulAction`。
形式化陈述：not_commute_of_disjoint_movedBy_preimage {g h : G} (ne_one : g != 1) (disj
oint : Disjoint (fixedBy α g)ᶜ (h • (fixedBy α g)ᶜ)) : ¬Commute g h
参数：ne_one : g != 1；disjoint : Disjoint (fixedBy α g)ᶜ (h • (fixedBy α g)ᶜ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.fixedBy_eq_univ_iff_eq_one`：fixedBy_eq_univ_iff_eq_one {m : M}
 : fixedBy α m = Set.univ ↔ m = 1
· 使用定理 `compl_inj_iff`：compl_inj_iff : xᶜ = yᶜ ↔ x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `Set.bot_eq_empty`：bot_eq_empty : (⊥ : Set α) = ∅
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
· 使用定理 `MulAction.movedBy_mem_fixedBy_of_commute`：movedBy_mem_fixedBy_of_commute
 {g h : G} (comm : Commute g h) : (fixedBy α g)ᶜ in fixedBy (Set α) h
-/
theorem not_commute_of_disjoint_movedBy_preimage {g h : G} (ne_one : g ≠ 1)
    (disjoint : Disjoint (fixedBy α g)ᶜ (h • (fixedBy α g)ᶜ)) : ¬Commute g h := by
  contrapose ne_one with comm
  rwa [movedBy_mem_fixedBy_of_commute comm, disjoint_self, Set.bot_eq_empty, ← Set.compl_univ,
    compl_inj_iff, fixedBy_eq_univ_iff_eq_one] at disjoint

end Faithful

end MulAction

namespace MulActionHom

/-- `MulActionHom` maps `fixedPoints` to `fixedPoints`. -/
@[to_additive /-- `AddActionHom` maps `fixedPoints` to `fixedPoints`. -/]
/-
**MulActionHom.map_mem_fixedPoints** 是 Mathlib 中的一个引理，位于命名空间 `MulActionHom`。
形式化陈述：map_mem_fixedPoints {G A B : Type*} [Monoid G] [MulAction G A] [MulAction 
G B] (f : A ->[G] B) {H : Submonoid G} {a : A} (ha : a in MulAction.fixedPoints 
H A) : f a in MulAction.fixedPoints H B
参数：f : A ->[G] B；ha : a in MulAction.fixedPoints H A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulActionHom.map_smul`：∀ {M' : Type u_1} {X : Type u_5} [inst : SMul M' 
X] {Y : Type u_6} [inst_1 : SMul M' Y] (f : X →ₑ[id] Y) (m : M')   (x : X), f (m
 • x) = m •…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`MulActionHom` maps `fixedPoints` to `fixedPoints`.
-/
lemma map_mem_fixedPoints {G A B : Type*} [Monoid G] [MulAction G A] [MulAction G B]
    (f : A →[G] B) {H : Submonoid G} {a : A} (ha : a ∈ MulAction.fixedPoints H A) :
    f a ∈ MulAction.fixedPoints H B := by
  intro ⟨h, _⟩
  simp_all [← f.map_smul h a]

/-- `MulActionHom` maps `fixedBy` to `fixedBy`. -/
@[to_additive /-- `AddActionHom` maps `fixedBy` to `fixedBy`. -/]
/-
**MulActionHom.map_mem_fixedBy** 是 Mathlib 中的一个引理，位于命名空间 `MulActionHom`。
形式化陈述：map_mem_fixedBy {G A B : Type*} [Monoid G] [MulAction G A] [MulAction G B]
 (f : A ->[G] B) {g : G} {a : A} (ha : a in MulAction.fixedBy A g) : f a in MulA
ction.fixedBy B g
参数：f : A ->[G] B；ha : a in MulAction.fixedBy A g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `instMulActionSemiHomClassMulActionHom`：∀ {M : Type u_2} {N : Type u_3} (
φ : M → N) (X : Type u_5) [inst : SMul M X] (Y : Type u_6) [inst_1 : SMul N Y], 
  MulActionSemiHomClass (X …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
`MulActionHom` maps `fixedBy` to `fixedBy`.
-/
lemma map_mem_fixedBy {G A B : Type*} [Monoid G] [MulAction G A] [MulAction G B]
    (f : A →[G] B) {g : G} {a : A} (ha : a ∈ MulAction.fixedBy A g) :
    f a ∈ MulAction.fixedBy B g := by
  simpa using congr_arg f ha

end MulActionHom

