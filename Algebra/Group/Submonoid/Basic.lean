/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Basic
public import Mathlib.Algebra.Group.Units.Defs

/-!
# Submonoids: `CompleteLattice` structure

This file defines a `CompleteLattice` structure on `Submonoid`s, define the closure of a set as the
minimal submonoid that includes this set, and prove a few results about extending properties from a
dense set (i.e. a set with `closure s = ⊤`) to the whole monoid, see `Submonoid.dense_induction` and
`MonoidHom.ofClosureEqTopLeft`/`MonoidHom.ofClosureEqTopRight`.

## Main definitions

For each of the following definitions in the `Submonoid` namespace, there is a corresponding
definition in the `AddSubmonoid` namespace.

* `Submonoid.copy` : copy of a submonoid with `carrier` replaced by a set that is equal but possibly
  not definitionally equal to the carrier of the original `Submonoid`.
* `Submonoid.closure` :  monoid closure of a set, i.e., the least submonoid that includes the set.
* `Submonoid.gi` : `closure : Set M → Submonoid M` and coercion `coe : Submonoid M → Set M`
  form a `GaloisInsertion`;
* `MonoidHom.eqLocus`: the submonoid of elements `x : M` such that `f x = g x`;
* `MonoidHom.ofClosureEqTopRight`:  if a map `f : M → N` between two monoids satisfies
  `f 1 = 1` and `f (x * y) = f x * f y` for `y` from some dense set `s`, then `f` is a monoid
  homomorphism. E.g., if `f : ℕ → M` satisfies `f 0 = 0` and `f (x + 1) = f x + f 1`, then `f` is
  an additive monoid homomorphism.

## Implementation notes

Submonoid inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a submonoid's underlying set.

Note that `Submonoid M` does not actually require `Monoid M`, instead requiring only the weaker
`MulOneClass M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers. `Submonoid` is implemented by extending `Subsemigroup` requiring `one_mem'`.

## Tags
submonoid, submonoids
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {M : Type*} {N : Type*}
variable {A : Type*}

section NonAssoc

variable [MulOneClass M] {s : Set M}
variable [AddZeroClass A] {t : Set A}

namespace Submonoid

variable (S : Submonoid M)

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (Submonoid M) :=
  ⟨fun s =>
    { carrier := ⋂ t ∈ s, ↑t
      one_mem' := Set.mem_biInter fun i _ => i.one_mem
      mul_mem' := fun hx hy =>
        Set.mem_biInter fun i h =>
          i.mul_mem (by apply Set.mem_iInter₂.1 hx i h) (by apply Set.mem_iInter₂.1 hy i h) }⟩

@[to_additive (attr := simp, norm_cast)]
/-
**Submonoid.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_sInf (S : Set (Submonoid M)) : ((sInf S : Submonoid M) : Set M) = ⋂ s 
in S, ↑s
参数：S : Set (Submonoid M)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sInf (S : Set (Submonoid M)) : ((sInf S : Submonoid M) : Set M) = ⋂ s ∈ S, ↑s :=
  rfl

@[to_additive (attr := simp)]
/-
**Submonoid.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_sInf {S : Set (Submonoid M)} {x : M} : x in sInf S ↔ forall p in S, x 
in p
参数：Submonoid M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_sInf {S : Set (Submonoid M)} {x : M} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂

@[to_additive (attr := simp)]
/-
**Submonoid.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_iInf {ι : Sort*} {S : ι -> Submonoid M} {x : M} : x in ⨅ i, S i ↔ fora
ll i, x in S i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iInf {ι : Sort*} {S : ι → Submonoid M} {x : M} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[to_additive (attr := simp, norm_cast)]
/-
**Submonoid.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_iInf {ι : Sort*} {S : ι -> Submonoid M} : (↑(⨅ i, S i) : Set M) = ⋂ i,
 S i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biInter_range`：biInter_range {f : ι -> α} {g : α -> Set β} : ⋂ x in 
range f, g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf {ι : Sort*} {S : ι → Submonoid M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

/-- Submonoids of a monoid form a complete lattice. -/
@[to_additive /-- The `AddSubmonoid`s of an `AddMonoid` form a complete lattice. -/]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Submonoids of a monoid form a complete lattice.
-/
instance : CompleteLattice (Submonoid M) :=
  { (completeLatticeOfInf (Submonoid M)) fun _ =>
      .of_image SetLike.coe_subset_coe isGLB_biInf with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun S _ hx => (mem_bot.1 hx).symm ▸ S.one_mem
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    le_inf := fun _ _ _ ha hb _ hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

/-- The `Submonoid` generated by a set. -/
@[to_additive /-- The `AddSubmonoid` generated by a set -/]
/-
**Submonoid.closure** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：closure (s : Set M) : Submonoid M
参数：s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Submonoid` generated by a set.
-/
def closure (s : Set M) : Submonoid M :=
  sInf { S | s ⊆ S }

@[to_additive]
/-
**Submonoid.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_closure {x : M} : x in closure s ↔ forall S : Submonoid M, s subseteq 
S -> x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.mem_sInf`：mem_sInf {S : Set (Submonoid M)} {x : M} : x in sInf
 S ↔ forall p in S, x in p
-/
theorem mem_closure {x : M} : x ∈ closure s ↔ ∀ S : Submonoid M, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The submonoid generated by a set includes the set. -/
@[to_additive (attr := simp, aesop safe 20 (rule_sets := [SetLike]))
  /-- The `AddSubmonoid` generated by a set includes the set. -/]
/-
**Submonoid.subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：subset_closure : s subseteq closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.mem_closure`：mem_closure {x : M} : x in closure s ↔ forall S :
 Submonoid M, s subseteq S -> x in S
-/
theorem subset_closure : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx

@[to_additive (attr := aesop 80% (rule_sets := [SetLike]))]
/-
**Submonoid.mem_closure_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_closure_of_mem {s : Set M} {x : M} (hx : x in s) : x in closure s
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
-/
theorem mem_closure_of_mem {s : Set M} {x : M} (hx : x ∈ s) : x ∈ closure s := subset_closure hx

@[to_additive]
/-
**Submonoid.notMem_of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：notMem_of_notMem_closure {P : M} (hP : P ∉ closure s) : P ∉ s
参数：hP : P ∉ closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
-/
theorem notMem_of_notMem_closure {P : M} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

variable {S}

open Set

/-- A submonoid `S` includes `closure s` if and only if it includes `s`. -/
@[to_additive (attr := simp)
/-- An additive submonoid `S` includes `closure s` if and only if it includes `s`. -/]
/-
**Submonoid.closure_le** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_le : closure s <= S ↔ s subseteq S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem closure_le : closure s ≤ S ↔ s ⊆ S :=
  ⟨Subset.trans subset_closure, fun h => sInf_le h⟩

/-- Submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[to_additive (attr := gcongr)
  /-- Additive submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
  then `closure s ≤ closure t`. -/]
/-
**Submonoid.closure_mono** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_mono ⦃s t : Set M⦄ (h : s subseteq t) : closure s <= closure t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
-/
theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Subset.trans h subset_closure

@[to_additive]
/-
**Submonoid.closure_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_eq_of_le (h₁ : s subseteq S) (h₂ : S <= closure s) : closure s = S
参数：h₁ : s subseteq S；h₂ : S <= closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
-/
theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure s) : closure s = S :=
  le_antisymm (closure_le.2 h₁) h₂

variable (S)

/-- An induction principle for closure membership. If `p` holds for `1` and all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[to_additive (attr := elab_as_elim)
  /-- An induction principle for additive closure membership. If `p` holds for `0` and all
  elements of `s`, and is preserved under addition, then `p` holds for all elements of the
  additive closure of `s`. -/]
/-
**Submonoid.closure_induction** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_induction {s : Set M} {motive : (x : M) -> x in closure s -> Prop}
 (mem : forall (x) (h : x in s), motive x (subset_closure h)) (one : motive 1 (o
ne_mem _)) (mul : forall x y hx hy, motive x hx -> motive y hy -> motive (x * y)
 (mul_mem hx hy)) {x} (hx : x in closure s) : motive x hx
参数：x : M；mem : forall (x) (h : x in s), motive x (subset_closure h)；one : motive
 1 (one_mem _)；mul : forall x y hx hy, motive x hx -> motive y hy -> motive (x *
 y) (mul_mem hx hy)；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
-/
theorem closure_induction {s : Set M} {motive : (x : M) → x ∈ closure s → Prop}
    (mem : ∀ (x) (h : x ∈ s), motive x (subset_closure h)) (one : motive 1 (one_mem _))
    (mul : ∀ x y hx hy, motive x hx → motive y hy → motive (x * y) (mul_mem hx hy)) {x}
    (hx : x ∈ closure s) : motive x hx :=
  let S : Submonoid M :=
    { carrier := { x | ∃ hx, motive x hx }
      one_mem' := ⟨_, one⟩
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩ }
  closure_le (S := S) |>.mpr (fun y hy ↦ ⟨subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

/-- An induction principle for closure membership for predicates with two arguments. -/
@[to_additive (attr := elab_as_elim)
  /-- An induction principle for additive closure membership for predicates with two arguments. -/]
/-
**Submonoid.closure_induction** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_induction {s : Set M} {motive : (x : M) -> x in closure s -> Prop}
 (mem : forall (x) (h : x in s), motive x (subset_closure h)) (one : motive 1 (o
ne_mem _)) (mul : forall x y hx hy, motive x hx -> motive y hy -> motive (x * y)
 (mul_mem hx hy)) {x} (hx : x in closure s) : motive x hx
参数：x : M；mem : forall (x) (h : x in s), motive x (subset_closure h)；one : motive
 1 (one_mem _)；mul : forall x y hx hy, motive x hx -> motive y hy -> motive (x *
 y) (mul_mem hx hy)；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
-/
theorem closure_induction₂ {motive : (x y : M) → x ∈ closure s → y ∈ closure s → Prop}
    (mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), motive x y (subset_closure hx) (subset_closure hy))
    (one_left : ∀ x hx, motive 1 x (one_mem _) hx) (one_right : ∀ x hx, motive x 1 hx (one_mem _))
    (mul_left : ∀ x y z hx hy hz,
      motive x z hx hz → motive y z hy hz → motive (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz,
      motive z x hz hx → motive z y hz hy → motive z (x * y) hz (mul_mem hx hy))
    {x y : M} (hx : x ∈ closure s) (hy : y ∈ closure s) : motive x y hx hy := by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem _ _ h hz
    | one => exact one_left _ (subset_closure hz)
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ hx h₁ h₂

/-- If `s` is a dense set in a monoid `M`, `Submonoid.closure s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, verify `p 1`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
@[to_additive (attr := elab_as_elim)
  /-- If `s` is a dense set in an additive monoid `M`, `AddSubmonoid.closure s = ⊤`, then in
  order to prove that some predicate `p` holds for all `x : M` it suffices to verify `p x` for
  `x ∈ s`, verify `p 0`, and verify that `p x` and `p y` imply `p (x + y)`. -/]
/-
**Submonoid.dense_induction** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：dense_induction {motive : M -> Prop} (s : Set M) (closure : closure s = ⊤)
 (mem : forall x in s, motive x) (one : motive 1) (mul : forall x y, motive x ->
 motive y -> motive (x * y)) (x : M) : motive x
参数：s : Set M；closure : closure s = ⊤；mem : forall x in s, motive x；one : motive 
1；mul : forall x y, motive x -> motive y -> motive (x * y)；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `Submonoid.mem_top`：mem_top (x : M) : x in (⊤ : Submonoid M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dense_induction {motive : M → Prop} (s : Set M) (closure : closure s = ⊤)
    (mem : ∀ x ∈ s, motive x) (one : motive 1) (mul : ∀ x y, motive x → motive y → motive (x * y))
    (x : M) : motive x := by
  induction closure.symm ▸ mem_top x using closure_induction with
  | mem _ h => exact mem _ h
  | one => exact one
  | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂

/-! The argument `s : Set M` is explicit in `Submonoid.dense_induction` because the type of the
induction variable, namely `x : M`, does not reference `x`. Making `s` explicit allows the user
to apply the induction principle while deferring the proof of `closure s = ⊤` without creating
metavariables, as in the following example. -/

/-
**Submonoid.** 是 Mathlib 中的一个示例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The argument `s : Set M` is explicit in `Submonoid.dense_induction` because the 
type of the
induction variable, namely `x : M`, does not reference `x`. Making `s` explicit 
allows the user
to apply the induction principle while deferring the proof of `closure s = ⊤` wi
thout creating
metavariables, as in the following example.
-/
example {p : M → Prop} (s : Set M) (closure : closure s = ⊤) (mem : ∀ x ∈ s, p x)
    (one : p 1) (mul : ∀ x y, p x → p y → p (x * y)) (x : M) : p x := by
  induction x using dense_induction s with
  | closure => exact closure
  | mem x hx => exact mem x hx
  | one => exact one
  | mul _ _ h₁ h₂ => exact mul _ _ h₁ h₂

/-- The `Submonoid.closure` of a set is the union of `{1}` and its `Subsemigroup.closure`. -/
/-
**Submonoid.closure_eq_one_union** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：closure_eq_one_union (s : Set M) : closure s = {(1 : M)} union (Subsemigro
up.closure s : Set M)
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
The `Submonoid.closure` of a set is the union of `{1}` and its `Subsemigroup.clo
sure`.
-/
lemma closure_eq_one_union (s : Set M) :
    closure s = {(1 : M)} ∪ (Subsemigroup.closure s : Set M) := by
  apply le_antisymm
  · intro x hx
    induction hx using closure_induction with
    | mem x hx => exact Or.inr <| Subsemigroup.subset_closure hx
    | one => exact Or.inl <| by simp
    | mul x hx y hy hx hy =>
      push _ ∈ _ at hx hy
      obtain ⟨(rfl | hx), (rfl | hy)⟩ := And.intro hx hy
      all_goals simp_all [mul_mem]
  · rintro x (hx | hx)
    · exact (show x = 1 by simpa using hx) ▸ one_mem (closure s)
    · exact Subsemigroup.closure_le.mpr subset_closure hx

variable (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive /-- `closure` forms a Galois insertion with the coercion to set. -/]
/-
**Submonoid.gi** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：(M : Type u_1) → [inst : MulOneClass M] → GaloisInsertion Submonoid.closur
e SetLike.coe
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S

--- 原说明 ---
`closure` forms a Galois insertion with the coercion to set.
-/
protected def gi : GaloisInsertion (@closure M _) SetLike.coe where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

variable {M}

/-- Closure of a submonoid `S` equals `S`. -/
@[to_additive (attr := simp) /-- Additive closure of an additive submonoid `S` equals `S` -/]
/-
**Submonoid.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_eq : closure (S : Set M) = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b

--- 原说明 ---
Closure of a submonoid `S` equals `S`.
-/
theorem closure_eq : closure (S : Set M) = S :=
  (Submonoid.gi M).l_u_eq S

@[to_additive (attr := simp)]
/-
**Submonoid.closure_empty** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_empty : closure (∅ : Set M) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem closure_empty : closure (∅ : Set M) = ⊥ :=
  (Submonoid.gi M).gc.l_bot

@[to_additive (attr := simp)]
/-
**Submonoid.closure_univ** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_univ : closure (univ : Set M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.closure_eq`：closure_eq : closure (S : Set M) = S
· 使用定理 `Submonoid.coe_top`：coe_top : ((⊤ : Submonoid M) : Set M) = Set.univ
-/
theorem closure_univ : closure (univ : Set M) = ⊤ :=
  @coe_top M _ ▸ closure_eq ⊤

@[to_additive]
/-
**Submonoid.closure_union** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_union (s t : Set M) : closure (s union t) = closure s ⊔ closure t
参数：s t : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem closure_union (s t : Set M) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Submonoid.gi M).gc.l_sup

@[to_additive]
/-
**Submonoid.sup_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：sup_eq_closure (N N' : Submonoid M) : N ⊔ N' = closure ((N : Set M) union 
(N' : Set M))
参数：N N' : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.closure_union`：closure_union (s t : Set M) : closure (s union 
t) = closure s ⊔ closure t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submonoid.closure_eq`：closure_eq : closure (S : Set M) = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup_eq_closure (N N' : Submonoid M) : N ⊔ N' = closure ((N : Set M) ∪ (N' : Set M)) := by
  simp_rw [closure_union, closure_eq]

@[to_additive]
/-
**Submonoid.closure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_iUnion {ι} (s : ι -> Set M) : closure (⋃ i, s i) = ⨆ i, closure (s
 i)
参数：s : ι -> Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem closure_iUnion {ι} (s : ι → Set M) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Submonoid.gi M).gc.l_iSup

@[to_additive]
/-
**Submonoid.closure_singleton_le_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_singleton_le_iff_mem (m : M) (p : Submonoid M) : closure {m} <= p 
↔ m in p
参数：m : M；p : Submonoid M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem closure_singleton_le_iff_mem (m : M) (p : Submonoid M) : closure {m} ≤ p ↔ m ∈ p := by
  rw [closure_le, singleton_subset_iff, SetLike.mem_coe]

@[to_additive (attr := simp)]
/-
**Submonoid.closure_insert_one** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_insert_one (s : Set M) : closure (insert 1 s) = closure s
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Submonoid.closure_union`：closure_union (s t : Set M) : closure (s union 
t) = closure s ⊔ closure t
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `Submonoid.closure_singleton_le_iff_mem`：closure_singleton_le_iff_mem (m 
: M) (p : Submonoid M) : closure {m} <= p ↔ m in p
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
theorem closure_insert_one (s : Set M) : closure (insert 1 s) = closure s := by
  rw [insert_eq, closure_union, sup_eq_right, closure_singleton_le_iff_mem]
  apply one_mem

@[to_additive]
/-
**Submonoid.mem_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_iSup {ι : Sort*} (p : ι -> Submonoid M) {m : M} : (m in ⨆ i, p i) ↔ fo
rall N, (forall i, p i <= N) -> m in N
参数：p : ι -> Submonoid M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.closure_singleton_le_iff_mem`：closure_singleton_le_iff_mem (m 
: M) (p : Submonoid M) : closure {m} <= p ↔ m in p
· 使用定理 `le_iSup_iff`：le_iSup_iff {s : ι -> α} : a <= iSup s ↔ forall b, (forall 
i, s i <= b) -> a <= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iSup {ι : Sort*} (p : ι → Submonoid M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  rw [← closure_singleton_le_iff_mem, le_iSup_iff]
  simp only [closure_singleton_le_iff_mem]

@[to_additive]
/-
**Submonoid.iSup_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：iSup_eq_closure {ι : Sort*} (p : ι -> Submonoid M) : ⨆ i, p i = Submonoid.
closure (⋃ i, (p i : Set M))
参数：p : ι -> Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.closure_iUnion`：closure_iUnion {ι} (s : ι -> Set M) : closure 
(⋃ i, s i) = ⨆ i, closure (s i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submonoid.closure_eq`：closure_eq : closure (S : Set M) = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_eq_closure {ι : Sort*} (p : ι → Submonoid M) :
    ⨆ i, p i = Submonoid.closure (⋃ i, (p i : Set M)) := by
  simp_rw [Submonoid.closure_iUnion, Submonoid.closure_eq]

@[to_additive]
/-
**Submonoid.disjoint_def** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：disjoint_def {p₁ p₂ : Submonoid M} : Disjoint p₁ p₂ ↔ forall {x : M}, x in
 p₁ -> x in p₂ -> x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_def {p₁ p₂ : Submonoid M} :
    Disjoint p₁ p₂ ↔ ∀ {x : M}, x ∈ p₁ → x ∈ p₂ → x = 1 := by
  simp_rw [disjoint_iff_inf_le, SetLike.le_def, mem_inf, and_imp, mem_bot]

@[to_additive]
/-
**Submonoid.disjoint_def'** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：disjoint_def' {p₁ p₂ : Submonoid M} : Disjoint p₁ p₂ ↔ forall {x y : M}, x
 in p₁ -> y in p₂ -> x = y -> x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submonoid.disjoint_def`：disjoint_def {p₁ p₂ : Submonoid M} : Disjoint p₁
 p₂ ↔ forall {x : M}, x in p₁ -> x in p₂ -> x = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem disjoint_def' {p₁ p₂ : Submonoid M} :
    Disjoint p₁ p₂ ↔ ∀ {x y : M}, x ∈ p₁ → y ∈ p₂ → x = y → x = 1 :=
  disjoint_def.trans ⟨fun h _ _ hx hy hxy => h hx <| hxy.symm ▸ hy, fun h _ hx hx' => h hx hx' rfl⟩

variable {t : Set M}

@[to_additive] -- this must not be a simp-lemma as the conclusion applies to `hts`, causing loops
/-
**Submonoid.closure_sdiff_eq_closure** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：closure_sdiff_eq_closure (hts : t subseteq closure (s \ t)) : closure (s \
 t) = closure s
参数：hts : t subseteq closure (s \ t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Submonoid.closure_mono`：closure_mono ⦃s t : Set M⦄ (h : s subseteq t) : 
closure s <= closure t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submonoid.mem_closure`：mem_closure {x : M} : x in closure s ↔ forall S :
 Submonoid M, s subseteq S -> x in S
· 使用定理 `Set.mem_sdiff_of_mem`：mem_sdiff_of_mem {s t : Set α} {x : α} (h1 : x in 
s) (h2 : x ∉ t) : x in s \ t
-/
lemma closure_sdiff_eq_closure (hts : t ⊆ closure (s \ t)) : closure (s \ t) = closure s := by
  refine (closure_mono Set.sdiff_subset).antisymm <| closure_le.mpr <| fun x hxs ↦ ?_
  by_cases hxt : x ∈ t
  · exact hts hxt
  · rw [SetLike.mem_coe, Submonoid.mem_closure]
    exact fun N hN ↦ hN <| Set.mem_sdiff_of_mem hxs hxt

@[to_additive (attr := simp)]
/-
**Submonoid.closure_sdiff_singleton_one** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：closure_sdiff_singleton_one (s : Set M) : closure (s \ {1}) = closure s
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submonoid.closure_sdiff_eq_closure`：closure_sdiff_eq_closure (hts : t su
bseteq closure (s \ t)) : closure (s \ t) = closure s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
lemma closure_sdiff_singleton_one (s : Set M) : closure (s \ {1}) = closure s :=
  closure_sdiff_eq_closure <| by simp [one_mem]

end Submonoid

namespace MonoidHom

variable [MulOneClass N]

open Submonoid

/-- If two monoid homomorphisms are equal on a set, then they are equal on its submonoid closure. -/
@[to_additive
  /-- If two monoid homomorphisms are equal on a set, then they are equal on its submonoid
  closure. -/]
/-
**MonoidHom.eqOn_closureM** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：eqOn_closureM {f g : M ->* N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn 
f g (closure s)
参数：h : Set.EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
-/
theorem eqOn_closureM {f g : M →* N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocusM g from closure_le.2 h

@[to_additive]
/-
**MonoidHom.eq_of_eqOn_denseM** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：eq_of_eqOn_denseM {s : Set M} (hs : closure s = ⊤) {f g : M ->* N} (h : s.
EqOn f g) : f = g
参数：hs : closure s = ⊤；h : s.EqOn f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.eq_of_eqOn_topM`：eq_of_eqOn_topM {f g : M ->* N} (h : Set.EqOn
 f g (⊤ : Submonoid M)) : f = g
· 使用定理 `MonoidHom.eqOn_closureM`：eqOn_closureM {f g : M ->* N} {s : Set M} (h : 
Set.EqOn f g s) : Set.EqOn f g (closure s)
-/
theorem eq_of_eqOn_denseM {s : Set M} (hs : closure s = ⊤) {f g : M →* N} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_topM <| hs ▸ eqOn_closureM h

end MonoidHom

end NonAssoc

section Assoc

variable [Monoid M] [Monoid N] {s : Set M}

section IsUnit

/-- The submonoid consisting of the units of a monoid -/
@[to_additive /-- The additive submonoid consisting of the additive units of an additive monoid -/]
/-
**IsUnit.submonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsUnit.submonoid (M : Type*) [Monoid M] : Submonoid M where carrier
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submonoid consisting of the units of a monoid
-/
def IsUnit.submonoid (M : Type*) [Monoid M] : Submonoid M where
  carrier := Set.ofPred IsUnit
  one_mem' := by simp only [isUnit_one, Set.mem_ofPred_eq]
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_ofPred_eq] at *
    exact IsUnit.mul ha hb

@[to_additive]
/-
**IsUnit.mem_submonoid_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.mem_submonoid_iff {M : Type*} [Monoid M] (a : M) : a in IsUnit.subm
onoid M ↔ IsUnit a
参数：a : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsUnit.mem_submonoid_iff {M : Type*} [Monoid M] (a : M) :
    a ∈ IsUnit.submonoid M ↔ IsUnit a := by
  change a ∈ Set.ofPred IsUnit ↔ IsUnit a
  rw [Set.mem_ofPred_eq]

end IsUnit

/-
**Submonoid.commute_coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ {S : Type u_4} {M : Type u_5} [inst : Mul M] [inst_1 : SetLike S M] [ins
t_2 : MulMemClass S M] {s : S} {x y : ↥s},   Commute ↑x ↑y ↔ Commute x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma Submonoid.commute_coe_coe {S M : Type*} [Mul M] [SetLike S M]
    [MulMemClass S M] {s : S} {x y : s} : Commute (x : M) (y : M) ↔ Commute x y := by
  simp [commute_iff_eq, Subtype.ext_iff]

namespace MonoidHom

open Submonoid

/-- Let `s` be a subset of a monoid `M` such that the closure of `s` is the whole monoid.
Then `MonoidHom.ofClosureEqTopLeft` defines a monoid homomorphism from `M` asking for
a proof of `f (x * y) = f x * f y` only for `x ∈ s`. -/
@[to_additive
  /-- Let `s` be a subset of an additive monoid `M` such that the closure of `s` is
  the whole monoid. Then `AddMonoidHom.ofClosureEqTopLeft` defines an additive monoid
  homomorphism from `M` asking for a proof of `f (x + y) = f x + f y` only for `x ∈ s`. -/]
/-
**MonoidHom.ofClosureMEqTopLeft** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：ofClosureMEqTopLeft {M N} [Monoid M] [Monoid N] {s : Set M} (f : M -> N) (
hs : closure s = ⊤) (h1 : f 1 = 1) (hmul : forall x in s, forall (y), f (x * y) 
= f x * f y) : M ->* N where toFun
参数：f : M -> N；hs : closure s = ⊤；h1 : f 1 = 1；hmul : forall x in s, forall (y), 
f (x * y) = f x * f y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofClosureMEqTopLeft {M N} [Monoid M] [Monoid N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (h1 : f 1 = 1) (hmul : ∀ x ∈ s, ∀ (y), f (x * y) = f x * f y) :
    M →* N where
  toFun := f
  map_one' := h1
  map_mul' x :=
    dense_induction (motive := _) _ hs hmul fun y => by rw [one_mul, h1, one_mul]
      (fun a b ha hb y => by rw [mul_assoc, ha, ha, hb, mul_assoc]) x

@[to_additive (attr := simp, norm_cast)]
/-
**MonoidHom.coe_ofClosureMEqTopLeft** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_ofClosureMEqTopLeft (f : M -> N) (hs : closure s = ⊤) (h1 hmul) : ⇑(of
ClosureMEqTopLeft f hs h1 hmul) = f
参数：f : M -> N；hs : closure s = ⊤；h1 hmul。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofClosureMEqTopLeft (f : M → N) (hs : closure s = ⊤) (h1 hmul) :
    ⇑(ofClosureMEqTopLeft f hs h1 hmul) = f :=
  rfl

/-- Let `s` be a subset of a monoid `M` such that the closure of `s` is the whole monoid.
Then `MonoidHom.ofClosureEqTopRight` defines a monoid homomorphism from `M` asking for
a proof of `f (x * y) = f x * f y` only for `y ∈ s`. -/
@[to_additive
  /-- Let `s` be a subset of an additive monoid `M` such that the closure of `s` is
  the whole monoid. Then `AddMonoidHom.ofClosureEqTopRight` defines an additive monoid
  homomorphism from `M` asking for a proof of `f (x + y) = f x + f y` only for `y ∈ s`. -/]
/-
**MonoidHom.ofClosureMEqTopRight** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：ofClosureMEqTopRight {M N} [Monoid M] [Monoid N] {s : Set M} (f : M -> N) 
(hs : closure s = ⊤) (h1 : f 1 = 1) (hmul : forall (x), forall y in s, f (x * y)
 = f x * f y) : M ->* N where toFun
参数：f : M -> N；hs : closure s = ⊤；h1 : f 1 = 1；hmul : forall (x), forall y in s, 
f (x * y) = f x * f y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofClosureMEqTopRight {M N} [Monoid M] [Monoid N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (h1 : f 1 = 1) (hmul : ∀ (x), ∀ y ∈ s, f (x * y) = f x * f y) :
    M →* N where
  toFun := f
  map_one' := h1
  map_mul' x y :=
    dense_induction _ hs (fun y hy x => hmul x y hy) (by simp [h1])
      (fun y₁ y₂ (h₁ : ∀ _, f _ = f _ * f _) (h₂ : ∀ _, f _ = f _ * f _) x => by
        simp [← mul_assoc, h₁, h₂]) y x

@[to_additive (attr := simp, norm_cast)]
/-
**MonoidHom.coe_ofClosureMEqTopRight** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_ofClosureMEqTopRight (f : M -> N) (hs : closure s = ⊤) (h1 hmul) : ⇑(o
fClosureMEqTopRight f hs h1 hmul) = f
参数：f : M -> N；hs : closure s = ⊤；h1 hmul。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofClosureMEqTopRight (f : M → N) (hs : closure s = ⊤) (h1 hmul) :
    ⇑(ofClosureMEqTopRight f hs h1 hmul) = f :=
  rfl

end MonoidHom

end Assoc

