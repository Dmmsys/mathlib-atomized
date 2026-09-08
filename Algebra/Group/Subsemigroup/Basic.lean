/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Data.Set.Lattice.Image

/-!
# Subsemigroups: `CompleteLattice` structure

This file defines a `CompleteLattice` structure on `Subsemigroup`s,
and define the closure of a set as the minimal subsemigroup that includes this set.

## Main definitions

For each of the following definitions in the `Subsemigroup` namespace, there is a corresponding
definition in the `AddSubsemigroup` namespace.

* `Subsemigroup.copy` : copy of a subsemigroup with `carrier` replaced by a set that is equal but
  possibly not definitionally equal to the carrier of the original `Subsemigroup`.
* `Subsemigroup.closure` :  semigroup closure of a set, i.e.,
  the least subsemigroup that includes the set.
* `Subsemigroup.gi` : `closure : Set M → Subsemigroup M` and coercion `coe : Subsemigroup M → Set M`
  form a `GaloisInsertion`;

## Implementation notes

Subsemigroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subsemigroup's underlying set.

Note that `Subsemigroup M` does not actually require `Semigroup M`,
instead requiring only the weaker `Mul M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers.

## Tags
subsemigroup, subsemigroups
-/

@[expose] public section

assert_not_exists MonoidWithZero

-- Only needed for notation
variable {M : Type*} {N : Type*}

section NonAssoc

variable [Mul M] {s : Set M}

namespace Subsemigroup

variable (S : Subsemigroup M)

@[to_additive]
/-
**Subsemigroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemigroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (Subsemigroup M) :=
  ⟨fun s =>
    { carrier := ⋂ t ∈ s, ↑t
      mul_mem' := fun hx hy =>
        Set.mem_biInter fun i h =>
          i.mul_mem (by apply Set.mem_iInter₂.1 hx i h) (by apply Set.mem_iInter₂.1 hy i h) }⟩

@[to_additive (attr := simp, norm_cast)]
/-
**Subsemigroup.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：coe_sInf (S : Set (Subsemigroup M)) : ((sInf S : Subsemigroup M) : Set M) 
= ⋂ s in S, ↑s
参数：S : Set (Subsemigroup M)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sInf (S : Set (Subsemigroup M)) : ((sInf S : Subsemigroup M) : Set M) = ⋂ s ∈ S, ↑s :=
  rfl

@[to_additive (attr := simp)]
/-
**Subsemigroup.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_sInf {S : Set (Subsemigroup M)} {x : M} : x in sInf S ↔ forall p in S,
 x in p
参数：Subsemigroup M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_sInf {S : Set (Subsemigroup M)} {x : M} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂

@[to_additive (attr := simp)]
/-
**Subsemigroup.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_iInf {ι : Sort*} {S : ι -> Subsemigroup M} {x : M} : x in ⨅ i, S i ↔ f
orall i, x in S i
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
theorem mem_iInf {ι : Sort*} {S : ι → Subsemigroup M} {x : M} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[to_additive (attr := simp, norm_cast)]
/-
**Subsemigroup.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：coe_iInf {ι : Sort*} {S : ι -> Subsemigroup M} : (↑(⨅ i, S i) : Set M) = ⋂
 i, S i
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
theorem coe_iInf {ι : Sort*} {S : ι → Subsemigroup M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

/-- subsemigroups of a monoid form a complete lattice. -/
@[to_additive /-- The `AddSubsemigroup`s of an `AddMonoid` form a complete lattice. -/]
/-
**Subsemigroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemigroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
subsemigroups of a monoid form a complete lattice.
-/
instance : CompleteLattice (Subsemigroup M) :=
  { completeLatticeOfInf (Subsemigroup M) fun _ =>
      IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun _ _ hx => (notMem_bot hx).elim
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    le_inf := fun _ _ _ ha hb _ hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

/-- The `Subsemigroup` generated by a set. -/
@[to_additive /-- The `AddSubsemigroup` generated by a set -/]
/-
**Subsemigroup.closure** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：closure (s : Set M) : Subsemigroup M
参数：s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Subsemigroup` generated by a set.
-/
def closure (s : Set M) : Subsemigroup M :=
  sInf { S | s ⊆ S }

@[to_additive]
/-
**Subsemigroup.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_closure {x : M} : x in closure s ↔ forall S : Subsemigroup M, s subset
eq S -> x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.mem_sInf`：mem_sInf {S : Set (Subsemigroup M)} {x : M} : x i
n sInf S ↔ forall p in S, x in p
-/
theorem mem_closure {x : M} : x ∈ closure s ↔ ∀ S : Subsemigroup M, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The subsemigroup generated by a set includes the set. -/
@[to_additive (attr := simp, aesop safe 20 (rule_sets := [SetLike]))
  /-- The `AddSubsemigroup` generated by a set includes the set. -/]
/-
**Subsemigroup.subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：subset_closure : s subseteq closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemigroup.mem_closure`：mem_closure {x : M} : x in closure s ↔ forall 
S : Subsemigroup M, s subseteq S -> x in S
-/
theorem subset_closure : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx

@[to_additive (attr := aesop 80% (rule_sets := [SetLike]))]
/-
**Subsemigroup.mem_closure_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_closure_of_mem {s : Set M} {x : M} (hx : x in s) : x in closure s
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
-/
theorem mem_closure_of_mem {s : Set M} {x : M} (hx : x ∈ s) : x ∈ closure s := subset_closure hx

@[to_additive]
/-
**Subsemigroup.notMem_of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`
。
形式化陈述：notMem_of_notMem_closure {P : M} (hP : P ∉ closure s) : P ∉ s
参数：hP : P ∉ closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
-/
theorem notMem_of_notMem_closure {P : M} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

variable {S}

open Set

/-- A subsemigroup `S` includes `closure s` if and only if it includes `s`. -/
@[to_additive (attr := simp)
  /-- An additive subsemigroup `S` includes `closure s` if and only if it includes `s` -/]
/-
**Subsemigroup.closure_le** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：closure_le : closure s <= S ↔ s subseteq S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem closure_le : closure s ≤ S ↔ s ⊆ S :=
  ⟨Subset.trans subset_closure, fun h => sInf_le h⟩

/-- subsemigroup closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[to_additive (attr := gcongr) /-- Additive subsemigroup closure of a set is monotone in its
argument: if `s ⊆ t`, then `closure s ≤ closure t` -/]
/-
**Subsemigroup.closure_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：closure_mono ⦃s t : Set M⦄ (h : s subseteq t) : closure s <= closure t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
-/
theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Subset.trans h subset_closure

@[to_additive]
/-
**Subsemigroup.closure_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：closure_eq_of_le (h₁ : s subseteq S) (h₂ : S <= closure s) : closure s = S
参数：h₁ : s subseteq S；h₂ : S <= closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S
-/
theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure s) : closure s = S :=
  le_antisymm (closure_le.2 h₁) h₂

variable (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[to_additive (attr := elab_as_elim) /-- An induction principle for additive closure membership. If
  `p` holds for all elements of `s`, and is preserved under addition, then `p` holds for all
  elements of the additive closure of `s`. -/]
/-
**Subsemigroup.closure_induction** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：closure_induction {p : (x : M) -> x in closure s -> Prop} (mem : forall (x
) (h : x in s), p x (subset_closure h)) (mul : forall x y hx hy, p x hx -> p y h
y -> p (x * y) (mul_mem hx hy)) {x} (hx : x in closure s) : p x hx
参数：x : M；mem : forall (x) (h : x in s), p x (subset_closure h)；mul : forall x y 
hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S
-/
theorem closure_induction {p : (x : M) → x ∈ closure s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (subset_closure h))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy)) {x} (hx : x ∈ closure s) :
    p x hx :=
  let S : Subsemigroup M :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩ }
  closure_le (S := S) |>.mpr (fun y hy ↦ ⟨subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

/-- An induction principle for closure membership for predicates with two arguments. -/
@[to_additive (attr := elab_as_elim) /-- An induction principle for additive closure membership for
  predicates with two arguments. -/]
/-
**Subsemigroup.closure_induction** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：closure_induction {p : (x : M) -> x in closure s -> Prop} (mem : forall (x
) (h : x in s), p x (subset_closure h)) (mul : forall x y hx hy, p x hx -> p y h
y -> p (x * y) (mul_mem hx hy)) {x} (hx : x in closure s) : p x hx
参数：x : M；mem : forall (x) (h : x in s), p x (subset_closure h)；mul : forall x y 
hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S
-/
theorem closure_induction₂ {p : (x y : M) → x ∈ closure s → y ∈ closure s → Prop}
    (mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (subset_closure hx) (subset_closure hy))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p z x hz hx → p z y hz hy → p z (x * y) hz (mul_mem hx hy))
    {x y : M} (hx : x ∈ closure s) (hy : y ∈ closure s) : p x y hx hy := by
  induction hx using closure_induction with
  | mem z hz => induction hy using closure_induction with
    | mem _ h => exact mem _ _ hz h
    | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ hy h₁ h₂

/-- If `s` is a dense set in a magma `M`, `Subsemigroup.closure s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
@[to_additive (attr := elab_as_elim) /-- If `s` is a dense set in an additive monoid `M`,
  `AddSubsemigroup.closure s = ⊤`, then in order to prove that some predicate `p` holds
  for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify that `p x` and `p y` imply
  `p (x + y)`. -/]
/-
**Subsemigroup.dense_induction** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：dense_induction {p : M -> Prop} (s : Set M) (closure : closure s = ⊤) (mem
 : forall x in s, p x) (mul : forall x y, p x -> p y -> p (x * y)) (x : M) : p x
参数：s : Set M；closure : closure s = ⊤；mem : forall x in s, p x；mul : forall x y, 
p x -> p y -> p (x * y)；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.closure_induction`：closure_induction {p : (x : M) -> x in c
losure s -> Prop} (mem : forall (x) (h : x in s), p x (subset_closure h)) (mul :
 forall x y hx hy, p…
· 使用定理 `Subsemigroup.mem_top`：mem_top (x : M) : x in (⊤ : Subsemigroup M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dense_induction {p : M → Prop} (s : Set M) (closure : closure s = ⊤)
    (mem : ∀ x ∈ s, p x) (mul : ∀ x y, p x → p y → p (x * y)) (x : M) :
    p x := by
  induction closure.symm ▸ mem_top x using closure_induction with
  | mem _ h => exact mem _ h
  | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂

/-! The argument `s : Set M` is explicit in `Subsemigroup.dense_induction` because the type of the
induction variable, namely `x : M`, does not reference `x`. Making `s` explicit allows the user
to apply the induction principle while deferring the proof of `closure s = ⊤` without creating
metavariables, as in the following example. -/

/-
**Subsemigroup.** 是 Mathlib 中的一个示例，位于命名空间 `Subsemigroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The argument `s : Set M` is explicit in `Subsemigroup.dense_induction` because t
he type of the
induction variable, namely `x : M`, does not reference `x`. Making `s` explicit 
allows the user
to apply the induction principle while deferring the proof of `closure s = ⊤` wi
thout creating
metavariables, as in the following example.
-/
example {p : M → Prop} (s : Set M) (closure : closure s = ⊤)
    (mem : ∀ x ∈ s, p x) (mul : ∀ x y, p x → p y → p (x * y)) (x : M) :
    p x := by
  induction x using dense_induction s with
  | closure => exact closure
  | mem x hx => exact mem x hx
  | mul _ _ h₁ h₂ => exact mul _ _ h₁ h₂

variable (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive /-- `closure` forms a Galois insertion with the coercion to set. -/]
/-
**Subsemigroup.gi** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：(M : Type u_1) → [inst : Mul M] → GaloisInsertion Subsemigroup.closure Set
Like.coe
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S

--- 原说明 ---
`closure` forms a Galois insertion with the coercion to set.
-/
protected def gi : GaloisInsertion (@closure M _) SetLike.coe :=
  GaloisConnection.toGaloisInsertion (fun _ _ => closure_le) fun _ => subset_closure

variable {M}

/-- Closure of a subsemigroup `S` equals `S`. -/
@[to_additive (attr := simp) /-- Additive closure of an additive subsemigroup `S` equals `S` -/]
/-
**Subsemigroup.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：closure_eq : closure (S : Set M) = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b

--- 原说明 ---
Closure of a subsemigroup `S` equals `S`.
-/
theorem closure_eq : closure (S : Set M) = S :=
  (Subsemigroup.gi M).l_u_eq S

@[to_additive (attr := simp)]
/-
**Subsemigroup.closure_empty** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
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
  (Subsemigroup.gi M).gc.l_bot

@[to_additive (attr := simp)]
/-
**Subsemigroup.closure_univ** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：closure_univ : closure (univ : Set M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.closure_eq`：closure_eq : closure (S : Set M) = S
· 使用定理 `Subsemigroup.coe_top`：coe_top : ((⊤ : Subsemigroup M) : Set M) = Set.uni
v
-/
theorem closure_univ : closure (univ : Set M) = ⊤ :=
  @coe_top M _ ▸ closure_eq ⊤

@[to_additive]
/-
**Subsemigroup.closure_union** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
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
  (Subsemigroup.gi M).gc.l_sup

@[to_additive]
/-
**Subsemigroup.closure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
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
  (Subsemigroup.gi M).gc.l_iSup

@[to_additive]
/-
**Subsemigroup.closure_singleton_le_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigr
oup`。
形式化陈述：closure_singleton_le_iff_mem (m : M) (p : Subsemigroup M) : closure {m} <=
 p ↔ m in p
参数：m : M；p : Subsemigroup M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem closure_singleton_le_iff_mem (m : M) (p : Subsemigroup M) : closure {m} ≤ p ↔ m ∈ p := by
  rw [closure_le, singleton_subset_iff, SetLike.mem_coe]

@[to_additive]
/-
**Subsemigroup.mem_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_iSup {ι : Sort*} (p : ι -> Subsemigroup M) {m : M} : (m in ⨆ i, p i) ↔
 forall N, (forall i, p i <= N) -> m in N
参数：p : ι -> Subsemigroup M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsemigroup.closure_singleton_le_iff_mem`：closure_singleton_le_iff_mem 
(m : M) (p : Subsemigroup M) : closure {m} <= p ↔ m in p
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
theorem mem_iSup {ι : Sort*} (p : ι → Subsemigroup M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  rw [← closure_singleton_le_iff_mem, le_iSup_iff]
  simp only [closure_singleton_le_iff_mem]

@[to_additive]
/-
**Subsemigroup.iSup_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：iSup_eq_closure {ι : Sort*} (p : ι -> Subsemigroup M) : ⨆ i, p i = Subsemi
group.closure (⋃ i, (p i : Set M))
参数：p : ι -> Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsemigroup.closure_iUnion`：closure_iUnion {ι} (s : ι -> Set M) : closu
re (⋃ i, s i) = ⨆ i, closure (s i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsemigroup.closure_eq`：closure_eq : closure (S : Set M) = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_eq_closure {ι : Sort*} (p : ι → Subsemigroup M) :
    ⨆ i, p i = Subsemigroup.closure (⋃ i, (p i : Set M)) := by
  simp_rw [Subsemigroup.closure_iUnion, Subsemigroup.closure_eq]

end Subsemigroup

namespace MulHom

variable [Mul N]

open Subsemigroup

/-- If two mul homomorphisms are equal on a set, then they are equal on its subsemigroup closure. -/
@[to_additive /-- If two add homomorphisms are equal on a set,
  then they are equal on its additive subsemigroup closure. -/]
/-
**MulHom.eqOn_closure** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：eqOn_closure {f g : M ->ₙ* N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn 
f g (closure s)
参数：h : Set.EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S
-/
theorem eqOn_closure {f g : M →ₙ* N} {s : Set M} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from closure_le.2 h

@[to_additive]
/-
**MulHom.eq_of_eqOn_dense** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：eq_of_eqOn_dense {s : Set M} (hs : closure s = ⊤) {f g : M ->ₙ* N} (h : s.
EqOn f g) : f = g
参数：hs : closure s = ⊤；h : s.EqOn f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.eq_of_eqOn_top`：eq_of_eqOn_top {f g : M ->ₙ* N} (h : Set.EqOn f g
 (⊤ : Subsemigroup M)) : f = g
· 使用定理 `MulHom.eqOn_closure`：eqOn_closure {f g : M ->ₙ* N} {s : Set M} (h : Set.
EqOn f g s) : Set.EqOn f g (closure s)
-/
theorem eq_of_eqOn_dense {s : Set M} (hs : closure s = ⊤) {f g : M →ₙ* N} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_top <| hs ▸ eqOn_closure h

end MulHom

end NonAssoc

section Assoc

namespace MulHom

open Subsemigroup

/-- Let `s` be a subset of a semigroup `M` such that the closure of `s` is the whole semigroup.
Then `MulHom.ofDense` defines a mul homomorphism from `M` asking for a proof
of `f (x * y) = f x * f y` only for `y ∈ s`. -/
@[to_additive]
/-
**MulHom.ofDense** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：ofDense {M N} [Semigroup M] [Semigroup N] {s : Set M} (f : M -> N) (hs : c
losure s = ⊤) (hmul : forall (x), forall y in s, f (x * y) = f x * f y) : M ->ₙ*
 N where toFun
参数：f : M -> N；hs : closure s = ⊤；hmul : forall (x), forall y in s, f (x * y) = f
 x * f y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `s` be a subset of a semigroup `M` such that the closure of `s` is the whole
 semigroup.
Then `MulHom.ofDense` defines a mul homomorphism from `M` asking for a proof
of `f (x * y) = f x * f y` only for `y ∈ s`.
-/
def ofDense {M N} [Semigroup M] [Semigroup N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (hmul : ∀ (x), ∀ y ∈ s, f (x * y) = f x * f y) :
    M →ₙ* N where
  toFun := f
  map_mul' x y :=
    dense_induction _ hs (fun y hy x => hmul x y hy)
      (fun y₁ y₂ h₁ h₂ x => by simp only [← mul_assoc, h₁, h₂]) y x

/-- Let `s` be a subset of an additive semigroup `M` such that the closure of `s` is the whole
semigroup.  Then `AddHom.ofDense` defines an additive homomorphism from `M` asking for a proof
of `f (x + y) = f x + f y` only for `y ∈ s`. -/
add_decl_doc AddHom.ofDense

@[to_additive (attr := simp, norm_cast)]
/-
**MulHom.coe_ofDense** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：coe_ofDense [Semigroup M] [Semigroup N] {s : Set M} (f : M -> N) (hs : clo
sure s = ⊤) (hmul) : (ofDense f hs hmul : M -> N) = f
参数：f : M -> N；hs : closure s = ⊤；hmul。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofDense [Semigroup M] [Semigroup N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (hmul) : (ofDense f hs hmul : M → N) = f :=
  rfl

end MulHom

end Assoc

