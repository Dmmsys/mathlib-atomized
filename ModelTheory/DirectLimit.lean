/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly
-/
module

public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fintype.Order
public import Mathlib.ModelTheory.FinitelyGenerated
public import Mathlib.ModelTheory.Quotients
public import Mathlib.Order.DirectedInverseSystem

/-!
# Direct Limits of First-Order Structures

This file constructs the direct limit of a directed system of first-order embeddings.

## Main Definitions

- `FirstOrder.Language.DirectLimit G f` is the direct limit of the directed system `f` of
  first-order embeddings between the structures indexed by `G`.
- `FirstOrder.Language.DirectLimit.lift` is the universal property of the direct limit: maps
  from the components to another module that respect the directed system structure give rise to
  a unique map out of the direct limit.
- `FirstOrder.Language.DirectLimit.equiv_lift` is the equivalence between limits of
  isomorphic direct systems.
-/

@[expose] public section


universe v w w' u₁ u₂

open FirstOrder

namespace FirstOrder

namespace Language

open Structure Set

variable {L : Language} {ι : Type v} [Preorder ι]
variable {G : ι → Type w} [∀ i, L.Structure (G i)]
variable (f : ∀ i j, i ≤ j → G i ↪[L] G j)

namespace DirectedSystem

alias map_self := DirectedSystem.map_self'
alias map_map := DirectedSystem.map_map'

variable {G' : ℕ → Type w} [∀ i, L.Structure (G' i)] (f' : ∀ n : ℕ, G' n ↪[L] G' (n + 1))

/-- Given a chain of embeddings of structures indexed by `ℕ`, defines a `DirectedSystem` by
composing them. -/
/-
**FirstOrder.Language.DirectedSystem.natLERec** 是 Mathlib 中的一个定义，位于命名空间 `FirstOr
der.Language.DirectedSystem`。
形式化陈述：natLERec (m n : Nat) (h : m <= n) : G' m ↪[L] G' n
参数：m n : Nat；h : m <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a chain of embeddings of structures indexed by `ℕ`, defines a `DirectedSys
tem` by
composing them.
-/
def natLERec (m n : ℕ) (h : m ≤ n) : G' m ↪[L] G' n :=
  Nat.leRecOn h (@fun k g => (f' k).comp g) (Embedding.refl L _)

@[simp]
/-
**FirstOrder.Language.DirectedSystem.coe_natLERec** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.DirectedSystem`。
形式化陈述：coe_natLERec (m n : Nat) (h : m <= n) : (natLERec f' m n h : G' m -> G' n)
 = Nat.leRecOn h (@fun k => f' k)
参数：m n : Nat；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.leRecOn_self`：leRecOn_self {C : Nat -> Sort*} {n} {next : forall {k}
, C k -> C (k + 1)} (x : C n) : (leRecOn n.le_refl next x : C n) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用引理 `Nat.leRecOn_succ`：leRecOn_succ {C : Nat -> Sort*} {n m} (h1 : n <= m) {h
2 : n <= m + 1} {next} (x : C n) : (leRecOn h2 next x : C (m + 1)) = next (leRec
On h1 …
· 使用定理 `FirstOrder.Language.DirectedSystem.natLERec.eq_1`：∀ {L : FirstOrder.Lang
uage} {G' : ℕ → Type w} [inst : (i : ℕ) → L.Structure (G' i)]   (f' : (n : ℕ) → 
L.Embedding (G' n) (G' (n + 1))) (m n …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Embedding.comp_apply`：comp_apply (g : N ↪[L] P) (f :
 M ↪[L] N) (x : M) : g.comp f x = g (f x)
-/
theorem coe_natLERec (m n : ℕ) (h : m ≤ n) :
    (natLERec f' m n h : G' m → G' n) = Nat.leRecOn h (@fun k => f' k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  ext x
  induction k with
  | zero => simp [natLERec, Nat.leRecOn_self]
  | succ k ih =>
    rw [Nat.leRecOn_succ le_self_add, natLERec, Nat.leRecOn_succ le_self_add, ← natLERec,
      Embedding.comp_apply, ih]
/-
**FirstOrder.Language.DirectedSystem.natLERec.directedSystem** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.DirectedSystem.natLERec`。
形式化陈述：∀ {L : FirstOrder.Language} {G' : ℕ → Type w} [inst : (i : ℕ) → L.Structur
e (G' i)]   (f' : (n : ℕ) → L.Embedding (G' n) (G' (n + 1))),   DirectedSystem G
' fun i j h => ⇑(FirstOrder.Language.DirectedSystem.natLERec f' i j h)
参数：i : ℕ；G' i；f' : (n : ℕ) → L.Embedding (G' n) (G' (n + 1))；FirstOrder.Language
.DirectedSystem.natLERec f' i j h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用引理 `Nat.leRecOn_self`：leRecOn_self {C : Nat -> Sort*} {n} {next : forall {k}
, C k -> C (k + 1)} (x : C n) : (leRecOn n.le_refl next x : C n) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FirstOrder.Language.DirectedSystem.coe_natLERec`：coe_natLERec (m n : Nat
) (h : m <= n) : (natLERec f' m n h : G' m -> G' n) = Nat.leRecOn h (@fun k => f
' k)
· 使用引理 `Nat.leRecOn_trans`：leRecOn_trans {C : Nat -> Sort*} {n m k} (hnm : n <= 
m) (hmk : m <= k) {next} (x : C n) : (leRecOn (Nat.le_trans hnm hmk) (@next) x :
 C k) =…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance natLERec.directedSystem : DirectedSystem G' fun i j h => natLERec f' i j h :=
  ⟨fun _ _ => congr (congr rfl (Nat.leRecOn_self _)) rfl,
   fun _ _ _ hij hjk => by simp [Nat.leRecOn_trans hij hjk]⟩

end DirectedSystem

set_option linter.unusedVariables false in
/-- Alias for `Σ i, G i`.

Instead of `Σ i, G i`, we use the alias `Language.Structure.Sigma` which depends on `f`.
This way, Lean can infer what `L` and `f` are in the `Setoid` instance.
Otherwise we have a "cannot find synthesization order" error.
See also the discussion at
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/local.20instance.20cannot.20find.20synthesization.20order.20in.20porting
-/
@[nolint unusedArguments]
/-
**FirstOrder.Language.Structure.Sigma** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage.Structure`。
形式化陈述：{L : FirstOrder.Language} →   {ι : Type v} →     [inst : Preorder ι] →    
   {G : ι → Type w} →         [inst_1 : (i : ι) → L.Structure (G i)] → ((i j : ι
) → i ≤ j → L.Embedding (G i) (G j)) → Type (max v w)
参数：i : ι；G i；(i j : ι) → i ≤ j → L.Embedding (G i) (G j)；max v w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alias for `Σ i, G i`.

Instead of `Σ i, G i`, we use the alias `Language.Structure.Sigma` which depends
 on `f`.
This way, Lean can infer what `L` and `f` are in the `Setoid` instance.
Otherwise we have a "cannot find synthesization order" error.
See also the discussion at
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/local.20in
stance.20cannot.20find.20synthesization.20order.20in.20porting
-/
protected abbrev Structure.Sigma (f : ∀ i j, i ≤ j → G i ↪[L] G j) := Σ i, G i

local notation "Σˣ" => Structure.Sigma

/-- Constructor for `FirstOrder.Language.Structure.Sigma` alias. -/
/-
**FirstOrder.Language.Structure.Sigma.mk** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.L
anguage.Structure.Sigma`。
形式化陈述：{L : FirstOrder.Language} →   {ι : Type v} →     [inst : Preorder ι] →    
   {G : ι → Type w} →         [inst_1 : (i : ι) → L.Structure (G i)] →          
 (f : (i j : ι) → i ≤ j → L.Embedding (G i) (G j)) → (i : ι) → G i → FirstOrder.
Language.Structure.Sigma f
参数：i : ι；G i；f : (i j : ι) → i ≤ j → L.Embedding (G i) (G j)；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `FirstOrder.Language.Structure.Sigma` alias.
-/
abbrev Structure.Sigma.mk (i : ι) (x : G i) : Σˣ f := ⟨i, x⟩

namespace DirectLimit

/-- Raises a family of elements in the `Σ`-type to the same level along the embeddings. -/
/-
**FirstOrder.Language.DirectLimit.unify** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage.DirectLimit`。
形式化陈述：unify {α : Type*} (x : α -> Σˣ f) (i : ι) (h : i in upperBounds (range (Si
gma.fst ∘ x))) (a : α) : G i
参数：x : α -> Σˣ f；i : ι；h : i in upperBounds (range (Sigma.fst ∘ x))；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Raises a family of elements in the `Σ`-type to the same level along the embeddin
gs.
-/
def unify {α : Type*} (x : α → Σˣ f) (i : ι) (h : i ∈ upperBounds (range (Sigma.fst ∘ x)))
    (a : α) : G i :=
  f (x a).1 i (h (mem_range_self a)) (x a).2

variable [DirectedSystem G fun i j h => f i j h]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**FirstOrder.Language.DirectLimit.unify_sigma_mk_self** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.DirectLimit`。
形式化陈述：unify_sigma_mk_self {α : Type*} {i : ι} {x : α -> G i} : (unify f (fun a =
> .mk f i (x a)) i fun _ ⟨_, hj⟩ => _root_.trans (le_of_eq hj.symm) (refl _)) = 
x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.DirectLimit.unify.eq_1`：∀ {L : FirstOrder.Language} 
{ι : Type v} [inst : Preorder ι] {G : ι → Type w} [inst_1 : (i : ι) → L.Structur
e (G i)]   (f : (i j : ι) → i ≤ …
· 使用定理 `FirstOrder.Language.DirectedSystem.map_self`：∀ {ι : Type u_1} [inst : Pr
eorder ι] {F : ι → Type u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι)
 → (h : i ≤ j) → T h) [inst_1 : ⦃…
-/
theorem unify_sigma_mk_self {α : Type*} {i : ι} {x : α → G i} :
    (unify f (fun a => .mk f i (x a)) i fun _ ⟨_, hj⟩ =>
      _root_.trans (le_of_eq hj.symm) (refl _)) = x := by
  ext a
  rw [unify]
  apply DirectedSystem.map_self
/-
**FirstOrder.Language.DirectLimit.comp_unify** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.DirectLimit`。
形式化陈述：comp_unify {α : Type*} {x : α -> Σˣ f} {i j : ι} (ij : i <= j) (h : i in u
pperBounds (range (Sigma.fst ∘ x))) : f i j ij ∘ unify f x i h = unify f x j fun
 k hk => _root_.trans (mem_upperBounds.1 h k hk) ij
参数：ij : i <= j；h : i in upperBounds (range (Sigma.fst ∘ x))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.DirectedSystem.map_map`：∀ {ι : Type u_1} [inst : Pre
order ι] {F : ι → Type u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) 
→ (h : i ≤ j) → T h) [inst_1 : ⦃…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_unify {α : Type*} {x : α → Σˣ f} {i j : ι} (ij : i ≤ j)
    (h : i ∈ upperBounds (range (Sigma.fst ∘ x))) :
    f i j ij ∘ unify f x i h = unify f x j
      fun k hk => _root_.trans (mem_upperBounds.1 h k hk) ij := by
  ext a
  simp [unify, DirectedSystem.map_map]

end DirectLimit

variable (G)

namespace DirectLimit

/-- The directed limit glues together the structures along the embeddings. -/
@[instance_reducible]
/-
**FirstOrder.Language.DirectLimit.setoid** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.L
anguage.DirectLimit`。
形式化陈述：setoid [DirectedSystem G fun i j h => f i j h] [IsDirectedOrder ι] : Setoi
d (Σˣ f) where r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The directed limit glues together the structures along the embeddings.
-/
def setoid [DirectedSystem G fun i j h => f i j h] [IsDirectedOrder ι] : Setoid (Σˣ f) where
  r := fun ⟨i, x⟩ ⟨j, y⟩ => ∃ (k : ι) (ik : i ≤ k) (jk : j ≤ k), f i k ik x = f j k jk y
  iseqv :=
    ⟨fun ⟨i, _⟩ => ⟨i, refl i, refl i, rfl⟩, @fun ⟨_, _⟩ ⟨_, _⟩ ⟨k, ik, jk, h⟩ =>
      ⟨k, jk, ik, h.symm⟩,
      @fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ ⟨ij, hiij, hjij, hij⟩ ⟨jk, hjjk, hkjk, hjk⟩ => by
        obtain ⟨ijk, hijijk, hjkijk⟩ := directed_of (· ≤ ·) ij jk
        refine ⟨ijk, le_trans hiij hijijk, le_trans hkjk hjkijk, ?_⟩
        rw [← DirectedSystem.map_map _ hiij hijijk, hij, DirectedSystem.map_map]
        rw [← DirectedSystem.map_map _ hkjk hjkijk, ← hjk, DirectedSystem.map_map]⟩

/-- The structure on the `Σ`-type which becomes the structure on the direct limit after quotienting.
-/
@[instance_reducible]
/-
**FirstOrder.Language.DirectLimit.sigmaStructure** 是 Mathlib 中的一个定义，位于命名空间 `Firs
tOrder.Language.DirectLimit`。
形式化陈述：sigmaStructure [IsDirectedOrder ι] [Nonempty ι] : L.Structure (Σˣ f) where
 funMap F x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure on the `Σ`-type which becomes the structure on the direct limit af
ter quotienting.
-/
noncomputable def sigmaStructure [IsDirectedOrder ι] [Nonempty ι] : L.Structure (Σˣ f) where
  funMap F x :=
    ⟨_,
      funMap F
        (unify f x (Classical.choose (Finite.bddAbove_range fun a => (x a).1))
          (Classical.choose_spec (Finite.bddAbove_range fun a => (x a).1)))⟩
  RelMap R x :=
    RelMap R
      (unify f x (Classical.choose (Finite.bddAbove_range fun a => (x a).1))
        (Classical.choose_spec (Finite.bddAbove_range fun a => (x a).1)))

end DirectLimit

/-- The direct limit of a directed system is the structures glued together along the embeddings. -/
/-
**FirstOrder.Language.DirectLimit** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
`。
形式化陈述：DirectLimit [DirectedSystem G fun i j h => f i j h] [IsDirectedOrder ι]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The direct limit of a directed system is the structures glued together along the
 embeddings.
-/
def DirectLimit [DirectedSystem G fun i j h => f i j h] [IsDirectedOrder ι] :=
  Quotient (DirectLimit.setoid G f)

attribute [local instance] DirectLimit.setoid DirectLimit.sigmaStructure
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DirectedSystem G fun i j h => f i j h] [IsDirectedOrder ι] [Inhabited ι]
    [Inhabited (G default)] : Inhabited (DirectLimit G f) :=
  ⟨⟦⟨default, default⟩⟧⟩

namespace DirectLimit

variable [IsDirectedOrder ι] [DirectedSystem G fun i j h => f i j h]

/-
**FirstOrder.Language.DirectLimit.equiv_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.DirectLimit`。
形式化陈述：equiv_iff {x y : Σˣ f} {i : ι} (hx : x.1 <= i) (hy : y.1 <= i) : x ≈ y ↔ (
f x.1 i hx) x.2 = (f y.1 i hy) y.2
参数：hx : x.1 <= i；hy : y.1 <= i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `directed_of`：directed_of (r : α -> α -> Prop) [IsDirected α r] (a b : α)
 : exists c, r a c ∧ r b c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Embedding.injective`：injective (f : M ↪[L] N) : Func
tion.Injective f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.DirectedSystem.map_map`：∀ {ι : Type u_1} [inst : Pre
order ι] {F : ι → Type u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) 
→ (h : i ≤ j) → T h) [inst_1 : ⦃…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem equiv_iff {x y : Σˣ f} {i : ι} (hx : x.1 ≤ i) (hy : y.1 ≤ i) :
    x ≈ y ↔ (f x.1 i hx) x.2 = (f y.1 i hy) y.2 := by
  cases x
  cases y
  refine ⟨fun xy => ?_, fun xy => ⟨i, hx, hy, xy⟩⟩
  obtain ⟨j, _, _, h⟩ := xy
  obtain ⟨k, ik, jk⟩ := directed_of (· ≤ ·) i j
  have h := congr_arg (f j k jk) h
  apply (f i k ik).injective
  rw [DirectedSystem.map_map, DirectedSystem.map_map] at *
  exact h
/-
**FirstOrder.Language.DirectLimit.funMap_unify_equiv** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.DirectLimit`。
形式化陈述：funMap_unify_equiv {n : Nat} (F : L.Functions n) (x : Fin n -> Σˣ f) (i j 
: ι) (hi : i in upperBounds (range (Sigma.fst ∘ x))) (hj : j in upperBounds (ran
ge (Sigma.fst ∘ x))) : Structure.Sigma.mk f i (funMap F (unify f x i hi)) ≈ .mk 
f j (funMap F (unify f x j hj))
参数：F : L.Functions n；x : Fin n -> Σˣ f；i j : ι；hi : i in upperBounds (range (Sig
ma.fst ∘ x))；hj : j in upperBounds (range (Sigma.fst ∘ x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `directed_of`：directed_of (r : α -> α -> Prop) [IsDirected α r] (a b : α)
 : exists c, r a c ∧ r b c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Embedding.map_fun`：map_fun (φ : M ↪[L] N) {n : Nat} 
(f : L.Functions n) (x : Fin n -> M) : φ (funMap f x) = funMap f (φ ∘ x)
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用定理 `FirstOrder.Language.DirectLimit.comp_unify`：comp_unify {α : Type*} {x : 
α -> Σˣ f} {i j : ι} (ij : i <= j) (h : i in upperBounds (range (Sigma.fst ∘ x))
) : f i j ij ∘ unify f x i h = u…
-/
theorem funMap_unify_equiv {n : ℕ} (F : L.Functions n) (x : Fin n → Σˣ f) (i j : ι)
    (hi : i ∈ upperBounds (range (Sigma.fst ∘ x))) (hj : j ∈ upperBounds (range (Sigma.fst ∘ x))) :
    Structure.Sigma.mk f i (funMap F (unify f x i hi)) ≈ .mk f j (funMap F (unify f x j hj)) := by
  obtain ⟨k, ik, jk⟩ := directed_of (· ≤ ·) i j
  refine ⟨k, ik, jk, ?_⟩
  rw [(f i k ik).map_fun, (f j k jk).map_fun, comp_unify, comp_unify]
/-
**FirstOrder.Language.DirectLimit.relMap_unify_equiv** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.DirectLimit`。
形式化陈述：relMap_unify_equiv {n : Nat} (R : L.Relations n) (x : Fin n -> Σˣ f) (i j 
: ι) (hi : i in upperBounds (range (Sigma.fst ∘ x))) (hj : j in upperBounds (ran
ge (Sigma.fst ∘ x))) : RelMap R (unify f x i hi) = RelMap R (unify f x j hj)
参数：R : L.Relations n；x : Fin n -> Σˣ f；i j : ι；hi : i in upperBounds (range (Sig
ma.fst ∘ x))；hj : j in upperBounds (range (Sigma.fst ∘ x))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `directed_of`：directed_of (r : α -> α -> Prop) [IsDirected α r] (a b : α)
 : exists c, r a c ∧ r b c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Embedding.map_rel`：map_rel (φ : M ↪[L] N) {n : Nat} 
(r : L.Relations n) (x : Fin n -> M) : RelMap r (φ ∘ x) ↔ RelMap r x
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用定理 `FirstOrder.Language.DirectLimit.comp_unify`：comp_unify {α : Type*} {x : 
α -> Σˣ f} {i j : ι} (ij : i <= j) (h : i in upperBounds (range (Sigma.fst ∘ x))
) : f i j ij ∘ unify f x i h = u…
-/
theorem relMap_unify_equiv {n : ℕ} (R : L.Relations n) (x : Fin n → Σˣ f) (i j : ι)
    (hi : i ∈ upperBounds (range (Sigma.fst ∘ x))) (hj : j ∈ upperBounds (range (Sigma.fst ∘ x))) :
    RelMap R (unify f x i hi) = RelMap R (unify f x j hj) := by
  obtain ⟨k, ik, jk⟩ := directed_of (· ≤ ·) i j
  rw [← (f i k ik).map_rel, comp_unify, ← (f j k jk).map_rel, comp_unify]

variable [Nonempty ι]
/-
**FirstOrder.Language.DirectLimit.exists_unify_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.DirectLimit`。
形式化陈述：exists_unify_eq {α : Type*} [Finite α] {x y : α -> Σˣ f} (xy : x ≈ y) : ex
ists (i : ι) (hx : i in upperBounds (range (Sigma.fst ∘ x))) (hy : i in upperBou
nds (range (Sigma.fst ∘ y))), unify f x i hx = unify f y i hy
参数：xy : x ≈ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.bddAbove_range`：Finite.bddAbove_range [IsDirectedOrder α] (f : ι 
-> α) : BddAbove (Set.range f)
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `upperBounds_union`：upperBounds_union : upperBounds (s union t) = upperBo
unds s inter upperBounds t
· 使用定理 `Set.Sum.elim_range`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : 
α → γ) (g : β → γ),   Set.range (Sum.elim f g) = Set.range f ∪ Set.range g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.DirectLimit.equiv_iff`：equiv_iff {x y : Σˣ f} {i : ι
} (hx : x.1 <= i) (hy : y.1 <= i) : x ≈ y ↔ (f x.1 i hx) x.2 = (f y.1 i hy) y.2
-/
theorem exists_unify_eq {α : Type*} [Finite α] {x y : α → Σˣ f} (xy : x ≈ y) :
    ∃ (i : ι) (hx : i ∈ upperBounds (range (Sigma.fst ∘ x)))
      (hy : i ∈ upperBounds (range (Sigma.fst ∘ y))), unify f x i hx = unify f y i hy := by
  obtain ⟨i, hi⟩ := Finite.bddAbove_range (Sum.elim (fun a => (x a).1) fun a => (y a).1)
  rw [Sum.elim_range, upperBounds_union] at hi
  simp_rw [← Function.comp_apply (f := Sigma.fst)] at hi
  exact ⟨i, hi.1, hi.2, funext fun a => (equiv_iff G f _ _).1 (xy a)⟩
/-
**FirstOrder.Language.DirectLimit.funMap_equiv_unify** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.DirectLimit`。
形式化陈述：funMap_equiv_unify {n : Nat} (F : L.Functions n) (x : Fin n -> Σˣ f) (i : 
ι) (hi : i in upperBounds (range (Sigma.fst ∘ x))) : funMap F x ≈ .mk f _ (funMa
p F (unify f x i hi))
参数：F : L.Functions n；x : Fin n -> Σˣ f；i : ι；hi : i in upperBounds (range (Sigma
.fst ∘ x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.DirectLimit.funMap_unify_equiv`：funMap_unify_equiv {
n : Nat} (F : L.Functions n) (x : Fin n -> Σˣ f) (i j : ι) (hi : i in upperBound
s (range (Sigma.fst ∘ x))) (hj : j in up…
· 使用定理 `Finite.bddAbove_range`：Finite.bddAbove_range [IsDirectedOrder α] (f : ι 
-> α) : BddAbove (Set.range f)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem funMap_equiv_unify {n : ℕ} (F : L.Functions n) (x : Fin n → Σˣ f) (i : ι)
    (hi : i ∈ upperBounds (range (Sigma.fst ∘ x))) :
    funMap F x ≈ .mk f _ (funMap F (unify f x i hi)) :=
  funMap_unify_equiv G f F x (Classical.choose (Finite.bddAbove_range fun a => (x a).1)) i _ hi
/-
**FirstOrder.Language.DirectLimit.relMap_equiv_unify** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.DirectLimit`。
形式化陈述：relMap_equiv_unify {n : Nat} (R : L.Relations n) (x : Fin n -> Σˣ f) (i : 
ι) (hi : i in upperBounds (range (Sigma.fst ∘ x))) : RelMap R x = RelMap R (unif
y f x i hi)
参数：R : L.Relations n；x : Fin n -> Σˣ f；i : ι；hi : i in upperBounds (range (Sigma
.fst ∘ x))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.DirectLimit.relMap_unify_equiv`：relMap_unify_equiv {
n : Nat} (R : L.Relations n) (x : Fin n -> Σˣ f) (i j : ι) (hi : i in upperBound
s (range (Sigma.fst ∘ x))) (hj : j in up…
· 使用定理 `Finite.bddAbove_range`：Finite.bddAbove_range [IsDirectedOrder α] (f : ι 
-> α) : BddAbove (Set.range f)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem relMap_equiv_unify {n : ℕ} (R : L.Relations n) (x : Fin n → Σˣ f) (i : ι)
    (hi : i ∈ upperBounds (range (Sigma.fst ∘ x))) :
    RelMap R x = RelMap R (unify f x i hi) :=
  relMap_unify_equiv G f R x (Classical.choose (Finite.bddAbove_range fun a => (x a).1)) i _ hi

/-- The direct limit `setoid` respects the structure `sigmaStructure`, so quotienting by it
  gives rise to a valid structure. -/
/-
**FirstOrder.Language.DirectLimit.prestructure** 是 Mathlib 中的一个实例，位于命名空间 `FirstO
rder.Language.DirectLimit`。
形式化陈述：prestructure : L.Prestructure (DirectLimit.setoid G f) where toStructure
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The direct limit `setoid` respects the structure `sigmaStructure`, so quotientin
g by it
  gives rise to a valid structure.
-/
noncomputable instance prestructure : L.Prestructure (DirectLimit.setoid G f) where
  toStructure := sigmaStructure G f
  fun_equiv {n} {F} x y xy := by
    obtain ⟨i, hx, hy, h⟩ := exists_unify_eq G f xy
    refine
      Setoid.trans (funMap_equiv_unify G f F x i hx)
        (Setoid.trans ?_ (Setoid.symm (funMap_equiv_unify G f F y i hy)))
    rw [h]
  rel_equiv {n} {R} x y xy := by
    obtain ⟨i, hx, hy, h⟩ := exists_unify_eq G f xy
    refine _root_.trans (relMap_equiv_unify G f R x i hx)
      (_root_.trans ?_ (symm (relMap_equiv_unify G f R y i hy)))
    rw [h]

/-- The `L.Structure` on a direct limit of `L.Structure`s. -/
/-
**FirstOrder.Language.DirectLimit.instStructureDirectLimit** 是 Mathlib 中的一个实例，位于
命名空间 `FirstOrder.Language.DirectLimit`。
形式化陈述：instStructureDirectLimit : L.Structure (DirectLimit G f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `L.Structure` on a direct limit of `L.Structure`s.
-/
noncomputable instance instStructureDirectLimit : L.Structure (DirectLimit G f) :=
  inferInstanceAs <| L.Structure (Quotient (DirectLimit.setoid G f))

@[simp]
/-
**FirstOrder.Language.DirectLimit.funMap_quotient_mk'_sigma_mk'** 是 Mathlib 中的一个
定理，位于命名空间 `FirstOrder.Language.DirectLimit`。
形式化陈述：∀ {L : FirstOrder.Language} {ι : Type v} [inst : Preorder ι] (G : ι → Type
 w) [inst_1 : (i : ι) → L.Structure (G i)]   (f : (i j : ι) → i ≤ j → L.Embeddin
g (G i) (G j)) [inst_2 : IsDirectedOrder ι]   [inst_3 : DirectedSystem G fun i j
 h => ⇑(f i j h)] [inst_4 : Nonempty ι] {n : ℕ} {F : L.Functions n} {i : ι}   {x
 : Fin n → G i},   (FirstOrder.Language.Structure.funMap F fun a => ⟦FirstOrder.
Language.Structure.Sigma.mk f i (x a)⟧) =     ⟦FirstOrder.Language.Structure.Sig
ma.mk f i (FirstOrder.Language.Structure.funMap F x)⟧
参数：G : ι → Type w；i : ι；G i；f : (i j : ι) → i ≤ j → L.Embedding (G i) (G j)；f i 
j h；FirstOrder.Language.Structure.funMap F fun a => ⟦FirstOrder.Language.Structu
re.Sigma.mk f i (x a)⟧；FirstOrder.Language.Structure.funMap F x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.funMap_quotient_mk'`：funMap_quotient_mk' {n : Nat} (
f : L.Functions n) (x : Fin n -> M) : (funMap f fun i => (⟦x i⟧ : Quotient s)) =
 ⟦@funMap _ _ ps.toStructure …
· 使用定理 `Finite.bddAbove_range`：Finite.bddAbove_range [IsDirectedOrder α] (f : ι 
-> α) : BddAbove (Set.range f)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `directed_of`：directed_of (r : α -> α -> Prop) [IsDirected α r] (a b : α)
 : exists c, r a c ∧ r b c
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Language.Embedding.map_fun`：map_fun (φ : M ↪[L] N) {n : Nat} 
(f : L.Functions n) (x : Fin n -> M) : φ (funMap f x) = funMap f (φ ∘ x)
· 使用定理 `FirstOrder.Language.DirectLimit.comp_unify`：comp_unify {α : Type*} {x : 
α -> Σˣ f} {i j : ι} (ij : i <= j) (h : i in upperBounds (range (Sigma.fst ∘ x))
) : f i j ij ∘ unify f x i h = u…
-/
theorem funMap_quotient_mk'_sigma_mk' {n : ℕ} {F : L.Functions n} {i : ι} {x : Fin n → G i} :
    funMap F (fun a => (⟦.mk f i (x a)⟧ : DirectLimit G f)) = ⟦.mk f i (funMap F x)⟧ := by
  simp only [funMap_quotient_mk', Quotient.eq]
  obtain ⟨k, ik, jk⟩ :=
    directed_of (· ≤ ·) i (Classical.choose (Finite.bddAbove_range fun _ : Fin n => i))
  refine ⟨k, jk, ik, ?_⟩
  simp only [Embedding.map_fun, comp_unify]
  rfl

@[simp]
/-
**FirstOrder.Language.DirectLimit.relMap_quotient_mk'_sigma_mk'** 是 Mathlib 中的一个
定理，位于命名空间 `FirstOrder.Language.DirectLimit`。
形式化陈述：∀ {L : FirstOrder.Language} {ι : Type v} [inst : Preorder ι] (G : ι → Type
 w) [inst_1 : (i : ι) → L.Structure (G i)]   (f : (i j : ι) → i ≤ j → L.Embeddin
g (G i) (G j)) [inst_2 : IsDirectedOrder ι]   [inst_3 : DirectedSystem G fun i j
 h => ⇑(f i j h)] [inst_4 : Nonempty ι] {n : ℕ} {R : L.Relations n} {i : ι}   {x
 : Fin n → G i},   (FirstOrder.Language.Structure.RelMap R fun a => ⟦FirstOrder.
Language.Structure.Sigma.mk f i (x a)⟧) =     FirstOrder.Language.Structure.RelM
ap R x
参数：G : ι → Type w；i : ι；G i；f : (i j : ι) → i ≤ j → L.Embedding (G i) (G j)；f i 
j h；FirstOrder.Language.Structure.RelMap R fun a => ⟦FirstOrder.Language.Structu
re.Sigma.mk f i (x a)⟧。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.relMap_quotient_mk'`：relMap_quotient_mk' {n : Nat} (
r : L.Relations n) (x : Fin n -> M) : (RelMap r fun i => (⟦x i⟧ : Quotient s)) ↔
 @RelMap _ _ ps.toStructure _…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.DirectLimit.relMap_equiv_unify`：relMap_equiv_unify {
n : Nat} (R : L.Relations n) (x : Fin n -> Σˣ f) (i : ι) (hi : i in upperBounds 
(range (Sigma.fst ∘ x))) : RelMap R x = …
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `FirstOrder.Language.DirectLimit.unify_sigma_mk_self`：unify_sigma_mk_self
 {α : Type*} {i : ι} {x : α -> G i} : (unify f (fun a => .mk f i (x a)) i fun _ 
⟨_, hj⟩ => _root_.trans (le_of_eq hj.symm…
-/
theorem relMap_quotient_mk'_sigma_mk' {n : ℕ} {R : L.Relations n} {i : ι} {x : Fin n → G i} :
    RelMap R (fun a => (⟦.mk f i (x a)⟧ : DirectLimit G f)) = RelMap R x := by
  rw [relMap_quotient_mk']
  rw [relMap_equiv_unify G f R (fun a => .mk f i (x a)) i (fun _ ⟨_, hj⟩ => le_of_eq hj.symm)]
  rw [unify_sigma_mk_self]

set_option backward.isDefEq.respectTransparency false in
/-
**FirstOrder.Language.DirectLimit.exists_quotient_mk'_sigma_mk'_eq** 是 Mathlib 中
的一个定理，位于命名空间 `FirstOrder.Language.DirectLimit`。
形式化陈述：∀ {L : FirstOrder.Language} {ι : Type v} [inst : Preorder ι] (G : ι → Type
 w) [inst_1 : (i : ι) → L.Structure (G i)]   (f : (i j : ι) → i ≤ j → L.Embeddin
g (G i) (G j)) [inst_2 : IsDirectedOrder ι]   [inst_3 : DirectedSystem G fun i j
 h => ⇑(f i j h)] [Nonempty ι] {α : Type u_1} [Finite α]   (x : α → FirstOrder.L
anguage.DirectLimit G f), ∃ i y, x = fun a => ⟦FirstOrder.Language.Structure.Sig
ma.mk f i (y a)⟧
参数：G : ι → Type w；i : ι；G i；f : (i j : ι) → i ≤ j → L.Embedding (G i) (G j)；f i 
j h；x : α → FirstOrder.Language.DirectLimit G f；y a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.bddAbove_range`：Finite.bddAbove_range [IsDirectedOrder α] (f : ι 
-> α) : BddAbove (Set.range f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.eq_mk_iff_out`：Quotient.eq_mk_iff_out {s : Setoid α} {x : Quoti
ent s} {y : α} : x = ⟦y⟧ ↔ Quotient.out x ≈ y
· 使用定理 `FirstOrder.Language.DirectLimit.unify.eq_1`：∀ {L : FirstOrder.Language} 
{ι : Type v} [inst : Preorder ι] {G : ι → Type w} [inst_1 : (i : ι) → L.Structur
e (G i)]   (f : (i j : ι) → i ≤ …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `FirstOrder.Language.DirectLimit.equiv_iff`：equiv_iff {x y : Σˣ f} {i : ι
} (hx : x.1 <= i) (hy : y.1 <= i) : x ≈ y ↔ (f x.1 i hx) x.2 = (f y.1 i hy) y.2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FirstOrder.Language.DirectedSystem.map_self`：∀ {ι : Type u_1} [inst : Pr
eorder ι] {F : ι → Type u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι)
 → (h : i ≤ j) → T h) [inst_1 : ⦃…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_quotient_mk'_sigma_mk'_eq {α : Type*} [Finite α] (x : α → DirectLimit G f) :
    ∃ (i : ι) (y : α → G i), x = fun a => ⟦.mk f i (y a)⟧ := by
  obtain ⟨i, hi⟩ := Finite.bddAbove_range fun a => (x a).out.1
  refine ⟨i, unify f (Quotient.out ∘ x) i hi, ?_⟩
  ext a
  rw [Quotient.eq_mk_iff_out, unify]
  generalize_proofs r
  change _ ≈ Structure.Sigma.mk f i (f (Quotient.out (x a)).fst i r (Quotient.out (x a)).snd)
  have : (.mk f i (f (Quotient.out (x a)).fst i r (Quotient.out (x a)).snd) : Σˣ f).fst ≤ i :=
    le_rfl
  rw [equiv_iff G f (i := i) (hi _) this]
  · simp only [DirectedSystem.map_self]
  exact ⟨a, rfl⟩

variable (L ι)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from a component to the direct limit. -/
/-
**FirstOrder.Language.DirectLimit.of** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age.DirectLimit`。
形式化陈述：of (i : ι) : G i ↪[L] DirectLimit G f where toFun
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from a component to the direct limit.
-/
noncomputable def of (i : ι) : G i ↪[L] DirectLimit G f where
  toFun := fun a => ⟦.mk f i a⟧
  inj' x y h := by
    rw [Quotient.eq] at h
    obtain ⟨j, h1, _, h3⟩ := h
    exact (f i j h1).injective h3
  map_fun' F x := by
    rw [← funMap_quotient_mk'_sigma_mk']
    rfl
  map_rel' := by
    intro n R x
    change RelMap R (fun a => (⟦.mk f i (x a)⟧ : DirectLimit G f)) ↔ _
    simp only [relMap_quotient_mk'_sigma_mk']



variable {L ι G f}

@[simp]
/-
**FirstOrder.Language.DirectLimit.of_apply** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.DirectLimit`。
形式化陈述：of_apply {i : ι} {x : G i} : of L ι G f i x = ⟦.mk f i x⟧
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_apply {i : ι} {x : G i} : of L ι G f i x = ⟦.mk f i x⟧ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
-- This is not a simp-lemma because it is not in simp-normal form,
-- but the simp-normal version of this theorem would not be useful.
/-
**FirstOrder.Language.DirectLimit.of_f** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.DirectLimit`。
形式化陈述：of_f {i j : ι} {hij : i <= j} {x : G i} : of L ι G f j (f i j hij x) = of 
L ι G f i x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.DirectLimit.of_apply`：of_apply {i : ι} {x : G i} : o
f L ι G f i x = ⟦.mk f i x⟧
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FirstOrder.Language.DirectedSystem.map_self`：∀ {ι : Type u_1} [inst : Pr
eorder ι] {F : ι → Type u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι)
 → (h : i ≤ j) → T h) [inst_1 : ⦃…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_f {i j : ι} {hij : i ≤ j} {x : G i} : of L ι G f j (f i j hij x) = of L ι G f i x := by
  rw [of_apply, of_apply, Quotient.eq]
  refine Setoid.symm ⟨j, hij, refl j, ?_⟩
  simp only [DirectedSystem.map_self]

set_option backward.isDefEq.respectTransparency.types false in
/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
/-
**FirstOrder.Language.DirectLimit.exists_of** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.DirectLimit`。
形式化陈述：exists_of (z : DirectLimit G f) : exists i x, of L ι G f i x = z
参数：z : DirectLimit G f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Every element of the direct limit corresponds to some element in
some component of the directed system.
-/
theorem exists_of (z : DirectLimit G f) : ∃ i x, of L ι G f i x = z :=
  ⟨z.out.1, z.out.2, by simp⟩

@[elab_as_elim]
/-
**FirstOrder.Language.DirectLimit.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.DirectLimit`。
形式化陈述：∀ {L : FirstOrder.Language} {ι : Type v} [inst : Preorder ι] {G : ι → Type
 w} [inst_1 : (i : ι) → L.Structure (G i)]   {f : (i j : ι) → i ≤ j → L.Embeddin
g (G i) (G j)} [inst_2 : IsDirectedOrder ι]   [inst_3 : DirectedSystem G fun i j
 h => ⇑(f i j h)] [inst_4 : Nonempty ι]   {C : FirstOrder.Language.DirectLimit G
 f → Prop} (z : FirstOrder.Language.DirectLimit G f),   (∀ (i : ι) (x : G i), C 
((FirstOrder.Language.DirectLimit.of L ι G f i) x)) → C z
参数：i : ι；G i；i j : ι；G i；G j；f i j h；z : FirstOrder.Language.DirectLimit G f；∀ (
i : ι) (x : G i), C ((FirstOrder.Language.DirectLimit.of L ι G f i) x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.DirectLimit.exists_of`：exists_of (z : DirectLimit G 
f) : exists i x, of L ι G f i x = z
-/
protected theorem inductionOn {C : DirectLimit G f → Prop} (z : DirectLimit G f)
    (ih : ∀ i x, C (of L ι G f i x)) : C z :=
  let ⟨i, x, h⟩ := exists_of z
  h ▸ ih i x
/-
**FirstOrder.Language.DirectLimit.iSup_range_of_eq_top** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.DirectLimit`。
形式化陈述：iSup_range_of_eq_top : ⨆ i, (of L ι G f i).toHom.range = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `FirstOrder.Language.DirectLimit.inductionOn`：∀ {L : FirstOrder.Language}
 {ι : Type v} [inst : Preorder ι] {G : ι → Type w} [inst_1 : (i : ι) → L.Structu
re (G i)]   {f : (i j : ι) → i ≤ …
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem iSup_range_of_eq_top : ⨆ i, (of L ι G f i).toHom.range = ⊤ :=
  eq_top_iff.2 (fun x _ ↦ DirectLimit.inductionOn x
    (fun i _ ↦ le_iSup (fun i ↦ Hom.range (Embedding.toHom (of L ι G f i))) i (mem_range_self _)))

set_option backward.isDefEq.respectTransparency.types false in
/-- Every finitely generated substructure of the direct limit corresponds to some
substructure in some component of the directed system. -/
/-
**FirstOrder.Language.DirectLimit.exists_fg_substructure_in_Sigma** 是 Mathlib 中的
一个定理，位于命名空间 `FirstOrder.Language.DirectLimit`。
形式化陈述：exists_fg_substructure_in_Sigma (S : L.Substructure (DirectLimit G f)) (S_
fg : S.FG) : exists i, exists T : L.Substructure (G i), T.map (of L ι G f i).toH
om = S
参数：S : L.Substructure (DirectLimit G f)；S_fg : S.FG。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.DirectLimit.exists_quotient_mk'_sigma_mk'_eq`：∀ {L :
 FirstOrder.Language} {ι : Type v} [inst : Preorder ι] (G : ι → Type w) [inst_1 
: (i : ι) → L.Structure (G i)]   (f : (i j : ι) → i ≤ …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Substructure.map_closure`：map_closure (f : M ->[L] N
) (s : Set M) : (closure L s).map f = closure L (f '' s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Finset.setOfPred_mem`：setOfPred_mem {α} {s : Finset α} : { a | a in s } 
= s

--- 原说明 ---
Every finitely generated substructure of the direct limit corresponds to some
substructure in some component of the directed system.
-/
theorem exists_fg_substructure_in_Sigma (S : L.Substructure (DirectLimit G f)) (S_fg : S.FG) :
    ∃ i, ∃ T : L.Substructure (G i), T.map (of L ι G f i).toHom = S := by
  let ⟨A, A_closure⟩ := S_fg
  let ⟨i, y, eq_y⟩ := exists_quotient_mk'_sigma_mk'_eq G _ (fun a : A ↦ a.1)
  use i
  use Substructure.closure L (range y)
  rw [Substructure.map_closure]
  simp only [Embedding.coe_toHom, of_apply]
  rw [← image_univ, image_image, image_univ, ← eq_y,
    Subtype.range_coe_subtype, Finset.setOfPred_mem, A_closure]

variable {P : Type u₁} [L.Structure P]

set_option backward.isDefEq.respectTransparency false in
variable (L ι G f) in
/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
/-
**FirstOrder.Language.DirectLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lan
guage.DirectLimit`。
形式化陈述：lift (g : forall i, G i ↪[L] P) (Hg : forall i j hij x, g j (f i j hij x) 
= g i x) : DirectLimit G f ↪[L] P where toFun
参数：g : forall i, G i ↪[L] P；Hg : forall i j hij x, g j (f i j hij x) = g i x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of the direct limit: maps from the components to another 
module
that respect the directed system structure (i.e. make some diagram commute) give
 rise
to a unique map out of the direct limit.
-/
noncomputable def lift (g : ∀ i, G i ↪[L] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f ↪[L] P where
  toFun :=
    Quotient.lift (fun x : Σˣ f => (g x.1) x.2) fun x y xy => by
      obtain ⟨i, hx, hy⟩ := directed_of (· ≤ ·) x.1 y.1
      rw [← Hg x.1 i hx, ← Hg y.1 i hy]
      exact congr_arg _ ((equiv_iff ..).1 xy)
  inj' x y xy := by
    rw [← Quotient.out_eq x, ← Quotient.out_eq y, Quotient.lift_mk, Quotient.lift_mk] at xy
    obtain ⟨i, hx, hy⟩ := directed_of (· ≤ ·) x.out.1 y.out.1
    rw [← Hg x.out.1 i hx, ← Hg y.out.1 i hy] at xy
    rw [← Quotient.out_eq x, ← Quotient.out_eq y, Quotient.eq_iff_equiv, equiv_iff G f hx hy]
    exact (g i).injective xy
  map_fun' F x := by
    obtain ⟨i, y, rfl⟩ := exists_quotient_mk'_sigma_mk'_eq G f x
    change _ = funMap F (Quotient.lift _ _ ∘ Quotient.mk _ ∘ Structure.Sigma.mk f i ∘ y)
    rw [funMap_quotient_mk'_sigma_mk', ← Function.comp_assoc, Quotient.lift_comp_mk]
    simp only [Quotient.lift_mk, Embedding.map_fun]
    rfl
  map_rel' R x := by
    obtain ⟨i, y, rfl⟩ := exists_quotient_mk'_sigma_mk'_eq G f x
    change RelMap R (Quotient.lift _ _ ∘ Quotient.mk _ ∘ Structure.Sigma.mk f i ∘ y) ↔ _
    rw [relMap_quotient_mk'_sigma_mk' G f, ← (g i).map_rel R y, ← Function.comp_assoc,
      Quotient.lift_comp_mk]
    rfl

variable (g : ∀ i, G i ↪[L] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp]
/-
**FirstOrder.Language.DirectLimit.lift_quotient_mk'_sigma_mk'** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.DirectLimit`。
形式化陈述：∀ {L : FirstOrder.Language} {ι : Type v} [inst : Preorder ι] {G : ι → Type
 w} [inst_1 : (i : ι) → L.Structure (G i)]   {f : (i j : ι) → i ≤ j → L.Embeddin
g (G i) (G j)} [inst_2 : IsDirectedOrder ι]   [inst_3 : DirectedSystem G fun i j
 h => ⇑(f i j h)] [inst_4 : Nonempty ι] {P : Type u₁} [inst_5 : L.Structure P]  
 (g : (i : ι) → L.Embedding (G i) P) (Hg : ∀ (i j : ι) (hij : i ≤ j) (x : G i), 
(g j) ((f i j hij) x) = (g i) x)   {i : ι} (x : G i),   (FirstOrder.Language.Dir
ectLimit.lift L ι G f g Hg) ⟦FirstOrder.Language.Structure.Sigma.mk f i x⟧ = (g 
i) x
参数：i : ι；G i；i j : ι；G i；G j；f i j h；g : (i : ι) → L.Embedding (G i) P；Hg : ∀ (i
 j : ι) (hij : i ≤ j) (x : G i), (g j) ((f i j hij) x) = (g i) x；x : G i；FirstOr
der.Language.DirectLimit.lift L ι G f g Hg；g i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_quotient_mk'_sigma_mk' {i} (x : G i) : lift L ι G f g Hg ⟦.mk f i x⟧ = (g i) x := by
  change (lift L ι G f g Hg).toFun ⟦.mk f i x⟧ = _
  simp only [lift, Quotient.lift_mk]
/-
**FirstOrder.Language.DirectLimit.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.DirectLimit`。
形式化陈述：lift_of {i} (x : G i) : lift L ι G f g Hg (of L ι G f i x) = g i x
参数：x : G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.DirectLimit.lift_quotient_mk'_sigma_mk'`：∀ {L : Firs
tOrder.Language} {ι : Type v} [inst : Preorder ι] {G : ι → Type w} [inst_1 : (i 
: ι) → L.Structure (G i)]   {f : (i j : ι) → i ≤ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_of {i} (x : G i) : lift L ι G f g Hg (of L ι G f i x) = g i x := by simp
/-
**FirstOrder.Language.DirectLimit.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.DirectLimit`。
形式化陈述：lift_unique (F : DirectLimit G f ↪[L] P) (x) : F x = lift L ι G f (fun i =
> F.comp <| of L ι G f i) (fun i j hij x => by rw [F.comp_apply, F.comp_apply, o
f_f]) x
参数：F : DirectLimit G f ↪[L] P；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.DirectLimit.inductionOn`：∀ {L : FirstOrder.Language}
 {ι : Type v} [inst : Preorder ι] {G : ι → Type w} [inst_1 : (i : ι) → L.Structu
re (G i)]   {f : (i j : ι) → i ≤ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.DirectLimit.lift_of`：lift_of {i} (x : G i) : lift L 
ι G f g Hg (of L ι G f i x) = g i x
-/
theorem lift_unique (F : DirectLimit G f ↪[L] P) (x) :
    F x =
      lift L ι G f (fun i => F.comp <| of L ι G f i)
        (fun i j hij x => by rw [F.comp_apply, F.comp_apply, of_f]) x :=
  DirectLimit.inductionOn x fun i x => by rw [lift_of]; rfl
/-
**FirstOrder.Language.DirectLimit.range_lift** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrd
er.Language.DirectLimit`。
形式化陈述：range_lift : (lift L ι G f g Hg).toHom.range = ⨆ i, (g i).toHom.range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Hom.range_eq_map`：range_eq_map (f : M ->[L] N) : f.r
ange = map f ⊤
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.DirectLimit.iSup_range_of_eq_top`：iSup_range_of_eq_t
op : ⨆ i, (of L ι G f i).toHom.range = ⊤
· 使用定理 `FirstOrder.Language.Substructure.map_iSup`：map_iSup {ι : Sort*} (f : M -
>[L] N) (s : ι -> L.Substructure M) : (⨆ i, s i).map f = ⨆ i, (s i).map f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.Substructure.map_map`：map_map (g : N ->[L] P) (f : M
 ->[L] N) : (S.map f).map g = S.map (g.comp f)
-/
lemma range_lift : (lift L ι G f g Hg).toHom.range = ⨆ i, (g i).toHom.range := by
  simp_rw [Hom.range_eq_map]
  rw [← iSup_range_of_eq_top, Substructure.map_iSup]
  simp_rw [Hom.range_eq_map, Substructure.map_map]
  rfl

variable (L ι G f)
variable (G' : ι → Type w') [∀ i, L.Structure (G' i)]
variable (f' : ∀ i j, i ≤ j → G' i ↪[L] G' j)
variable (g : ∀ i, G i ≃[L] G' i)
variable [DirectedSystem G' fun i j h => f' i j h]

/-- The isomorphism between limits of isomorphic systems. -/
/-
**FirstOrder.Language.DirectLimit.equiv_lift** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrd
er.Language.DirectLimit`。
形式化陈述：equiv_lift (H_commuting : forall i j hij x, g j (f i j hij x) = f' i j hij
 (g i x)) : DirectLimit G f ≃[L] DirectLimit G' f'
参数：H_commuting : forall i j hij x, g j (f i j hij x) = f' i j hij (g i x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between limits of isomorphic systems.
-/
noncomputable def equiv_lift (H_commuting : ∀ i j hij x, g j (f i j hij x) = f' i j hij (g i x)) :
    DirectLimit G f ≃[L] DirectLimit G' f' := by
  let U i : G i ↪[L] DirectLimit G' f' := (of L _ G' f' i).comp (g i).toEmbedding
  let F : DirectLimit G f ↪[L] DirectLimit G' f' := lift L _ G f U <| by
    intro _ _ _ _
    simp only [U, Embedding.comp_apply, Equiv.coe_toEmbedding, H_commuting, of_f]
  have surj_f : Function.Surjective F := by
    intro x
    rcases x with ⟨i, pre_x⟩
    use of L _ G f i ((g i).symm pre_x)
    simp only [F, U, lift_of, Embedding.comp_apply, Equiv.coe_toEmbedding, Equiv.apply_symm_apply]
    rfl
  exact ⟨Equiv.ofBijective F ⟨F.injective, surj_f⟩, F.map_fun', F.map_rel'⟩

variable (H_commuting : ∀ i j hij x, g j (f i j hij x) = f' i j hij (g i x))
/-
**FirstOrder.Language.DirectLimit.equiv_lift_of** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.DirectLimit`。
形式化陈述：equiv_lift_of {i : ι} (x : G i) : equiv_lift L ι G f G' f' g H_commuting (
of L ι G f i x) = of L ι G' f' i (g i x)
参数：x : G i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_lift_of {i : ι} (x : G i) :
    equiv_lift L ι G f G' f' g H_commuting (of L ι G f i x) = of L ι G' f' i (g i x) := rfl

variable {L ι G f}

set_option backward.isDefEq.respectTransparency.types false in
/-- The direct limit of countably many countably generated structures is countably generated. -/
/-
**FirstOrder.Language.DirectLimit.cg** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langu
age.DirectLimit`。
形式化陈述：cg {ι : Type*} [Countable ι] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
 {G : ι -> Type w} [forall i, L.Structure (G i)] (f : forall i j, i <= j -> G i 
↪[L] G j) (h : forall i, Structure.CG L (G i)) [DirectedSystem G fun i j h => f 
i j h] : Structure.CG L (DirectLimit G f)
参数：G i；f : forall i j, i <= j -> G i ↪[L] G j；h : forall i, Structure.CG L (G i)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Structure.CG.out`：∀ {L : FirstOrder.Language} {M : T
ype u_1} {inst : L.Structure M} [self : FirstOrder.Language.Structure.CG L M], ⊤
.CG
· 使用定理 `Set.countable_iUnion`：countable_iUnion {t : ι -> Set α} [Countable ι] (h
t : forall i, (t i).Countable) : (⋃ i, t i).Countable
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `FirstOrder.Language.Substructure.closure_iUnion`：closure_iUnion {ι} (s :
 ι -> Set M) : closure L (⋃ i, s i) = ⨆ i, closure L (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `FirstOrder.Language.Substructure.closure_image`：closure_image (f : M ->[
L] N) : closure L (f '' s) = map f (closure L s)
· 使用定理 `le_iSup_iff`：le_iSup_iff {s : ι -> α} : a <= iSup s ↔ forall b, (forall 
i, s i <= b) -> a <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The direct limit of countably many countably generated structures is countably g
enerated.
-/
theorem cg {ι : Type*} [Countable ι] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {G : ι → Type w} [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    (h : ∀ i, Structure.CG L (G i)) [DirectedSystem G fun i j h => f i j h] :
    Structure.CG L (DirectLimit G f) := by
  refine ⟨⟨⋃ i, DirectLimit.of L ι G f i '' Classical.choose (h i).out, ?_, ?_⟩⟩
  · exact Set.countable_iUnion fun i => Set.Countable.image (Classical.choose_spec (h i).out).1 _
  · rw [eq_top_iff, Substructure.closure_iUnion]
    simp_rw [← Embedding.coe_toHom, Substructure.closure_image]
    rw [le_iSup_iff]
    intro S hS x _
    let out := Quotient.out (s := DirectLimit.setoid G f)
    refine hS (out x).1 ⟨(out x).2, ?_, ?_⟩
    · rw [(Classical.choose_spec (h (out x).1).out).2]
      trivial
    · simp only [out, Embedding.coe_toHom, DirectLimit.of_apply, Sigma.eta, Quotient.out_eq]
/-
**FirstOrder.Language.DirectLimit.cg'** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Lang
uage.DirectLimit`。
形式化陈述：cg' {ι : Type*} [Countable ι] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι
] {G : ι -> Type w} [forall i, L.Structure (G i)] (f : forall i j, i <= j -> G i
 ↪[L] G j) [h : forall i, Structure.CG L (G i)] [DirectedSystem G fun i j h => f
 i j h] : Structure.CG L (DirectLimit G f)
参数：G i；f : forall i j, i <= j -> G i ↪[L] G j；G i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.DirectLimit.cg`：cg {ι : Type*} [Countable ι] [Preord
er ι] [IsDirectedOrder ι] [Nonempty ι] {G : ι -> Type w} [forall i, L.Structure 
(G i)] (f : forall i j, …
-/
instance cg' {ι : Type*} [Countable ι] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {G : ι → Type w} [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [h : ∀ i, Structure.CG L (G i)] [DirectedSystem G fun i j h => f i j h] :
    Structure.CG L (DirectLimit G f) :=
  cg f h

end DirectLimit

section Substructure

variable [Nonempty ι] [IsDirectedOrder ι]
variable {M : Type*} [L.Structure M] (S : ι →o L.Substructure M)

/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DirectedSystem (fun i ↦ S i) (fun _ _ h ↦ Substructure.inclusion (S.monotone h)) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

namespace DirectLimit

/-- The map from a direct limit of a system of substructures of `M` into `M`. -/
/-
**FirstOrder.Language.DirectLimit.liftInclusion** 是 Mathlib 中的一个定义，位于命名空间 `First
Order.Language.DirectLimit`。
形式化陈述：liftInclusion : DirectLimit (fun i => S i) (fun _ _ h => Substructure.incl
usion (S.monotone h)) ↪[L] M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.instDirectedSystemSubtypeMemSubstructureCoeOrderHomE
mbeddingInclusion`：∀ {L : FirstOrder.Language} {ι : Type v} [inst : Preorder ι] 
{M : Type u_1} [inst_1 : L.Structure M]   (S : ι →o L.Substructure M),   Direct…

--- 原说明 ---
The map from a direct limit of a system of substructures of `M` into `M`.
-/
noncomputable def liftInclusion :
    DirectLimit (fun i ↦ S i) (fun _ _ h ↦ Substructure.inclusion (S.monotone h)) ↪[L] M :=
  DirectLimit.lift L ι (fun i ↦ S i) (fun _ _ h ↦ Substructure.inclusion (S.monotone h))
    (fun _ ↦ Substructure.subtype _) (fun _ _ _ _ ↦ rfl)
/-
**FirstOrder.Language.DirectLimit.liftInclusion_of** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.DirectLimit`。
形式化陈述：liftInclusion_of {i : ι} (x : S i) : (liftInclusion S) (of L ι _ (fun _ _ 
h => Substructure.inclusion (S.monotone h)) i x) = Substructure.subtype (S i) x
参数：x : S i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `FirstOrder.Language.instDirectedSystemSubtypeMemSubstructureCoeOrderHomE
mbeddingInclusion`：∀ {L : FirstOrder.Language} {ι : Type v} [inst : Preorder ι] 
{M : Type u_1} [inst_1 : L.Structure M]   (S : ι →o L.Substructure M),   Direct…
-/
theorem liftInclusion_of {i : ι} (x : S i) :
    (liftInclusion S) (of L ι _ (fun _ _ h ↦ Substructure.inclusion (S.monotone h)) i x)
    = Substructure.subtype (S i) x := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**FirstOrder.Language.DirectLimit.rangeLiftInclusion** 是 Mathlib 中的一个引理，位于命名空间 `
FirstOrder.Language.DirectLimit`。
形式化陈述：rangeLiftInclusion : (liftInclusion S).toHom.range = ⨆ i, S i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `FirstOrder.Language.instDirectedSystemSubtypeMemSubstructureCoeOrderHomE
mbeddingInclusion`：∀ {L : FirstOrder.Language} {ι : Type v} [inst : Preorder ι] 
{M : Type u_1} [inst_1 : L.Structure M]   (S : ι →o L.Substructure M),   Direct…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FirstOrder.Language.DirectLimit.range_lift`：range_lift : (lift L ι G f g
 Hg).toHom.range = ⨆ i, (g i).toHom.range
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.Substructure.range_subtype`：range_subtype (S : L.Sub
structure M) : S.subtype.toHom.range = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rangeLiftInclusion : (liftInclusion S).toHom.range = ⨆ i, S i := by
  simp_rw [liftInclusion, range_lift, Substructure.range_subtype]

/-- The isomorphism between a direct limit of a system of substructures and their union. -/
/-
**FirstOrder.Language.DirectLimit.Equiv_iSup** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrd
er.Language.DirectLimit`。
形式化陈述：Equiv_iSup : DirectLimit (fun i => S i) (fun _ _ h => Substructure.inclusi
on (S.monotone h)) ≃[L] (iSup S : L.Substructure M)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.instDirectedSystemSubtypeMemSubstructureCoeOrderHomE
mbeddingInclusion`：∀ {L : FirstOrder.Language} {ι : Type v} [inst : Preorder ι] 
{M : Type u_1} [inst_1 : L.Structure M]   (S : ι →o L.Substructure M),   Direct…

--- 原说明 ---
The isomorphism between a direct limit of a system of substructures and their un
ion.
-/
noncomputable def Equiv_iSup :
    DirectLimit (fun i ↦ S i) (fun _ _ h ↦ Substructure.inclusion (S.monotone h)) ≃[L]
    (iSup S : L.Substructure M) := by
  have liftInclusion_in_sup : ∀ x, liftInclusion S x ∈ (⨆ i, S i) := by
    simp only [← rangeLiftInclusion, Hom.mem_range, Embedding.coe_toHom]
    intro x; use x
  let F := Embedding.codRestrict (⨆ i, S i) _ liftInclusion_in_sup
  have F_surj : Function.Surjective F := by
    rintro ⟨m, hm⟩
    rw [← rangeLiftInclusion, Hom.mem_range] at hm
    rcases hm with ⟨a, _⟩; use a
    simpa only [F, Embedding.codRestrict_apply', Subtype.mk.injEq]
  exact ⟨Equiv.ofBijective F ⟨F.injective, F_surj⟩, F.map_fun', F.map_rel'⟩
/-
**FirstOrder.Language.DirectLimit.Equiv_isup_of_apply** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.DirectLimit`。
形式化陈述：Equiv_isup_of_apply {i : ι} (x : S i) : Equiv_iSup S (of L ι _ (fun _ _ h 
=> Substructure.inclusion (S.monotone h)) i x) = Substructure.inclusion (le_iSup
 _ _) x
参数：x : S i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `FirstOrder.Language.instDirectedSystemSubtypeMemSubstructureCoeOrderHomE
mbeddingInclusion`：∀ {L : FirstOrder.Language} {ι : Type v} [inst : Preorder ι] 
{M : Type u_1} [inst_1 : L.Structure M]   (S : ι →o L.Substructure M),   Direct…
-/
theorem Equiv_isup_of_apply {i : ι} (x : S i) :
    Equiv_iSup S (of L ι _ (fun _ _ h ↦ Substructure.inclusion (S.monotone h)) i x)
    = Substructure.inclusion (le_iSup _ _) x := rfl
/-
**FirstOrder.Language.DirectLimit.Equiv_isup_symm_inclusion_apply** 是 Mathlib 中的
一个定理，位于命名空间 `FirstOrder.Language.DirectLimit`。
形式化陈述：Equiv_isup_symm_inclusion_apply {i : ι} (x : S i) : (Equiv_iSup S).symm (S
ubstructure.inclusion (le_iSup _ _) x) = of L ι _ (fun _ _ h => Substructure.inc
lusion (S.monotone h)) i x
参数：x : S i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Equiv.injective`：injective (f : M ≃[L] N) : Function
.Injective f
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `FirstOrder.Language.instDirectedSystemSubtypeMemSubstructureCoeOrderHomE
mbeddingInclusion`：∀ {L : FirstOrder.Language} {ι : Type v} [inst : Preorder ι] 
{M : Type u_1} [inst_1 : L.Structure M]   (S : ι →o L.Substructure M),   Direct…
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Equiv.apply_symm_apply`：apply_symm_apply (f : M ≃[L]
 N) (a : N) : f (f.symm a) = a
-/
theorem Equiv_isup_symm_inclusion_apply {i : ι} (x : S i) :
    (Equiv_iSup S).symm (Substructure.inclusion (le_iSup _ _) x)
    = of L ι _ (fun _ _ h ↦ Substructure.inclusion (S.monotone h)) i x := by
  apply (Equiv_iSup S).injective
  simp only [Equiv.apply_symm_apply]
  rfl

@[simp]
/-
**FirstOrder.Language.DirectLimit.Equiv_isup_symm_inclusion** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Language.DirectLimit`。
形式化陈述：Equiv_isup_symm_inclusion (i : ι) : (Equiv_iSup S).symm.toEmbedding.comp (
Substructure.inclusion (le_iSup _ _)) = of L ι _ (fun _ _ h => Substructure.incl
usion (S.monotone h)) i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `FirstOrder.Language.instDirectedSystemSubtypeMemSubstructureCoeOrderHomE
mbeddingInclusion`：∀ {L : FirstOrder.Language} {ι : Type v} [inst : Preorder ι] 
{M : Type u_1} [inst_1 : L.Structure M]   (S : ι →o L.Substructure M),   Direct…
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `FirstOrder.Language.DirectLimit.Equiv_isup_symm_inclusion_apply`：Equiv_i
sup_symm_inclusion_apply {i : ι} (x : S i) : (Equiv_iSup S).symm (Substructure.i
nclusion (le_iSup _ _) x) = of L ι _ (fun _ _ h => Su…
-/
theorem Equiv_isup_symm_inclusion (i : ι) :
    (Equiv_iSup S).symm.toEmbedding.comp (Substructure.inclusion (le_iSup _ _))
    = of L ι _ (fun _ _ h ↦ Substructure.inclusion (S.monotone h)) i := by
  ext x; exact Equiv_isup_symm_inclusion_apply _ x

end DirectLimit

end Substructure

end Language

end FirstOrder

