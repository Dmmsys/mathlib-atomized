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
variable {G : ι -> Type w} [forall i, L.Structure (G i)]
variable (f : forall i j, i <= j -> G i ↪[L] G j)

namespace DirectedSystem

alias map_self := DirectedSystem.map_self'
alias map_map := DirectedSystem.map_map'

variable {G' : Nat -> Type w} [forall i, L.Structure (G' i)] (f' : forall n : Nat, G' n ↪[L] G' (n + 1))

/--
Definition of `natLERec` / `natLERec` 的定义

English:
definition natLERec
  signature: (m n : Nat) (h : m <= n)
  body: Nat.leRecOn h (@fun k g => (f' k).comp g) (Embedding.refl L _)

@[simp]

中文:
定义 natLERec
  签名: (m n : 自然数) (h : m <= n)
  定义体: Nat.leRecOn h (@fun k g => (f' k).comp g) (Embedding.refl L _)

@[simp]

Depends on / 依赖: Embedding, Embedding.refl, Nat.leRecOn, leRecOn
-/
def natLERec (m n : Nat) (h : m <= n) : G' m ↪[L] G' n :=
  Nat.leRecOn h (@fun k g => (f' k).comp g) (Embedding.refl L _)

@[simp]
/--
theorem `coe_natLERec` / 定理 `coe_natLERec`

English:
theorem coe_natLERec
  given: (m n : Nat) (h : m <= n)
  proof: by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  ext x
  induction k with
  | zero => simp [natLERec, Nat.leRecOn_self]
  | succ k ih =>
    rw [Nat.leRecOn_succ le_self_add]; rw [natLERec]; rw [Nat.leRecOn_succ le_self_add]; rw [← natLERec]; rw [Embedding.comp_apply]; rw [ih]

中文:
定理 coe_natLERec
  条件: (m n : 自然数) (h : m <= n)
  证明: by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  ext x
  induction k with
  | zero => simp [natLERec, Nat.leRecOn_self]
  | succ k ih =>
    rw [Nat.leRecOn_succ le_self_add]; rw [natLERec]; rw [Nat.leRecOn_succ le_self_add]; rw [← natLERec]; rw [Embedding.comp_apply]; rw [ih]

Depends on / 依赖: Embedding, Embedding.comp_apply, Nat.exists_eq_add_of_le, Nat.leRecOn_self, Nat.leRecOn_succ, comp_apply, exists_eq_add_of_le, leRecOn_self, leRecOn_succ, le_self_add, natLERec
-/
theorem coe_natLERec (m n : Nat) (h : m <= n) :
    (natLERec f' m n h : G' m -> G' n) = Nat.leRecOn h (@fun k => f' k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  ext x
  induction k with
  | zero => simp [natLERec, Nat.leRecOn_self]
  | succ k ih =>
    rw [Nat.leRecOn_succ le_self_add]; rw [natLERec]; rw [Nat.leRecOn_succ le_self_add]; rw [← natLERec]; rw [Embedding.comp_apply]; rw [ih]

/--
Instance `natLERec.directedSystem` / 实例 `natLERec.directedSystem`

English:
instance natLERec.directedSystem
  signature: : DirectedSystem G' fun i j h => natLERec f' i j h
  body: ⟨fun _ _ => congr (congr rfl (Nat.leRecOn_self _)) rfl,
   fun _ _ _ hij hjk => by simp [Nat.leRecOn_trans hij hjk]⟩

中文:
实例 natLERec.directedSystem
  签名: : DirectedSystem G' fun i j h => natLERec f' i j h
  定义体: ⟨fun _ _ => congr (congr rfl (Nat.leRecOn_self _)) rfl,
   fun _ _ _ hij hjk => by simp [Nat.leRecOn_trans hij hjk]⟩

Depends on / 依赖: Nat.leRecOn_self, Nat.leRecOn_trans, leRecOn_self, leRecOn_trans
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
/--
Definition of `Structure.Sigma` / `Structure.Sigma` 的定义

English:
abbreviation Structure.Sigma
  signature: (f : forall i j, i <= j -> G i ↪[L] G j)
  body: Σ i, G i

local notation "Σˣ" => Structure.Sigma

中文:
缩写 Structure.Sigma
  签名: (f : 对任意 i j, i <= j -> G i ↪[L] G j)
  定义体: Σ i, G i

local notation "Σˣ" => Structure.Sigma
-/
protected abbrev Structure.Sigma (f : forall i j, i <= j -> G i ↪[L] G j) := Σ i, G i

local notation "Σˣ" => Structure.Sigma

/--
Definition of `Structure.Sigma.mk` / `Structure.Sigma.mk` 的定义

English:
abbreviation Structure.Sigma.mk
  signature: (i : ι) (x : G i)
  body: ⟨i, x⟩

中文:
缩写 Structure.Sigma.mk
  签名: (i : ι) (x : G i)
  定义体: ⟨i, x⟩
-/
abbrev Structure.Sigma.mk (i : ι) (x : G i) : Σˣ f := ⟨i, x⟩

namespace DirectLimit

/--
Definition of `unify` / `unify` 的定义

English:
definition unify
  signature: {α : Type*} (x : α -> Σˣ f) (i : ι) (h : i in upperBounds (range (Sigma.fst ∘ x)))
  body: f (x a).1 i (h (mem_range_self a)) (x a).2

中文:
定义 unify
  签名: {α : 类型} (x : α -> Σˣ f) (i : ι) (h : i in upperBounds (range (Sigma.fst ∘ x)))
  定义体: f (x a).1 i (h (mem_range_self a)) (x a).2

Depends on / 依赖: mem_range_self
-/
def unify {α : Type*} (x : α -> Σˣ f) (i : ι) (h : i in upperBounds (range (Sigma.fst ∘ x)))
    (a : α) : G i :=
  f (x a).1 i (h (mem_range_self a)) (x a).2

variable [DirectedSystem G fun i j h => f i j h]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `unify_sigma_mk_self` / 定理 `unify_sigma_mk_self`

English:
theorem unify_sigma_mk_self
  given: {α : Type*} {i : ι} {x : α -> G i}
  proof: by
  ext a
  rw [unify]
  apply DirectedSystem.map_self

中文:
定理 unify_sigma_mk_self
  条件: {α : 类型} {i : ι} {x : α -> G i}
  证明: by
  ext a
  rw [unify]
  apply DirectedSystem.map_self

Depends on / 依赖: DirectedSystem, DirectedSystem.map_self, map_self
-/
theorem unify_sigma_mk_self {α : Type*} {i : ι} {x : α -> G i} :
    (unify f (fun a => .mk f i (x a)) i fun _ ⟨_, hj⟩ =>
      _root_.trans (le_of_eq hj.symm) (refl _)) = x := by
  ext a
  rw [unify]
  apply DirectedSystem.map_self

/--
theorem `comp_unify` / 定理 `comp_unify`

English:
theorem comp_unify
  statement: {α : Type*} {x : α -> Σˣ f} {i j : ι} (ij : i <= j)
  proof: by
  ext a
  simp [unify, DirectedSystem.map_map]

中文:
定理 comp_unify
  结论: {α : 类型} {x : α -> Σˣ f} {i j : ι} (ij : i <= j)
  证明: by
  ext a
  simp [unify, DirectedSystem.map_map]

Depends on / 依赖: DirectedSystem, DirectedSystem.map_map, map_map
-/
theorem comp_unify {α : Type*} {x : α -> Σˣ f} {i j : ι} (ij : i <= j)
    (h : i in upperBounds (range (Sigma.fst ∘ x))) :
    f i j ij ∘ unify f x i h = unify f x j
      fun k hk => _root_.trans (mem_upperBounds.1 h k hk) ij := by
  ext a
  simp [unify, DirectedSystem.map_map]

end DirectLimit

variable (G)

namespace DirectLimit

/-- The directed limit glues together the structures along the embeddings. -/
@[instance_reducible]
/--
Definition of `setoid` / `setoid` 的定义

English:
definition setoid
  signature: [DirectedSystem G fun i j h => f i j h] [IsDirectedOrder ι]
  body: fun ⟨i, x⟩ ⟨j, y⟩ => exists (k : ι) (ik : i <= k) (jk : j <= k), f i k ik x = f j k jk y
  iseqv :=
    ⟨fun ⟨i, _⟩ => ⟨i, refl i, refl i, rfl⟩, @fun ⟨_, _⟩ ⟨_, _⟩ ⟨k, ik, jk, h⟩ =>
      ⟨k, jk, ik, h.symm⟩,
      @fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ ⟨ij, hiij, hjij, hij⟩ ⟨jk, hjjk, hkjk, hjk⟩ => by
        o

中文:
定义 setoid
  签名: [DirectedSystem G fun i j h => f i j h] [IsDirectedOrder ι]
  定义体: fun ⟨i, x⟩ ⟨j, y⟩ => exists (k : ι) (ik : i <= k) (jk : j <= k), f i k ik x = f j k jk y
  iseqv :=
    ⟨fun ⟨i, _⟩ => ⟨i, refl i, refl i, rfl⟩, @fun ⟨_, _⟩ ⟨_, _⟩ ⟨k, ik, jk, h⟩ =>
      ⟨k, jk, ik, h.symm⟩,
      @fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ ⟨ij, hiij, hjij, hij⟩ ⟨jk, hjjk, hkjk, hjk⟩ => by
        o
-/
def setoid [DirectedSystem G fun i j h => f i j h] [IsDirectedOrder ι] : Setoid (Σˣ f) where
  r := fun ⟨i, x⟩ ⟨j, y⟩ => exists (k : ι) (ik : i <= k) (jk : j <= k), f i k ik x = f j k jk y
  iseqv :=
    ⟨fun ⟨i, _⟩ => ⟨i, refl i, refl i, rfl⟩, @fun ⟨_, _⟩ ⟨_, _⟩ ⟨k, ik, jk, h⟩ =>
      ⟨k, jk, ik, h.symm⟩,
      @fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ ⟨ij, hiij, hjij, hij⟩ ⟨jk, hjjk, hkjk, hjk⟩ => by
        obtain ⟨ijk, hijijk, hjkijk⟩ := directed_of (· <= ·) ij jk
        refine ⟨ijk, le_trans hiij hijijk, le_trans hkjk hjkijk, ?_⟩
        rw [← DirectedSystem.map_map _ hiij hijijk]; rw [hij]; rw [DirectedSystem.map_map]
        rw [← DirectedSystem.map_map _ hkjk hjkijk]; rw [← hjk]; rw [DirectedSystem.map_map]⟩

/-- The structure on the `Σ`-type which becomes the structure on the direct limit after quotienting.
-/
@[instance_reducible]
/--
Definition of `sigmaStructure` / `sigmaStructure` 的定义

English:
definition sigmaStructure
  signature: [IsDirectedOrder ι] [Nonempty ι]
  body: ⟨_,
      funMap F
        (unify f x (Classical.choose (Finite.bddAbove_range fun a => (x a).1))
          (Classical.choose_spec (Finite.bddAbove_range fun a => (x a).1)))⟩
  RelMap R x :=
    RelMap R
      (unify f x (Classical.choose (Finite.bddAbove_range fun a => (x a).1))
        (Classical.

中文:
定义 sigmaStructure
  签名: [IsDirectedOrder ι] [Nonempty ι]
  定义体: ⟨_,
      funMap F
        (unify f x (Classical.choose (Finite.bddAbove_range fun a => (x a).1))
          (Classical.choose_spec (Finite.bddAbove_range fun a => (x a).1)))⟩
  RelMap R x :=
    RelMap R
      (unify f x (Classical.choose (Finite.bddAbove_range fun a => (x a).1))
        (Classical.

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, Finite, Finite.bddAbove_range, RelMap, bddAbove_range, choose_spec, funMap
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

/--
Definition of `DirectLimit` / `DirectLimit` 的定义

English:
definition DirectLimit
  signature: [DirectedSystem G fun i j h => f i j h] [IsDirectedOrder ι]
  body: Quotient (DirectLimit.setoid G f)

中文:
定义 DirectLimit
  签名: [DirectedSystem G fun i j h => f i j h] [IsDirectedOrder ι]
  定义体: Quotient (DirectLimit.setoid G f)

Depends on / 依赖: DirectLimit, DirectLimit.setoid, Quotient, setoid
-/
def DirectLimit [DirectedSystem G fun i j h => f i j h] [IsDirectedOrder ι] :=
  Quotient (DirectLimit.setoid G f)

attribute [local instance] DirectLimit.setoid DirectLimit.sigmaStructure

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DirectedSystem
  signature: G fun i j h => f i j h] [IsDirectedOrder ι] [Inhabited ι]
  body: ⟨⟦⟨default, default⟩⟧⟩

中文:
实例 [DirectedSystem
  签名: G fun i j h => f i j h] [IsDirectedOrder ι] [Inhabited ι]
  定义体: ⟨⟦⟨default, default⟩⟧⟩
-/
instance [DirectedSystem G fun i j h => f i j h] [IsDirectedOrder ι] [Inhabited ι]
    [Inhabited (G default)] : Inhabited (DirectLimit G f) :=
  ⟨⟦⟨default, default⟩⟧⟩

namespace DirectLimit

variable [IsDirectedOrder ι] [DirectedSystem G fun i j h => f i j h]

/--
theorem `equiv_iff` / 定理 `equiv_iff`

English:
theorem equiv_iff
  given: {x y : Σˣ f} {i : ι} (hx : x.1 <= i) (hy : y.1 <= i)
  proof: by
  cases x
  cases y
  refine ⟨fun xy => ?_, fun xy => ⟨i, hx, hy, xy⟩⟩
  obtain ⟨j, _, _, h⟩ := xy
  obtain ⟨k, ik, jk⟩ := directed_of (· <= ·) i j
  have h := congr_arg (f j k jk) h
  apply (f i k ik).injective
  rw [DirectedSystem.map_map]; rw [DirectedSystem.map_map] at *
  exact h

中文:
定理 equiv_iff
  条件: {x y : Σˣ f} {i : ι} (hx : x.1 <= i) (hy : y.1 <= i)
  证明: by
  cases x
  cases y
  refine ⟨fun xy => ?_, fun xy => ⟨i, hx, hy, xy⟩⟩
  obtain ⟨j, _, _, h⟩ := xy
  obtain ⟨k, ik, jk⟩ := directed_of (· <= ·) i j
  have h := congr_arg (f j k jk) h
  apply (f i k ik).injective
  rw [DirectedSystem.map_map]; rw [DirectedSystem.map_map] at *
  exact h

Depends on / 依赖: DirectedSystem, DirectedSystem.map_map, congr_arg, directed_of, injective, map_map
-/
theorem equiv_iff {x y : Σˣ f} {i : ι} (hx : x.1 <= i) (hy : y.1 <= i) :
    x ≈ y ↔ (f x.1 i hx) x.2 = (f y.1 i hy) y.2 := by
  cases x
  cases y
  refine ⟨fun xy => ?_, fun xy => ⟨i, hx, hy, xy⟩⟩
  obtain ⟨j, _, _, h⟩ := xy
  obtain ⟨k, ik, jk⟩ := directed_of (· <= ·) i j
  have h := congr_arg (f j k jk) h
  apply (f i k ik).injective
  rw [DirectedSystem.map_map]; rw [DirectedSystem.map_map] at *
  exact h

/--
theorem `funMap_unify_equiv` / 定理 `funMap_unify_equiv`

English:
theorem funMap_unify_equiv
  statement: {n : Nat} (F : L.Functions n) (x : Fin n -> Σˣ f) (i j : ι)
  proof: by
  obtain ⟨k, ik, jk⟩ := directed_of (· <= ·) i j
  refine ⟨k, ik, jk, ?_⟩
  rw [(f i k ik).map_fun]; rw [(f j k jk).map_fun]; rw [comp_unify]; rw [comp_unify]

中文:
定理 funMap_unify_equiv
  结论: {n : 自然数} (F : L.Functions n) (x : Fin n -> Σˣ f) (i j : ι)
  证明: by
  obtain ⟨k, ik, jk⟩ := directed_of (· <= ·) i j
  refine ⟨k, ik, jk, ?_⟩
  rw [(f i k ik).map_fun]; rw [(f j k jk).map_fun]; rw [comp_unify]; rw [comp_unify]

Depends on / 依赖: comp_unify, directed_of, map_fun
-/
theorem funMap_unify_equiv {n : Nat} (F : L.Functions n) (x : Fin n -> Σˣ f) (i j : ι)
    (hi : i in upperBounds (range (Sigma.fst ∘ x))) (hj : j in upperBounds (range (Sigma.fst ∘ x))) :
    Structure.Sigma.mk f i (funMap F (unify f x i hi)) ≈ .mk f j (funMap F (unify f x j hj)) := by
  obtain ⟨k, ik, jk⟩ := directed_of (· <= ·) i j
  refine ⟨k, ik, jk, ?_⟩
  rw [(f i k ik).map_fun]; rw [(f j k jk).map_fun]; rw [comp_unify]; rw [comp_unify]

/--
theorem `relMap_unify_equiv` / 定理 `relMap_unify_equiv`

English:
theorem relMap_unify_equiv
  statement: {n : Nat} (R : L.Relations n) (x : Fin n -> Σˣ f) (i j : ι)
  proof: by
  obtain ⟨k, ik, jk⟩ := directed_of (· <= ·) i j
  rw [← (f i k ik).map_rel]; rw [comp_unify]; rw [← (f j k jk).map_rel]; rw [comp_unify]

中文:
定理 relMap_unify_equiv
  结论: {n : 自然数} (R : L.Relations n) (x : Fin n -> Σˣ f) (i j : ι)
  证明: by
  obtain ⟨k, ik, jk⟩ := directed_of (· <= ·) i j
  rw [← (f i k ik).map_rel]; rw [comp_unify]; rw [← (f j k jk).map_rel]; rw [comp_unify]

Depends on / 依赖: comp_unify, directed_of, map_rel
-/
theorem relMap_unify_equiv {n : Nat} (R : L.Relations n) (x : Fin n -> Σˣ f) (i j : ι)
    (hi : i in upperBounds (range (Sigma.fst ∘ x))) (hj : j in upperBounds (range (Sigma.fst ∘ x))) :
    RelMap R (unify f x i hi) = RelMap R (unify f x j hj) := by
  obtain ⟨k, ik, jk⟩ := directed_of (· <= ·) i j
  rw [← (f i k ik).map_rel]; rw [comp_unify]; rw [← (f j k jk).map_rel]; rw [comp_unify]

variable [Nonempty ι]

/--
theorem `exists_unify_eq` / 定理 `exists_unify_eq`

English:
theorem exists_unify_eq
  given: {α : Type*} [Finite α] {x y : α -> Σˣ f} (xy : x ≈ y)
  proof: by
  obtain ⟨i, hi⟩ := Finite.bddAbove_range (Sum.elim (fun a => (x a).1) fun a => (y a).1)
  rw [Sum.elim_range]; rw [upperBounds_union] at hi
  simp_rw [← Function.comp_apply (f := Sigma.fst)] at hi
  exact ⟨i, hi.1, hi.2, funext fun a => (equiv_iff G f _ _).1 (xy a)⟩

中文:
定理 exists_unify_eq
  条件: {α : 类型} [Finite α] {x y : α -> Σˣ f} (xy : x ≈ y)
  证明: by
  obtain ⟨i, hi⟩ := Finite.bddAbove_range (Sum.elim (fun a => (x a).1) fun a => (y a).1)
  rw [Sum.elim_range]; rw [upperBounds_union] at hi
  simp_rw [← Function.comp_apply (f := Sigma.fst)] at hi
  exact ⟨i, hi.1, hi.2, funext fun a => (equiv_iff G f _ _).1 (xy a)⟩

Depends on / 依赖: Finite, Finite.bddAbove_range, Function, Function.comp_apply, Sigma.fst, Sum.elim, Sum.elim_range, bddAbove_range, comp_apply, elim_range, equiv_iff, simp_rw, upperBounds_union
-/
theorem exists_unify_eq {α : Type*} [Finite α] {x y : α -> Σˣ f} (xy : x ≈ y) :
    exists (i : ι) (hx : i in upperBounds (range (Sigma.fst ∘ x)))
      (hy : i in upperBounds (range (Sigma.fst ∘ y))), unify f x i hx = unify f y i hy := by
  obtain ⟨i, hi⟩ := Finite.bddAbove_range (Sum.elim (fun a => (x a).1) fun a => (y a).1)
  rw [Sum.elim_range]; rw [upperBounds_union] at hi
  simp_rw [← Function.comp_apply (f := Sigma.fst)] at hi
  exact ⟨i, hi.1, hi.2, funext fun a => (equiv_iff G f _ _).1 (xy a)⟩

/--
theorem `funMap_equiv_unify` / 定理 `funMap_equiv_unify`

English:
theorem funMap_equiv_unify
  statement: {n : Nat} (F : L.Functions n) (x : Fin n -> Σˣ f) (i : ι)
  proof: funMap_unify_equiv G f F x (Classical.choose (Finite.bddAbove_range fun a => (x a).1)) i _ hi

中文:
定理 funMap_equiv_unify
  结论: {n : 自然数} (F : L.Functions n) (x : Fin n -> Σˣ f) (i : ι)
  证明: funMap_unify_equiv G f F x (Classical.choose (Finite.bddAbove_range fun a => (x a).1)) i _ hi

Depends on / 依赖: Classical, Classical.choose, Finite, Finite.bddAbove_range, bddAbove_range, funMap_unify_equiv
-/
theorem funMap_equiv_unify {n : Nat} (F : L.Functions n) (x : Fin n -> Σˣ f) (i : ι)
    (hi : i in upperBounds (range (Sigma.fst ∘ x))) :
    funMap F x ≈ .mk f _ (funMap F (unify f x i hi)) :=
  funMap_unify_equiv G f F x (Classical.choose (Finite.bddAbove_range fun a => (x a).1)) i _ hi

/--
theorem `relMap_equiv_unify` / 定理 `relMap_equiv_unify`

English:
theorem relMap_equiv_unify
  statement: {n : Nat} (R : L.Relations n) (x : Fin n -> Σˣ f) (i : ι)
  proof: relMap_unify_equiv G f R x (Classical.choose (Finite.bddAbove_range fun a => (x a).1)) i _ hi

中文:
定理 relMap_equiv_unify
  结论: {n : 自然数} (R : L.Relations n) (x : Fin n -> Σˣ f) (i : ι)
  证明: relMap_unify_equiv G f R x (Classical.choose (Finite.bddAbove_range fun a => (x a).1)) i _ hi

Depends on / 依赖: Classical, Classical.choose, Finite, Finite.bddAbove_range, bddAbove_range, relMap_unify_equiv
-/
theorem relMap_equiv_unify {n : Nat} (R : L.Relations n) (x : Fin n -> Σˣ f) (i : ι)
    (hi : i in upperBounds (range (Sigma.fst ∘ x))) :
    RelMap R x = RelMap R (unify f x i hi) :=
  relMap_unify_equiv G f R x (Classical.choose (Finite.bddAbove_range fun a => (x a).1)) i _ hi

/--
Instance `prestructure` / 实例 `prestructure`

English:
instance prestructure
  signature: : L.Prestructure (DirectLimit.setoid G f) where
  body: sigmaStructure G f
  fun_equiv {n} {F} x y xy := by
    obtain ⟨i, hx, hy, h⟩ := exists_unify_eq G f xy
    refine
      Setoid.trans (funMap_equiv_unify G f F x i hx)
        (Setoid.trans ?_ (Setoid.symm (funMap_equiv_unify G f F y i hy)))
    rw [h]
  rel_equiv {n} {R} x y xy := by
    obtain ⟨i,

中文:
实例 prestructure
  签名: : L.Prestructure (DirectLimit.setoid G f) where
  定义体: sigmaStructure G f
  fun_equiv {n} {F} x y xy := by
    obtain ⟨i, hx, hy, h⟩ := exists_unify_eq G f xy
    refine
      Setoid.trans (funMap_equiv_unify G f F x i hx)
        (Setoid.trans ?_ (Setoid.symm (funMap_equiv_unify G f F y i hy)))
    rw [h]
  rel_equiv {n} {R} x y xy := by
    obtain ⟨i,

Depends on / 依赖: sigmaStructure
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

/--
Instance `instStructureDirectLimit` / 实例 `instStructureDirectLimit`

English:
instance instStructureDirectLimit
  signature: : L.Structure (DirectLimit G f)
  body: inferInstanceAs L.Structure (Quotient (DirectLimit.setoid G f))

@[simp]

中文:
实例 instStructureDirectLimit
  签名: : L.Structure (DirectLimit G f)
  定义体: inferInstanceAs L.Structure (Quotient (DirectLimit.setoid G f))

@[simp]

Depends on / 依赖: DirectLimit, DirectLimit.setoid, L.Structure, Quotient, Structure, setoid
-/
noncomputable instance instStructureDirectLimit : L.Structure (DirectLimit G f) :=
inferInstanceAs L.Structure (Quotient (DirectLimit.setoid G f))

@[simp]
/--
theorem `funMap_quotient_mk'_sigma_mk'` / 定理 `funMap_quotient_mk'_sigma_mk'`

English:
theorem funMap_quotient_mk'_sigma_mk'
  given: {n : Nat} {F : L.Functions n} {i : ι} {x : Fin n -> G i}
  proof: by
  simp only [funMap_quotient_mk', Quotient.eq]
  obtain ⟨k, ik, jk⟩ :=
    directed_of (· <= ·) i (Classical.choose (Finite.bddAbove_range fun _ : Fin n => i))
  refine ⟨k, jk, ik, ?_⟩
  simp only [Embedding.map_fun, comp_unify]
  rfl

@[simp]

中文:
定理 funMap_quotient_mk'_sigma_mk'
  条件: {n : 自然数} {F : L.Functions n} {i : ι} {x : Fin n -> G i}
  证明: by
  simp only [funMap_quotient_mk', Quotient.eq]
  obtain ⟨k, ik, jk⟩ :=
    directed_of (· <= ·) i (Classical.choose (Finite.bddAbove_range fun _ : Fin n => i))
  refine ⟨k, jk, ik, ?_⟩
  simp only [Embedding.map_fun, comp_unify]
  rfl

@[simp]

Depends on / 依赖: Classical, Classical.choose, Embedding, Embedding.map_fun, Finite, Finite.bddAbove_range, Quotient, Quotient.eq, bddAbove_range, comp_unify, directed_of, funMap_quotient_mk, map_fun
-/
theorem funMap_quotient_mk'_sigma_mk' {n : Nat} {F : L.Functions n} {i : ι} {x : Fin n -> G i} :
    funMap F (fun a => (⟦.mk f i (x a)⟧ : DirectLimit G f)) = ⟦.mk f i (funMap F x)⟧ := by
  simp only [funMap_quotient_mk', Quotient.eq]
  obtain ⟨k, ik, jk⟩ :=
    directed_of (· <= ·) i (Classical.choose (Finite.bddAbove_range fun _ : Fin n => i))
  refine ⟨k, jk, ik, ?_⟩
  simp only [Embedding.map_fun, comp_unify]
  rfl

@[simp]
/--
theorem `relMap_quotient_mk'_sigma_mk'` / 定理 `relMap_quotient_mk'_sigma_mk'`

English:
theorem relMap_quotient_mk'_sigma_mk'
  given: {n : Nat} {R : L.Relations n} {i : ι} {x : Fin n -> G i}
  proof: by
  rw [relMap_quotient_mk']
  rw [relMap_equiv_unify G f R (fun a => .mk f i (x a)) i (fun _ ⟨_]; rw [hj⟩ => le_of_eq hj.symm)]
  rw [unify_sigma_mk_self]

中文:
定理 relMap_quotient_mk'_sigma_mk'
  条件: {n : 自然数} {R : L.Relations n} {i : ι} {x : Fin n -> G i}
  证明: by
  rw [relMap_quotient_mk']
  rw [relMap_equiv_unify G f R (fun a => .mk f i (x a)) i (fun _ ⟨_]; rw [hj⟩ => le_of_eq hj.symm)]
  rw [unify_sigma_mk_self]

Depends on / 依赖: hj.symm, le_of_eq, relMap_equiv_unify, relMap_quotient_mk, unify_sigma_mk_self
-/
theorem relMap_quotient_mk'_sigma_mk' {n : Nat} {R : L.Relations n} {i : ι} {x : Fin n -> G i} :
    RelMap R (fun a => (⟦.mk f i (x a)⟧ : DirectLimit G f)) = RelMap R x := by
  rw [relMap_quotient_mk']
  rw [relMap_equiv_unify G f R (fun a => .mk f i (x a)) i (fun _ ⟨_]; rw [hj⟩ => le_of_eq hj.symm)]
  rw [unify_sigma_mk_self]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_quotient_mk'_sigma_mk'_eq` / 定理 `exists_quotient_mk'_sigma_mk'_eq`

English:
theorem exists_quotient_mk'_sigma_mk'_eq
  given: {α : Type*} [Finite α] (x : α -> DirectLimit G f)
  proof: by
  obtain ⟨i, hi⟩ := Finite.bddAbove_range fun a => (x a).out.1
  refine ⟨i, unify f (Quotient.out ∘ x) i hi, ?_⟩
  ext a
  rw [Quotient.eq_mk_iff_out]; rw [unify]
  generalize_proofs r
  change _ ≈ Structure.Sigma.mk f i (f (Quotient.out (x a)).fst i r (Quotient.out (x a)).snd)
  have : (.mk f i 

中文:
定理 exists_quotient_mk'_sigma_mk'_eq
  条件: {α : 类型} [Finite α] (x : α -> DirectLimit G f)
  证明: by
  obtain ⟨i, hi⟩ := Finite.bddAbove_range fun a => (x a).out.1
  refine ⟨i, unify f (Quotient.out ∘ x) i hi, ?_⟩
  ext a
  rw [Quotient.eq_mk_iff_out]; rw [unify]
  generalize_proofs r
  change _ ≈ Structure.Sigma.mk f i (f (Quotient.out (x a)).fst i r (Quotient.out (x a)).snd)
  have : (.mk f i 

Depends on / 依赖: DirectedSystem, DirectedSystem.map_self, Finite, Finite.bddAbove_range, Quotient, Quotient.eq_mk_iff_out, Quotient.out, Structure, Structure.Sigma.mk, bddAbove_range, eq_mk_iff_out, equiv_iff, generalize_proofs, le_rfl, map_self
-/
theorem exists_quotient_mk'_sigma_mk'_eq {α : Type*} [Finite α] (x : α -> DirectLimit G f) :
    exists (i : ι) (y : α -> G i), x = fun a => ⟦.mk f i (y a)⟧ := by
  obtain ⟨i, hi⟩ := Finite.bddAbove_range fun a => (x a).out.1
  refine ⟨i, unify f (Quotient.out ∘ x) i hi, ?_⟩
  ext a
  rw [Quotient.eq_mk_iff_out]; rw [unify]
  generalize_proofs r
  change _ ≈ Structure.Sigma.mk f i (f (Quotient.out (x a)).fst i r (Quotient.out (x a)).snd)
  have : (.mk f i (f (Quotient.out (x a)).fst i r (Quotient.out (x a)).snd) : Σˣ f).fst <= i :=
    le_rfl
  rw [equiv_iff G f (i := i) (hi _) this]
  · simp only [DirectedSystem.map_self]
  exact ⟨a, rfl⟩

variable (L ι)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (i : ι)
  body: fun a => ⟦.mk f i a⟧
  inj' x y h := by
    rw [Quotient.eq] at h
    obtain ⟨j, h1, _, h3⟩ := h
    exact (f i j h1).injective h3
  map_fun' F x := by
    rw [← funMap_quotient_mk'_sigma_mk']
    rfl
  map_rel' := by
    intro n R x
    change RelMap R (fun a => (⟦.mk f i (x a)⟧ : DirectLimit G f))

中文:
定义 of
  签名: (i : ι)
  定义体: fun a => ⟦.mk f i a⟧
  inj' x y h := by
    rw [Quotient.eq] at h
    obtain ⟨j, h1, _, h3⟩ := h
    exact (f i j h1).injective h3
  map_fun' F x := by
    rw [← funMap_quotient_mk'_sigma_mk']
    rfl
  map_rel' := by
    intro n R x
    change RelMap R (fun a => (⟦.mk f i (x a)⟧ : DirectLimit G f))
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
/--
theorem `of_apply` / 定理 `of_apply`

English:
theorem of_apply
  given: {i : ι} {x : G i}
  statement: of L ι G f i x = ⟦.mk f i x⟧
  proof: rfl

中文:
定理 of_apply
  条件: {i : ι} {x : G i}
  结论: of L ι G f i x = ⟦.mk f i x⟧
  证明: rfl
-/
theorem of_apply {i : ι} {x : G i} : of L ι G f i x = ⟦.mk f i x⟧ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
-- This is not a simp-lemma because it is not in simp-normal form,
-- but the simp-normal version of this theorem would not be useful.
/--
theorem `of_f` / 定理 `of_f`

English:
theorem of_f
  given: {i j : ι} {hij : i <= j} {x : G i}
  statement: of L ι G f j (f i j hij x) = of L ι G f i x
  proof: by
  rw [of_apply]; rw [of_apply]; rw [Quotient.eq]
  refine Setoid.symm ⟨j, hij, refl j, ?_⟩
  simp only [DirectedSystem.map_self]

中文:
定理 of_f
  条件: {i j : ι} {hij : i <= j} {x : G i}
  结论: of L ι G f j (f i j hij x) = of L ι G f i x
  证明: by
  rw [of_apply]; rw [of_apply]; rw [Quotient.eq]
  refine Setoid.symm ⟨j, hij, refl j, ?_⟩
  simp only [DirectedSystem.map_self]

Depends on / 依赖: DirectedSystem, DirectedSystem.map_self, Quotient, Quotient.eq, Setoid, Setoid.symm, map_self, of_apply
-/
theorem of_f {i j : ι} {hij : i <= j} {x : G i} : of L ι G f j (f i j hij x) = of L ι G f i x := by
  rw [of_apply]; rw [of_apply]; rw [Quotient.eq]
  refine Setoid.symm ⟨j, hij, refl j, ?_⟩
  simp only [DirectedSystem.map_self]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `exists_of` / 定理 `exists_of`

English:
theorem exists_of
  given: (z : DirectLimit G f)
  statement: exists i x, of L ι G f i x = z
  proof: ⟨z.out.1, z.out.2, by simp⟩

@[elab_as_elim]

中文:
定理 exists_of
  条件: (z : DirectLimit G f)
  结论: 存在 i x, of L ι G f i x = z
  证明: ⟨z.out.1, z.out.2, by simp⟩

@[elab_as_elim]

Depends on / 依赖: z.out
-/
theorem exists_of (z : DirectLimit G f) : exists i x, of L ι G f i x = z :=
  ⟨z.out.1, z.out.2, by simp⟩

@[elab_as_elim]
/--
theorem `inductionOn` / 定理 `inductionOn`

English:
theorem inductionOn
  statement: {C : DirectLimit G f -> Prop} (z : DirectLimit G f)
  proof: let ⟨i, x, h⟩ := exists_of z
  h ▸ ih i x

中文:
定理 inductionOn
  结论: {C : DirectLimit G f -> 命题} (z : DirectLimit G f)
  证明: let ⟨i, x, h⟩ := exists_of z
  h ▸ ih i x
-/
protected theorem inductionOn {C : DirectLimit G f -> Prop} (z : DirectLimit G f)
    (ih : forall i x, C (of L ι G f i x)) : C z :=
  let ⟨i, x, h⟩ := exists_of z
  h ▸ ih i x

/--
theorem `iSup_range_of_eq_top` / 定理 `iSup_range_of_eq_top`

English:
theorem iSup_range_of_eq_top
  statement: ⨆ i, (of L ι G f i).toHom.range = ⊤
  proof: eq_top_iff.2 (fun x _ => DirectLimit.inductionOn x
    (fun i _ => le_iSup (fun i => Hom.range (Embedding.toHom (of L ι G f i))) i (mem_range_self _)))

中文:
定理 iSup_range_of_eq_top
  结论: ⨆ i, (of L ι G f i).toHom.range = ⊤
  证明: eq_top_iff.2 (fun x _ => DirectLimit.inductionOn x
    (fun i _ => le_iSup (fun i => Hom.range (Embedding.toHom (of L ι G f i))) i (mem_range_self _)))

Depends on / 依赖: DirectLimit, DirectLimit.inductionOn, Embedding, Embedding.toHom, Hom.range, eq_top_iff, inductionOn, le_iSup, mem_range_self
-/
theorem iSup_range_of_eq_top : ⨆ i, (of L ι G f i).toHom.range = ⊤ :=
  eq_top_iff.2 (fun x _ => DirectLimit.inductionOn x
    (fun i _ => le_iSup (fun i => Hom.range (Embedding.toHom (of L ι G f i))) i (mem_range_self _)))

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `exists_fg_substructure_in_Sigma` / 定理 `exists_fg_substructure_in_Sigma`

English:
theorem exists_fg_substructure_in_Sigma
  given: (S : L.Substructure (DirectLimit G f)) (S_fg : S.FG)
  proof: by
  let ⟨A, A_closure⟩ := S_fg
  let ⟨i, y, eq_y⟩ := exists_quotient_mk'_sigma_mk'_eq G _ (fun a : A => a.1)
  use i
  use Substructure.closure L (range y)
  rw [Substructure.map_closure]
  simp only [Embedding.coe_toHom, of_apply]
  rw [← image_univ]; rw [image_image]; rw [image_univ]; rw [← eq_y]

中文:
定理 exists_fg_substructure_in_Sigma
  条件: (S : L.Substructure (DirectLimit G f)) (S_fg : S.FG)
  证明: by
  let ⟨A, A_closure⟩ := S_fg
  let ⟨i, y, eq_y⟩ := exists_quotient_mk'_sigma_mk'_eq G _ (fun a : A => a.1)
  use i
  use Substructure.closure L (range y)
  rw [Substructure.map_closure]
  simp only [Embedding.coe_toHom, of_apply]
  rw [← image_univ]; rw [image_image]; rw [image_univ]; rw [← eq_y]

Depends on / 依赖: A_closure, Embedding, Embedding.coe_toHom, Finset, Finset.setOfPred_mem, S_fg, Substructure, Substructure.closure, Substructure.map_closure, Subtype, Subtype.range_coe_subtype, _sigma_mk, closure, coe_toHom, eq_y, exists_quotient_mk, image_image, image_univ, map_closure, of_apply
-/
theorem exists_fg_substructure_in_Sigma (S : L.Substructure (DirectLimit G f)) (S_fg : S.FG) :
    exists i, exists T : L.Substructure (G i), T.map (of L ι G f i).toHom = S := by
  let ⟨A, A_closure⟩ := S_fg
  let ⟨i, y, eq_y⟩ := exists_quotient_mk'_sigma_mk'_eq G _ (fun a : A => a.1)
  use i
  use Substructure.closure L (range y)
  rw [Substructure.map_closure]
  simp only [Embedding.coe_toHom, of_apply]
  rw [← image_univ]; rw [image_image]; rw [image_univ]; rw [← eq_y]; rw [Subtype.range_coe_subtype]; rw [Finset.setOfPred_mem]; rw [A_closure]

variable {P : Type u₁} [L.Structure P]

set_option backward.isDefEq.respectTransparency false in
variable (L ι G f) in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (g : forall i, G i ↪[L] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)
  body: Quotient.lift (fun x : Σˣ f => (g x.1) x.2) fun x y xy => by
      obtain ⟨i, hx, hy⟩ := directed_of (· <= ·) x.1 y.1
      rw [← Hg x.1 i hx]; rw [← Hg y.1 i hy]
      exact congr_arg _ ((equiv_iff ..).1 xy)
  inj' x y xy := by
    rw [← Quotient.out_eq x]; rw [← Quotient.out_eq y]; rw [Quotient.li

中文:
定义 lift
  签名: (g : 对任意 i, G i ↪[L] P) (Hg : 对任意 i j hij x, g j (f i j hij x) = g i x)
  定义体: Quotient.lift (fun x : Σˣ f => (g x.1) x.2) fun x y xy => by
      obtain ⟨i, hx, hy⟩ := directed_of (· <= ·) x.1 y.1
      rw [← Hg x.1 i hx]; rw [← Hg y.1 i hy]
      exact congr_arg _ ((equiv_iff ..).1 xy)
  inj' x y xy := by
    rw [← Quotient.out_eq x]; rw [← Quotient.out_eq y]; rw [Quotient.li

Depends on / 依赖: Quotient, Quotient.eq_iff_equi, Quotient.lift, Quotient.lift_mk, Quotient.out_eq, congr_arg, directed_of, eq_iff_equi, equiv_iff, lift_mk, out_eq, x.out, y.out
-/
noncomputable def lift (g : forall i, G i ↪[L] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f ↪[L] P where
  toFun :=
    Quotient.lift (fun x : Σˣ f => (g x.1) x.2) fun x y xy => by
      obtain ⟨i, hx, hy⟩ := directed_of (· <= ·) x.1 y.1
      rw [← Hg x.1 i hx]; rw [← Hg y.1 i hy]
      exact congr_arg _ ((equiv_iff ..).1 xy)
  inj' x y xy := by
    rw [← Quotient.out_eq x]; rw [← Quotient.out_eq y]; rw [Quotient.lift_mk]; rw [Quotient.lift_mk] at xy
    obtain ⟨i, hx, hy⟩ := directed_of (· <= ·) x.out.1 y.out.1
    rw [← Hg x.out.1 i hx]; rw [← Hg y.out.1 i hy] at xy
    rw [← Quotient.out_eq x]; rw [← Quotient.out_eq y]; rw [Quotient.eq_iff_equiv]; rw [equiv_iff G f hx hy]
    exact (g i).injective xy
  map_fun' F x := by
    obtain ⟨i, y, rfl⟩ := exists_quotient_mk'_sigma_mk'_eq G f x
    change _ = funMap F (Quotient.lift _ _ ∘ Quotient.mk _ ∘ Structure.Sigma.mk f i ∘ y)
    rw [funMap_quotient_mk'_sigma_mk']; rw [← Function.comp_assoc]; rw [Quotient.lift_comp_mk]
    simp only [Quotient.lift_mk, Embedding.map_fun]
    rfl
  map_rel' R x := by
    obtain ⟨i, y, rfl⟩ := exists_quotient_mk'_sigma_mk'_eq G f x
    change RelMap R (Quotient.lift _ _ ∘ Quotient.mk _ ∘ Structure.Sigma.mk f i ∘ y) ↔ _
    rw [relMap_quotient_mk'_sigma_mk' G f]; rw [← (g i).map_rel R y]; rw [← Function.comp_assoc]; rw [Quotient.lift_comp_mk]
    rfl

variable (g : forall i, G i ↪[L] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)

@[simp]
/--
theorem `lift_quotient_mk'_sigma_mk'` / 定理 `lift_quotient_mk'_sigma_mk'`

English:
theorem lift_quotient_mk'_sigma_mk'
  given: {i} (x : G i)
  statement: lift L ι G f g Hg ⟦.mk f i x⟧ = (g i) x
  proof: by
  change (lift L ι G f g Hg).toFun ⟦.mk f i x⟧ = _
  simp only [lift, Quotient.lift_mk]

中文:
定理 lift_quotient_mk'_sigma_mk'
  条件: {i} (x : G i)
  结论: lift L ι G f g Hg ⟦.mk f i x⟧ = (g i) x
  证明: by
  change (lift L ι G f g Hg).toFun ⟦.mk f i x⟧ = _
  simp only [lift, Quotient.lift_mk]

Depends on / 依赖: Quotient, Quotient.lift_mk, lift_mk
-/
theorem lift_quotient_mk'_sigma_mk' {i} (x : G i) : lift L ι G f g Hg ⟦.mk f i x⟧ = (g i) x := by
  change (lift L ι G f g Hg).toFun ⟦.mk f i x⟧ = _
  simp only [lift, Quotient.lift_mk]

/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: {i} (x : G i)
  statement: lift L ι G f g Hg (of L ι G f i x) = g i x
  proof: by simp

中文:
定理 lift_of
  条件: {i} (x : G i)
  结论: lift L ι G f g Hg (of L ι G f i x) = g i x
  证明: by simp
-/
theorem lift_of {i} (x : G i) : lift L ι G f g Hg (of L ι G f i x) = g i x := by simp

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (F : DirectLimit G f ↪[L] P) (x)
  proof: DirectLimit.inductionOn x fun i x => by rw [lift_of]; rfl

中文:
定理 lift_unique
  条件: (F : DirectLimit G f ↪[L] P) (x)
  证明: DirectLimit.inductionOn x fun i x => by rw [lift_of]; rfl

Depends on / 依赖: DirectLimit, DirectLimit.inductionOn, inductionOn, lift_of
-/
theorem lift_unique (F : DirectLimit G f ↪[L] P) (x) :
    F x =
      lift L ι G f (fun i => F.comp <| of L ι G f i)
        (fun i j hij x => by rw [F.comp_apply, F.comp_apply, of_f]) x :=
  DirectLimit.inductionOn x fun i x => by rw [lift_of]; rfl

/--
lemma `range_lift` / 引理 `range_lift`

English:
lemma range_lift
  statement: (lift L ι G f g Hg).toHom.range = ⨆ i, (g i).toHom.range
  proof: by
  simp_rw [Hom.range_eq_map]
  rw [← iSup_range_of_eq_top]; rw [Substructure.map_iSup]
  simp_rw [Hom.range_eq_map, Substructure.map_map]
  rfl

中文:
引理 range_lift
  结论: (lift L ι G f g Hg).toHom.range = ⨆ i, (g i).toHom.range
  证明: by
  simp_rw [Hom.range_eq_map]
  rw [← iSup_range_of_eq_top]; rw [Substructure.map_iSup]
  simp_rw [Hom.range_eq_map, Substructure.map_map]
  rfl

Depends on / 依赖: Hom.range_eq_map, Substructure, Substructure.map_iSup, Substructure.map_map, iSup_range_of_eq_top, map_iSup, map_map, range_eq_map, simp_rw
-/
lemma range_lift : (lift L ι G f g Hg).toHom.range = ⨆ i, (g i).toHom.range := by
  simp_rw [Hom.range_eq_map]
  rw [← iSup_range_of_eq_top]; rw [Substructure.map_iSup]
  simp_rw [Hom.range_eq_map, Substructure.map_map]
  rfl

variable (L ι G f)
variable (G' : ι -> Type w') [forall i, L.Structure (G' i)]
variable (f' : forall i j, i <= j -> G' i ↪[L] G' j)
variable (g : forall i, G i ≃[L] G' i)
variable [DirectedSystem G' fun i j h => f' i j h]

/--
Definition of `equiv_lift` / `equiv_lift` 的定义

English:
definition equiv_lift
  signature: (H_commuting : forall i j hij x, g j (f i j hij x) = f' i j hij (g i x))
  body: by
  let U i : G i ↪[L] DirectLimit G' f' := (of L _ G' f' i).comp (g i).toEmbedding
let F : DirectLimit G f ↪[L] DirectLimit G' f' := lift L _ G f U by
    intro _ _ _ _
    simp only [U, Embedding.comp_apply, Equiv.coe_toEmbedding, H_commuting, of_f]
  have surj_f : Function.Surjective F := by
   

中文:
定义 equiv_lift
  签名: (H_commuting : 对任意 i j hij x, g j (f i j hij x) = f' i j hij (g i x))
  定义体: by
  let U i : G i ↪[L] DirectLimit G' f' := (of L _ G' f' i).comp (g i).toEmbedding
let F : DirectLimit G f ↪[L] DirectLimit G' f' := lift L _ G f U by
    intro _ _ _ _
    simp only [U, Embedding.comp_apply, Equiv.coe_toEmbedding, H_commuting, of_f]
  have surj_f : Function.Surjective F := by
   

Depends on / 依赖: DirectLimit, Embedding, Embedding.comp_apply, Equiv.apply_symm_apply, Equiv.coe_toEmbedding, Equiv.ofBijective, F.injective, Function, Function.Surjective, H_commuting, Surjective, apply_symm_apply, coe_toEmbedding, comp_apply, injective, lift_of, ofBijective, of_f, pre_x, surj_f
-/
noncomputable def equiv_lift (H_commuting : forall i j hij x, g j (f i j hij x) = f' i j hij (g i x)) :
    DirectLimit G f ≃[L] DirectLimit G' f' := by
  let U i : G i ↪[L] DirectLimit G' f' := (of L _ G' f' i).comp (g i).toEmbedding
let F : DirectLimit G f ↪[L] DirectLimit G' f' := lift L _ G f U by
    intro _ _ _ _
    simp only [U, Embedding.comp_apply, Equiv.coe_toEmbedding, H_commuting, of_f]
  have surj_f : Function.Surjective F := by
    intro x
    rcases x with ⟨i, pre_x⟩
    use of L _ G f i ((g i).symm pre_x)
    simp only [F, U, lift_of, Embedding.comp_apply, Equiv.coe_toEmbedding, Equiv.apply_symm_apply]
    rfl
  exact ⟨Equiv.ofBijective F ⟨F.injective, surj_f⟩, F.map_fun', F.map_rel'⟩

variable (H_commuting : forall i j hij x, g j (f i j hij x) = f' i j hij (g i x))

/--
theorem `equiv_lift_of` / 定理 `equiv_lift_of`

English:
theorem equiv_lift_of
  given: {i : ι} (x : G i)
  proof: rfl

中文:
定理 equiv_lift_of
  条件: {i : ι} (x : G i)
  证明: rfl
-/
theorem equiv_lift_of {i : ι} (x : G i) :
    equiv_lift L ι G f G' f' g H_commuting (of L ι G f i x) = of L ι G' f' i (g i x) := rfl

variable {L ι G f}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `cg` / 定理 `cg`

English:
theorem cg
  statement: {ι : Type*} [Countable ι] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  proof: by
  refine ⟨⟨⋃ i, DirectLimit.of L ι G f i '' Classical.choose (h i).out, ?_, ?_⟩⟩
  · exact Set.countable_iUnion fun i => Set.Countable.image (Classical.choose_spec (h i).out).1 _
  · rw [eq_top_iff, Substructure.closure_iUnion]
    simp_rw [← Embedding.coe_toHom, Substructure.closure_image]
    r

中文:
定理 cg
  结论: {ι : 类型} [Countable ι] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  证明: by
  refine ⟨⟨⋃ i, DirectLimit.of L ι G f i '' Classical.choose (h i).out, ?_, ?_⟩⟩
  · exact Set.countable_iUnion fun i => Set.Countable.image (Classical.choose_spec (h i).out).1 _
  · rw [eq_top_iff, Substructure.closure_iUnion]
    simp_rw [← Embedding.coe_toHom, Substructure.closure_image]
    r

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, Countable, DirectLimit, DirectLimit.of, DirectLimit.setoid, Embedding, Embedding.co, Embedding.coe_toHom, Quotient, Quotient.out, Set.Countable.image, Set.countable_iUnion, Substructure, Substructure.closure_iUnion, Substructure.closure_image, choose_spec, closure_iUnion, closure_image
-/
theorem cg {ι : Type*} [Countable ι] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {G : ι -> Type w} [forall i, L.Structure (G i)] (f : forall i j, i <= j -> G i ↪[L] G j)
    (h : forall i, Structure.CG L (G i)) [DirectedSystem G fun i j h => f i j h] :
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

/--
Instance `cg'` / 实例 `cg'`

English:
instance cg'
  signature: {ι : Type*} [Countable ι] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  body: cg f h

中文:
实例 cg'
  签名: {ι : 类型} [Countable ι] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  定义体: cg f h
-/
instance cg' {ι : Type*} [Countable ι] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {G : ι -> Type w} [forall i, L.Structure (G i)] (f : forall i j, i <= j -> G i ↪[L] G j)
    [h : forall i, Structure.CG L (G i)] [DirectedSystem G fun i j h => f i j h] :
    Structure.CG L (DirectLimit G f) :=
  cg f h

end DirectLimit

section Substructure

variable [Nonempty ι] [IsDirectedOrder ι]
variable {M : Type*} [L.Structure M] (S : ι ->o L.Substructure M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DirectedSystem (fun i => S i) (fun _ _ h => Substructure.inclusion (S.monotone h))
  body: rfl
  map_map _ _ _ _ _ _ := rfl

中文:
实例 :
  签名: DirectedSystem (fun i => S i) (fun _ _ h => Substructure.inclusion (S.monotone h))
  定义体: rfl
  map_map _ _ _ _ _ _ := rfl
-/
instance : DirectedSystem (fun i => S i) (fun _ _ h => Substructure.inclusion (S.monotone h)) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

namespace DirectLimit

/--
Definition of `liftInclusion` / `liftInclusion` 的定义

English:
definition liftInclusion
  signature: :
  body: DirectLimit.lift L ι (fun i => S i) (fun _ _ h => Substructure.inclusion (S.monotone h))
    (fun _ => Substructure.subtype _) (fun _ _ _ _ => rfl)

中文:
定义 liftInclusion
  签名: :
  定义体: DirectLimit.lift L ι (fun i => S i) (fun _ _ h => Substructure.inclusion (S.monotone h))
    (fun _ => Substructure.subtype _) (fun _ _ _ _ => rfl)

Depends on / 依赖: DirectLimit, DirectLimit.lift, S.monotone, Substructure, Substructure.inclusion, Substructure.subtype, inclusion, monotone, subtype
-/
noncomputable def liftInclusion :
    DirectLimit (fun i => S i) (fun _ _ h => Substructure.inclusion (S.monotone h)) ↪[L] M :=
  DirectLimit.lift L ι (fun i => S i) (fun _ _ h => Substructure.inclusion (S.monotone h))
    (fun _ => Substructure.subtype _) (fun _ _ _ _ => rfl)

/--
theorem `liftInclusion_of` / 定理 `liftInclusion_of`

English:
theorem liftInclusion_of
  given: {i : ι} (x : S i)
  proof: rfl

中文:
定理 liftInclusion_of
  条件: {i : ι} (x : S i)
  证明: rfl
-/
theorem liftInclusion_of {i : ι} (x : S i) :
    (liftInclusion S) (of L ι _ (fun _ _ h => Substructure.inclusion (S.monotone h)) i x)
    = Substructure.subtype (S i) x := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `rangeLiftInclusion` / 引理 `rangeLiftInclusion`

English:
lemma rangeLiftInclusion
  statement: (liftInclusion S).toHom.range = ⨆ i, S i
  proof: by
  simp_rw [liftInclusion, range_lift, Substructure.range_subtype]

中文:
引理 rangeLiftInclusion
  结论: (liftInclusion S).toHom.range = ⨆ i, S i
  证明: by
  simp_rw [liftInclusion, range_lift, Substructure.range_subtype]

Depends on / 依赖: Substructure, Substructure.range_subtype, liftInclusion, range_lift, range_subtype, simp_rw
-/
lemma rangeLiftInclusion : (liftInclusion S).toHom.range = ⨆ i, S i := by
  simp_rw [liftInclusion, range_lift, Substructure.range_subtype]

/--
Definition of `Equiv_iSup` / `Equiv_iSup` 的定义

English:
definition Equiv_iSup
  signature: :
  body: by
  have liftInclusion_in_sup : forall x, liftInclusion S x in (⨆ i, S i) := by
    simp only [← rangeLiftInclusion, Hom.mem_range, Embedding.coe_toHom]
    intro x; use x
  let F := Embedding.codRestrict (⨆ i, S i) _ liftInclusion_in_sup
  have F_surj : Function.Surjective F := by
    rintro ⟨m, h

中文:
定义 Equiv_iSup
  签名: :
  定义体: by
  have liftInclusion_in_sup : forall x, liftInclusion S x in (⨆ i, S i) := by
    simp only [← rangeLiftInclusion, Hom.mem_range, Embedding.coe_toHom]
    intro x; use x
  let F := Embedding.codRestrict (⨆ i, S i) _ liftInclusion_in_sup
  have F_surj : Function.Surjective F := by
    rintro ⟨m, h

Depends on / 依赖: Embedding, Embedding.codRestrict, Embedding.codRestrict_apply, Embedding.coe_toHom, Equiv.ofBijective, F.injective, F.map_fun, F.map_rel, F_surj, Function, Function.Surjective, Hom.mem_range, Subtype, Subtype.mk.injEq, Surjective, codRestrict, codRestrict_apply, coe_toHom, injective, liftInclusion
-/
noncomputable def Equiv_iSup :
    DirectLimit (fun i => S i) (fun _ _ h => Substructure.inclusion (S.monotone h)) ≃[L]
    (iSup S : L.Substructure M) := by
  have liftInclusion_in_sup : forall x, liftInclusion S x in (⨆ i, S i) := by
    simp only [← rangeLiftInclusion, Hom.mem_range, Embedding.coe_toHom]
    intro x; use x
  let F := Embedding.codRestrict (⨆ i, S i) _ liftInclusion_in_sup
  have F_surj : Function.Surjective F := by
    rintro ⟨m, hm⟩
    rw [← rangeLiftInclusion]; rw [Hom.mem_range] at hm
    rcases hm with ⟨a, _⟩; use a
    simpa only [F, Embedding.codRestrict_apply', Subtype.mk.injEq]
  exact ⟨Equiv.ofBijective F ⟨F.injective, F_surj⟩, F.map_fun', F.map_rel'⟩

/--
theorem `Equiv_isup_of_apply` / 定理 `Equiv_isup_of_apply`

English:
theorem Equiv_isup_of_apply
  given: {i : ι} (x : S i)
  proof: rfl

中文:
定理 Equiv_isup_of_apply
  条件: {i : ι} (x : S i)
  证明: rfl
-/
theorem Equiv_isup_of_apply {i : ι} (x : S i) :
    Equiv_iSup S (of L ι _ (fun _ _ h => Substructure.inclusion (S.monotone h)) i x)
    = Substructure.inclusion (le_iSup _ _) x := rfl

/--
theorem `Equiv_isup_symm_inclusion_apply` / 定理 `Equiv_isup_symm_inclusion_apply`

English:
theorem Equiv_isup_symm_inclusion_apply
  given: {i : ι} (x : S i)
  proof: by
  apply (Equiv_iSup S).injective
  simp only [Equiv.apply_symm_apply]
  rfl

@[simp]

中文:
定理 Equiv_isup_symm_inclusion_apply
  条件: {i : ι} (x : S i)
  证明: by
  apply (Equiv_iSup S).injective
  simp only [Equiv.apply_symm_apply]
  rfl

@[simp]

Depends on / 依赖: Equiv.apply_symm_apply, Equiv_iSup, apply_symm_apply, injective
-/
theorem Equiv_isup_symm_inclusion_apply {i : ι} (x : S i) :
    (Equiv_iSup S).symm (Substructure.inclusion (le_iSup _ _) x)
    = of L ι _ (fun _ _ h => Substructure.inclusion (S.monotone h)) i x := by
  apply (Equiv_iSup S).injective
  simp only [Equiv.apply_symm_apply]
  rfl

@[simp]
/--
theorem `Equiv_isup_symm_inclusion` / 定理 `Equiv_isup_symm_inclusion`

English:
theorem Equiv_isup_symm_inclusion
  given: (i : ι)
  proof: by
  ext x; exact Equiv_isup_symm_inclusion_apply _ x

中文:
定理 Equiv_isup_symm_inclusion
  条件: (i : ι)
  证明: by
  ext x; exact Equiv_isup_symm_inclusion_apply _ x

Depends on / 依赖: Equiv_isup_symm_inclusion_apply
-/
theorem Equiv_isup_symm_inclusion (i : ι) :
    (Equiv_iSup S).symm.toEmbedding.comp (Substructure.inclusion (le_iSup _ _))
    = of L ι _ (fun _ _ h => Substructure.inclusion (S.monotone h)) i := by
  ext x; exact Equiv_isup_symm_inclusion_apply _ x

end DirectLimit

end Substructure

end Language

end FirstOrder
