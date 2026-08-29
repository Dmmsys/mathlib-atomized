/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Fintype.Quotient
public import Mathlib.ModelTheory.Semantics

/-!
# Quotients of First-Order Structures

This file defines prestructures and quotients of first-order structures.

## Main Definitions

- If `s` is a setoid (equivalence relation) on `M`, a `FirstOrder.Language.Prestructure s` is the
  data for a first-order structure on `M` that will still be a structure when modded out by `s`.
- The structure `FirstOrder.Language.quotientStructure s` is the resulting structure on
  `Quotient s`.
-/

public section


namespace FirstOrder

namespace Language

variable (L : Language) {M : Type*}

open FirstOrder

open Structure

/--
Definition of `Prestructure` / `Prestructure` 的定义

English:
class Prestructure
  parameters: (s : Setoid M)
  axioms and operations (3):
    - toStructure : L.Structure M
    - fun_equiv : forall {n} {f : L.Functions n} (x y : Fin n -> M), x ≈ y -> funMap f x ≈ funMap f y
    - rel_equiv : forall {n} {r : L.Relations n} (x y : Fin n -> M) (_ : x ≈ y), RelMap r x = RelMap r y

中文:
类 Prestructure
  参数: (s : 集合等价关系 M)
  公理与运算 (3 个):
    - toStructure : L.结构 M
    - fun_equiv : 对任意 {n} {f : L.函数 n} (x y : 有限集 n -> M), x ≈ y -> funMap f x ≈ funMap f y
    - rel_equiv : 对任意 {n} {r : L.关系 n} (x y : 有限集 n -> M) (_ : x ≈ y), RelMap r x = RelMap r y
-/
class Prestructure (s : Setoid M) where
  /-- The underlying first-order structure -/
  toStructure : L.Structure M
  fun_equiv : forall {n} {f : L.Functions n} (x y : Fin n -> M), x ≈ y -> funMap f x ≈ funMap f y
  rel_equiv : forall {n} {r : L.Relations n} (x y : Fin n -> M) (_ : x ≈ y), RelMap r x = RelMap r y

variable {L} {s : Setoid M}
variable [ps : L.Prestructure s]

/--
Instance `quotientStructure` / 实例 `quotientStructure`

English:
instance quotientStructure
  signature: : L.Structure (Quotient s) where
  body: Quotient.map (@funMap L M ps.toStructure n f) Prestructure.fun_equiv (Quotient.finChoice x)
  RelMap {n} r x :=
    Quotient.lift (@RelMap L M ps.toStructure n r) Prestructure.rel_equiv (Quotient.finChoice x)

中文:
实例 quotientStructure
  签名: : L.结构 (商 s) where
  定义体: Quotient.map (@funMap L M ps.toStructure n f) Prestructure.fun_equiv (Quotient.finChoice x)
  RelMap {n} r x :=
    Quotient.lift (@RelMap L M ps.toStructure n r) Prestructure.rel_equiv (Quotient.finChoice x)

Depends on / 依赖: Prestructure, Prestructure.fun_equiv, Prestructure.rel_equiv, Quotient, Quotient.finChoice, Quotient.lift, Quotient.map, RelMap, finChoice, funMap, fun_equiv, ps.toStructure, rel_equiv, toStructure
-/
instance quotientStructure : L.Structure (Quotient s) where
  funMap {n} f x :=
    Quotient.map (@funMap L M ps.toStructure n f) Prestructure.fun_equiv (Quotient.finChoice x)
  RelMap {n} r x :=
    Quotient.lift (@RelMap L M ps.toStructure n r) Prestructure.rel_equiv (Quotient.finChoice x)

variable (s)

/--
theorem `funMap_quotient_mk'` / 定理 `funMap_quotient_mk'`

English:
theorem funMap_quotient_mk'
  given: {n : Nat} (f : L.Functions n) (x : Fin n -> M)
  proof: by
  change
    Quotient.map (@funMap L M ps.toStructure n f) Prestructure.fun_equiv (Quotient.finChoice _) =
      _
  rw [Quotient.finChoice_eq]; rw [Quotient.map_mk]

中文:
定理 funMap_quotient_mk'
  条件: {n : 自然数} (f : L.函数 n) (x : 有限集 n -> M)
  证明: by
  change
    Quotient.map (@funMap L M ps.toStructure n f) Prestructure.fun_equiv (Quotient.finChoice _) =
      _
  rw [Quotient.finChoice_eq]; rw [Quotient.map_mk]

Depends on / 依赖: Prestructure, Prestructure.fun_equiv, Quotient, Quotient.finChoice, Quotient.finChoice_eq, Quotient.map, Quotient.map_mk, finChoice, finChoice_eq, funMap, fun_equiv, map_mk, ps.toStructure, toStructure
-/
theorem funMap_quotient_mk' {n : Nat} (f : L.Functions n) (x : Fin n -> M) :
    (funMap f fun i => (⟦x i⟧ : Quotient s)) = ⟦@funMap _ _ ps.toStructure _ f x⟧ := by
  change
    Quotient.map (@funMap L M ps.toStructure n f) Prestructure.fun_equiv (Quotient.finChoice _) =
      _
  rw [Quotient.finChoice_eq]; rw [Quotient.map_mk]

/--
theorem `relMap_quotient_mk'` / 定理 `relMap_quotient_mk'`

English:
theorem relMap_quotient_mk'
  given: {n : Nat} (r : L.Relations n) (x : Fin n -> M)
  proof: by
  change
    Quotient.lift (@RelMap L M ps.toStructure n r) Prestructure.rel_equiv (Quotient.finChoice _) ↔
      _
  rw [Quotient.finChoice_eq]; rw [Quotient.lift_mk]

中文:
定理 relMap_quotient_mk'
  条件: {n : 自然数} (r : L.关系 n) (x : 有限集 n -> M)
  证明: by
  change
    Quotient.lift (@RelMap L M ps.toStructure n r) Prestructure.rel_equiv (Quotient.finChoice _) ↔
      _
  rw [Quotient.finChoice_eq]; rw [Quotient.lift_mk]

Depends on / 依赖: Prestructure, Prestructure.rel_equiv, Quotient, Quotient.finChoice, Quotient.finChoice_eq, Quotient.lift, Quotient.lift_mk, RelMap, finChoice, finChoice_eq, lift_mk, ps.toStructure, rel_equiv, toStructure
-/
theorem relMap_quotient_mk' {n : Nat} (r : L.Relations n) (x : Fin n -> M) :
    (RelMap r fun i => (⟦x i⟧ : Quotient s)) ↔ @RelMap _ _ ps.toStructure _ r x := by
  change
    Quotient.lift (@RelMap L M ps.toStructure n r) Prestructure.rel_equiv (Quotient.finChoice _) ↔
      _
  rw [Quotient.finChoice_eq]; rw [Quotient.lift_mk]

/--
theorem `Term.realize_quotient_mk'` / 定理 `Term.realize_quotient_mk'`

English:
theorem Term.realize_quotient_mk'
  given: {β : Type*} (t : L.Term β) (x : β -> M)
  proof: by
  induction t with
  | var => rfl
  | func _ _ ih => simp only [ih, funMap_quotient_mk', Term.realize]

中文:
定理 项.realize_quotient_mk'
  条件: {β : 类型} (t : L.项 β) (x : β -> M)
  证明: by
  induction t with
  | var => rfl
  | func _ _ ih => simp only [ih, funMap_quotient_mk', Term.realize]

Depends on / 依赖: Term.realize, funMap_quotient_mk, realize
-/
theorem Term.realize_quotient_mk' {β : Type*} (t : L.Term β) (x : β -> M) :
    (t.realize fun i => (⟦x i⟧ : Quotient s)) = ⟦@Term.realize _ _ ps.toStructure _ x t⟧ := by
  induction t with
  | var => rfl
  | func _ _ ih => simp only [ih, funMap_quotient_mk', Term.realize]

end Language

end FirstOrder
