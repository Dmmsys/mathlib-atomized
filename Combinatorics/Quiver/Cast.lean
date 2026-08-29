/-
Copyright (c) 2022 Antoine Labelle, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle, Rémi Bottinelli
-/
module

public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.Path

/-!

# Rewriting arrows and paths along vertex equalities

This file defines `Hom.cast` and `Path.cast` (and associated lemmas) in order to allow
rewriting arrows and paths along equalities of their endpoints.

-/

@[expose] public section


universe v v₁ v₂ u u₁ u₂

variable {U : Type*} [Quiver.{u} U]


namespace Quiver

/-!
### Rewriting arrows along equalities of vertices
-/


/--
Definition of `Hom.cast` / `Hom.cast` 的定义

English:
definition Hom.cast
  signature: {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v)
  body: Eq.ndrec (motive := (· ⟶ v')) (Eq.ndrec e hv) hu

中文:
定义 Hom.cast
  签名: {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v)
  定义体: Eq.ndrec (motive := (· ⟶ v')) (Eq.ndrec e hv) hu

Depends on / 依赖: Eq.ndrec, motive
-/
def Hom.cast {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) : u' ⟶ v' :=
  Eq.ndrec (motive := (· ⟶ v')) (Eq.ndrec e hv) hu

/--
theorem `Hom.cast_eq_cast` / 定理 `Hom.cast_eq_cast`

English:
theorem Hom.cast_eq_cast
  given: {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v)
  proof: by
  subst_vars
  rfl

@[simp]

中文:
定理 Hom.cast_eq_cast
  条件: {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v)
  证明: by
  subst_vars
  rfl

@[simp]
-/
theorem Hom.cast_eq_cast {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) :
    e.cast hu hv = _root_.cast (by {rw [hu, hv]}) e := by
  subst_vars
  rfl

@[simp]
/--
theorem `Hom.cast_rfl_rfl` / 定理 `Hom.cast_rfl_rfl`

English:
theorem Hom.cast_rfl_rfl
  given: {u v : U} (e : u ⟶ v)
  statement: e.cast rfl rfl = e
  proof: rfl

@[simp]

中文:
定理 Hom.cast_rfl_rfl
  条件: {u v : U} (e : u ⟶ v)
  结论: e.cast rfl rfl = e
  证明: rfl

@[simp]
-/
theorem Hom.cast_rfl_rfl {u v : U} (e : u ⟶ v) : e.cast rfl rfl = e :=
  rfl

@[simp]
/--
theorem `Hom.cast_cast` / 定理 `Hom.cast_cast`

English:
theorem Hom.cast_cast
  statement: {u v u' v' u'' v'' : U} (e : u ⟶ v) (hu : u = u') (hv : v = v')
  proof: by
  subst_vars
  rfl

中文:
定理 Hom.cast_cast
  结论: {u v u' v' u'' v'' : U} (e : u ⟶ v) (hu : u = u') (hv : v = v')
  证明: by
  subst_vars
  rfl
-/
theorem Hom.cast_cast {u v u' v' u'' v'' : U} (e : u ⟶ v) (hu : u = u') (hv : v = v')
    (hu' : u' = u'') (hv' : v' = v'') :
    (e.cast hu hv).cast hu' hv' = e.cast (hu.trans hu') (hv.trans hv') := by
  subst_vars
  rfl

/--
theorem `Hom.cast_heq` / 定理 `Hom.cast_heq`

English:
theorem Hom.cast_heq
  given: {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v)
  proof: by
  subst_vars
  rfl

中文:
定理 Hom.cast_heq
  条件: {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v)
  证明: by
  subst_vars
  rfl
-/
theorem Hom.cast_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) :
    e.cast hu hv ≍ e := by
  subst_vars
  rfl

/--
theorem `Hom.cast_eq_iff_heq` / 定理 `Hom.cast_eq_iff_heq`

English:
theorem Hom.cast_eq_iff_heq
  given: {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) (e' : u' ⟶ v')
  proof: by
  rw [Hom.cast_eq_cast]
  exact _root_.cast_eq_iff_heq

中文:
定理 Hom.cast_eq_iff_heq
  条件: {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) (e' : u' ⟶ v')
  证明: by
  rw [Hom.cast_eq_cast]
  exact _root_.cast_eq_iff_heq

Depends on / 依赖: Hom.cast_eq_cast, _root_, _root_.cast_eq_iff_heq, cast_eq_cast, cast_eq_iff_heq
-/
theorem Hom.cast_eq_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) (e' : u' ⟶ v') :
    e.cast hu hv = e' ↔ e ≍ e' := by
  rw [Hom.cast_eq_cast]
  exact _root_.cast_eq_iff_heq

/--
theorem `Hom.eq_cast_iff_heq` / 定理 `Hom.eq_cast_iff_heq`

English:
theorem Hom.eq_cast_iff_heq
  given: {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) (e' : u' ⟶ v')
  proof: by
  rw [eq_comm]; rw [Hom.cast_eq_iff_heq]
  exact ⟨HEq.symm, HEq.symm⟩

中文:
定理 Hom.eq_cast_iff_heq
  条件: {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) (e' : u' ⟶ v')
  证明: by
  rw [eq_comm]; rw [Hom.cast_eq_iff_heq]
  exact ⟨HEq.symm, HEq.symm⟩

Depends on / 依赖: HEq.symm, Hom.cast_eq_iff_heq, cast_eq_iff_heq, eq_comm
-/
theorem Hom.eq_cast_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) (e' : u' ⟶ v') :
    e' = e.cast hu hv ↔ e' ≍ e := by
  rw [eq_comm]; rw [Hom.cast_eq_iff_heq]
  exact ⟨HEq.symm, HEq.symm⟩

/-!
### Rewriting paths along equalities of vertices
-/


open Path

/--
Definition of `Path.cast` / `Path.cast` 的定义

English:
definition Path.cast
  signature: {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
  body: Eq.ndrec (motive := (Path · v')) (Eq.ndrec p hv) hu

中文:
定义 Path.cast
  签名: {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
  定义体: Eq.ndrec (motive := (Path · v')) (Eq.ndrec p hv) hu

Depends on / 依赖: Eq.ndrec, motive
-/
def Path.cast {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v) : Path u' v' :=
  Eq.ndrec (motive := (Path · v')) (Eq.ndrec p hv) hu

/--
theorem `Path.cast_eq_cast` / 定理 `Path.cast_eq_cast`

English:
theorem Path.cast_eq_cast
  given: {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
  proof: by
  subst_vars
  rfl

@[simp]

中文:
定理 Path.cast_eq_cast
  条件: {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
  证明: by
  subst_vars
  rfl

@[simp]
-/
theorem Path.cast_eq_cast {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v) :
    p.cast hu hv = _root_.cast (by rw [hu, hv]) p := by
  subst_vars
  rfl

@[simp]
/--
theorem `Path.cast_rfl_rfl` / 定理 `Path.cast_rfl_rfl`

English:
theorem Path.cast_rfl_rfl
  given: {u v : U} (p : Path u v)
  statement: p.cast rfl rfl = p
  proof: rfl

@[simp]

中文:
定理 Path.cast_rfl_rfl
  条件: {u v : U} (p : Path u v)
  结论: p.cast rfl rfl = p
  证明: rfl

@[simp]
-/
theorem Path.cast_rfl_rfl {u v : U} (p : Path u v) : p.cast rfl rfl = p :=
  rfl

@[simp]
/--
theorem `Path.cast_cast` / 定理 `Path.cast_cast`

English:
theorem Path.cast_cast
  statement: {u v u' v' u'' v'' : U} (p : Path u v) (hu : u = u') (hv : v = v')
  proof: by
  subst_vars
  rfl

@[simp]

中文:
定理 Path.cast_cast
  结论: {u v u' v' u'' v'' : U} (p : Path u v) (hu : u = u') (hv : v = v')
  证明: by
  subst_vars
  rfl

@[simp]
-/
theorem Path.cast_cast {u v u' v' u'' v'' : U} (p : Path u v) (hu : u = u') (hv : v = v')
    (hu' : u' = u'') (hv' : v' = v'') :
    (p.cast hu hv).cast hu' hv' = p.cast (hu.trans hu') (hv.trans hv') := by
  subst_vars
  rfl

@[simp]
/--
theorem `Path.cast_nil` / 定理 `Path.cast_nil`

English:
theorem Path.cast_nil
  given: {u u' : U} (hu : u = u')
  statement: (Path.nil : Path u u).cast hu hu = Path.nil
  proof: by
  subst_vars
  rfl

中文:
定理 Path.cast_nil
  条件: {u u' : U} (hu : u = u')
  结论: (Path.nil : Path u u).cast hu hu = Path.nil
  证明: by
  subst_vars
  rfl
-/
theorem Path.cast_nil {u u' : U} (hu : u = u') : (Path.nil : Path u u).cast hu hu = Path.nil := by
  subst_vars
  rfl

/--
theorem `Path.cast_heq` / 定理 `Path.cast_heq`

English:
theorem Path.cast_heq
  given: {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
  proof: by
  rw [Path.cast_eq_cast]
  exact _root_.cast_heq _ _

中文:
定理 Path.cast_heq
  条件: {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
  证明: by
  rw [Path.cast_eq_cast]
  exact _root_.cast_heq _ _

Depends on / 依赖: Path.cast_eq_cast, _root_, _root_.cast_heq, cast_eq_cast, cast_heq
-/
theorem Path.cast_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v) :
    p.cast hu hv ≍ p := by
  rw [Path.cast_eq_cast]
  exact _root_.cast_heq _ _

/--
theorem `Path.cast_eq_iff_heq` / 定理 `Path.cast_eq_iff_heq`

English:
theorem Path.cast_eq_iff_heq
  statement: {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
  proof: by
  rw [Path.cast_eq_cast]
  exact _root_.cast_eq_iff_heq

中文:
定理 Path.cast_eq_iff_heq
  结论: {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
  证明: by
  rw [Path.cast_eq_cast]
  exact _root_.cast_eq_iff_heq

Depends on / 依赖: Path.cast_eq_cast, _root_, _root_.cast_eq_iff_heq, cast_eq_cast, cast_eq_iff_heq
-/
theorem Path.cast_eq_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
    (p' : Path u' v') : p.cast hu hv = p' ↔ p ≍ p' := by
  rw [Path.cast_eq_cast]
  exact _root_.cast_eq_iff_heq

/--
theorem `Path.eq_cast_iff_heq` / 定理 `Path.eq_cast_iff_heq`

English:
theorem Path.eq_cast_iff_heq
  statement: {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
  proof: ⟨fun h => ((p.cast_eq_iff_heq hu hv p').1 h.symm).symm, fun h =>
    ((p.cast_eq_iff_heq hu hv p').2 h.symm).symm⟩

中文:
定理 Path.eq_cast_iff_heq
  结论: {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
  证明: ⟨fun h => ((p.cast_eq_iff_heq hu hv p').1 h.symm).symm, fun h =>
    ((p.cast_eq_iff_heq hu hv p').2 h.symm).symm⟩

Depends on / 依赖: cast_eq_iff_heq, h.symm, p.cast_eq_iff_heq
-/
theorem Path.eq_cast_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
    (p' : Path u' v') : p' = p.cast hu hv ↔ p' ≍ p :=
  ⟨fun h => ((p.cast_eq_iff_heq hu hv p').1 h.symm).symm, fun h =>
    ((p.cast_eq_iff_heq hu hv p').2 h.symm).symm⟩

/--
theorem `Path.cast_cons` / 定理 `Path.cast_cons`

English:
theorem Path.cast_cons
  given: {u v w u' w' : U} (p : Path u v) (e : v ⟶ w) (hu : u = u') (hw : w = w')
  proof: by
  subst_vars
  rfl

中文:
定理 Path.cast_cons
  条件: {u v w u' w' : U} (p : Path u v) (e : v ⟶ w) (hu : u = u') (hw : w = w')
  证明: by
  subst_vars
  rfl
-/
theorem Path.cast_cons {u v w u' w' : U} (p : Path u v) (e : v ⟶ w) (hu : u = u') (hw : w = w') :
    (p.cons e).cast hu hw = (p.cast hu rfl).cons (e.cast rfl hw) := by
  subst_vars
  rfl

/--
theorem `cast_eq_of_cons_eq_cons` / 定理 `cast_eq_of_cons_eq_cons`

English:
theorem cast_eq_of_cons_eq_cons
  statement: {u v v' w : U} {p : Path u v} {p' : Path u v'} {e : v ⟶ w}
  proof: by
  rw [Path.cast_eq_iff_heq]
  exact heq_of_cons_eq_cons h

中文:
定理 cast_eq_of_cons_eq_cons
  结论: {u v v' w : U} {p : Path u v} {p' : Path u v'} {e : v ⟶ w}
  证明: by
  rw [Path.cast_eq_iff_heq]
  exact heq_of_cons_eq_cons h

Depends on / 依赖: Path.cast_eq_iff_heq, cast_eq_iff_heq, heq_of_cons_eq_cons
-/
theorem cast_eq_of_cons_eq_cons {u v v' w : U} {p : Path u v} {p' : Path u v'} {e : v ⟶ w}
    {e' : v' ⟶ w} (h : p.cons e = p'.cons e') : p.cast rfl (obj_eq_of_cons_eq_cons h) = p' := by
  rw [Path.cast_eq_iff_heq]
  exact heq_of_cons_eq_cons h

/--
theorem `hom_cast_eq_of_cons_eq_cons` / 定理 `hom_cast_eq_of_cons_eq_cons`

English:
theorem hom_cast_eq_of_cons_eq_cons
  statement: {u v v' w : U} {p : Path u v} {p' : Path u v'} {e : v ⟶ w}
  proof: by
  rw [Hom.cast_eq_iff_heq]
  exact hom_heq_of_cons_eq_cons h

中文:
定理 hom_cast_eq_of_cons_eq_cons
  结论: {u v v' w : U} {p : Path u v} {p' : Path u v'} {e : v ⟶ w}
  证明: by
  rw [Hom.cast_eq_iff_heq]
  exact hom_heq_of_cons_eq_cons h

Depends on / 依赖: Hom.cast_eq_iff_heq, cast_eq_iff_heq, hom_heq_of_cons_eq_cons
-/
theorem hom_cast_eq_of_cons_eq_cons {u v v' w : U} {p : Path u v} {p' : Path u v'} {e : v ⟶ w}
    {e' : v' ⟶ w} (h : p.cons e = p'.cons e') : e.cast (obj_eq_of_cons_eq_cons h) rfl = e' := by
  rw [Hom.cast_eq_iff_heq]
  exact hom_heq_of_cons_eq_cons h

/--
theorem `eq_nil_of_length_zero` / 定理 `eq_nil_of_length_zero`

English:
theorem eq_nil_of_length_zero
  given: {u v : U} (p : Path u v) (hzero : p.length = 0)
  proof: by
  cases p
  · rfl
  · simp only [Nat.succ_ne_zero, length_cons] at hzero

中文:
定理 eq_nil_of_length_zero
  条件: {u v : U} (p : Path u v) (hzero : p.length = 0)
  证明: by
  cases p
  · rfl
  · simp only [Nat.succ_ne_zero, length_cons] at hzero

Depends on / 依赖: Nat.succ_ne_zero, length_cons, succ_ne_zero
-/
theorem eq_nil_of_length_zero {u v : U} (p : Path u v) (hzero : p.length = 0) :
    p.cast (eq_of_length_zero p hzero) rfl = Path.nil := by
  cases p
  · rfl
  · simp only [Nat.succ_ne_zero, length_cons] at hzero

end Quiver
