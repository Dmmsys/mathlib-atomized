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


/-- Change the endpoints of an arrow using equalities. -/
/-
**Quiver.Hom.cast** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Hom`。
形式化陈述：{U : Type u_1} → [inst : Quiver U] → {u v u' v' : U} → u = u' → v = v' → (
u ⟶ v) → (u' ⟶ v')
参数：u ⟶ v；u' ⟶ v'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change the endpoints of an arrow using equalities.
-/
def Hom.cast {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) : u' ⟶ v' :=
  Eq.ndrec (motive := (· ⟶ v')) (Eq.ndrec e hv) hu
/-
**Quiver.Hom.cast_eq_cast** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Hom`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {u v u' v' : U} (hu : u = u') (hv : v =
 v') (e : u ⟶ v),   Quiver.Hom.cast hu hv e = cast ⋯ e
参数：hu : u = u'；hv : v = v'；e : u ⟶ v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Hom.cast_eq_cast {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) :
    e.cast hu hv = _root_.cast (by {rw [hu, hv]}) e := by
  subst_vars
  rfl

@[simp]
/-
**Quiver.Hom.cast_rfl_rfl** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Hom`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {u v : U} (e : u ⟶ v), Quiver.Hom.cast 
⋯ ⋯ e = e
参数：e : u ⟶ v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Hom.cast_rfl_rfl {u v : U} (e : u ⟶ v) : e.cast rfl rfl = e :=
  rfl

@[simp]
/-
**Quiver.Hom.cast_cast** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Hom`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {u v u' v' u'' v'' : U} (e : u ⟶ v) (hu
 : u = u') (hv : v = v') (hu' : u' = u'')   (hv' : v' = v''), Quiver.Hom.cast hu
' hv' (Quiver.Hom.cast hu hv e) = Quiver.Hom.cast ⋯ ⋯ e
参数：e : u ⟶ v；hu : u = u'；hv : v = v'；hu' : u' = u''；hv' : v' = v''；Quiver.Hom.ca
st hu hv e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem Hom.cast_cast {u v u' v' u'' v'' : U} (e : u ⟶ v) (hu : u = u') (hv : v = v')
    (hu' : u' = u'') (hv' : v' = v'') :
    (e.cast hu hv).cast hu' hv' = e.cast (hu.trans hu') (hv.trans hv') := by
  subst_vars
  rfl
/-
**Quiver.Hom.cast_heq** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Hom`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {u v u' v' : U} (hu : u = u') (hv : v =
 v') (e : u ⟶ v), Quiver.Hom.cast hu hv e ≍ e
参数：hu : u = u'；hv : v = v'；e : u ⟶ v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Hom.cast_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) :
    e.cast hu hv ≍ e := by
  subst_vars
  rfl
/-
**Quiver.Hom.cast_eq_iff_heq** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Hom`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {u v u' v' : U} (hu : u = u') (hv : v =
 v') (e : u ⟶ v) (e' : u' ⟶ v'),   Quiver.Hom.cast hu hv e = e' ↔ e ≍ e'
参数：hu : u = u'；hv : v = v'；e : u ⟶ v；e' : u' ⟶ v'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Hom.cast_eq_cast`：∀ {U : Type u_1} [inst : Quiver U] {u v u' v' :
 U} (hu : u = u') (hv : v = v') (e : u ⟶ v),   Quiver.Hom.cast hu hv e = cast ⋯ 
e
· 使用定理 `cast_eq_iff_heq`：∀ {a a_1 : Sort u_1} {e : a = a_1} {a_2 : a} {a' : a_1}
, cast e a_2 = a' ↔ a_2 ≍ a'
-/
theorem Hom.cast_eq_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) (e' : u' ⟶ v') :
    e.cast hu hv = e' ↔ e ≍ e' := by
  rw [Hom.cast_eq_cast]
  exact _root_.cast_eq_iff_heq
/-
**Quiver.Hom.eq_cast_iff_heq** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Hom`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {u v u' v' : U} (hu : u = u') (hv : v =
 v') (e : u ⟶ v) (e' : u' ⟶ v'),   e' = Quiver.Hom.cast hu hv e ↔ e' ≍ e
参数：hu : u = u'；hv : v = v'；e : u ⟶ v；e' : u' ⟶ v'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Quiver.Hom.cast_eq_iff_heq`：∀ {U : Type u_1} [inst : Quiver U] {u v u' v
' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) (e' : u' ⟶ v'),   Quiver.Hom.cast
 hu hv e = e' ↔ …
· 使用定理 `HEq.symm`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → b ≍ a
-/
theorem Hom.eq_cast_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) (e' : u' ⟶ v') :
    e' = e.cast hu hv ↔ e' ≍ e := by
  rw [eq_comm, Hom.cast_eq_iff_heq]
  exact ⟨HEq.symm, HEq.symm⟩

/-!
### Rewriting paths along equalities of vertices
-/


open Path

/-- Change the endpoints of a path using equalities. -/
/-
**Quiver.Path.cast** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Path`。
形式化陈述：{U : Type u_1} → [inst : Quiver U] → {u v u' v' : U} → u = u' → v = v' → Q
uiver.Path u v → Quiver.Path u' v'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change the endpoints of a path using equalities.
-/
def Path.cast {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v) : Path u' v' :=
  Eq.ndrec (motive := (Path · v')) (Eq.ndrec p hv) hu
/-
**Quiver.Path.cast_eq_cast** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {u v u' v' : U} (hu : u = u') (hv : v =
 v') (p : Quiver.Path u v),   Quiver.Path.cast hu hv p = cast ⋯ p
参数：hu : u = u'；hv : v = v'；p : Quiver.Path u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Path.cast_eq_cast {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v) :
    p.cast hu hv = _root_.cast (by rw [hu, hv]) p := by
  subst_vars
  rfl

@[simp]
/-
**Quiver.Path.cast_rfl_rfl** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {u v : U} (p : Quiver.Path u v), Quiver
.Path.cast ⋯ ⋯ p = p
参数：p : Quiver.Path u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Path.cast_rfl_rfl {u v : U} (p : Path u v) : p.cast rfl rfl = p :=
  rfl

@[simp]
/-
**Quiver.Path.cast_cast** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {u v u' v' u'' v'' : U} (p : Quiver.Pat
h u v) (hu : u = u') (hv : v = v')   (hu' : u' = u'') (hv' : v' = v''), Quiver.P
ath.cast hu' hv' (Quiver.Path.cast hu hv p) = Quiver.Path.cast ⋯ ⋯ p
参数：p : Quiver.Path u v；hu : u = u'；hv : v = v'；hu' : u' = u''；hv' : v' = v''；Qui
ver.Path.cast hu hv p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem Path.cast_cast {u v u' v' u'' v'' : U} (p : Path u v) (hu : u = u') (hv : v = v')
    (hu' : u' = u'') (hv' : v' = v'') :
    (p.cast hu hv).cast hu' hv' = p.cast (hu.trans hu') (hv.trans hv') := by
  subst_vars
  rfl

@[simp]
/-
**Quiver.Path.cast_nil** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {u u' : U} (hu : u = u'), Quiver.Path.c
ast hu hu Quiver.Path.nil = Quiver.Path.nil
参数：hu : u = u'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Path.cast_nil {u u' : U} (hu : u = u') : (Path.nil : Path u u).cast hu hu = Path.nil := by
  subst_vars
  rfl
/-
**Quiver.Path.cast_heq** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {u v u' v' : U} (hu : u = u') (hv : v =
 v') (p : Quiver.Path u v),   Quiver.Path.cast hu hv p ≍ p
参数：hu : u = u'；hv : v = v'；p : Quiver.Path u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.cast_eq_cast`：∀ {U : Type u_1} [inst : Quiver U] {u v u' v' 
: U} (hu : u = u') (hv : v = v') (p : Quiver.Path u v),   Quiver.Path.cast hu hv
 p = cast ⋯ p
· 使用定理 `cast_heq`：∀ {α β : Sort u} (h : α = β) (a : α), cast h a ≍ a
-/
theorem Path.cast_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v) :
    p.cast hu hv ≍ p := by
  rw [Path.cast_eq_cast]
  exact _root_.cast_heq _ _
/-
**Quiver.Path.cast_eq_iff_heq** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {u v u' v' : U} (hu : u = u') (hv : v =
 v') (p : Quiver.Path u v)   (p' : Quiver.Path u' v'), Quiver.Path.cast hu hv p 
= p' ↔ p ≍ p'
参数：hu : u = u'；hv : v = v'；p : Quiver.Path u v；p' : Quiver.Path u' v'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.cast_eq_cast`：∀ {U : Type u_1} [inst : Quiver U] {u v u' v' 
: U} (hu : u = u') (hv : v = v') (p : Quiver.Path u v),   Quiver.Path.cast hu hv
 p = cast ⋯ p
· 使用定理 `cast_eq_iff_heq`：∀ {a a_1 : Sort u_1} {e : a = a_1} {a_2 : a} {a' : a_1}
, cast e a_2 = a' ↔ a_2 ≍ a'
-/
theorem Path.cast_eq_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
    (p' : Path u' v') : p.cast hu hv = p' ↔ p ≍ p' := by
  rw [Path.cast_eq_cast]
  exact _root_.cast_eq_iff_heq
/-
**Quiver.Path.eq_cast_iff_heq** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {u v u' v' : U} (hu : u = u') (hv : v =
 v') (p : Quiver.Path u v)   (p' : Quiver.Path u' v'), p' = Quiver.Path.cast hu 
hv p ↔ p' ≍ p
参数：hu : u = u'；hv : v = v'；p : Quiver.Path u v；p' : Quiver.Path u' v'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HEq.symm`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → b ≍ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quiver.Path.cast_eq_iff_heq`：∀ {U : Type u_1} [inst : Quiver U] {u v u' 
v' : U} (hu : u = u') (hv : v = v') (p : Quiver.Path u v)   (p' : Quiver.Path u'
 v'), Quiver.Path…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem Path.eq_cast_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
    (p' : Path u' v') : p' = p.cast hu hv ↔ p' ≍ p :=
  ⟨fun h => ((p.cast_eq_iff_heq hu hv p').1 h.symm).symm, fun h =>
    ((p.cast_eq_iff_heq hu hv p').2 h.symm).symm⟩
/-
**Quiver.Path.cast_cons** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {U : Type u_1} [inst : Quiver U] {u v w u' w' : U} (p : Quiver.Path u v)
 (e : v ⟶ w) (hu : u = u') (hw : w = w'),   Quiver.Path.cast hu hw (p.cons e) = 
(Quiver.Path.cast hu ⋯ p).cons (Quiver.Hom.cast ⋯ hw e)
参数：p : Quiver.Path u v；e : v ⟶ w；hu : u = u'；hw : w = w'；p.cons e；Quiver.Path.ca
st hu ⋯ p；Quiver.Hom.cast ⋯ hw e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Path.cast_cons {u v w u' w' : U} (p : Path u v) (e : v ⟶ w) (hu : u = u') (hw : w = w') :
    (p.cons e).cast hu hw = (p.cast hu rfl).cons (e.cast rfl hw) := by
  subst_vars
  rfl
/-
**Quiver.cast_eq_of_cons_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `Quiver`。
形式化陈述：cast_eq_of_cons_eq_cons {u v v' w : U} {p : Path u v} {p' : Path u v'} {e 
: v ⟶ w} {e' : v' ⟶ w} (h : p.cons e = p'.cons e') : p.cast rfl (obj_eq_of_cons_
eq_cons h) = p'
参数：h : p.cons e = p'.cons e'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Quiver.Path.obj_eq_of_cons_eq_cons`：obj_eq_of_cons_eq_cons {p : Path a b
} {p' : Path a c} {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.cast_eq_iff_heq`：∀ {U : Type u_1} [inst : Quiver U] {u v u' 
v' : U} (hu : u = u') (hv : v = v') (p : Quiver.Path u v)   (p' : Quiver.Path u'
 v'), Quiver.Path…
· 使用引理 `Quiver.Path.heq_of_cons_eq_cons`：heq_of_cons_eq_cons {p : Path a b} {p' 
: Path a c} {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : p ≍ p'
-/
theorem cast_eq_of_cons_eq_cons {u v v' w : U} {p : Path u v} {p' : Path u v'} {e : v ⟶ w}
    {e' : v' ⟶ w} (h : p.cons e = p'.cons e') : p.cast rfl (obj_eq_of_cons_eq_cons h) = p' := by
  rw [Path.cast_eq_iff_heq]
  exact heq_of_cons_eq_cons h
/-
**Quiver.hom_cast_eq_of_cons_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `Quiver`。
形式化陈述：hom_cast_eq_of_cons_eq_cons {u v v' w : U} {p : Path u v} {p' : Path u v'}
 {e : v ⟶ w} {e' : v' ⟶ w} (h : p.cons e = p'.cons e') : e.cast (obj_eq_of_cons_
eq_cons h) rfl = e'
参数：h : p.cons e = p'.cons e'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Quiver.Path.obj_eq_of_cons_eq_cons`：obj_eq_of_cons_eq_cons {p : Path a b
} {p' : Path a c} {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Hom.cast_eq_iff_heq`：∀ {U : Type u_1} [inst : Quiver U] {u v u' v
' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) (e' : u' ⟶ v'),   Quiver.Hom.cast
 hu hv e = e' ↔ …
· 使用引理 `Quiver.Path.hom_heq_of_cons_eq_cons`：hom_heq_of_cons_eq_cons {p : Path a
 b} {p' : Path a c} {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : e ≍ e
'
-/
theorem hom_cast_eq_of_cons_eq_cons {u v v' w : U} {p : Path u v} {p' : Path u v'} {e : v ⟶ w}
    {e' : v' ⟶ w} (h : p.cons e = p'.cons e') : e.cast (obj_eq_of_cons_eq_cons h) rfl = e' := by
  rw [Hom.cast_eq_iff_heq]
  exact hom_heq_of_cons_eq_cons h
/-
**Quiver.eq_nil_of_length_zero** 是 Mathlib 中的一个定理，位于命名空间 `Quiver`。
形式化陈述：eq_nil_of_length_zero {u v : U} (p : Path u v) (hzero : p.length = 0) : p.
cast (eq_of_length_zero p hzero) rfl = Path.nil
参数：p : Path u v；hzero : p.length = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Path.eq_of_length_zero`：eq_of_length_zero (p : Path a b) (hzero :
 p.length = 0) : a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem eq_nil_of_length_zero {u v : U} (p : Path u v) (hzero : p.length = 0) :
    p.cast (eq_of_length_zero p hzero) rfl = Path.nil := by
  cases p
  · rfl
  · simp only [Nat.succ_ne_zero, length_cons] at hzero

end Quiver

