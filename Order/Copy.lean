/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Yaël Dillies
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Tooling to make copies of lattice structures

Sometimes it is useful to make a copy of a lattice structure
where one replaces the data parts with provably equal definitions
that have better definitional properties.
-/

@[expose] public section


open Order

universe u

variable {α : Type u}

/-- A function to create a provable equal copy of a top order
with possibly different definitional equalities. -/
@[instance_reducible]
/-
**OrderTop.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderTop.copy {h : LE α} {h' : LE α} (c : @OrderTop α h') (top : α) (eq_to
p : top = (by infer_instance : Top α).top) (le_eq : forall x y : α, (@LE.le α h)
 x y ↔ x <= y) : @OrderTop α h
参数：c : @OrderTop α h'；top : α；eq_top : top = (by infer_instance : Top α).top；le_
eq : forall x y : α, (@LE.le α h) x y ↔ x <= y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function to create a provable equal copy of a top order
with possibly different definitional equalities.
-/
def OrderTop.copy {h : LE α} {h' : LE α} (c : @OrderTop α h')
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (le_eq : ∀ x y : α, (@LE.le α h) x y ↔ x ≤ y) : @OrderTop α h :=
  @OrderTop.mk α h { top := top } fun _ ↦ by simp [eq_top, le_eq]

/-- A function to create a provable equal copy of a bottom order
with possibly different definitional equalities. -/
@[instance_reducible]
/-
**OrderBot.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderBot.copy {h : LE α} {h' : LE α} (c : @OrderBot α h') (bot : α) (eq_bo
t : bot = (by infer_instance : Bot α).bot) (le_eq : forall x y : α, (@LE.le α h)
 x y ↔ x <= y) : @OrderBot α h
参数：c : @OrderBot α h'；bot : α；eq_bot : bot = (by infer_instance : Bot α).bot；le_
eq : forall x y : α, (@LE.le α h) x y ↔ x <= y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function to create a provable equal copy of a bottom order
with possibly different definitional equalities.
-/
def OrderBot.copy {h : LE α} {h' : LE α} (c : @OrderBot α h')
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (le_eq : ∀ x y : α, (@LE.le α h) x y ↔ x ≤ y) : @OrderBot α h :=
  @OrderBot.mk α h { bot := bot } fun _ ↦ by simp [eq_bot, le_eq]

/-- A function to create a provable equal copy of a bounded order
with possibly different definitional equalities. -/
@[instance_reducible]
/-
**BoundedOrder.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：BoundedOrder.copy {h : LE α} {h' : LE α} (c : @BoundedOrder α h') (top : α
) (eq_top : top = (by infer_instance : Top α).top) (bot : α) (eq_bot : bot = (by
 infer_instance : Bot α).bot) (le_eq : forall x y : α, (@LE.le α h) x y ↔ x <= y
) : @BoundedOrder α h
参数：c : @BoundedOrder α h'；top : α；eq_top : top = (by infer_instance : Top α).top
；bot : α；eq_bot : bot = (by infer_instance : Bot α).bot；le_eq : forall x y : α, 
(@LE.le α h) x y ↔ x <= y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function to create a provable equal copy of a bounded order
with possibly different definitional equalities.
-/
def BoundedOrder.copy {h : LE α} {h' : LE α} (c : @BoundedOrder α h')
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (le_eq : ∀ x y : α, (@LE.le α h) x y ↔ x ≤ y) : @BoundedOrder α h :=
  @BoundedOrder.mk α h (@OrderTop.mk α h { top := top } (fun _ ↦ by simp [eq_top, le_eq]))
    (@OrderBot.mk α h { bot := bot } (fun _ ↦ by simp [eq_bot, le_eq]))

/-- A function to create a provable equal copy of a lattice
with possibly different definitional equalities. -/
@[instance_reducible]
/-
**Lattice.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Lattice.copy (c : Lattice α) (le : α -> α -> Prop) (eq_le : le = (by infer
_instance : LE α).le) (sup : α -> α -> α) (eq_sup : sup = (by infer_instance : M
ax α).max) (inf : α -> α -> α) (eq_inf : inf = (by infer_instance : Min α).min) 
: Lattice α where le
参数：c : Lattice α；le : α -> α -> Prop；eq_le : le = (by infer_instance : LE α).le；
sup : α -> α -> α；eq_sup : sup = (by infer_instance : Max α).max；inf : α -> α ->
 α；eq_inf : inf = (by infer_instance : Min α).min。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function to create a provable equal copy of a lattice
with possibly different definitional equalities.
-/
def Lattice.copy (c : Lattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min) : Lattice α where
  le := le
  sup := sup
  inf := inf
  lt := fun a b ↦ le a b ∧ ¬ le b a
  le_refl := by intros; simp [eq_le]
  le_trans := by intro _ _ _ hab hbc; rw [eq_le] at hab hbc ⊢; exact le_trans hab hbc
  le_antisymm := by intro _ _ hab hba; simp_rw [eq_le] at hab hba; exact le_antisymm hab hba
  le_sup_left := by intros; simp [eq_le, eq_sup]
  le_sup_right := by intros; simp [eq_le, eq_sup]
  sup_le := by intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_sup, hac, hbc]
  inf_le_left := by intros; simp [eq_le, eq_inf]
  inf_le_right := by intros; simp [eq_le, eq_inf]
  le_inf := by intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_inf, hac, hbc]

/-- A function to create a provable equal copy of a distributive lattice
with possibly different definitional equalities. -/
@[instance_reducible]
/-
**DistribLattice.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DistribLattice.copy (c : DistribLattice α) (le : α -> α -> Prop) (eq_le : 
le = (by infer_instance : LE α).le) (sup : α -> α -> α) (eq_sup : sup = (by infe
r_instance : Max α).max) (inf : α -> α -> α) (eq_inf : inf = (by infer_instance 
: Min α).min) : DistribLattice α where toLattice
参数：c : DistribLattice α；le : α -> α -> Prop；eq_le : le = (by infer_instance : LE
 α).le；sup : α -> α -> α；eq_sup : sup = (by infer_instance : Max α).max；inf : α 
-> α -> α；eq_inf : inf = (by infer_instance : Min α).min。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function to create a provable equal copy of a distributive lattice
with possibly different definitional equalities.
-/
def DistribLattice.copy (c : DistribLattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min) : DistribLattice α where
  toLattice := Lattice.copy (@DistribLattice.toLattice α c) le eq_le sup eq_sup inf eq_inf
  le_sup_inf := by intros; simp +instances [eq_le, eq_sup, eq_inf, le_sup_inf]

/-- A function to create a provable equal copy of a generalised heyting algebra
with possibly different definitional equalities. -/
@[instance_reducible]
/-
**GeneralizedHeytingAlgebra.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GeneralizedHeytingAlgebra.copy (c : GeneralizedHeytingAlgebra α) (le : α -
> α -> Prop) (eq_le : le = (by infer_instance : LE α).le) (top : α) (eq_top : to
p = (by infer_instance : Top α).top) (sup : α -> α -> α) (eq_sup : sup = (by inf
er_instance : Max α).max) (inf : α -> α -> α) (eq_inf : inf = (by infer_instance
 : Min α).min) (himp : α -> α -> α) (eq_himp : himp = (by infer_instance : HImp 
α).himp) : GeneralizedHeytingAlgebra α where __
参数：c : GeneralizedHeytingAlgebra α；le : α -> α -> Prop；eq_le : le = (by infer_in
stance : LE α).le；top : α；eq_top : top = (by infer_instance : Top α).top；sup : α
 -> α -> α；eq_sup : sup = (by infer_instance : Max α).max；inf : α -> α -> α；eq_i
nf : inf = (by infer_instance : Min α).min；himp : α -> α -> α；eq_himp : himp = (
by infer_instance : HImp α).himp。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function to create a provable equal copy of a generalised heyting algebra
with possibly different definitional equalities.
-/
def GeneralizedHeytingAlgebra.copy (c : GeneralizedHeytingAlgebra α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (himp : α → α → α) (eq_himp : himp = (by infer_instance : HImp α).himp) :
    GeneralizedHeytingAlgebra α where
  __ := Lattice.copy (@GeneralizedHeytingAlgebra.toLattice α c) le eq_le sup eq_sup inf eq_inf
  __ := OrderTop.copy (@GeneralizedHeytingAlgebra.toOrderTop α c) top eq_top
    (by rw [← eq_le]; exact fun _ _ ↦ .rfl)
  himp := himp
  le_himp_iff _ _ _ := by simp +instances [eq_le, eq_himp, eq_inf]

/-- A function to create a provable equal copy of a generalised co-Heyting algebra
with possibly different definitional equalities. -/
@[instance_reducible]
/-
**GeneralizedCoheytingAlgebra.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GeneralizedCoheytingAlgebra.copy (c : GeneralizedCoheytingAlgebra α) (le :
 α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le) (bot : α) (eq_bot 
: bot = (by infer_instance : Bot α).bot) (sup : α -> α -> α) (eq_sup : sup = (by
 infer_instance : Max α).max) (inf : α -> α -> α) (eq_inf : inf = (by infer_inst
ance : Min α).min) (sdiff : α -> α -> α) (eq_sdiff : sdiff = (by infer_instance 
: SDiff α).sdiff) : GeneralizedCoheytingAlgebra α where __
参数：c : GeneralizedCoheytingAlgebra α；le : α -> α -> Prop；eq_le : le = (by infer_
instance : LE α).le；bot : α；eq_bot : bot = (by infer_instance : Bot α).bot；sup :
 α -> α -> α；eq_sup : sup = (by infer_instance : Max α).max；inf : α -> α -> α；eq
_inf : inf = (by infer_instance : Min α).min；sdiff : α -> α -> α；eq_sdiff : sdif
f = (by infer_instance : SDiff α).sdiff。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function to create a provable equal copy of a generalised co-Heyting algebra
with possibly different definitional equalities.
-/
def GeneralizedCoheytingAlgebra.copy (c : GeneralizedCoheytingAlgebra α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α → α → α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff) :
    GeneralizedCoheytingAlgebra α where
  __ := Lattice.copy (@GeneralizedCoheytingAlgebra.toLattice α c) le eq_le sup eq_sup inf eq_inf
  __ := OrderBot.copy (@GeneralizedCoheytingAlgebra.toOrderBot α c) bot eq_bot
    (by rw [← eq_le]; exact fun _ _ ↦ .rfl)
  sdiff := sdiff
  sdiff_le_iff := by simp +instances [eq_le, eq_sdiff, eq_sup]

/-- A function to create a provable equal copy of a heyting algebra
with possibly different definitional equalities. -/
@[instance_reducible]
/-
**HeytingAlgebra.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HeytingAlgebra.copy (c : HeytingAlgebra α) (le : α -> α -> Prop) (eq_le : 
le = (by infer_instance : LE α).le) (top : α) (eq_top : top = (by infer_instance
 : Top α).top) (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot) (sup :
 α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max) (inf : α -> α -> 
α) (eq_inf : inf = (by infer_instance : Min α).min) (himp : α -> α -> α) (eq_him
p : himp = (by infer_instance : HImp α).himp) (compl : α -> α) (eq_compl : compl
 = (by infer_instance : Co
参数：c : HeytingAlgebra α；le : α -> α -> Prop；eq_le : le = (by infer_instance : LE
 α).le；top : α；eq_top : top = (by infer_instance : Top α).top；bot : α；eq_bot : b
ot = (by infer_instance : Bot α).bot；sup : α -> α -> α；eq_sup : sup = (by infer_
instance : Max α).max；inf : α -> α -> α；eq_inf : inf = (by infer_instance : Min 
α).min；himp : α -> α -> α；eq_himp : himp = (by infer_instance : HImp α).himp；com
pl : α -> α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function to create a provable equal copy of a heyting algebra
with possibly different definitional equalities.
-/
def HeytingAlgebra.copy (c : HeytingAlgebra α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (himp : α → α → α) (eq_himp : himp = (by infer_instance : HImp α).himp)
    (compl : α → α) (eq_compl : compl = (by infer_instance : Compl α).compl) :
    HeytingAlgebra α where
  toGeneralizedHeytingAlgebra := GeneralizedHeytingAlgebra.copy
    (@HeytingAlgebra.toGeneralizedHeytingAlgebra α c) le eq_le top eq_top sup eq_sup inf eq_inf himp
    eq_himp
  __ := OrderBot.copy (@HeytingAlgebra.toOrderBot α c) bot eq_bot
    (by rw [← eq_le]; exact fun _ _ ↦ .rfl)
  compl := compl
  himp_bot := by simp +instances [eq_le, eq_himp, eq_bot, eq_compl]

/-- A function to create a provable equal copy of a co-Heyting algebra
with possibly different definitional equalities. -/
@[instance_reducible]
/-
**CoheytingAlgebra.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CoheytingAlgebra.copy (c : CoheytingAlgebra α) (le : α -> α -> Prop) (eq_l
e : le = (by infer_instance : LE α).le) (top : α) (eq_top : top = (by infer_inst
ance : Top α).top) (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot) (s
up : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max) (inf : α -> α
 -> α) (eq_inf : inf = (by infer_instance : Min α).min) (sdiff : α -> α -> α) (e
q_sdiff : sdiff = (by infer_instance : SDiff α).sdiff) (hnot : α -> α) (eq_hnot 
: hnot = (by infer_instanc
参数：c : CoheytingAlgebra α；le : α -> α -> Prop；eq_le : le = (by infer_instance : 
LE α).le；top : α；eq_top : top = (by infer_instance : Top α).top；bot : α；eq_bot :
 bot = (by infer_instance : Bot α).bot；sup : α -> α -> α；eq_sup : sup = (by infe
r_instance : Max α).max；inf : α -> α -> α；eq_inf : inf = (by infer_instance : Mi
n α).min；sdiff : α -> α -> α；eq_sdiff : sdiff = (by infer_instance : SDiff α).sd
iff；hnot : α -> α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function to create a provable equal copy of a co-Heyting algebra
with possibly different definitional equalities.
-/
def CoheytingAlgebra.copy (c : CoheytingAlgebra α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α → α → α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff)
    (hnot : α → α) (eq_hnot : hnot = (by infer_instance : HNot α).hnot) :
    CoheytingAlgebra α where
  toGeneralizedCoheytingAlgebra := GeneralizedCoheytingAlgebra.copy
    (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra α c) le eq_le bot eq_bot sup eq_sup inf eq_inf
      sdiff eq_sdiff
  __ := OrderTop.copy (@CoheytingAlgebra.toOrderTop α c) top eq_top
    (by rw [← eq_le]; exact fun _ _ ↦ .rfl)
  hnot := hnot
  top_sdiff := by simp +instances [eq_le, eq_sdiff, eq_top, eq_hnot]

/-- A function to create a provable equal copy of a bi-Heyting algebra
with possibly different definitional equalities. -/
@[instance_reducible]
/-
**BiheytingAlgebra.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：BiheytingAlgebra.copy (c : BiheytingAlgebra α) (le : α -> α -> Prop) (eq_l
e : le = (by infer_instance : LE α).le) (top : α) (eq_top : top = (by infer_inst
ance : Top α).top) (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot) (s
up : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max) (inf : α -> α
 -> α) (eq_inf : inf = (by infer_instance : Min α).min) (sdiff : α -> α -> α) (e
q_sdiff : sdiff = (by infer_instance : SDiff α).sdiff) (hnot : α -> α) (eq_hnot 
: hnot = (by infer_instanc
参数：c : BiheytingAlgebra α；le : α -> α -> Prop；eq_le : le = (by infer_instance : 
LE α).le；top : α；eq_top : top = (by infer_instance : Top α).top；bot : α；eq_bot :
 bot = (by infer_instance : Bot α).bot；sup : α -> α -> α；eq_sup : sup = (by infe
r_instance : Max α).max；inf : α -> α -> α；eq_inf : inf = (by infer_instance : Mi
n α).min；sdiff : α -> α -> α；eq_sdiff : sdiff = (by infer_instance : SDiff α).sd
iff；hnot : α -> α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CoheytingAlgebra.top_sdiff`：∀ {α : Type u_4} [self : CoheytingAlgebra α]
 (a : α), ⊤ \ a = ￢a

--- 原说明 ---
A function to create a provable equal copy of a bi-Heyting algebra
with possibly different definitional equalities.
-/
def BiheytingAlgebra.copy (c : BiheytingAlgebra α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α → α → α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff)
    (hnot : α → α) (eq_hnot : hnot = (by infer_instance : HNot α).hnot)
    (himp : α → α → α) (eq_himp : himp = (by infer_instance : HImp α).himp)
    (compl : α → α) (eq_compl : compl = (by infer_instance : Compl α).compl) :
    BiheytingAlgebra α where
  toHeytingAlgebra := HeytingAlgebra.copy (@BiheytingAlgebra.toHeytingAlgebra α c) le eq_le top
    eq_top bot eq_bot sup eq_sup inf eq_inf himp eq_himp compl eq_compl
  __ := CoheytingAlgebra.copy (@BiheytingAlgebra.toCoheytingAlgebra α c) le eq_le top eq_top bot
    eq_bot sup eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot

/-- A function to create a provable equal copy of a complete lattice
with possibly different definitional equalities. -/
@[instance_reducible]
/-
**CompleteLattice.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CompleteLattice.copy (c : CompleteLattice α) (le : α -> α -> Prop) (eq_le 
: le = (by infer_instance : LE α).le) (top : α) (eq_top : top = (by infer_instan
ce : Top α).top) (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot) (sup
 : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max) (inf : α -> α -
> α) (eq_inf : inf = (by infer_instance : Min α).min) (sSup : Set α -> α) (eq_sS
up : sSup = (by infer_instance : SupSet α).sSup) (sInf : Set α -> α) (eq_sInf : 
sInf = (by infer_instance 
参数：c : CompleteLattice α；le : α -> α -> Prop；eq_le : le = (by infer_instance : L
E α).le；top : α；eq_top : top = (by infer_instance : Top α).top；bot : α；eq_bot : 
bot = (by infer_instance : Bot α).bot；sup : α -> α -> α；eq_sup : sup = (by infer
_instance : Max α).max；inf : α -> α -> α；eq_inf : inf = (by infer_instance : Min
 α).min；sSup : Set α -> α；eq_sSup : sSup = (by infer_instance : SupSet α).sSup；s
Inf : Set α -> α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function to create a provable equal copy of a complete lattice
with possibly different definitional equalities.
-/
def CompleteLattice.copy (c : CompleteLattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) :
    CompleteLattice α where
  toLattice := Lattice.copy (@CompleteLattice.toLattice α c) le eq_le sup eq_sup inf eq_inf
  top := top
  bot := bot
  sSup := sSup
  sInf := sInf
  isLUB_sSup _ := by simp +instances only [eq_le, eq_sSup, isLUB_sSup]
  isGLB_sInf _ := by simp +instances only [eq_le, eq_sInf, isGLB_sInf]
  le_top := by intros; simp +instances [eq_le, eq_top]
  bot_le := by intros; simp +instances [eq_le, eq_bot]

/-- A function to create a provable equal copy of a frame with possibly different definitional
equalities. -/
@[instance_reducible]
/-
**Frame.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Frame.copy (c : Frame α) (le : α -> α -> Prop) (eq_le : le = (by infer_ins
tance : LE α).le) (top : α) (eq_top : top = (by infer_instance : Top α).top) (bo
t : α) (eq_bot : bot = (by infer_instance : Bot α).bot) (sup : α -> α -> α) (eq_
sup : sup = (by infer_instance : Max α).max) (inf : α -> α -> α) (eq_inf : inf =
 (by infer_instance : Min α).min) (himp : α -> α -> α) (eq_himp : himp = (by inf
er_instance : HImp α).himp) (compl : α -> α) (eq_compl : compl = (by infer_insta
nce : Compl α).compl) (sSu
参数：c : Frame α；le : α -> α -> Prop；eq_le : le = (by infer_instance : LE α).le；to
p : α；eq_top : top = (by infer_instance : Top α).top；bot : α；eq_bot : bot = (by 
infer_instance : Bot α).bot；sup : α -> α -> α；eq_sup : sup = (by infer_instance 
: Max α).max；inf : α -> α -> α；eq_inf : inf = (by infer_instance : Min α).min；hi
mp : α -> α -> α；eq_himp : himp = (by infer_instance : HImp α).himp；compl : α ->
 α；eq_compl : compl = (by infer_instance : Compl α).compl。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HeytingAlgebra.himp_bot`：∀ {α : Type u_4} [self : HeytingAlgebra α] (a :
 α), a ⇨ ⊥ = aᶜ

--- 原说明 ---
A function to create a provable equal copy of a frame with possibly different de
finitional
equalities.
-/
def Frame.copy (c : Frame α) (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (himp : α → α → α) (eq_himp : himp = (by infer_instance : HImp α).himp)
    (compl : α → α) (eq_compl : compl = (by infer_instance : Compl α).compl)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) : Frame α where
  toCompleteLattice := CompleteLattice.copy (@Frame.toCompleteLattice α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sSup eq_sSup sInf eq_sInf
  __ := HeytingAlgebra.copy (@Frame.toHeytingAlgebra α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf himp eq_himp compl eq_compl

/-- A function to create a provable equal copy of a coframe with possibly different definitional
equalities. -/
@[instance_reducible]
/-
**Coframe.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Coframe.copy (c : Coframe α) (le : α -> α -> Prop) (eq_le : le = (by infer
_instance : LE α).le) (top : α) (eq_top : top = (by infer_instance : Top α).top)
 (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot) (sup : α -> α -> α) 
(eq_sup : sup = (by infer_instance : Max α).max) (inf : α -> α -> α) (eq_inf : i
nf = (by infer_instance : Min α).min) (sdiff : α -> α -> α) (eq_sdiff : sdiff = 
(by infer_instance : SDiff α).sdiff) (hnot : α -> α) (eq_hnot : hnot = (by infer
_instance : HNot α).hnot) 
参数：c : Coframe α；le : α -> α -> Prop；eq_le : le = (by infer_instance : LE α).le；
top : α；eq_top : top = (by infer_instance : Top α).top；bot : α；eq_bot : bot = (b
y infer_instance : Bot α).bot；sup : α -> α -> α；eq_sup : sup = (by infer_instanc
e : Max α).max；inf : α -> α -> α；eq_inf : inf = (by infer_instance : Min α).min；
sdiff : α -> α -> α；eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff；hnot 
: α -> α；eq_hnot : hnot = (by infer_instance : HNot α).hnot。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CoheytingAlgebra.top_sdiff`：∀ {α : Type u_4} [self : CoheytingAlgebra α]
 (a : α), ⊤ \ a = ￢a

--- 原说明 ---
A function to create a provable equal copy of a coframe with possibly different 
definitional
equalities.
-/
def Coframe.copy (c : Coframe α) (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α → α → α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff)
    (hnot : α → α) (eq_hnot : hnot = (by infer_instance : HNot α).hnot)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) : Coframe α where
  toCompleteLattice := CompleteLattice.copy (@Coframe.toCompleteLattice α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sSup eq_sSup sInf eq_sInf
  __ := CoheytingAlgebra.copy (@Coframe.toCoheytingAlgebra α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot

/-- A function to create a provable equal copy of a complete distributive lattice
with possibly different definitional equalities. -/
@[instance_reducible]
/-
**CompleteDistribLattice.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CompleteDistribLattice.copy (c : CompleteDistribLattice α) (le : α -> α ->
 Prop) (eq_le : le = (by infer_instance : LE α).le) (top : α) (eq_top : top = (b
y infer_instance : Top α).top) (bot : α) (eq_bot : bot = (by infer_instance : Bo
t α).bot) (sup : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max) (
inf : α -> α -> α) (eq_inf : inf = (by infer_instance : Min α).min) (sdiff : α -
> α -> α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff) (hnot : α -> 
α) (eq_hnot : hnot = (by i
参数：c : CompleteDistribLattice α；le : α -> α -> Prop；eq_le : le = (by infer_insta
nce : LE α).le；top : α；eq_top : top = (by infer_instance : Top α).top；bot : α；eq
_bot : bot = (by infer_instance : Bot α).bot；sup : α -> α -> α；eq_sup : sup = (b
y infer_instance : Max α).max；inf : α -> α -> α；eq_inf : inf = (by infer_instanc
e : Min α).min；sdiff : α -> α -> α；eq_sdiff : sdiff = (by infer_instance : SDiff
 α).sdiff；hnot : α -> α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Coframe.sdiff_le_iff`：∀ {α : Type u_1} [self : Order.Coframe α] (a
 b c : α), a \ b ≤ c ↔ a ≤ b ⊔ c
· 使用定理 `Order.Coframe.top_sdiff`：∀ {α : Type u_1} [self : Order.Coframe α] (a : 
α), ⊤ \ a = ￢a

--- 原说明 ---
A function to create a provable equal copy of a complete distributive lattice
with possibly different definitional equalities.
-/
def CompleteDistribLattice.copy (c : CompleteDistribLattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α → α → α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff)
    (hnot : α → α) (eq_hnot : hnot = (by infer_instance : HNot α).hnot)
    (himp : α → α → α) (eq_himp : himp = (by infer_instance : HImp α).himp)
    (compl : α → α) (eq_compl : compl = (by infer_instance : Compl α).compl)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) :
    CompleteDistribLattice α where
  toFrame := Frame.copy (@CompleteDistribLattice.toFrame α c) le eq_le top eq_top bot eq_bot sup
    eq_sup inf eq_inf himp eq_himp compl eq_compl sSup eq_sSup sInf eq_sInf
  __ := Coframe.copy (@CompleteDistribLattice.toCoframe α c) le eq_le top eq_top bot eq_bot sup
    eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot sSup eq_sSup sInf eq_sInf

/-- A function to create a provable equal copy of a conditionally complete lattice
with possibly different definitional equalities. -/
@[instance_reducible]
/-
**ConditionallyCompleteLattice.copy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ConditionallyCompleteLattice.copy (c : ConditionallyCompleteLattice α) (le
 : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le) (sup : α -> α ->
 α) (eq_sup : sup = (by infer_instance : Max α).max) (inf : α -> α -> α) (eq_inf
 : inf = (by infer_instance : Min α).min) (sSup : Set α -> α) (eq_sSup : sSup = 
(by infer_instance : SupSet α).sSup) (sInf : Set α -> α) (eq_sInf : sInf = (by i
nfer_instance : InfSet α).sInf) : ConditionallyCompleteLattice α where toLattice
参数：c : ConditionallyCompleteLattice α；le : α -> α -> Prop；eq_le : le = (by infer
_instance : LE α).le；sup : α -> α -> α；eq_sup : sup = (by infer_instance : Max α
).max；inf : α -> α -> α；eq_inf : inf = (by infer_instance : Min α).min；sSup : Se
t α -> α；eq_sSup : sSup = (by infer_instance : SupSet α).sSup；sInf : Set α -> α；
eq_sInf : sInf = (by infer_instance : InfSet α).sInf。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function to create a provable equal copy of a conditionally complete lattice
with possibly different definitional equalities.
-/
def ConditionallyCompleteLattice.copy (c : ConditionallyCompleteLattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) :
    ConditionallyCompleteLattice α where
  toLattice := Lattice.copy (@ConditionallyCompleteLattice.toLattice α c)
    le eq_le sup eq_sup inf eq_inf
  sSup := sSup
  sInf := sInf
  isLUB_csSup := by subst_vars; exact c.isLUB_csSup
  isGLB_csInf := by subst_vars; exact c.isGLB_csInf
