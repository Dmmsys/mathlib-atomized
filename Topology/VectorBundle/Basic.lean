/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Patrick Massot, Floris van Doorn
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Vector bundles

In this file we define (topological) vector bundles.

Let `B` be the base space, let `F` be a normed space over a normed field `R`, and let
`E : B → Type*` be a `FiberBundle` with fiber `F`, in which, for each `x`, the fiber `E x` is a
topological vector space over `R`.

To have a vector bundle structure on `Bundle.TotalSpace F E`, one should additionally have the
following properties:

* The bundle trivializations in the trivialization atlas should be continuous linear equivs in the
  fibers;
* For any two trivializations `e`, `e'` in the atlas the transition function considered as a map
  from `B` into `F →L[R] F` is continuous on `e.baseSet ∩ e'.baseSet` with respect to the operator
  norm topology on `F →L[R] F`.

If these conditions are satisfied, we register the typeclass `VectorBundle R F E`.

We define constructions on vector bundles like pullbacks and direct sums in other files.

## Main Definitions

* `Bundle.Trivialization.IsLinear`: a class stating that a trivialization is fiberwise linear
  on its base set.
* `Bundle.Trivialization.linearEquivAt` and `Bundle.Trivialization.continuousLinearMapAt` are the
  (continuous) linear fiberwise equivalences a trivialization induces.
* They have forward maps `Bundle.Trivialization.linearMapAt` /
  `Bundle.Trivialization.continuousLinearMapAt` and inverses `Bundle.Trivialization.symmₗ` /
  `Bundle.Trivialization.symmL`. Note that these are all defined
  everywhere, since they are extended using the zero function.
* `Bundle.Trivialization.coordChangeL` is the coordinate change induced by two trivializations.
  It only makes sense on the intersection of their base sets,
  but is extended outside it using the identity.
* Given a continuous (semi)linear map between `E x` and `E' y` where `E` and `E'` are bundles over
  possibly different base sets, `ContinuousLinearMap.inCoordinates` turns this into a continuous
  (semi)linear map between the chosen fibers of those bundles.

## Implementation notes

The implementation choices in the vector bundle definition are discussed in the "Implementation
notes" section of `Mathlib/Topology/FiberBundle/Basic.lean`.

## Tags
Vector bundle
-/

@[expose] public section

noncomputable section

open Bundle Set Topology

variable (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)

section TopologicalVectorSpace

variable {F E}
variable [Semiring R] [TopologicalSpace F] [TopologicalSpace B]

/-- A mixin class for `Pretrivialization`, stating that a pretrivialization is fiberwise linear with
respect to given module structures on its fibers and the model fiber. -/
/-
**Bundle.Pretrivialization.IsLinear** 是 Mathlib 中的一个归纳类型，位于命名空间 `Bundle.Pretrivi
alization`。
形式化陈述：(R : Type u_1) →   {B : Type u_2} →     {F : Type u_3} →       {E : B → Ty
pe u_4} →         [inst : Semiring R] →           [inst_1 : TopologicalSpace F] 
→             [inst_2 : TopologicalSpace B] →               [inst_3 : AddCommMon
oid F] →                 [_root_.Module R F] →                   [inst_5 : (x : 
B) → AddCommMonoid (E x)] →                     [(x : B) → _root_.Module R (E x)
] → Bundle.Pretrivialization F Bundle.TotalSpace.proj → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mixin class for `Pretrivialization`, stating that a pretrivialization is fiber
wise linear with
respect to given module structures on its fibers and the model fiber.
-/
protected class Bundle.Pretrivialization.IsLinear [AddCommMonoid F] [Module R F]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)] (e : Pretrivialization F (π F E)) : Prop where
  linear : ∀ b ∈ e.baseSet, IsLinearMap R fun x : E b => (e ⟨b, x⟩).2

namespace Bundle.Pretrivialization

variable (e : Pretrivialization F (π F E)) {x : TotalSpace F E} {b : B} {y : E b}

/-
**Bundle.Pretrivialization.linear** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretrivializ
ation`。
形式化陈述：linear [AddCommMonoid F] [Module R F] [forall x, AddCommMonoid (E x)] [for
all x, Module R (E x)] [e.IsLinear R] {b : B} (hb : b in e.baseSet) : IsLinearMa
p R fun x : E b => (e ⟨b, x⟩).2
参数：E x；E x；hb : b in e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.IsLinear.linear`：∀ {R : Type u_1} {B : Type u_2
} {F : Type u_3} {E : B → Type u_4} {inst : Semiring R} {inst_1 : TopologicalSpa
ce F}   {inst_2 : TopologicalS…
-/
theorem linear [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
    [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet) :
    IsLinearMap R fun x : E b => (e ⟨b, x⟩).2 :=
  IsLinear.linear b hb

variable [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]

open scoped Classical in
/-- A fiberwise linear inverse to `e`. -/
/-
**Bundle.Pretrivialization.symm** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pretrivializat
ion`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {E : B → Type u_3} →       [inst :
 TopologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [∀ (x :
 B), Nonempty (E x)] → Bundle.Pretrivialization F Bundle.TotalSpace.proj → (b : 
B) → F → E b
参数：x : B；E x；b : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fiberwise linear inverse to `e`.
-/
protected def symmₗ (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) : F →ₗ[R] E b := by
  refine if hb : b ∈ e.baseSet then IsLinearMap.mk' (e.symm b) ?_ else 0
  exact (((e.linear R hb).mk' _).inverse (e.symm b) (e.symm_apply_apply_mk hb) fun v ↦
    congr_arg Prod.snd <| e.apply_mk_symm hb v).isLinear

@[simp]
/-
**Bundle.Pretrivialization.symm** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pretrivializat
ion`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {E : B → Type u_3} →       [inst :
 TopologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [∀ (x :
 B), Nonempty (E x)] → Bundle.Pretrivialization F Bundle.TotalSpace.proj → (b : 
B) → F → E b
参数：x : B；E x；b : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symmₗ_apply (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet)
    (y : F) : e.symmₗ R b y = e.symm b y := by
  simp [Pretrivialization.symmₗ, hb]

@[simp]
/-
**Bundle.Pretrivialization.symm** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pretrivializat
ion`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {E : B → Type u_3} →       [inst :
 TopologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [∀ (x :
 B), Nonempty (E x)] → Bundle.Pretrivialization F Bundle.TotalSpace.proj → (b : 
B) → F → E b
参数：x : B；E x；b : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symmₗ_apply_of_notMem (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) (y : F) : e.symmₗ R b y = 0 := by
  simp [Pretrivialization.symmₗ, hb]

/-- A pretrivialization for a vector bundle defines linear equivalences between the
fibers and the model space. -/
@[simps -fullyApplied]
/-
**Bundle.Pretrivialization.linearEquivAt** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pretr
ivialization`。
形式化陈述：linearEquivAt (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) (hb
 : b in e.baseSet) : E b ≃ₗ[R] F where toFun y
参数：e : Pretrivialization F (π F E)；b : B；hb : b in e.baseSet。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pretrivialization for a vector bundle defines linear equivalences between the
fibers and the model space.
-/
def linearEquivAt (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) (hb : b ∈ e.baseSet) :
    E b ≃ₗ[R] F where
  toFun y := (e ⟨b, y⟩).2
  invFun := e.symm b
  left_inv := e.symm_apply_apply_mk hb
  right_inv v := by simp_rw [e.apply_mk_symm hb v]
  map_add' v w := (e.linear R hb).map_add v w
  map_smul' c v := (e.linear R hb).map_smul c v

open scoped Classical in
/-- A fiberwise linear map equal to `e` on `e.baseSet`. -/
/-
**Bundle.Pretrivialization.linearMapAt** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pretriv
ialization`。
形式化陈述：(R : Type u_1) →   {B : Type u_2} →     {F : Type u_3} →       {E : B → Ty
pe u_4} →         [inst : Semiring R] →           [inst_1 : TopologicalSpace F] 
→             [inst_2 : TopologicalSpace B] →               [inst_3 : AddCommMon
oid F] →                 [inst_4 : _root_.Module R F] →                   [inst_
5 : (x : B) → AddCommMonoid (E x)] →                     [inst_6 : (x : B) → _ro
ot_.Module R (E x)] →                       (e : Bundle.Pretrivialization F Bund
le.TotalSpace.proj) →                         [Bundle.Pretrivialization.IsLinear
 R e] → (b : B) → E b →ₗ[R] F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fiberwise linear map equal to `e` on `e.baseSet`.
-/
protected def linearMapAt (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) : E b →ₗ[R] F :=
  if hb : b ∈ e.baseSet then e.linearEquivAt R b hb else 0

variable {R}

open scoped Classical in
/-
**Bundle.Pretrivialization.coe_linearMapAt** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pre
trivialization`。
形式化陈述：coe_linearMapAt (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) :
 ⇑(e.linearMapAt R b) = fun y => if b in e.baseSet then (e ⟨b, y⟩).2 else 0
参数：e : Pretrivialization F (π F E)；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.linearMapAt.eq_1`：∀ (R : Type u_1) {B : Type u_
2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSp
ace F]   [inst_2 : TopologicalS…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem coe_linearMapAt (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) :
    ⇑(e.linearMapAt R b) = fun y => if b ∈ e.baseSet then (e ⟨b, y⟩).2 else 0 := by
  rw [Pretrivialization.linearMapAt]
  split_ifs <;> rfl

@[simp]
/-
**Bundle.Pretrivialization.coe_linearMapAt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Bun
dle.Pretrivialization`。
形式化陈述：coe_linearMapAt_of_mem (e : Pretrivialization F (π F E)) [e.IsLinear R] {b
 : B} (hb : b in e.baseSet) : ⇑(e.linearMapAt R b) = fun y => (e ⟨b, y⟩).2
参数：e : Pretrivialization F (π F E)；hb : b in e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.coe_linearMapAt`：coe_linearMapAt (e : Pretrivia
lization F (π F E)) [e.IsLinear R] (b : B) : ⇑(e.linearMapAt R b) = fun y => if 
b in e.baseSet then (e ⟨b, y⟩)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_linearMapAt_of_mem (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) : ⇑(e.linearMapAt R b) = fun y => (e ⟨b, y⟩).2 := by
  simp_rw [coe_linearMapAt, if_pos hb]

open scoped Classical in
/-
**Bundle.Pretrivialization.linearMapAt_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.P
retrivialization`。
形式化陈述：linearMapAt_apply (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
 (y : E b) : e.linearMapAt R b y = if b in e.baseSet then (e ⟨b, y⟩).2 else 0
参数：e : Pretrivialization F (π F E)；y : E b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.coe_linearMapAt`：coe_linearMapAt (e : Pretrivia
lization F (π F E)) [e.IsLinear R] (b : B) : ⇑(e.linearMapAt R b) = fun y => if 
b in e.baseSet then (e ⟨b, y⟩)…
-/
theorem linearMapAt_apply (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B} (y : E b) :
    e.linearMapAt R b y = if b ∈ e.baseSet then (e ⟨b, y⟩).2 else 0 := by
  rw [coe_linearMapAt]
/-
**Bundle.Pretrivialization.linearMapAt_def_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Bun
dle.Pretrivialization`。
形式化陈述：linearMapAt_def_of_mem (e : Pretrivialization F (π F E)) [e.IsLinear R] {b
 : B} (hb : b in e.baseSet) : e.linearMapAt R b = e.linearEquivAt R b hb
参数：e : Pretrivialization F (π F E)；hb : b in e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem linearMapAt_def_of_mem (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) : e.linearMapAt R b = e.linearEquivAt R b hb :=
  dif_pos hb
/-
**Bundle.Pretrivialization.linearMapAt_def_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `
Bundle.Pretrivialization`。
形式化陈述：linearMapAt_def_of_notMem (e : Pretrivialization F (π F E)) [e.IsLinear R]
 {b : B} (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0
参数：e : Pretrivialization F (π F E)；hb : b ∉ e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem linearMapAt_def_of_notMem (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0 :=
  dif_neg hb
/-
**Bundle.Pretrivialization.linearMapAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Bundle
.Pretrivialization`。
形式化陈述：linearMapAt_eq_zero (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : 
B} (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0
参数：e : Pretrivialization F (π F E)；hb : b ∉ e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem linearMapAt_eq_zero (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0 :=
  dif_neg hb
/-
**Bundle.Pretrivialization.symm** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pretrivializat
ion`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {E : B → Type u_3} →       [inst :
 TopologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [∀ (x :
 B), Nonempty (E x)] → Bundle.Pretrivialization F Bundle.TotalSpace.proj → (b : 
B) → F → E b
参数：x : B；E x；b : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symmₗ_linearMapAt (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) (y : E b) : e.symmₗ R b (e.linearMapAt R b y) = y := by simp [hb]
/-
**Bundle.Pretrivialization.linearMapAt_symm** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pr
etrivialization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linearMapAt_symmₗ (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) (y : F) : e.linearMapAt R b (e.symmₗ R b y) = y := by simp [hb]

end Pretrivialization

variable [TopologicalSpace (TotalSpace F E)]

/-- A mixin class for `Bundle.Trivialization`, stating that a trivialization is fiberwise linear
with respect to given module structures on its fibers and the model fiber. -/
/-
**Bundle.Trivialization.IsLinear** 是 Mathlib 中的一个归纳类型，位于命名空间 `Bundle.Trivializat
ion`。
形式化陈述：(R : Type u_1) →   {B : Type u_2} →     {F : Type u_3} →       {E : B → Ty
pe u_4} →         [inst : Semiring R] →           [inst_1 : TopologicalSpace F] 
→             [inst_2 : TopologicalSpace B] →               [inst_3 : Topologica
lSpace (Bundle.TotalSpace F E)] →                 [inst_4 : AddCommMonoid F] →  
                 [_root_.Module R F] →                     [inst_6 : (x : B) → A
ddCommMonoid (E x)] →                       [(x : B) → _root_.Module R (E x)] → 
Bundle.Trivialization F Bundle.TotalSpace.proj → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mixin class for `Bundle.Trivialization`, stating that a trivialization is fibe
rwise linear
with respect to given module structures on its fibers and the model fiber.
-/
protected class Trivialization.IsLinear [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)]
  [∀ x, Module R (E x)] (e : Trivialization F (π F E)) : Prop where
  linear : ∀ b ∈ e.baseSet, IsLinearMap R fun x : E b => (e ⟨b, x⟩).2

namespace Trivialization

variable (e : Trivialization F (π F E)) {x : TotalSpace F E} {b : B} {y : E b}

/-
**Bundle.Trivialization.linear** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivialization`
。
形式化陈述：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)]   (e : Bundle.Trivialization F Bun
dle.TotalSpace.proj) [inst_4 : AddCommMonoid F] [inst_5 : _root_.Module R F]   [
inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : B) → _root_.Module R (E x
)]   [Bundle.Trivialization.IsLinear R e] {b : B}, b ∈ e.baseSet → IsLinearMap R
 fun y => (↑e ⟨b, y⟩).2
参数：R : Type u_1；Bundle.TotalSpace F E；e : Bundle.Trivialization F Bundle.TotalSp
ace.proj；x : B；E x；x : B；E x；↑e ⟨b, y⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.IsLinear.linear`：∀ {R : Type u_1} {B : Type u_2} {
F : Type u_3} {E : B → Type u_4} {inst : Semiring R} {inst_1 : TopologicalSpace 
F}   {inst_2 : TopologicalS…
-/
protected theorem linear [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)]
    [∀ x, Module R (E x)] [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet) :
    IsLinearMap R fun y : E b => (e ⟨b, y⟩).2 :=
  Trivialization.IsLinear.linear b hb
/-
**Bundle.Trivialization.toPretrivialization.isLinear** 是 Mathlib 中的一个定理，位于命名空间 `
Bundle.Trivialization.toPretrivialization`。
形式化陈述：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)]   (e : Bundle.Trivialization F Bun
dle.TotalSpace.proj) [inst_4 : AddCommMonoid F] [inst_5 : _root_.Module R F]   [
inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : B) → _root_.Module R (E x
)]   [Bundle.Trivialization.IsLinear R e], Bundle.Pretrivialization.IsLinear R e
.toPretrivialization
参数：R : Type u_1；Bundle.TotalSpace F E；e : Bundle.Trivialization F Bundle.TotalSp
ace.proj；x : B；E x；x : B；E x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.IsLinear.linear`：∀ {R : Type u_1} {B : Type u_2} {
F : Type u_3} {E : B → Type u_4} {inst : Semiring R} {inst_1 : TopologicalSpace 
F}   {inst_2 : TopologicalS…
-/
instance toPretrivialization.isLinear [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)]
    [∀ x, Module R (E x)] [e.IsLinear R] : e.toPretrivialization.IsLinear R :=
  { (‹_› : e.IsLinear R) with }

variable [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]

/-- A trivialization for a vector bundle defines linear equivalences between the
fibers and the model space. -/
/-
**Bundle.Trivialization.linearEquivAt** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Triviali
zation`。
形式化陈述：(R : Type u_1) →   {B : Type u_2} →     {F : Type u_3} →       {E : B → Ty
pe u_4} →         [inst : Semiring R] →           [inst_1 : TopologicalSpace F] 
→             [inst_2 : TopologicalSpace B] →               [inst_3 : Topologica
lSpace (Bundle.TotalSpace F E)] →                 [inst_4 : AddCommMonoid F] →  
                 [inst_5 : _root_.Module R F] →                     [inst_6 : (x
 : B) → AddCommMonoid (E x)] →                       [inst_7 : (x : B) → _root_.
Module R (E x)] →                         (e : Bundle.Trivialization F Bundle.To
talSpace.proj) →                           [Bundle.Trivialization.IsLinear R e] 
→ (b : B) → b ∈ e.baseSet → E b ≃ₗ[R] F
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.toPretrivialization.isLinear`：∀ (R : Type u_1) {B 
: Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topo
logicalSpace F]   [inst_2 : TopologicalS…

--- 原说明 ---
A trivialization for a vector bundle defines linear equivalences between the
fibers and the model space.
-/
def linearEquivAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) (hb : b ∈ e.baseSet) :
    E b ≃ₗ[R] F :=
  e.toPretrivialization.linearEquivAt R b hb

variable {R}

@[simp]
/-
**Bundle.Trivialization.linearEquivAt_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Tr
ivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e : Bundle.Trivialization F Bundle.TotalSpace.pro
j) [inst_8 : Bundle.Trivialization.IsLinear R e] (b : B)   (hb : b ∈ e.baseSet) 
(v : E b), (Bundle.Trivialization.linearEquivAt R e b hb) v = (↑e ⟨b, v⟩).2
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e : Bundle.Trivialization F Bundle.
TotalSpace.proj；b : B；hb : b ∈ e.baseSet；v : E b；Bundle.Trivialization.linearEqu
ivAt R e b hb；↑e ⟨b, v⟩。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linearEquivAt_apply (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
    (hb : b ∈ e.baseSet) (v : E b) : e.linearEquivAt R b hb v = (e ⟨b, v⟩).2 :=
  rfl

@[simp]
/-
**Bundle.Trivialization.linearEquivAt_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bund
le.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e : Bundle.Trivialization F Bundle.TotalSpace.pro
j) [inst_8 : Bundle.Trivialization.IsLinear R e] (b : B)   (hb : b ∈ e.baseSet) 
(v : F), (Bundle.Trivialization.linearEquivAt R e b hb).symm v = e.symm b v
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e : Bundle.Trivialization F Bundle.
TotalSpace.proj；b : B；hb : b ∈ e.baseSet；v : F；Bundle.Trivialization.linearEquiv
At R e b hb。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linearEquivAt_symm_apply (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
    (hb : b ∈ e.baseSet) (v : F) : (e.linearEquivAt R b hb).symm v = e.symm b v :=
  rfl

variable (R) in
/-- A fiberwise linear inverse to `e`. -/
/-
**Bundle.Trivialization.symm** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivialization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {E : B → Type u_3} →       [inst :
 TopologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [inst_2
 : TopologicalSpace (Bundle.TotalSpace F E)] →             [∀ (x : B), Nonempty 
(E x)] → Bundle.Trivialization F Bundle.TotalSpace.proj → (b : B) → F → E b
参数：Bundle.TotalSpace F E；x : B；E x；b : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fiberwise linear inverse to `e`.
-/
protected def symmₗ (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : F →ₗ[R] E b :=
  e.toPretrivialization.symmₗ R b
/-
**Bundle.Trivialization.coe_symm** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializatio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symmₗ (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet) :
    ⇑(e.symmₗ R b) = e.symm b := by
  ext y; exact e.toPretrivialization.symmₗ_apply R hb y

@[simp]
/-
**Bundle.Trivialization.symm** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivialization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {E : B → Type u_3} →       [inst :
 TopologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [inst_2
 : TopologicalSpace (Bundle.TotalSpace F E)] →             [∀ (x : B), Nonempty 
(E x)] → Bundle.Trivialization F Bundle.TotalSpace.proj → (b : B) → F → E b
参数：Bundle.TotalSpace F E；x : B；E x；b : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symmₗ_apply (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet)
    (y : F) : e.symmₗ R b y = e.symm b y :=
  e.toPretrivialization.symmₗ_apply R hb y

@[simp]
/-
**Bundle.Trivialization.symm** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivialization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {E : B → Type u_3} →       [inst :
 TopologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [inst_2
 : TopologicalSpace (Bundle.TotalSpace F E)] →             [∀ (x : B), Nonempty 
(E x)] → Bundle.Trivialization F Bundle.TotalSpace.proj → (b : B) → F → E b
参数：Bundle.TotalSpace F E；x : B；E x；b : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symmₗ_apply_of_notMem (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) (y : F) : e.symmₗ R b y = 0 :=
  e.toPretrivialization.symmₗ_apply_of_notMem R hb y

variable (R) in
/-- A fiberwise linear map equal to `e` on `e.baseSet`. -/
/-
**Bundle.Trivialization.linearMapAt** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivializa
tion`。
形式化陈述：(R : Type u_1) →   {B : Type u_2} →     {F : Type u_3} →       {E : B → Ty
pe u_4} →         [inst : Semiring R] →           [inst_1 : TopologicalSpace F] 
→             [inst_2 : TopologicalSpace B] →               [inst_3 : Topologica
lSpace (Bundle.TotalSpace F E)] →                 [inst_4 : AddCommMonoid F] →  
                 [inst_5 : _root_.Module R F] →                     [inst_6 : (x
 : B) → AddCommMonoid (E x)] →                       [inst_7 : (x : B) → _root_.
Module R (E x)] →                         (e : Bundle.Trivialization F Bundle.To
talSpace.proj) →                           [Bundle.Trivialization.IsLinear R e] 
→ (b : B) → E b →ₗ[R] F
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.toPretrivialization.isLinear`：∀ (R : Type u_1) {B 
: Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topo
logicalSpace F]   [inst_2 : TopologicalS…

--- 原说明 ---
A fiberwise linear map equal to `e` on `e.baseSet`.
-/
protected def linearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : E b →ₗ[R] F :=
  e.toPretrivialization.linearMapAt R b

open scoped Classical in
/-
**Bundle.Trivialization.coe_linearMapAt** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivia
lization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e : Bundle.Trivialization F Bundle.TotalSpace.pro
j) [inst_8 : Bundle.Trivialization.IsLinear R e] (b : B),   ⇑(Bundle.Trivializat
ion.linearMapAt R e b) = fun y => if b ∈ e.baseSet then (↑e ⟨b, y⟩).2 else 0
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e : Bundle.Trivialization F Bundle.
TotalSpace.proj；b : B；Bundle.Trivialization.linearMapAt R e b；↑e ⟨b, y⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.coe_linearMapAt`：coe_linearMapAt (e : Pretrivia
lization F (π F E)) [e.IsLinear R] (b : B) : ⇑(e.linearMapAt R b) = fun y => if 
b in e.baseSet then (e ⟨b, y⟩)…
· 使用定理 `Bundle.Trivialization.toPretrivialization.isLinear`：∀ (R : Type u_1) {B 
: Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topo
logicalSpace F]   [inst_2 : TopologicalS…
-/
theorem coe_linearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) :
    ⇑(e.linearMapAt R b) = fun y => if b ∈ e.baseSet then (e ⟨b, y⟩).2 else 0 :=
  e.toPretrivialization.coe_linearMapAt b

@[simp]
/-
**Bundle.Trivialization.coe_linearMapAt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Bundle
.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e : Bundle.Trivialization F Bundle.TotalSpace.pro
j) [inst_8 : Bundle.Trivialization.IsLinear R e] {b : B},   b ∈ e.baseSet → ⇑(Bu
ndle.Trivialization.linearMapAt R e b) = fun y => (↑e ⟨b, y⟩).2
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e : Bundle.Trivialization F Bundle.
TotalSpace.proj；Bundle.Trivialization.linearMapAt R e b；↑e ⟨b, y⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coe_linearMapAt`：∀ {R : Type u_1} {B : Type u_2} {
F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace 
F]   [inst_2 : TopologicalS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_linearMapAt_of_mem (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) : ⇑(e.linearMapAt R b) = fun y => (e ⟨b, y⟩).2 := by
  simp_rw [coe_linearMapAt, if_pos hb]

open scoped Classical in
/-
**Bundle.Trivialization.linearMapAt_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triv
ialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e : Bundle.Trivialization F Bundle.TotalSpace.pro
j) [inst_8 : Bundle.Trivialization.IsLinear R e] {b : B} (y : E b),   (Bundle.Tr
ivialization.linearMapAt R e b) y = if b ∈ e.baseSet then (↑e ⟨b, y⟩).2 else 0
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e : Bundle.Trivialization F Bundle.
TotalSpace.proj；y : E b；Bundle.Trivialization.linearMapAt R e b；↑e ⟨b, y⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coe_linearMapAt`：∀ {R : Type u_1} {B : Type u_2} {
F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace 
F]   [inst_2 : TopologicalS…
-/
theorem linearMapAt_apply (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (y : E b) :
    e.linearMapAt R b y = if b ∈ e.baseSet then (e ⟨b, y⟩).2 else 0 := by
  rw [coe_linearMapAt]
/-
**Bundle.Trivialization.linearMapAt_def_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Bundle
.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e : Bundle.Trivialization F Bundle.TotalSpace.pro
j) [inst_8 : Bundle.Trivialization.IsLinear R e] {b : B}   (hb : b ∈ e.baseSet),
 Bundle.Trivialization.linearMapAt R e b = ↑(Bundle.Trivialization.linearEquivAt
 R e b hb)
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e : Bundle.Trivialization F Bundle.
TotalSpace.proj；hb : b ∈ e.baseSet；Bundle.Trivialization.linearEquivAt R e b hb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Bundle.Trivialization.toPretrivialization.isLinear`：∀ (R : Type u_1) {B 
: Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topo
logicalSpace F]   [inst_2 : TopologicalS…
-/
theorem linearMapAt_def_of_mem (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) : e.linearMapAt R b = e.linearEquivAt R b hb :=
  dif_pos hb
/-
**Bundle.Trivialization.linearMapAt_def_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Bun
dle.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e : Bundle.Trivialization F Bundle.TotalSpace.pro
j) [inst_8 : Bundle.Trivialization.IsLinear R e] {b : B},   b ∉ e.baseSet → Bund
le.Trivialization.linearMapAt R e b = 0
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e : Bundle.Trivialization F Bundle.
TotalSpace.proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Bundle.Trivialization.toPretrivialization.isLinear`：∀ (R : Type u_1) {B 
: Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topo
logicalSpace F]   [inst_2 : TopologicalS…
-/
theorem linearMapAt_def_of_notMem (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0 :=
  dif_neg hb
/-
**Bundle.Trivialization.symm_linearMapAt** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivi
alization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e : Bundle.Trivialization F Bundle.TotalSpace.pro
j) [inst_8 : Bundle.Trivialization.IsLinear R e] {b : B},   b ∈ e.baseSet → ∀ (y
 : E b), e.symm b ((Bundle.Trivialization.linearMapAt R e b) y) = y
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e : Bundle.Trivialization F Bundle.
TotalSpace.proj；y : E b；(Bundle.Trivialization.linearMapAt R e b) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.symm.congr_simp`：∀ {B : Type u_1} {F : Type u_2} {
E : B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [i
nst_2 : TopologicalSpace (B…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Bundle.Trivialization.coe_linearMapAt_of_mem`：∀ {R : Type u_1} {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topologica
lSpace F]   [inst_2 : TopologicalS…
· 使用定理 `Bundle.Trivialization.symm_apply_apply_mk`：∀ {B : Type u_1} {F : Type u_
2} {E : B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] 
  [inst_2 : TopologicalSpace (B…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_linearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet)
    (y : E b) : e.symm b (e.linearMapAt R b y) = y := by
  simp [hb]
/-
**Bundle.Trivialization.symm** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivialization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {E : B → Type u_3} →       [inst :
 TopologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [inst_2
 : TopologicalSpace (Bundle.TotalSpace F E)] →             [∀ (x : B), Nonempty 
(E x)] → Bundle.Trivialization F Bundle.TotalSpace.proj → (b : B) → F → E b
参数：Bundle.TotalSpace F E；x : B；E x；b : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symmₗ_linearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet)
    (y : E b) : e.symmₗ R b (e.linearMapAt R b y) = y :=
  e.toPretrivialization.symmₗ_linearMapAt hb y

@[simp]
/-
**Bundle.Trivialization.linearMapAt_symm** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivi
alization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e : Bundle.Trivialization F Bundle.TotalSpace.pro
j) [inst_8 : Bundle.Trivialization.IsLinear R e] {b : B},   b ∈ e.baseSet → ∀ (y
 : F), (Bundle.Trivialization.linearMapAt R e b) (e.symm b y) = y
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e : Bundle.Trivialization F Bundle.
TotalSpace.proj；y : F；Bundle.Trivialization.linearMapAt R e b；e.symm b y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Bundle.Trivialization.coe_linearMapAt_of_mem`：∀ {R : Type u_1} {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topologica
lSpace F]   [inst_2 : TopologicalS…
· 使用定理 `Bundle.Trivialization.apply_mk_symm`：∀ {B : Type u_1} {F : Type u_2} {E 
: B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalSpace (B…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearMapAt_symm (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet)
    (y : F) : e.linearMapAt R b (e.symm b y) = y := by
  simp [hb]
/-
**Bundle.Trivialization.linearMapAt_symm** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivi
alization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e : Bundle.Trivialization F Bundle.TotalSpace.pro
j) [inst_8 : Bundle.Trivialization.IsLinear R e] {b : B},   b ∈ e.baseSet → ∀ (y
 : F), (Bundle.Trivialization.linearMapAt R e b) (e.symm b y) = y
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e : Bundle.Trivialization F Bundle.
TotalSpace.proj；y : F；Bundle.Trivialization.linearMapAt R e b；e.symm b y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Bundle.Trivialization.coe_linearMapAt_of_mem`：∀ {R : Type u_1} {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topologica
lSpace F]   [inst_2 : TopologicalS…
· 使用定理 `Bundle.Trivialization.apply_mk_symm`：∀ {B : Type u_1} {F : Type u_2} {E 
: B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalSpace (B…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearMapAt_symmₗ (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet)
    (y : F) : e.linearMapAt R b (e.symmₗ R b y) = y :=
  e.toPretrivialization.linearMapAt_symmₗ hb y

variable (R) in
open scoped Classical in
/-- A coordinate change function between two trivializations, as a continuous linear equivalence.
  Defined to be the identity when `b` does not lie in the base set of both trivializations. -/
/-
**Bundle.Trivialization.coordChangeL** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivializ
ation`。
形式化陈述：(R : Type u_1) →   {B : Type u_2} →     {F : Type u_3} →       {E : B → Ty
pe u_4} →         [inst : Semiring R] →           [inst_1 : TopologicalSpace F] 
→             [inst_2 : TopologicalSpace B] →               [inst_3 : Topologica
lSpace (Bundle.TotalSpace F E)] →                 [inst_4 : AddCommMonoid F] →  
                 [inst_5 : _root_.Module R F] →                     [inst_6 : (x
 : B) → AddCommMonoid (E x)] →                       [inst_7 : (x : B) → _root_.
Module R (E x)] →                         (e e' : Bundle.Trivialization F Bundle
.TotalSpace.proj) →                           [Bundle.Trivialization.IsLinear R 
e] → [Bundle.Trivialization.IsLinear R e'] → B → F ≃L[R] F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coordinate change function between two trivializations, as a continuous linear
 equivalence.
  Defined to be the identity when `b` does not lie in the base set of both trivi
alizations.
-/
def coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] (b : B) :
    F ≃L[R] F :=
  { toLinearEquiv := if hb : b ∈ e.baseSet ∩ e'.baseSet
      then (e.linearEquivAt R b (hb.1 :)).symm.trans (e'.linearEquivAt R b hb.2)
      else LinearEquiv.refl R F
    continuous_toFun := by
      by_cases hb : b ∈ e.baseSet ∩ e'.baseSet
      · rw [dif_pos hb]
        refine (e'.continuousOn.comp_continuous ?_ ?_).snd
        · exact e.continuousOn_symm.comp_continuous (Continuous.prodMk_right b) fun y =>
            mk_mem_prod hb.1 (mem_univ y)
        · exact fun y => e'.mem_source.mpr hb.2
      · rw [dif_neg hb]
        exact continuous_id
    continuous_invFun := by
      by_cases hb : b ∈ e.baseSet ∩ e'.baseSet
      · rw [dif_pos hb]
        refine (e.continuousOn.comp_continuous ?_ ?_).snd
        · exact e'.continuousOn_symm.comp_continuous (Continuous.prodMk_right b) fun y =>
            mk_mem_prod hb.2 (mem_univ y)
        exact fun y => e.mem_source.mpr hb.1
      · rw [dif_neg hb]
        exact continuous_id }
/-
**Bundle.Trivialization.coe_coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivi
alization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e e' : Bundle.Trivialization F Bundle.TotalSpace.
proj) [inst_8 : Bundle.Trivialization.IsLinear R e]   [inst_9 : Bundle.Trivializ
ation.IsLinear R e'] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet),   ⇑(Bundle.Trivi
alization.coordChangeL R e e' b) =     ⇑((Bundle.Trivialization.linearEquivAt R 
e b ⋯).symm ≪≫ₗ Bundle.Trivialization.linearEquivAt R e' b ⋯)
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj；hb : b ∈ e.baseSet ∩ e'.baseSet；Bundle.Trivialization.coordCh
angeL R e e' b；(Bundle.Trivialization.linearEquivAt R e b ⋯).symm ≪≫ₗ Bundle.Tri
vialization.linearEquivAt R e' b ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem coe_coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    ⇑(coordChangeL R e e' b) = (e.linearEquivAt R b hb.1).symm.trans (e'.linearEquivAt R b hb.2) :=
  congr_arg (fun f : F ≃ₗ[R] F ↦ ⇑f) (dif_pos hb)
/-
**Bundle.Trivialization.coe_coordChangeL'** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triv
ialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e e' : Bundle.Trivialization F Bundle.TotalSpace.
proj) [inst_8 : Bundle.Trivialization.IsLinear R e]   [inst_9 : Bundle.Trivializ
ation.IsLinear R e'] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet),   ↑(Bundle.Trivi
alization.coordChangeL R e e' b) =     (Bundle.Trivialization.linearEquivAt R e 
b ⋯).symm ≪≫ₗ Bundle.Trivialization.linearEquivAt R e' b ⋯
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj；hb : b ∈ e.baseSet ∩ e'.baseSet；Bundle.Trivialization.coordCh
angeL R e e' b；Bundle.Trivialization.linearEquivAt R e b ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.coe_injective`：coe_injective : @Injective (M ≃ₛₗ[σ] M₂) (M -
> M₂) DFunLike.coe
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Bundle.Trivialization.coe_coordChangeL`：∀ {R : Type u_1} {B : Type u_2} 
{F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace
 F]   [inst_2 : TopologicalS…
-/
theorem coe_coordChangeL' (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (coordChangeL R e e' b).toLinearEquiv =
      (e.linearEquivAt R b hb.1).symm.trans (e'.linearEquivAt R b hb.2) :=
  LinearEquiv.coe_injective (coe_coordChangeL _ _ hb)
/-
**Bundle.Trivialization.symm_coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triv
ialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e e' : Bundle.Trivialization F Bundle.TotalSpace.
proj) [inst_8 : Bundle.Trivialization.IsLinear R e]   [inst_9 : Bundle.Trivializ
ation.IsLinear R e'] {b : B},   b ∈ e'.baseSet ∩ e.baseSet →     (Bundle.Trivial
ization.coordChangeL R e e' b).symm = Bundle.Trivialization.coordChangeL R e' e 
b
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj；Bundle.Trivialization.coordChangeL R e e' b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.toLinearEquiv_injective`：toLinearEquiv_injective :
 Function.Injective (toLinearEquiv : (M₁ ≃SL[σ₁₂] M₂) -> M₁ ≃ₛₗ[σ₁₂] M₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coe_coordChangeL'`：∀ {R : Type u_1} {B : Type u_2}
 {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpac
e F]   [inst_2 : TopologicalS…
· 使用定理 `ContinuousLinearEquiv.toLinearEquiv_symm`：toLinearEquiv_symm (e : M₁ ≃SL
[σ₁₂] M₂) : e.symm.toLinearEquiv = e.toLinearEquiv.symm
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
· 使用定理 `LinearEquiv.trans_symm`：trans_symm : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).sy
mm = e₂₃.symm.trans e₁₂.symm
· 使用定理 `LinearEquiv.symm_symm`：symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e
-/
theorem symm_coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b ∈ e'.baseSet ∩ e.baseSet) : (e.coordChangeL R e' b).symm = e'.coordChangeL R e b := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  rw [coe_coordChangeL' e' e hb, (coordChangeL R e e' b).toLinearEquiv_symm,
    coe_coordChangeL' e e' hb.symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm]
/-
**Bundle.Trivialization.coordChangeL_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Tri
vialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e e' : Bundle.Trivialization F Bundle.TotalSpace.
proj) [inst_8 : Bundle.Trivialization.IsLinear R e]   [inst_9 : Bundle.Trivializ
ation.IsLinear R e'] {b : B},   b ∈ e.baseSet ∩ e'.baseSet → ∀ (y : F), (Bundle.
Trivialization.coordChangeL R e e' b) y = (↑e' ⟨b, e.symm b y⟩).2
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj；y : F；Bundle.Trivialization.coordChangeL R e e' b；↑e' ⟨b, e.s
ymm b y⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Bundle.Trivialization.coe_coordChangeL`：∀ {R : Type u_1} {B : Type u_2} 
{F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace
 F]   [inst_2 : TopologicalS…
-/
theorem coordChangeL_apply (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (y : F) :
    coordChangeL R e e' b y = (e' ⟨b, e.symm b y⟩).2 :=
  congr_fun (coe_coordChangeL e e' hb) y
/-
**Bundle.Trivialization.mk_coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivia
lization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e e' : Bundle.Trivialization F Bundle.TotalSpace.
proj) [inst_8 : Bundle.Trivialization.IsLinear R e]   [inst_9 : Bundle.Trivializ
ation.IsLinear R e'] {b : B},   b ∈ e.baseSet ∩ e'.baseSet → ∀ (y : F), (b, (Bun
dle.Trivialization.coordChangeL R e e' b) y) = ↑e' ⟨b, e.symm b y⟩
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj；y : F；b, (Bundle.Trivialization.coordChangeL R e e' b) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.mk_symm`：∀ {B : Type u_1} {F : Type u_2} {E : B → 
Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : 
TopologicalSpace (B…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Bundle.Trivialization.coe_fst'`：∀ {B : Type u_1} {F : Type u_2} {Z : Typ
e u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B} 
  [inst_2 : Topologi…
· 使用定理 `Bundle.Trivialization.proj_symm_apply'`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Bundle.Trivialization.coordChangeL_apply`：∀ {R : Type u_1} {B : Type u_2
} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpa
ce F]   [inst_2 : TopologicalS…
-/
theorem mk_coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (y : F) :
    (b, coordChangeL R e e' b y) = e' ⟨b, e.symm b y⟩ := by
  ext
  · rw [e.mk_symm hb.1 y, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
  · exact e.coordChangeL_apply e' hb y
/-
**Bundle.Trivialization.apply_symm_apply_eq_coordChangeL** 是 Mathlib 中的一个定理，位于命名
空间 `Bundle.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e e' : Bundle.Trivialization F Bundle.TotalSpace.
proj) [inst_8 : Bundle.Trivialization.IsLinear R e]   [inst_9 : Bundle.Trivializ
ation.IsLinear R e'] {b : B},   b ∈ e.baseSet ∩ e'.baseSet → ∀ (v : F), ↑e' (↑e.
symm (b, v)) = (b, (Bundle.Trivialization.coordChangeL R e e' b) v)
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj；v : F；↑e.symm (b, v)；b, (Bundle.Trivialization.coordChangeL R
 e e' b) v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.mk_coordChangeL`：∀ {R : Type u_1} {B : Type u_2} {
F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace 
F]   [inst_2 : TopologicalS…
· 使用定理 `Bundle.Trivialization.mk_symm`：∀ {B : Type u_1} {F : Type u_2} {E : B → 
Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : 
TopologicalSpace (B…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem apply_symm_apply_eq_coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R]
    [e'.IsLinear R] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    e' (e.toOpenPartialHomeomorph.symm (b, v)) = (b, e.coordChangeL R e' b v) := by
  rw [e.mk_coordChangeL e' hb, e.mk_symm hb.1]

/-- A version of `Bundle.Trivialization.coordChangeL_apply` that fully unfolds `coordChange`. The
right-hand side is ugly, but has good definitional properties for specifically defined
trivializations. -/
/-
**Bundle.Trivialization.coordChangeL_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Tr
ivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e e' : Bundle.Trivialization F Bundle.TotalSpace.
proj) [inst_8 : Bundle.Trivialization.IsLinear R e]   [inst_9 : Bundle.Trivializ
ation.IsLinear R e'] {b : B},   b ∈ e.baseSet ∩ e'.baseSet → ∀ (y : F), (Bundle.
Trivialization.coordChangeL R e e' b) y = (↑e' (↑e.symm (b, y))).2
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj；y : F；Bundle.Trivialization.coordChangeL R e e' b；↑e' (↑e.sym
m (b, y))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coordChangeL_apply`：∀ {R : Type u_1} {B : Type u_2
} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpa
ce F]   [inst_2 : TopologicalS…
· 使用定理 `Bundle.Trivialization.mk_symm`：∀ {B : Type u_1} {F : Type u_2} {E : B → 
Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : 
TopologicalSpace (B…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A version of `Bundle.Trivialization.coordChangeL_apply` that fully unfolds `coor
dChange`. The
right-hand side is ugly, but has good definitional properties for specifically d
efined
trivializations.
-/
theorem coordChangeL_apply' (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (y : F) :
    coordChangeL R e e' b y = (e' (e.toOpenPartialHomeomorph.symm (b, y))).2 := by
  rw [e.coordChangeL_apply e' hb, e.mk_symm hb.1]
/-
**Bundle.Trivialization.coordChangeL_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundl
e.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
Semiring R] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace B] [inst_
3 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_4 : AddCommMonoid F]   [inst
_5 : _root_.Module R F] [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : 
B) → _root_.Module R (E x)]   (e e' : Bundle.Trivialization F Bundle.TotalSpace.
proj) [inst_8 : Bundle.Trivialization.IsLinear R e]   [inst_9 : Bundle.Trivializ
ation.IsLinear R e'] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet),   ⇑(Bundle.Trivi
alization.coordChangeL R e e' b).symm =     ⇑((Bundle.Trivialization.linearEquiv
At R e' b ⋯).symm ≪≫ₗ Bundle.Trivialization.linearEquivAt R e b ⋯)
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj；hb : b ∈ e.baseSet ∩ e'.baseSet；Bundle.Trivialization.coordCh
angeL R e e' b；(Bundle.Trivialization.linearEquivAt R e' b ⋯).symm ≪≫ₗ Bundle.Tr
ivialization.linearEquivAt R e b ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem coordChangeL_symm_apply (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R]
    {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    ⇑(coordChangeL R e e' b).symm =
      (e'.linearEquivAt R b hb.2).symm.trans (e.linearEquivAt R b hb.1) :=
  congr_arg LinearEquiv.invFun (dif_pos hb)

end Bundle.Trivialization

end TopologicalVectorSpace

section

namespace Bundle

/-- The zero section of a vector bundle -/
/-
**Bundle.zeroSection** 是 Mathlib 中的一个定义，位于命名空间 `Bundle`。
形式化陈述：{B : Type u_2} → (F : Type u_3) → (E : B → Type u_4) → [(x : B) → Zero (E 
x)] → B → Bundle.TotalSpace F E
参数：F : Type u_3；E : B → Type u_4；x : B；E x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zero section of a vector bundle
-/
def zeroSection [∀ x, Zero (E x)] : B → TotalSpace F E := (⟨·, 0⟩)

@[simp, mfld_simps]
/-
**Bundle.zeroSection_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：∀ {B : Type u_2} (F : Type u_3) (E : B → Type u_4) [inst : (x : B) → Zero 
(E x)] (x : B),   (Bundle.zeroSection F E x).proj = x
参数：F : Type u_3；E : B → Type u_4；x : B；E x；x : B；Bundle.zeroSection F E x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zeroSection_proj [∀ x, Zero (E x)] (x : B) : (zeroSection F E x).proj = x :=
  rfl

@[simp, mfld_simps]
/-
**Bundle.zeroSection_snd** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：∀ {B : Type u_2} (F : Type u_3) (E : B → Type u_4) [inst : (x : B) → Zero 
(E x)] (x : B),   (Bundle.zeroSection F E x).snd = 0
参数：F : Type u_3；E : B → Type u_4；x : B；E x；x : B；Bundle.zeroSection F E x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zeroSection_snd [∀ x, Zero (E x)] (x : B) : (zeroSection F E x).2 = 0 :=
  rfl

end Bundle

open Bundle

variable [NontriviallyNormedField R] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
  [NormedAddCommGroup F] [NormedSpace R F] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

/-- The space `Bundle.TotalSpace F E` (for `E : B → Type*` such that each `E x` is a topological
vector space) has a topological vector space structure with fiber `F` (denoted with
`VectorBundle R F E`) if around every point there is a fiber bundle trivialization which is linear
in the fibers. -/
/-
**VectorBundle** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   {B : Type u_2} →     (F : Type u_3) →       (E : B → Ty
pe u_4) →         [inst : NontriviallyNormedField R] →           [inst_1 : (x : 
B) → AddCommMonoid (E x)] →             [(x : B) → _root_.Module R (E x)] →     
          [inst_3 : NormedAddCommGroup F] →                 [NormedSpace R F] → 
                  [inst : TopologicalSpace B] →                     [inst_4 : To
pologicalSpace (Bundle.TotalSpace F E)] →                       [inst_5 : (x : B
) → TopologicalSpace (E x)] → [FiberBundle F E] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space `Bundle.TotalSpace F E` (for `E : B → Type*` such that each `E x` is a
 topological
vector space) has a topological vector space structure with fiber `F` (denoted w
ith
`VectorBundle R F E`) if around every point there is a fiber bundle trivializati
on which is linear
in the fibers.
-/
class VectorBundle : Prop where
  trivialization_linear' : ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e], e.IsLinear R
  continuousOn_coordChange' :
    ∀ (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ContinuousOn (fun b => Trivialization.coordChangeL R e e' b : B → F →L[R] F)
        (e.baseSet ∩ e'.baseSet)

variable {F E}
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) trivialization_linear [VectorBundle R F E] (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] : e.IsLinear R :=
  VectorBundle.trivialization_linear' e
/-
**continuousOn_coordChange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E] [inst_9 : VectorBundle R F E]   (e e' : Bundle.Trivialization F Bundle.
TotalSpace.proj) [inst_10 : MemTrivializationAtlas e]   [inst_11 : MemTrivializa
tionAtlas e'],   ContinuousOn (fun b => ↑(Bundle.Trivialization.coordChangeL R e
 e' b)) (e.baseSet ∩ e'.baseSet)
参数：R : Type u_1；x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e e' : Bundl
e.Trivialization F Bundle.TotalSpace.proj；fun b => ↑(Bundle.Trivialization.coord
ChangeL R e e' b)；e.baseSet ∩ e'.baseSet。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundle.continuousOn_coordChange'`：∀ {R : Type u_1} {B : Type u_2} 
{F : Type u_3} {E : B → Type u_4} {inst : NontriviallyNormedField R}   {inst_1 :
 (x : B) → AddCommMonoid (E …
-/
theorem continuousOn_coordChange [VectorBundle R F E] (e e' : Trivialization F (π F E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContinuousOn (fun b => Trivialization.coordChangeL R e e' b : B → F →L[R] F)
      (e.baseSet ∩ e'.baseSet) :=
  VectorBundle.continuousOn_coordChange' e e'

namespace Bundle.Trivialization

/-- Forward map of `Bundle.Trivialization.continuousLinearEquivAt` (only propositionally equal),
  defined everywhere (`0` outside domain). -/
@[simps -fullyApplied apply]
/-
**Bundle.Trivialization.continuousLinearMapAt** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.
Trivialization`。
形式化陈述：(R : Type u_1) →   {B : Type u_2} →     {F : Type u_3} →       {E : B → Ty
pe u_4} →         [inst : NontriviallyNormedField R] →           [inst_1 : (x : 
B) → AddCommMonoid (E x)] →             [inst_2 : (x : B) → _root_.Module R (E x
)] →               [inst_3 : NormedAddCommGroup F] →                 [inst_4 : N
ormedSpace R F] →                   [inst_5 : TopologicalSpace B] →             
        [inst_6 : TopologicalSpace (Bundle.TotalSpace F E)] →                   
    [inst_7 : (x : B) → TopologicalSpace (E x)] →                         [Fiber
Bundle F E] →                           (e : Bundle.Trivialization F Bundle.Tota
lSpace.proj) →                             [Bundle.Trivialization.IsLinear R e] 
→ (b : B) → E b →L[R] F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forward map of `Bundle.Trivialization.continuousLinearEquivAt` (only proposition
ally equal),
  defined everywhere (`0` outside domain).
-/
def continuousLinearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : E b →L[R] F :=
  { e.linearMapAt R b with
    toFun := e.linearMapAt R b -- given explicitly to help `simps`
    cont := by
      rw [e.coe_linearMapAt b]
      classical
      refine continuous_if_const _ (fun hb => ?_) fun _ => continuous_zero
      exact (e.continuousOn.comp_continuous (FiberBundle.totalSpaceMk_isInducing F E b).continuous
        fun x => e.mem_source.mpr hb).snd }
/-
**Bundle.Trivialization.continuousLinearMapAt_apply_of_mem** 是 Mathlib 中的一个定理，位于
命名空间 `Bundle.Trivialization`。
形式化陈述：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E]   (e : Bundle.Trivialization F Bundle.TotalSpace.proj) [inst_9 : Bundle
.Trivialization.IsLinear R e] {b : B},   b ∈ e.baseSet → ∀ (y : E b), (Bundle.Tr
ivialization.continuousLinearMapAt R e b) y = (↑e ⟨b, y⟩).2
参数：R : Type u_1；x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e : Bundle.T
rivialization F Bundle.TotalSpace.proj；y : E b；Bundle.Trivialization.continuousL
inearMapAt R e b；↑e ⟨b, y⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Bundle.Trivialization.continuousLinearMapAt_apply`：∀ (R : Type u_1) {B :
 Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R] 
  [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Bundle.Trivialization.coe_linearMapAt_of_mem`：∀ {R : Type u_1} {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topologica
lSpace F]   [inst_2 : TopologicalS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma continuousLinearMapAt_apply_of_mem (e : Trivialization F TotalSpace.proj)
    [Trivialization.IsLinear R e] {b : B} (hb : b ∈ e.baseSet) (y : E b) :
    (continuousLinearMapAt R e b) y = (e ⟨b, y⟩).2 := by
  simp [coe_linearMapAt_of_mem e hb]

/-- Backwards map of `Bundle.Trivialization.continuousLinearEquivAt`, defined everywhere. -/
/-
**Bundle.Trivialization.symmL** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivialization`。
形式化陈述：(R : Type u_1) →   {B : Type u_2} →     {F : Type u_3} →       {E : B → Ty
pe u_4} →         [inst : NontriviallyNormedField R] →           [inst_1 : (x : 
B) → AddCommMonoid (E x)] →             [inst_2 : (x : B) → _root_.Module R (E x
)] →               [inst_3 : NormedAddCommGroup F] →                 [inst_4 : N
ormedSpace R F] →                   [inst_5 : TopologicalSpace B] →             
        [inst_6 : TopologicalSpace (Bundle.TotalSpace F E)] →                   
    [inst_7 : (x : B) → TopologicalSpace (E x)] →                         [Fiber
Bundle F E] →                           (e : Bundle.Trivialization F Bundle.Tota
lSpace.proj) →                             [Bundle.Trivialization.IsLinear R e] 
→ (b : B) → F →L[R] E b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Backwards map of `Bundle.Trivialization.continuousLinearEquivAt`, defined everyw
here.
-/
def symmL (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : F →L[R] E b :=
  { e.symmₗ R b with
    cont := by
      by_cases hb : b ∈ e.baseSet
      · rw [(FiberBundle.totalSpaceMk_isInducing F E b).continuous_iff]
        refine .congr (f := TotalSpace.mk b ∘ e.symm b) ?_ (by simp [hb])
        exact e.continuousOn_symm.comp_continuous (.prodMk_right _) fun x ↦
          mk_mem_prod hb (mem_univ x)
      · exact continuous_zero.congr fun x => (e.symmₗ_apply_of_notMem hb x).symm }

variable {R}

@[simp]
/-
**Bundle.Trivialization.symmL_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializa
tion`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E]   (e : Bundle.Trivialization F Bundle.TotalSpace.proj) [inst_9 : Bundle
.Trivialization.IsLinear R e] {b : B},   b ∈ e.baseSet → ∀ (y : F), (Bundle.Triv
ialization.symmL R e b) y = e.symm b y
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization
 F Bundle.TotalSpace.proj；y : F；Bundle.Trivialization.symmL R e b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Bundle.Pretrivialization.symmₗ_apply`：symmₗ_apply (e : Pretrivialization
 F (π F E)) [e.IsLinear R] {b : B} (hb : b in e.baseSet) (y : F) : e.symmₗ R b y
 = e.symm b y
· 使用定理 `Bundle.Trivialization.toPretrivialization.isLinear`：∀ (R : Type u_1) {B 
: Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topo
logicalSpace F]   [inst_2 : TopologicalS…
-/
theorem symmL_apply (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet)
    (y : F) : e.symmL R b y = e.symm b y :=
  e.toPretrivialization.symmₗ_apply R hb y

@[simp]
/-
**Bundle.Trivialization.symmL_apply_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.
Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E]   (e : Bundle.Trivialization F Bundle.TotalSpace.proj) [inst_9 : Bundle
.Trivialization.IsLinear R e] {b : B},   b ∉ e.baseSet → ∀ (y : F), (Bundle.Triv
ialization.symmL R e b) y = 0
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization
 F Bundle.TotalSpace.proj；y : F；Bundle.Trivialization.symmL R e b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Bundle.Pretrivialization.symmₗ_apply_of_notMem`：symmₗ_apply_of_notMem (e
 : Pretrivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b ∉ e.baseSet) (y :
 F) : e.symmₗ R b y = 0
· 使用定理 `Bundle.Trivialization.toPretrivialization.isLinear`：∀ (R : Type u_1) {B 
: Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topo
logicalSpace F]   [inst_2 : TopologicalS…
-/
lemma symmL_apply_of_notMem (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) (y : F) : e.symmL R b y = 0 :=
  e.toPretrivialization.symmₗ_apply_of_notMem _ hb _
/-
**Bundle.Trivialization.symmL_continuousLinearMapAt** 是 Mathlib 中的一个定理，位于命名空间 `B
undle.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E]   (e : Bundle.Trivialization F Bundle.TotalSpace.proj) [inst_9 : Bundle
.Trivialization.IsLinear R e] {b : B},   b ∈ e.baseSet →     ∀ (y : E b), (Bundl
e.Trivialization.symmL R e b) ((Bundle.Trivialization.continuousLinearMapAt R e 
b) y) = y
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization
 F Bundle.TotalSpace.proj；y : E b；Bundle.Trivialization.symmL R e b；(Bundle.Triv
ialization.continuousLinearMapAt R e b) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.symmₗ_linearMapAt`：∀ {R : Type u_1} {B : Type u_2}
 {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpac
e F]   [inst_2 : TopologicalS…
-/
theorem symmL_continuousLinearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) (y : E b) : e.symmL R b (e.continuousLinearMapAt R b y) = y :=
  e.symmₗ_linearMapAt hb y
/-
**Bundle.Trivialization.continuousLinearMapAt_symmL** 是 Mathlib 中的一个定理，位于命名空间 `B
undle.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E]   (e : Bundle.Trivialization F Bundle.TotalSpace.proj) [inst_9 : Bundle
.Trivialization.IsLinear R e] {b : B},   b ∈ e.baseSet →     ∀ (y : F), (Bundle.
Trivialization.continuousLinearMapAt R e b) ((Bundle.Trivialization.symmL R e b)
 y) = y
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization
 F Bundle.TotalSpace.proj；y : F；Bundle.Trivialization.continuousLinearMapAt R e 
b；(Bundle.Trivialization.symmL R e b) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.linearMapAt_symmₗ`：∀ {R : Type u_1} {B : Type u_2}
 {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpac
e F]   [inst_2 : TopologicalS…
-/
theorem continuousLinearMapAt_symmL (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) (y : F) : e.continuousLinearMapAt R b (e.symmL R b y) = y :=
  e.linearMapAt_symmₗ hb y

variable (R) in
/-- In a vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
@[simps -fullyApplied apply symm_apply]
/-
**Bundle.Trivialization.continuousLinearEquivAt** 是 Mathlib 中的一个定义，位于命名空间 `Bundl
e.Trivialization`。
形式化陈述：(R : Type u_1) →   {B : Type u_2} →     {F : Type u_3} →       {E : B → Ty
pe u_4} →         [inst : NontriviallyNormedField R] →           [inst_1 : (x : 
B) → AddCommMonoid (E x)] →             [inst_2 : (x : B) → _root_.Module R (E x
)] →               [inst_3 : NormedAddCommGroup F] →                 [inst_4 : N
ormedSpace R F] →                   [inst_5 : TopologicalSpace B] →             
        [inst_6 : TopologicalSpace (Bundle.TotalSpace F E)] →                   
    [inst_7 : (x : B) → TopologicalSpace (E x)] →                         [Fiber
Bundle F E] →                           (e : Bundle.Trivialization F Bundle.Tota
lSpace.proj) →                             [Bundle.Trivialization.IsLinear R e] 
→ (b : B) → b ∈ e.baseSet → E b ≃L[R] F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a vector bundle, a trivialization in the fiber (which is a priori only linear
)
is in fact a continuous linear equiv between the fibers and the model fiber.
-/
def continuousLinearEquivAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
    (hb : b ∈ e.baseSet) : E b ≃L[R] F :=
  { e.toPretrivialization.linearEquivAt R b hb with
    toFun := fun y => (e ⟨b, y⟩).2 -- given explicitly to help `simps`
    invFun := e.symm b -- given explicitly to help `simps`
    continuous_toFun := (e.continuousOn.comp_continuous
      (FiberBundle.totalSpaceMk_isInducing F E b).continuous fun _ => e.mem_source.mpr hb).snd
    continuous_invFun := by convert (e.symmL R b).continuous; ext; simp [hb] }
/-
**Bundle.Trivialization.coe_continuousLinearEquivAt_eq** 是 Mathlib 中的一个定理，位于命名空间
 `Bundle.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E]   (e : Bundle.Trivialization F Bundle.TotalSpace.proj) [inst_9 : Bundle
.Trivialization.IsLinear R e] {b : B}   (hb : b ∈ e.baseSet),   ⇑(Bundle.Trivial
ization.continuousLinearEquivAt R e b hb) = ⇑(Bundle.Trivialization.continuousLi
nearMapAt R e b)
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization
 F Bundle.TotalSpace.proj；hb : b ∈ e.baseSet；Bundle.Trivialization.continuousLin
earEquivAt R e b hb；Bundle.Trivialization.continuousLinearMapAt R e b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.coe_linearMapAt_of_mem`：∀ {R : Type u_1} {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topologica
lSpace F]   [inst_2 : TopologicalS…
-/
theorem coe_continuousLinearEquivAt_eq (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) :
    (e.continuousLinearEquivAt R b hb : E b → F) = e.continuousLinearMapAt R b :=
  (e.coe_linearMapAt_of_mem hb).symm
/-
**Bundle.Trivialization.coe_continuousLinearEquivAt_eq'** 是 Mathlib 中的一个定理，位于命名空
间 `Bundle.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E]   (e : Bundle.Trivialization F Bundle.TotalSpace.proj) [inst_9 : Bundle
.Trivialization.IsLinear R e] {b : B}   (hb : b ∈ e.baseSet),   ↑(Bundle.Trivial
ization.continuousLinearEquivAt R e b hb) = Bundle.Trivialization.continuousLine
arMapAt R e b
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization
 F Bundle.TotalSpace.proj；hb : b ∈ e.baseSet；Bundle.Trivialization.continuousLin
earEquivAt R e b hb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.coe_linearMapAt_of_mem`：∀ {R : Type u_1} {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topologica
lSpace F]   [inst_2 : TopologicalS…
-/
theorem coe_continuousLinearEquivAt_eq' (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) :
    (e.continuousLinearEquivAt R b hb : E b →L[R] F) = e.continuousLinearMapAt R b :=
  DFunLike.coe_injective (e.coe_linearMapAt_of_mem hb).symm
/-
**Bundle.Trivialization.symm_continuousLinearEquivAt_eq** 是 Mathlib 中的一个定理，位于命名空
间 `Bundle.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E]   (e : Bundle.Trivialization F Bundle.TotalSpace.proj) [inst_9 : Bundle
.Trivialization.IsLinear R e] {b : B}   (hb : b ∈ e.baseSet),   ⇑(Bundle.Trivial
ization.continuousLinearEquivAt R e b hb).symm = ⇑(Bundle.Trivialization.symmL R
 e b)
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization
 F Bundle.TotalSpace.proj；hb : b ∈ e.baseSet；Bundle.Trivialization.continuousLin
earEquivAt R e b hb；Bundle.Trivialization.symmL R e b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Bundle.Trivialization.continuousLinearEquivAt_symm_apply`：∀ (R : Type u_
1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedFi
eld R]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Bundle.Trivialization.symmL_apply`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x :
 B) → AddCommMonoid (E …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_continuousLinearEquivAt_eq (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) : ((e.continuousLinearEquivAt R b hb).symm : F → E b) = e.symmL R b := by
  ext; simp [hb]
/-
**Bundle.Trivialization.symm_continuousLinearEquivAt_eq'** 是 Mathlib 中的一个定理，位于命名
空间 `Bundle.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E]   (e : Bundle.Trivialization F Bundle.TotalSpace.proj) [inst_9 : Bundle
.Trivialization.IsLinear R e] {b : B}   (hb : b ∈ e.baseSet),   ↑(Bundle.Trivial
ization.continuousLinearEquivAt R e b hb).symm = Bundle.Trivialization.symmL R e
 b
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization
 F Bundle.TotalSpace.proj；hb : b ∈ e.baseSet；Bundle.Trivialization.continuousLin
earEquivAt R e b hb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Bundle.Trivialization.continuousLinearEquivAt_symm_apply`：∀ (R : Type u_
1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedFi
eld R]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Bundle.Trivialization.symmL_apply`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x :
 B) → AddCommMonoid (E …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_continuousLinearEquivAt_eq' (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) :
    ((e.continuousLinearEquivAt R b hb).symm : F →L[R] E b) = e.symmL R b := by
  ext; simp [hb]

@[simp]
/-
**Bundle.Trivialization.continuousLinearEquivAt_apply'** 是 Mathlib 中的一个定理，位于命名空间
 `Bundle.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E]   (e : Bundle.Trivialization F Bundle.TotalSpace.proj) [inst_9 : Bundle
.Trivialization.IsLinear R e]   (x : Bundle.TotalSpace F E) (hx : x ∈ e.source),
   (Bundle.Trivialization.continuousLinearEquivAt R e x.proj ⋯) x.snd = (↑e x).2
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization
 F Bundle.TotalSpace.proj；x : Bundle.TotalSpace F E；hx : x ∈ e.source；Bundle.Tri
vialization.continuousLinearEquivAt R e x.proj ⋯；↑e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
-/
theorem continuousLinearEquivAt_apply' (e : Trivialization F (π F E)) [e.IsLinear R]
    (x : TotalSpace F E) (hx : x ∈ e.source) :
    e.continuousLinearEquivAt R x.proj (e.mem_source.1 hx) x.2 = (e x).2 := rfl

variable (R)
/-
**Bundle.Trivialization.apply_eq_prod_continuousLinearEquivAt** 是 Mathlib 中的一个定理
，位于命名空间 `Bundle.Trivialization`。
形式化陈述：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E]   (e : Bundle.Trivialization F Bundle.TotalSpace.proj) [inst_9 : Bundle
.Trivialization.IsLinear R e] (b : B)   (hb : b ∈ e.baseSet) (z : E b), ↑e ⟨b, z
⟩ = (b, (Bundle.Trivialization.continuousLinearEquivAt R e b hb) z)
参数：R : Type u_1；x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e : Bundle.T
rivialization F Bundle.TotalSpace.proj；b : B；hb : b ∈ e.baseSet；z : E b；b, (Bund
le.Trivialization.continuousLinearEquivAt R e b hb) z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Bundle.Trivialization.coe_fst`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace Z] {pr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Bundle.Trivialization.continuousLinearEquivAt_apply`：∀ (R : Type u_1) {B
 : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R
]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem apply_eq_prod_continuousLinearEquivAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
    (hb : b ∈ e.baseSet) (z : E b) : e ⟨b, z⟩ = (b, e.continuousLinearEquivAt R b hb z) := by
  ext
  · refine e.coe_fst ?_
    rw [e.source_eq]
    exact hb
  · simp only [continuousLinearEquivAt_apply]
/-
**Bundle.Trivialization.zeroSection** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializa
tion`。
形式化陈述：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [FiberBundle F E] 
(e : Bundle.Trivialization F Bundle.TotalSpace.proj)   [Bundle.Trivialization.Is
Linear R e] {x : B}, x ∈ e.baseSet → ↑e (Bundle.zeroSection F E x) = (x, 0)
参数：R : Type u_1；x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e : Bundle.T
rivialization F Bundle.TotalSpace.proj；Bundle.zeroSection F E x；x, 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.apply_eq_prod_continuousLinearEquivAt`：∀ (R : Type
 u_1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNorme
dField R]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem zeroSection (e : Trivialization F (π F E)) [e.IsLinear R] {x : B}
    (hx : x ∈ e.baseSet) : e (zeroSection F E x) = (x, 0) := by
  simp_rw [zeroSection, e.apply_eq_prod_continuousLinearEquivAt R x hx 0, map_zero]

/-- The zero section of a vector bundle is continuous. -/
/-
**Bundle.Trivialization.continuous_zeroSection** 是 Mathlib 中的一个定理，位于命名空间 `Bundle
.Trivialization`。
形式化陈述：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E] [VectorBundle R F E],   Continuous (Bundle.zeroSection F E)
参数：R : Type u_1；x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；Bundle.zeroS
ection F E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiberBundle.continuousAt_section`：continuousAt_section {s : forall x, E 
x} (x₀ : B) : ContinuousAt (fun x => TotalSpace.mk' F x (s x)) x₀ ↔ ContinuousAt
 (fun x => (trivializa…
· 使用定理 `ContinuousAt.congr_of_eventuallyEq`：ContinuousAt.congr_of_eventuallyEq (
h : ContinuousAt f x) (hg : g =ᶠ[𝓝 x] f) : ContinuousAt g x
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.zeroSection`：∀ (R : Type u_1) {B : Type u_2} {F : 
Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x :
 B) → AddCommMonoid (E …
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…

--- 原说明 ---
The zero section of a vector bundle is continuous.
-/
theorem continuous_zeroSection [VectorBundle R F E] :
    Continuous (zeroSection F E) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  unfold zeroSection
  rw [FiberBundle.continuousAt_section]
  apply (continuousAt_const (y := 0)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
    using congr_arg Prod.snd <| (trivializationAt F E x).zeroSection R hy

/-- The zero section of a vector bundle is continuous on any set. -/
/-
**Bundle.Trivialization.continuousOn_zeroSection** 是 Mathlib 中的一个定理，位于命名空间 `Bund
le.Trivialization`。
形式化陈述：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E] [VectorBundle R F E] (s : Set B),   ContinuousOn (Bundle.zeroSection F 
E) s
参数：R : Type u_1；x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；s : Set B；Bu
ndle.zeroSection F E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Bundle.Trivialization.continuous_zeroSection`：∀ (R : Type u_1) {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [in
st_1 : (x : B) → AddCommMonoid (E …

--- 原说明 ---
The zero section of a vector bundle is continuous on any set.
-/
theorem continuousOn_zeroSection [VectorBundle R F E] (s : Set B) :
    ContinuousOn (zeroSection F E) s :=
  (continuous_zeroSection R).continuousOn

/-- The zero section of a vector bundle is continuous at each point. -/
/-
**Bundle.Trivialization.continuousAt_zeroSection** 是 Mathlib 中的一个定理，位于命名空间 `Bund
le.Trivialization`。
形式化陈述：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E] [VectorBundle R F E] (x : B),   ContinuousAt (Bundle.zeroSection F E) x
参数：R : Type u_1；x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；x : B；Bundle
.zeroSection F E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Bundle.Trivialization.continuous_zeroSection`：∀ (R : Type u_1) {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [in
st_1 : (x : B) → AddCommMonoid (E …

--- 原说明 ---
The zero section of a vector bundle is continuous at each point.
-/
theorem continuousAt_zeroSection [VectorBundle R F E] (x : B) :
    ContinuousAt (zeroSection F E) x :=
  (continuous_zeroSection R).continuousAt

variable {R}
/-
**Bundle.Trivialization.symm_apply_eq_mk_continuousLinearEquivAt_symm** 是 Mathli
b 中的一个定理，位于命名空间 `Bundle.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E]   (e : Bundle.Trivialization F Bundle.TotalSpace.proj) [inst_9 : Bundle
.Trivialization.IsLinear R e] (b : B)   (hb : b ∈ e.baseSet) (z : F), ↑e.symm (b
, z) = ⟨b, (Bundle.Trivialization.continuousLinearEquivAt R e b hb).symm z⟩
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization
 F Bundle.TotalSpace.proj；b : B；hb : b ∈ e.baseSet；z : F；b, z；Bundle.Trivializat
ion.continuousLinearEquivAt R e b hb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Bundle.Trivialization.continuousLinearEquivAt_symm_apply`：∀ (R : Type u_
1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedFi
eld R]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Bundle.Trivialization.mk_symm`：∀ {B : Type u_1} {F : Type u_2} {E : B → 
Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : 
TopologicalSpace (B…
-/
theorem symm_apply_eq_mk_continuousLinearEquivAt_symm (e : Trivialization F (π F E)) [e.IsLinear R]
    (b : B) (hb : b ∈ e.baseSet) (z : F) :
    e.toOpenPartialHomeomorph.symm ⟨b, z⟩ = ⟨b, (e.continuousLinearEquivAt R b hb).symm z⟩ := by
  simpa using (mk_symm _ hb _).symm
/-
**Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change** 是 Mathlib
 中的一个定理，位于命名空间 `Bundle.Trivialization`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : TopologicalSpace (Bundle.T
otalSpace F E)]   [inst_7 : (x : B) → TopologicalSpace (E x)] [inst_8 : FiberBun
dle F E]   (e e' : Bundle.Trivialization F Bundle.TotalSpace.proj) [inst_9 : Bun
dle.Trivialization.IsLinear R e]   [inst_10 : Bundle.Trivialization.IsLinear R e
'] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet),   (Bundle.Trivialization.continuou
sLinearEquivAt R e b ⋯).symm.trans       (Bundle.Trivialization.continuousLinear
EquivAt R e' b ⋯) =     Bundle.Trivialization.coordChangeL R e e' b
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；e e' : Bundle.Trivializat
ion F Bundle.TotalSpace.proj；hb : b ∈ e.baseSet ∩ e'.baseSet；Bundle.Trivializati
on.continuousLinearEquivAt R e b ⋯；Bundle.Trivialization.continuousLinearEquivAt
 R e' b ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.ext`：ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂
) = g) : f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coordChangeL_apply`：∀ {R : Type u_1} {B : Type u_2
} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpa
ce F]   [inst_2 : TopologicalS…
-/
theorem comp_continuousLinearEquivAt_eq_coord_change (e e' : Trivialization F (π F E))
    [e.IsLinear R] [e'.IsLinear R] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (e.continuousLinearEquivAt R b hb.1).symm.trans (e'.continuousLinearEquivAt R b hb.2) =
      coordChangeL R e e' b := by
  ext v
  rw [coordChangeL_apply e e' hb]
  rfl

end Bundle.Trivialization

variable (F E) [VectorBundle R F E] in
/-- A continuous linear equivalence between the fiber at `b` and the model fiber,
induced by the preferred trivialisation at each `b`. -/
@[simps!]
/-
**VectorBundle.continuousLinearEquivAt** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pretriv
ialization.Trivialization`。
形式化陈述：VectorBundle.continuousLinearEquivAt (b : B) : E b ≃L[R] F
参数：b : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear equivalence between the fiber at `b` and the model fiber,
induced by the preferred trivialisation at each `b`.
-/
noncomputable def VectorBundle.continuousLinearEquivAt (b : B) : E b ≃L[R] F :=
  (trivializationAt F E b).continuousLinearEquivAt R b (FiberBundle.mem_baseSet_trivializationAt' b)

/-! ### Constructing vector bundles -/

variable (B F)

/-- Analogous construction of `FiberBundleCore` for vector bundles. This
construction gives a way to construct vector bundles from a structure registering how
trivialization changes act on fibers. -/
/-
**VectorBundleCore** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (B : Type u_2) →     (F : Type u_3) →       [inst : Non
triviallyNormedField R] →         [inst_1 : NormedAddCommGroup F] →           [N
ormedSpace R F] → [TopologicalSpace B] → Type u_5 → Type (max (max u_2 u_3) u_5)
参数：max u_2 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Analogous construction of `FiberBundleCore` for vector bundles. This
construction gives a way to construct vector bundles from a structure registerin
g how
trivialization changes act on fibers.
-/
structure VectorBundleCore (ι : Type*) where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  coordChange : ι → ι → B → F →L[R] F
  coordChange_self : ∀ i, ∀ x ∈ baseSet i, ∀ v, coordChange i i x v = v
  continuousOn_coordChange : ∀ i j, ContinuousOn (coordChange i j) (baseSet i ∩ baseSet j)
  coordChange_comp : ∀ i j k, ∀ x ∈ baseSet i ∩ baseSet j ∩ baseSet k, ∀ v,
    (coordChange j k x) (coordChange i j x v) = coordChange i k x v

/-- The trivial vector bundle core, in which all the changes of coordinates are the
identity. -/
/-
**trivialVectorBundleCore** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (B : Type u_2) →     (F : Type u_3) →       [inst : Non
triviallyNormedField R] →         [inst_1 : NormedAddCommGroup F] →           [i
nst_2 : NormedSpace R F] →             [inst_3 : TopologicalSpace B] → (ι : Type
 u_5) → [Inhabited ι] → VectorBundleCore R B F ι
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The trivial vector bundle core, in which all the changes of coordinates are the
identity.
-/
def trivialVectorBundleCore (ι : Type*) [Inhabited ι] : VectorBundleCore R B F ι where
  baseSet _ := univ
  isOpen_baseSet _ := isOpen_univ
  indexAt := default
  mem_baseSet_at x := mem_univ x
  coordChange _ _ _ := ContinuousLinearMap.id R F
  coordChange_self _ _ _ _ := rfl
  coordChange_comp _ _ _ _ _ _ := rfl
  continuousOn_coordChange _ _ := continuousOn_const
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (ι : Type*) [Inhabited ι] : Inhabited (VectorBundleCore R B F ι) :=
  ⟨trivialVectorBundleCore R B F ι⟩

namespace VectorBundleCore

variable {R B F} {ι : Type*}
variable (Z : VectorBundleCore R B F ι)

/-- Natural identification to a `FiberBundleCore`. -/
@[simps (attr := mfld_simps) -fullyApplied]
/-
**VectorBundleCore.toFiberBundleCore** 是 Mathlib 中的一个定义，位于命名空间 `VectorBundleCore
`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField R] →         [inst_1 : NormedAddCommGroup F] →           [i
nst_2 : NormedSpace R F] →             [inst_3 : TopologicalSpace B] → {ι : Type
 u_5} → VectorBundleCore R B F ι → FiberBundleCore ι B F
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundleCore.isOpen_baseSet`：∀ {R : Type u_1} {B : Type u_2} {F : Ty
pe u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [in
st_2 : NormedSpace R …
· 使用定理 `VectorBundleCore.mem_baseSet_at`：∀ {R : Type u_1} {B : Type u_2} {F : Ty
pe u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [in
st_2 : NormedSpace R …
· 使用定理 `VectorBundleCore.coordChange_self`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [
inst_2 : NormedSpace R …
· 使用定理 `VectorBundleCore.coordChange_comp`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [
inst_2 : NormedSpace R …

--- 原说明 ---
Natural identification to a `FiberBundleCore`.
-/
def toFiberBundleCore : FiberBundleCore ι B F :=
  { Z with
    coordChange := fun i j b => Z.coordChange i j b
    continuousOn_coordChange := fun i j =>
      isBoundedBilinearMap_apply.continuous.comp_continuousOn
        ((Z.continuousOn_coordChange i j).prodMap continuousOn_id) }

-- TODO: restore coercion?
-- instance toFiberBundleCoreCoe : Coe (VectorBundleCore R B F ι) (FiberBundleCore ι B F) :=
--   ⟨toFiberBundleCore⟩
/-
**VectorBundleCore.coordChange_linear_comp** 是 Mathlib 中的一个定理，位于命名空间 `VectorBund
leCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (i j k : ι),   
∀ x ∈ Z.baseSet i ∩ Z.baseSet j ∩ Z.baseSet k, Z.coordChange j k x ∘SL Z.coordCh
ange i j x = Z.coordChange i k x
参数：Z : VectorBundleCore R B F ι；i j k : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `VectorBundleCore.coordChange_comp`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [
inst_2 : NormedSpace R …
-/
theorem coordChange_linear_comp (i j k : ι) :
    ∀ x ∈ Z.baseSet i ∩ Z.baseSet j ∩ Z.baseSet k,
      (Z.coordChange j k x).comp (Z.coordChange i j x) = Z.coordChange i k x :=
  fun x hx => by
  ext v
  exact Z.coordChange_comp i j k x hx v

/-- The index set of a vector bundle core, as a convenience function for dot notation -/
@[nolint unusedArguments]
/-
**VectorBundleCore.Index** 是 Mathlib 中的一个定义，位于命名空间 `VectorBundleCore`。
形式化陈述：{ι : Type u_5} → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The index set of a vector bundle core, as a convenience function for dot notatio
n
-/
def Index := ι

/-- The base space of a vector bundle core, as a convenience function for dot notation -/
@[nolint unusedArguments, reducible]
/-
**VectorBundleCore.Base** 是 Mathlib 中的一个定义，位于命名空间 `VectorBundleCore`。
形式化陈述：{B : Type u_2} → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base space of a vector bundle core, as a convenience function for dot notati
on
-/
def Base := B

/-- The fiber of a vector bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unusedArguments]
/-
**VectorBundleCore.Fiber** 是 Mathlib 中的一个定义，位于命名空间 `VectorBundleCore`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField R] →         [inst_1 : NormedAddCommGroup F] →           [i
nst_2 : NormedSpace R F] →             [inst_3 : TopologicalSpace B] → {ι : Type
 u_5} → VectorBundleCore R B F ι → B → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber of a vector bundle core, as a convenience function for dot notation an
d
typeclass inference
-/
def Fiber : B → Type _ :=
  Z.toFiberBundleCore.Fiber
/-
**VectorBundleCore.topologicalSpaceFiber** 是 Mathlib 中的一个定义，位于命名空间 `VectorBundle
Core`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField R] →         [inst_1 : NormedAddCommGroup F] →           [i
nst_2 : NormedSpace R F] →             [inst_3 : TopologicalSpace B] →          
     {ι : Type u_5} → (Z : VectorBundleCore R B F ι) → (x : B) → TopologicalSpac
e (Z.Fiber x)
参数：Z : VectorBundleCore R B F ι；x : B；Z.Fiber x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance topologicalSpaceFiber (x : B) : TopologicalSpace (Z.Fiber x) :=
  letI : TopologicalSpace (Z.toFiberBundleCore.Fiber x) :=
    Z.toFiberBundleCore.topologicalSpaceFiber x
  inferInstanceAs <| TopologicalSpace (Z.toFiberBundleCore.Fiber x)
/-
**VectorBundleCore.addCommGroupFiber** 是 Mathlib 中的一个定义，位于命名空间 `VectorBundleCore
`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField R] →         [inst_1 : NormedAddCommGroup F] →           [i
nst_2 : NormedSpace R F] →             [inst_3 : TopologicalSpace B] →          
     {ι : Type u_5} → (Z : VectorBundleCore R B F ι) → (x : B) → AddCommGroup (Z
.Fiber x)
参数：Z : VectorBundleCore R B F ι；x : B；Z.Fiber x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroupFiber (x : B) : AddCommGroup (Z.Fiber x) :=
  inferInstanceAs <| AddCommGroup F
/-
**VectorBundleCore.moduleFiber** 是 Mathlib 中的一个定义，位于命名空间 `VectorBundleCore`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField R] →         [inst_1 : NormedAddCommGroup F] →           [i
nst_2 : NormedSpace R F] →             [inst_3 : TopologicalSpace B] →          
     {ι : Type u_5} → (Z : VectorBundleCore R B F ι) → (x : B) → _root_.Module R
 (Z.Fiber x)
参数：Z : VectorBundleCore R B F ι；x : B；Z.Fiber x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance moduleFiber (x : B) : Module R (Z.Fiber x) :=
  inferInstanceAs <| Module R F

/-- The projection from the total space of a fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
/-
**VectorBundleCore.proj** 是 Mathlib 中的一个定义，位于命名空间 `VectorBundleCore`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField R] →         [inst_1 : NormedAddCommGroup F] →           [i
nst_2 : NormedSpace R F] →             [inst_3 : TopologicalSpace B] →          
     {ι : Type u_5} → (Z : VectorBundleCore R B F ι) → Bundle.TotalSpace F Z.Fib
er → B
参数：Z : VectorBundleCore R B F ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from the total space of a fiber bundle core, on its base.
-/
protected def proj : TotalSpace F Z.Fiber → B :=
  TotalSpace.proj

/-- The total space of the vector bundle, as a convenience function for dot notation.
It is by definition equal to `Bundle.TotalSpace F Z.Fiber`. -/
@[nolint unusedArguments, reducible]
/-
**VectorBundleCore.TotalSpace** 是 Mathlib 中的一个定义，位于命名空间 `VectorBundleCore`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField R] →         [inst_1 : NormedAddCommGroup F] →           [i
nst_2 : NormedSpace R F] →             [inst_3 : TopologicalSpace B] → {ι : Type
 u_5} → VectorBundleCore R B F ι → Type (max u_2 u_3)
参数：max u_2 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The total space of the vector bundle, as a convenience function for dot notation
.
It is by definition equal to `Bundle.TotalSpace F Z.Fiber`.
-/
protected def TotalSpace :=
  Bundle.TotalSpace F Z.Fiber

/-- Local homeomorphism version of the trivialization change. -/
/-
**VectorBundleCore.trivChange** 是 Mathlib 中的一个定义，位于命名空间 `VectorBundleCore`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField R] →         [inst_1 : NormedAddCommGroup F] →           [i
nst_2 : NormedSpace R F] →             [inst_3 : TopologicalSpace B] →          
     {ι : Type u_5} → VectorBundleCore R B F ι → ι → ι → OpenPartialHomeomorph (
B × F) (B × F)
参数：B × F；B × F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Local homeomorphism version of the trivialization change.
-/
def trivChange (i j : ι) : OpenPartialHomeomorph (B × F) (B × F) :=
  Z.toFiberBundleCore.trivChange i j

@[simp, mfld_simps]
/-
**VectorBundleCore.mem_trivChange_source** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundle
Core`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (i j : ι)   (p 
: B × F), p ∈ (Z.trivChange i j).source ↔ p.1 ∈ Z.baseSet i ∩ Z.baseSet j
参数：Z : VectorBundleCore R B F ι；i j : ι；p : B × F；Z.trivChange i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundleCore.mem_trivChange_source`：mem_trivChange_source (i j : ι) (
p : B × F) : p in (Z.trivChange i j).source ↔ p.1 in Z.baseSet i inter Z.baseSet
 j
-/
theorem mem_trivChange_source (i j : ι) (p : B × F) :
    p ∈ (Z.trivChange i j).source ↔ p.1 ∈ Z.baseSet i ∩ Z.baseSet j :=
  Z.toFiberBundleCore.mem_trivChange_source i j p

/-- Topological structure on the total space of a vector bundle created from core, designed so
that all the local trivialization are continuous. -/
/-
**VectorBundleCore.toTopologicalSpace** 是 Mathlib 中的一个定义，位于命名空间 `VectorBundleCor
e`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField R] →         [inst_1 : NormedAddCommGroup F] →           [i
nst_2 : NormedSpace R F] →             [inst_3 : TopologicalSpace B] →          
     {ι : Type u_5} → (Z : VectorBundleCore R B F ι) → TopologicalSpace Z.TotalS
pace
参数：Z : VectorBundleCore R B F ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Topological structure on the total space of a vector bundle created from core, d
esigned so
that all the local trivialization are continuous.
-/
instance toTopologicalSpace : TopologicalSpace Z.TotalSpace :=
  fast_instance% Z.toFiberBundleCore.toTopologicalSpace

variable (b : B) (a : F)

@[simp, mfld_simps]
/-
**VectorBundleCore.coe_coordChange** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (b : B)   (i j 
: ι), Z.toFiberBundleCore.coordChange i j b = ⇑(Z.coordChange i j b)
参数：Z : VectorBundleCore R B F ι；b : B；i j : ι；Z.coordChange i j b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coordChange (i j : ι) : Z.toFiberBundleCore.coordChange i j b = Z.coordChange i j b :=
  rfl

/-- One of the standard local trivializations of a vector bundle constructed from core, taken by
considering this in particular as a fiber bundle constructed from core. -/
/-
**VectorBundleCore.localTriv** 是 Mathlib 中的一个定义，位于命名空间 `VectorBundleCore`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField R] →         [inst_1 : NormedAddCommGroup F] →           [i
nst_2 : NormedSpace R F] →             [inst_3 : TopologicalSpace B] →          
     {ι : Type u_5} → (Z : VectorBundleCore R B F ι) → ι → Bundle.Trivialization
 F Bundle.TotalSpace.proj
参数：Z : VectorBundleCore R B F ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One of the standard local trivializations of a vector bundle constructed from co
re, taken by
considering this in particular as a fiber bundle constructed from core.
-/
def localTriv (i : ι) : Trivialization F (π F Z.Fiber) :=
  Z.toFiberBundleCore.localTriv i

@[simp, mfld_simps]
/-
**VectorBundleCore.localTriv_apply** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) {i : ι}   (p : 
Z.TotalSpace), ↑(Z.localTriv i) p = (p.proj, (Z.coordChange (Z.indexAt p.proj) i
 p.proj) p.snd)
参数：Z : VectorBundleCore R B F ι；p : Z.TotalSpace；Z.localTriv i；p.proj, (Z.coordC
hange (Z.indexAt p.proj) i p.proj) p.snd。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localTriv_apply {i : ι} (p : Z.TotalSpace) :
    (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The standard local trivializations of a vector bundle constructed from core are linear. -/
/-
**VectorBundleCore.localTriv.isLinear** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleCor
e.localTriv`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (i : ι),   Bund
le.Trivialization.IsLinear R (Z.localTriv i)
参数：Z : VectorBundleCore R B F ι；i : ι；Z.localTriv i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…

--- 原说明 ---
The standard local trivializations of a vector bundle constructed from core are 
linear.
-/
instance localTriv.isLinear (i : ι) : (Z.localTriv i).IsLinear R where
  linear x _ :=
    { map_add := fun _ _ => by simp only [map_add, localTriv_apply, mfld_simps]
      map_smul := fun _ _ => by simp only [map_smul, localTriv_apply, mfld_simps] }

variable (i j : ι)

@[simp, mfld_simps]
/-
**VectorBundleCore.mem_localTriv_source** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleC
ore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (i : ι)   (p : 
Z.TotalSpace), p ∈ (Z.localTriv i).source ↔ p.proj ∈ Z.baseSet i
参数：Z : VectorBundleCore R B F ι；i : ι；p : Z.TotalSpace；Z.localTriv i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_localTriv_source (p : Z.TotalSpace) : p ∈ (Z.localTriv i).source ↔ p.1 ∈ Z.baseSet i :=
  Iff.rfl

@[simp, mfld_simps]
/-
**VectorBundleCore.baseSet_at** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (i : ι),   Z.ba
seSet i = (Z.localTriv i).baseSet
参数：Z : VectorBundleCore R B F ι；i : ι；Z.localTriv i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem baseSet_at : Z.baseSet i = (Z.localTriv i).baseSet :=
  rfl

@[simp, mfld_simps]
/-
**VectorBundleCore.mem_localTriv_target** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleC
ore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (i : ι)   (p : 
B × F), p ∈ (Z.localTriv i).target ↔ p.1 ∈ (Z.localTriv i).baseSet
参数：Z : VectorBundleCore R B F ι；i : ι；p : B × F；Z.localTriv i；Z.localTriv i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundleCore.mem_localTriv_target`：mem_localTriv_target (p : B × F) :
 p in (Z.localTriv i).target ↔ p.1 in (Z.localTriv i).baseSet
-/
theorem mem_localTriv_target (p : B × F) :
    p ∈ (Z.localTriv i).target ↔ p.1 ∈ (Z.localTriv i).baseSet :=
  Z.toFiberBundleCore.mem_localTriv_target i p

@[simp, mfld_simps]
/-
**VectorBundleCore.localTriv_symm_fst** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleCor
e`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (i : ι)   (p : 
B × F), ↑(Z.localTriv i).symm p = ⟨p.1, (Z.coordChange i (Z.indexAt p.1) p.1) p.
2⟩
参数：Z : VectorBundleCore R B F ι；i : ι；p : B × F；Z.localTriv i；Z.coordChange i (Z
.indexAt p.1) p.1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localTriv_symm_fst (p : B × F) :
    (Z.localTriv i).toOpenPartialHomeomorph.symm p =
      ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩ :=
  rfl

@[simp, mfld_simps]
/-
**VectorBundleCore.localTriv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleC
ore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (i : ι)   {b : 
B}, b ∈ (Z.localTriv i).baseSet → ∀ (v : F), (Z.localTriv i).symm b v = (Z.coord
Change i (Z.indexAt b) b) v
参数：Z : VectorBundleCore R B F ι；i : ι；Z.localTriv i；v : F；Z.localTriv i；Z.coordC
hange i (Z.indexAt b) b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.symm_apply`：∀ {B : Type u_1} {F : Type u_2} {E : B
 → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2
 : TopologicalSpace (B…
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
-/
theorem localTriv_symm_apply {b : B} (hb : b ∈ (Z.localTriv i).baseSet) (v : F) :
    (Z.localTriv i).symm b v = Z.coordChange i (Z.indexAt b) b v := by
  apply (Z.localTriv i).symm_apply hb v

@[simp, mfld_simps]
/-
**VectorBundleCore.localTriv_coordChange_eq** 是 Mathlib 中的一个定理，位于命名空间 `VectorBun
dleCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (i j : ι)   {b 
: B},   b ∈ (Z.localTriv i).baseSet ∧ b ∈ (Z.localTriv j).baseSet →     ∀ (v : F
), (Bundle.Trivialization.coordChangeL R (Z.localTriv i) (Z.localTriv j) b) v = 
(Z.coordChange i j b) v
参数：Z : VectorBundleCore R B F ι；i j : ι；Z.localTriv i；Z.localTriv j；v : F；Bundle
.Trivialization.coordChangeL R (Z.localTriv i) (Z.localTriv j) b；Z.coordChange i
 j b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundleCore.localTriv.isLinear`：∀ {R : Type u_1} {B : Type u_2} {F 
: Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]  
 [inst_2 : NormedSpace R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coordChangeL_apply'`：∀ {R : Type u_1} {B : Type u_
2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSp
ace F]   [inst_2 : TopologicalS…
· 使用定理 `VectorBundleCore.localTriv_symm_fst`：∀ {R : Type u_1} {B : Type u_2} {F 
: Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]  
 [inst_2 : NormedSpace R …
· 使用定理 `VectorBundleCore.localTriv_apply`：∀ {R : Type u_1} {B : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [i
nst_2 : NormedSpace R …
· 使用定理 `VectorBundleCore.coordChange_comp`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [
inst_2 : NormedSpace R …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `VectorBundleCore.mem_baseSet_at`：∀ {R : Type u_1} {B : Type u_2} {F : Ty
pe u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [in
st_2 : NormedSpace R …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem localTriv_coordChange_eq {b : B}
    (hb : b ∈ (Z.localTriv i).baseSet ∧ b ∈ (Z.localTriv j).baseSet) (v : F) :
    (Z.localTriv i).coordChangeL R (Z.localTriv j) b v = Z.coordChange i j b v := by
  rw [Trivialization.coordChangeL_apply', localTriv_symm_fst, localTriv_apply, coordChange_comp]
  exacts [⟨⟨hb.1, Z.mem_baseSet_at b⟩, hb.2⟩, hb]

/-- Preferred local trivialization of a vector bundle constructed from core, at a given point, as
a bundle trivialization -/
/-
**VectorBundleCore.localTrivAt** 是 Mathlib 中的一个定义，位于命名空间 `VectorBundleCore`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField R] →         [inst_1 : NormedAddCommGroup F] →           [i
nst_2 : NormedSpace R F] →             [inst_3 : TopologicalSpace B] →          
     {ι : Type u_5} → (Z : VectorBundleCore R B F ι) → B → Bundle.Trivialization
 F Bundle.TotalSpace.proj
参数：Z : VectorBundleCore R B F ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preferred local trivialization of a vector bundle constructed from core, at a gi
ven point, as
a bundle trivialization
-/
def localTrivAt (b : B) : Trivialization F (π F Z.Fiber) :=
  Z.localTriv (Z.indexAt b)

@[simp, mfld_simps]
/-
**VectorBundleCore.localTrivAt_def** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (b : B),   Z.lo
calTriv (Z.indexAt b) = Z.localTrivAt b
参数：Z : VectorBundleCore R B F ι；b : B；Z.indexAt b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localTrivAt_def : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl

@[simp, mfld_simps]
/-
**VectorBundleCore.mem_source_at** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (b : B)   (a : 
F), ⟨b, a⟩ ∈ (Z.localTrivAt b).source
参数：Z : VectorBundleCore R B F ι；b : B；a : F；Z.localTrivAt b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VectorBundleCore.localTrivAt.eq_1`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [
inst_2 : NormedSpace R …
· 使用定理 `VectorBundleCore.mem_localTriv_source`：∀ {R : Type u_1} {B : Type u_2} {
F : Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]
   [inst_2 : NormedSpace R …
· 使用定理 `VectorBundleCore.mem_baseSet_at`：∀ {R : Type u_1} {B : Type u_2} {F : Ty
pe u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [in
st_2 : NormedSpace R …
-/
theorem mem_source_at : (⟨b, a⟩ : Z.TotalSpace) ∈ (Z.localTrivAt b).source := by
  rw [localTrivAt, mem_localTriv_source]
  exact Z.mem_baseSet_at b

@[simp, mfld_simps]
/-
**VectorBundleCore.localTrivAt_apply** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleCore
`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι)   (p : Z.TotalS
pace), ↑(Z.localTrivAt p.proj) p = (p.proj, p.snd)
参数：Z : VectorBundleCore R B F ι；p : Z.TotalSpace；Z.localTrivAt p.proj；p.proj, p.
snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundleCore.localTrivAt_apply`：localTrivAt_apply (p : Z.TotalSpace) 
: (Z.localTrivAt p.1) p = ⟨p.1, p.2⟩
-/
theorem localTrivAt_apply (p : Z.TotalSpace) : Z.localTrivAt p.1 p = ⟨p.1, p.2⟩ :=
  Z.toFiberBundleCore.localTrivAt_apply p

@[simp, mfld_simps]
/-
**VectorBundleCore.localTrivAt_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleC
ore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (b : B)   (a : 
F), ↑(Z.localTrivAt b) ⟨b, a⟩ = (b, a)
参数：Z : VectorBundleCore R B F ι；b : B；a : F；Z.localTrivAt b；b, a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundleCore.localTrivAt_apply`：∀ {R : Type u_1} {B : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   
[inst_2 : NormedSpace R …
-/
theorem localTrivAt_apply_mk (b : B) (a : F) : Z.localTrivAt b ⟨b, a⟩ = ⟨b, a⟩ :=
  Z.localTrivAt_apply _

@[simp, mfld_simps]
/-
**VectorBundleCore.mem_localTrivAt_baseSet** 是 Mathlib 中的一个定理，位于命名空间 `VectorBund
leCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (b : B),   b ∈ 
(Z.localTrivAt b).baseSet
参数：Z : VectorBundleCore R B F ι；b : B；Z.localTrivAt b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundleCore.mem_localTrivAt_baseSet`：mem_localTrivAt_baseSet (b : B)
 : b in (Z.localTrivAt b).baseSet
-/
theorem mem_localTrivAt_baseSet : b ∈ (Z.localTrivAt b).baseSet :=
  Z.toFiberBundleCore.mem_localTrivAt_baseSet b
/-
**VectorBundleCore.fiberBundle** 是 Mathlib 中的一个定义，位于命名空间 `VectorBundleCore`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField R] →         [inst_1 : NormedAddCommGroup F] →           [i
nst_2 : NormedSpace R F] →             [inst_3 : TopologicalSpace B] → {ι : Type
 u_5} → (Z : VectorBundleCore R B F ι) → FiberBundle F Z.Fiber
参数：Z : VectorBundleCore R B F ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fiberBundle : FiberBundle F Z.Fiber :=
  fast_instance% Z.toFiberBundleCore.fiberBundle
/-
**VectorBundleCore.trivializationAt** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleCore`
。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) (b : B),   triv
ializationAt F Z.Fiber b = Z.localTrivAt b
参数：Z : VectorBundleCore R B F ι；b : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma trivializationAt : trivializationAt F Z.Fiber b = Z.localTrivAt b := rfl
/-
**VectorBundleCore.vectorBundle** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι),   VectorBundle
 R F Z.Fiber
参数：Z : VectorBundleCore R B F ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundleCore.localTriv.isLinear`：∀ {R : Type u_1} {B : Type u_2} {F 
: Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]  
 [inst_2 : NormedSpace R …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `VectorBundleCore.continuousOn_coordChange`：∀ {R : Type u_1} {B : Type u_
2} {F : Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGrou
p F]   [inst_2 : NormedSpace R …
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `VectorBundleCore.localTriv_coordChange_eq`：∀ {R : Type u_1} {B : Type u_
2} {F : Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGrou
p F]   [inst_2 : NormedSpace R …
-/
instance vectorBundle : VectorBundle R F Z.Fiber where
  trivialization_linear' := by
    rintro _ ⟨i, rfl⟩
    apply localTriv.isLinear
  continuousOn_coordChange' := by
    rintro _ _ ⟨i, rfl⟩ ⟨i', rfl⟩
    refine (Z.continuousOn_coordChange i i').congr fun b hb => ?_
    ext v
    exact Z.localTriv_coordChange_eq i i' hb v

/-- The projection on the base of a vector bundle created from core is continuous -/
@[continuity]
/-
**VectorBundleCore.continuous_proj** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι),   Continuous Z
.proj
参数：Z : VectorBundleCore R B F ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundleCore.continuous_proj`：∀ {ι : Type u_1} {B : Type u_2} {F : Ty
pe u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   (Z : FiberBu
ndleCore ι B F), Cont…

--- 原说明 ---
The projection on the base of a vector bundle created from core is continuous
-/
theorem continuous_proj : Continuous Z.proj :=
  Z.toFiberBundleCore.continuous_proj

/-- The projection on the base of a vector bundle created from core is an open map -/
/-
**VectorBundleCore.isOpenMap_proj** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι),   IsOpenMap Z.
proj
参数：Z : VectorBundleCore R B F ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundleCore.isOpenMap_proj`：∀ {ι : Type u_1} {B : Type u_2} {F : Typ
e u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   (Z : FiberBun
dleCore ι B F), IsOp…

--- 原说明 ---
The projection on the base of a vector bundle created from core is an open map
-/
theorem isOpenMap_proj : IsOpenMap Z.proj :=
  Z.toFiberBundleCore.isOpenMap_proj

variable {i j}

@[simp, mfld_simps]
/-
**VectorBundleCore.localTriv_continuousLinearMapAt** 是 Mathlib 中的一个定理，位于命名空间 `Ve
ctorBundleCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) {i : ι}   {b : 
B},   b ∈ (Z.localTriv i).baseSet →     Bundle.Trivialization.continuousLinearMa
pAt R (Z.localTriv i) b = Z.coordChange (Z.indexAt b) i b
参数：Z : VectorBundleCore R B F ι；Z.localTriv i；Z.localTriv i；Z.indexAt b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `VectorBundleCore.localTriv.isLinear`：∀ {R : Type u_1} {B : Type u_2} {F 
: Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]  
 [inst_2 : NormedSpace R …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Bundle.Trivialization.continuousLinearMapAt_apply`：∀ (R : Type u_1) {B :
 Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R] 
  [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Bundle.Trivialization.coe_linearMapAt_of_mem`：∀ {R : Type u_1} {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topologica
lSpace F]   [inst_2 : TopologicalS…
-/
theorem localTriv_continuousLinearMapAt {b : B} (hb : b ∈ (Z.localTriv i).baseSet) :
    (Z.localTriv i).continuousLinearMapAt R b = Z.coordChange (Z.indexAt b) i b := by
  ext1 v
  simp_all
  rfl

@[simp, mfld_simps]
/-
**VectorBundleCore.trivializationAt_continuousLinearMapAt** 是 Mathlib 中的一个定理，位于命
名空间 `VectorBundleCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) {b₀ b : B},   b
 ∈ (trivializationAt F Z.Fiber b₀).baseSet →     Bundle.Trivialization.continuou
sLinearMapAt R (trivializationAt F Z.Fiber b₀) b =       Z.coordChange (Z.indexA
t b) (Z.indexAt b₀) b
参数：Z : VectorBundleCore R B F ι；trivializationAt F Z.Fiber b₀；trivializationAt F
 Z.Fiber b₀；Z.indexAt b；Z.indexAt b₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundleCore.localTriv_continuousLinearMapAt`：∀ {R : Type u_1} {B : 
Type u_2} {F : Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddC
ommGroup F]   [inst_2 : NormedSpace R …
-/
theorem trivializationAt_continuousLinearMapAt {b₀ b : B}
    (hb : b ∈ (trivializationAt F Z.Fiber b₀).baseSet) :
    (trivializationAt F Z.Fiber b₀).continuousLinearMapAt R b =
      Z.coordChange (Z.indexAt b) (Z.indexAt b₀) b :=
  Z.localTriv_continuousLinearMapAt hb

@[simp, mfld_simps]
/-
**VectorBundleCore.localTriv_symmL** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundleCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) {i : ι}   {b : 
B},   b ∈ (Z.localTriv i).baseSet → Bundle.Trivialization.symmL R (Z.localTriv i
) b = Z.coordChange i (Z.indexAt b) b
参数：Z : VectorBundleCore R B F ι；Z.localTriv i；Z.localTriv i；Z.indexAt b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `VectorBundleCore.localTriv.isLinear`：∀ {R : Type u_1} {B : Type u_2} {F 
: Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]  
 [inst_2 : NormedSpace R …
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.symmL_apply`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x :
 B) → AddCommMonoid (E …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.symm_coe_proj`：∀ {B : Type u_1} {F : Type u_2} {E 
: B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalSpace (B…
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Bundle.Trivialization.symm_apply`：∀ {B : Type u_1} {F : Type u_2} {E : B
 → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2
 : TopologicalSpace (B…
-/
theorem localTriv_symmL {b : B} (hb : b ∈ (Z.localTriv i).baseSet) :
    (Z.localTriv i).symmL R b = Z.coordChange i (Z.indexAt b) b := by
  ext1 v
  rw [(Z.localTriv i).symmL_apply hb, (Z.localTriv i).symm_apply]
  exacts [rfl, hb]

@[simp, mfld_simps]
/-
**VectorBundleCore.trivializationAt_symmL** 是 Mathlib 中的一个定理，位于命名空间 `VectorBundl
eCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) {b₀ b : B},   b
 ∈ (trivializationAt F Z.Fiber b₀).baseSet →     Bundle.Trivialization.symmL R (
trivializationAt F Z.Fiber b₀) b = Z.coordChange (Z.indexAt b₀) (Z.indexAt b) b
参数：Z : VectorBundleCore R B F ι；trivializationAt F Z.Fiber b₀；trivializationAt F
 Z.Fiber b₀；Z.indexAt b₀；Z.indexAt b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundleCore.localTriv_symmL`：∀ {R : Type u_1} {B : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [i
nst_2 : NormedSpace R …
-/
theorem trivializationAt_symmL {b₀ b : B} (hb : b ∈ (trivializationAt F Z.Fiber b₀).baseSet) :
    (trivializationAt F Z.Fiber b₀).symmL R b = Z.coordChange (Z.indexAt b₀) (Z.indexAt b) b :=
  Z.localTriv_symmL hb

@[simp, mfld_simps]
/-
**VectorBundleCore.trivializationAt_coordChange_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ve
ctorBundleCore`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield R] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace R F] [inst_3 : T
opologicalSpace B] {ι : Type u_5} (Z : VectorBundleCore R B F ι) {b₀ b₁ b : B}, 
  b ∈ (trivializationAt F Z.Fiber b₀).baseSet ∩ (trivializationAt F Z.Fiber b₁).
baseSet →     ∀ (v : F),       (Bundle.Trivialization.coordChangeL R (trivializa
tionAt F Z.Fiber b₀) (trivializationAt F Z.Fiber b₁) b) v =         (Z.coordChan
ge (Z.indexAt b₀) (Z.indexAt b₁) b) v
参数：Z : VectorBundleCore R B F ι；trivializationAt F Z.Fiber b₀；trivializationAt F
 Z.Fiber b₁；v : F；Bundle.Trivialization.coordChangeL R (trivializationAt F Z.Fib
er b₀) (trivializationAt F Z.Fiber b₁) b；Z.coordChange (Z.indexAt b₀) (Z.indexAt
 b₁) b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundleCore.localTriv_coordChange_eq`：∀ {R : Type u_1} {B : Type u_
2} {F : Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGrou
p F]   [inst_2 : NormedSpace R …
-/
theorem trivializationAt_coordChange_eq {b₀ b₁ b : B}
    (hb : b ∈ (trivializationAt F Z.Fiber b₀).baseSet ∩ (trivializationAt F Z.Fiber b₁).baseSet)
    (v : F) :
    (trivializationAt F Z.Fiber b₀).coordChangeL R (trivializationAt F Z.Fiber b₁) b v =
      Z.coordChange (Z.indexAt b₀) (Z.indexAt b₁) b v :=
  Z.localTriv_coordChange_eq _ _ hb v

end VectorBundleCore

end

/-! ### Vector prebundle -/

section

variable [NontriviallyNormedField R] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
  [NormedAddCommGroup F] [NormedSpace R F] [TopologicalSpace B] [∀ x, TopologicalSpace (E x)]

open TopologicalSpace

open VectorBundle

/-- This structure permits to define a vector bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space or the fibers.
The total space is hence given a topology in such a way that there is a fiber bundle structure for
which the partial equivalences are also open partial homeomorphisms and hence vector bundle
trivializations. The topology on the fibers is induced from the one on the total space.

The field `exists_coordChange` is stated as an existential statement (instead of 3 separate
fields), since it depends on propositional information (namely `e e' ∈ pretrivializationAtlas`).
This makes it inconvenient to explicitly define a `coordChange` function when constructing a
`VectorPrebundle`. -/
/-
**VectorPrebundle** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   {B : Type u_2} →     (F : Type u_3) →       (E : B → Ty
pe u_4) →         [inst : NontriviallyNormedField R] →           [inst_1 : (x : 
B) → AddCommMonoid (E x)] →             [(x : B) → _root_.Module R (E x)] →     
          [inst_3 : NormedAddCommGroup F] →                 [NormedSpace R F] → 
                  [TopologicalSpace B] → [(x : B) → TopologicalSpace (E x)] → Ty
pe (max (max u_2 u_3) u_4)
参数：max u_2 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This structure permits to define a vector bundle when trivializations are given 
as local
equivalences but there is not yet a topology on the total space or the fibers.
The total space is hence given a topology in such a way that there is a fiber bu
ndle structure for
which the partial equivalences are also open partial homeomorphisms and hence ve
ctor bundle
trivializations. The topology on the fibers is induced from the one on the total
 space.

The field `exists_coordChange` is stated as an existential statement (instead of
 3 separate
fields), since it depends on propositional information (namely `e e' ∈ pretrivia
lizationAtlas`).
This makes it inconvenient to explicitly define a `coordChange` function when co
nstructing a
`VectorPrebundle`.
-/
structure VectorPrebundle where
  pretrivializationAtlas : Set (Pretrivialization F (π F E))
  pretrivialization_linear' : ∀ e, e ∈ pretrivializationAtlas → e.IsLinear R
  pretrivializationAt : B → Pretrivialization F (π F E)
  mem_base_pretrivializationAt : ∀ x : B, x ∈ (pretrivializationAt x).baseSet
  pretrivialization_mem_atlas : ∀ x : B, pretrivializationAt x ∈ pretrivializationAtlas
  exists_coordChange : ∀ᵉ (e ∈ pretrivializationAtlas) (e' ∈ pretrivializationAtlas),
    ∃ f : B → F →L[R] F, ContinuousOn f (e.baseSet ∩ e'.baseSet) ∧
      ∀ᵉ (b ∈ e.baseSet ∩ e'.baseSet) (v : F), f b v = (e' ⟨b, e.symm b v⟩).2
  totalSpaceMk_isInducing : ∀ b : B, IsInducing (pretrivializationAt b ∘ .mk b)

namespace VectorPrebundle

variable {R E F}

/-- A randomly chosen coordinate change on a `VectorPrebundle`, given by
  the field `exists_coordChange`. -/
/-
**VectorPrebundle.coordChange** 是 Mathlib 中的一个定义，位于命名空间 `VectorPrebundle`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       {E : B → Ty
pe u_4} →         [inst : NontriviallyNormedField R] →           [inst_1 : (x : 
B) → AddCommMonoid (E x)] →             [inst_2 : (x : B) → _root_.Module R (E x
)] →               [inst_3 : NormedAddCommGroup F] →                 [inst_4 : N
ormedSpace R F] →                   [inst_5 : TopologicalSpace B] →             
        [inst_6 : (x : B) → TopologicalSpace (E x)] →                       (a :
 VectorPrebundle R F E) →                         {e e' : Bundle.Pretrivializati
on F Bundle.TotalSpace.proj} →                           e ∈ a.pretrivialization
Atlas → e' ∈ a.pretrivializationAtlas → B → F →L[R] F
参数：x : B；E x；x : B；E x；x : B；E x；a : VectorPrebundle R F E。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `VectorPrebundle.exists_coordChange`：∀ {R : Type u_1} {B : Type u_2} {F :
 Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x 
: B) → AddCommMonoid (E …

--- 原说明 ---
A randomly chosen coordinate change on a `VectorPrebundle`, given by
  the field `exists_coordChange`.
-/
def coordChange (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretrivializationAtlas) (b : B) : F →L[R] F :=
  Classical.choose (a.exists_coordChange e he e' he') b
/-
**VectorPrebundle.continuousOn_coordChange** 是 Mathlib 中的一个定理，位于命名空间 `VectorPreb
undle`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : (x : B) → TopologicalSpace
 (E x)]   (a : VectorPrebundle R F E) {e e' : Bundle.Pretrivialization F Bundle.
TotalSpace.proj}   (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretriviali
zationAtlas),   ContinuousOn (a.coordChange he he') (e.baseSet ∩ e'.baseSet)
参数：x : B；E x；x : B；E x；x : B；E x；a : VectorPrebundle R F E；he : e ∈ a.pretrivial
izationAtlas；he' : e' ∈ a.pretrivializationAtlas；a.coordChange he he'；e.baseSet 
∩ e'.baseSet。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `VectorPrebundle.exists_coordChange`：∀ {R : Type u_1} {B : Type u_2} {F :
 Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x 
: B) → AddCommMonoid (E …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem continuousOn_coordChange (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretrivializationAtlas) :
    ContinuousOn (a.coordChange he he') (e.baseSet ∩ e'.baseSet) :=
  (Classical.choose_spec (a.exists_coordChange e he e' he')).1
/-
**VectorPrebundle.coordChange_apply** 是 Mathlib 中的一个定理，位于命名空间 `VectorPrebundle`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : (x : B) → TopologicalSpace
 (E x)]   (a : VectorPrebundle R F E) {e e' : Bundle.Pretrivialization F Bundle.
TotalSpace.proj}   (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretriviali
zationAtlas) {b : B},   b ∈ e.baseSet ∩ e'.baseSet → ∀ (v : F), (a.coordChange h
e he' b) v = (↑e' ⟨b, e.symm b v⟩).2
参数：x : B；E x；x : B；E x；x : B；E x；a : VectorPrebundle R F E；he : e ∈ a.pretrivial
izationAtlas；he' : e' ∈ a.pretrivializationAtlas；v : F；a.coordChange he he' b；↑e
' ⟨b, e.symm b v⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `VectorPrebundle.exists_coordChange`：∀ {R : Type u_1} {B : Type u_2} {F :
 Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x 
: B) → AddCommMonoid (E …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem coordChange_apply (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretrivializationAtlas) {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    a.coordChange he he' b v = (e' ⟨b, e.symm b v⟩).2 :=
  (Classical.choose_spec (a.exists_coordChange e he e' he')).2 b hb v
/-
**VectorPrebundle.mk_coordChange** 是 Mathlib 中的一个定理，位于命名空间 `VectorPrebundle`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : (x : B) → TopologicalSpace
 (E x)]   (a : VectorPrebundle R F E) {e e' : Bundle.Pretrivialization F Bundle.
TotalSpace.proj}   (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretriviali
zationAtlas) {b : B},   b ∈ e.baseSet ∩ e'.baseSet → ∀ (v : F), (b, (a.coordChan
ge he he' b) v) = ↑e' ⟨b, e.symm b v⟩
参数：x : B；E x；x : B；E x；x : B；E x；a : VectorPrebundle R F E；he : e ∈ a.pretrivial
izationAtlas；he' : e' ∈ a.pretrivializationAtlas；v : F；b, (a.coordChange he he' 
b) v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.mk_symm`：mk_symm (e : Pretrivialization F (π F 
E)) {b : B} (hb : b in e.baseSet) (y : F) : TotalSpace.mk b (e.symm b y) = e.toP
artialEquiv.symm (b, y…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Bundle.Pretrivialization.coe_fst'`：coe_fst' (ex : proj x in e.baseSet) :
 (e x).1 = proj x
· 使用定理 `Bundle.Pretrivialization.proj_symm_apply'`：proj_symm_apply' {b : B} {x :
 F} (hx : b in e.baseSet) : proj (e.toPartialEquiv.symm (b, x)) = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `VectorPrebundle.coordChange_apply`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x :
 B) → AddCommMonoid (E …
-/
theorem mk_coordChange (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretrivializationAtlas) {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    (b, a.coordChange he he' b v) = e' ⟨b, e.symm b v⟩ := by
  ext
  · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
  · exact a.coordChange_apply he he' hb v

/-- Natural identification of `VectorPrebundle` as a `FiberPrebundle`. -/
/-
**VectorPrebundle.toFiberPrebundle** 是 Mathlib 中的一个定义，位于命名空间 `VectorPrebundle`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       {E : B → Ty
pe u_4} →         [inst : NontriviallyNormedField R] →           [inst_1 : (x : 
B) → AddCommMonoid (E x)] →             [inst_2 : (x : B) → _root_.Module R (E x
)] →               [inst_3 : NormedAddCommGroup F] →                 [inst_4 : N
ormedSpace R F] →                   [inst_5 : TopologicalSpace B] →             
        [inst_6 : (x : B) → TopologicalSpace (E x)] → VectorPrebundle R F E → Fi
berPrebundle F E
参数：x : B；E x；x : B；E x；x : B；E x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `VectorPrebundle.mem_base_pretrivializationAt`：∀ {R : Type u_1} {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [in
st_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `VectorPrebundle.pretrivialization_mem_atlas`：∀ {R : Type u_1} {B : Type 
u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [ins
t_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `VectorPrebundle.totalSpaceMk_isInducing`：∀ {R : Type u_1} {B : Type u_2}
 {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 
: (x : B) → AddCommMonoid (E …

--- 原说明 ---
Natural identification of `VectorPrebundle` as a `FiberPrebundle`.
-/
def toFiberPrebundle (a : VectorPrebundle R F E) : FiberPrebundle F E :=
  { a with
    continuous_trivChange := fun e he e' he' ↦ by
      have : ContinuousOn (fun x : B × F ↦ a.coordChange he' he x.1 x.2)
          ((e'.baseSet ∩ e.baseSet) ×ˢ univ) :=
        isBoundedBilinearMap_apply.continuous.comp_continuousOn
          ((a.continuousOn_coordChange he' he).prodMap continuousOn_id)
      rw [e.target_inter_preimage_symm_source_eq e', inter_comm]
      refine (continuousOn_fst.prodMk this).congr ?_
      rintro ⟨b, f⟩ ⟨hb, -⟩
      dsimp only [Function.comp_def, Prod.map]
      rw [a.mk_coordChange _ _ hb, e'.mk_symm hb.1] }

/-- Topology on the total space that will make the prebundle into a bundle. -/
@[instance_reducible]
/-
**VectorPrebundle.totalSpaceTopology** 是 Mathlib 中的一个定义，位于命名空间 `VectorPrebundle`
。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       {E : B → Ty
pe u_4} →         [inst : NontriviallyNormedField R] →           [inst_1 : (x : 
B) → AddCommMonoid (E x)] →             [inst_2 : (x : B) → _root_.Module R (E x
)] →               [inst_3 : NormedAddCommGroup F] →                 [inst_4 : N
ormedSpace R F] →                   [inst_5 : TopologicalSpace B] →             
        [inst_6 : (x : B) → TopologicalSpace (E x)] →                       Vect
orPrebundle R F E → TopologicalSpace (Bundle.TotalSpace F E)
参数：x : B；E x；x : B；E x；x : B；E x；Bundle.TotalSpace F E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Topology on the total space that will make the prebundle into a bundle.
-/
def totalSpaceTopology (a : VectorPrebundle R F E) : TopologicalSpace (TotalSpace F E) :=
  a.toFiberPrebundle.totalSpaceTopology

/-- Promotion from a `Pretrivialization` in the `pretrivializationAtlas` of a
`VectorPrebundle` to a `Trivialization`. -/
/-
**VectorPrebundle.trivializationOfMemPretrivializationAtlas** 是 Mathlib 中的一个定义，位
于命名空间 `VectorPrebundle`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       {E : B → Ty
pe u_4} →         [inst : NontriviallyNormedField R] →           [inst_1 : (x : 
B) → AddCommMonoid (E x)] →             [inst_2 : (x : B) → _root_.Module R (E x
)] →               [inst_3 : NormedAddCommGroup F] →                 [inst_4 : N
ormedSpace R F] →                   [inst_5 : TopologicalSpace B] →             
        [inst_6 : (x : B) → TopologicalSpace (E x)] →                       (a :
 VectorPrebundle R F E) →                         {e : Bundle.Pretrivialization 
F Bundle.TotalSpace.proj} →                           e ∈ a.pretrivializationAtl
as → Bundle.Trivialization F Bundle.TotalSpace.proj
参数：x : B；E x；x : B；E x；x : B；E x；a : VectorPrebundle R F E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promotion from a `Pretrivialization` in the `pretrivializationAtlas` of a
`VectorPrebundle` to a `Trivialization`.
-/
def trivializationOfMemPretrivializationAtlas (a : VectorPrebundle R F E)
    {e : Pretrivialization F (π F E)} (he : e ∈ a.pretrivializationAtlas) :
    @Trivialization B F _ _ _ a.totalSpaceTopology (π F E) :=
  a.toFiberPrebundle.trivializationOfMemPretrivializationAtlas he
/-
**VectorPrebundle.linear_trivializationOfMemPretrivializationAtlas** 是 Mathlib 中
的一个定理，位于命名空间 `VectorPrebundle`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : (x : B) → TopologicalSpace
 (E x)]   (a : VectorPrebundle R F E) {e : Bundle.Pretrivialization F Bundle.Tot
alSpace.proj}   (he : e ∈ a.pretrivializationAtlas), Bundle.Trivialization.IsLin
ear R (a.trivializationOfMemPretrivializationAtlas he)
参数：x : B；E x；x : B；E x；x : B；E x；a : VectorPrebundle R F E；he : e ∈ a.pretrivial
izationAtlas；a.trivializationOfMemPretrivializationAtlas he。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.IsLinear.linear`：∀ {R : Type u_1} {B : Type u_2
} {F : Type u_3} {E : B → Type u_4} {inst : Semiring R} {inst_1 : TopologicalSpa
ce F}   {inst_2 : TopologicalS…
· 使用定理 `VectorPrebundle.pretrivialization_linear'`：∀ {R : Type u_1} {B : Type u_
2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_
1 : (x : B) → AddCommMonoid (E …
-/
theorem linear_trivializationOfMemPretrivializationAtlas (a : VectorPrebundle R F E)
    {e : Pretrivialization F (π F E)} (he : e ∈ a.pretrivializationAtlas) :
    letI := a.totalSpaceTopology
    Trivialization.IsLinear R (trivializationOfMemPretrivializationAtlas a he) :=
  letI := a.totalSpaceTopology
  { linear := (a.pretrivialization_linear' e he).linear }

variable (a : VectorPrebundle R F E)
/-
**VectorPrebundle.mem_trivialization_at_source** 是 Mathlib 中的一个定理，位于命名空间 `Vector
Prebundle`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : (x : B) → TopologicalSpace
 (E x)]   (a : VectorPrebundle R F E) (b : B) (x : E b), ⟨b, x⟩ ∈ (a.pretriviali
zationAt b).source
参数：x : B；E x；x : B；E x；x : B；E x；a : VectorPrebundle R F E；b : B；x : E b；a.pretr
ivializationAt b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberPrebundle.mem_pretrivializationAt_source`：∀ {B : Type u_2} {F : Typ
e u_3} {E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace
 F]   [inst_2 : (x : B) → Topologic…
-/
theorem mem_trivialization_at_source (b : B) (x : E b) :
    ⟨b, x⟩ ∈ (a.pretrivializationAt b).source :=
  a.toFiberPrebundle.mem_pretrivializationAt_source b x

@[simp]
/-
**VectorPrebundle.totalSpaceMk_preimage_source** 是 Mathlib 中的一个定理，位于命名空间 `Vector
Prebundle`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : (x : B) → TopologicalSpace
 (E x)]   (a : VectorPrebundle R F E) (b : B), Bundle.TotalSpace.mk b ⁻¹' (a.pre
trivializationAt b).source = Set.univ
参数：x : B；E x；x : B；E x；x : B；E x；a : VectorPrebundle R F E；b : B；a.pretrivializa
tionAt b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberPrebundle.totalSpaceMk_preimage_source`：∀ {B : Type u_2} {F : Type 
u_3} {E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F
]   [inst_2 : (x : B) → Topologic…
-/
theorem totalSpaceMk_preimage_source (b : B) :
    .mk b ⁻¹' (a.pretrivializationAt b).source = univ :=
  a.toFiberPrebundle.totalSpaceMk_preimage_source b

@[continuity]
/-
**VectorPrebundle.continuous_totalSpaceMk** 是 Mathlib 中的一个定理，位于命名空间 `VectorPrebu
ndle`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : (x : B) → TopologicalSpace
 (E x)]   (a : VectorPrebundle R F E) (b : B), Continuous (Bundle.TotalSpace.mk 
b)
参数：x : B；E x；x : B；E x；x : B；E x；a : VectorPrebundle R F E；b : B；Bundle.TotalSpa
ce.mk b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberPrebundle.continuous_totalSpaceMk`：∀ {B : Type u_2} {F : Type u_3} 
{E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [
inst_2 : (x : B) → Topologic…
-/
theorem continuous_totalSpaceMk (b : B) :
    Continuous[_, a.totalSpaceTopology] (.mk b) :=
  a.toFiberPrebundle.continuous_totalSpaceMk b

/-- Make a `FiberBundle` from a `VectorPrebundle`; auxiliary construction for
`VectorPrebundle.toVectorBundle`. -/
@[instance_reducible]
/-
**VectorPrebundle.toFiberBundle** 是 Mathlib 中的一个定义，位于命名空间 `VectorPrebundle`。
形式化陈述：{R : Type u_1} →   {B : Type u_2} →     {F : Type u_3} →       {E : B → Ty
pe u_4} →         [inst : NontriviallyNormedField R] →           [inst_1 : (x : 
B) → AddCommMonoid (E x)] →             [inst_2 : (x : B) → _root_.Module R (E x
)] →               [inst_3 : NormedAddCommGroup F] →                 [inst_4 : N
ormedSpace R F] →                   [inst_5 : TopologicalSpace B] →             
        [inst_6 : (x : B) → TopologicalSpace (E x)] → (a : VectorPrebundle R F E
) → FiberBundle F E
参数：x : B；E x；x : B；E x；x : B；E x；a : VectorPrebundle R F E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a `FiberBundle` from a `VectorPrebundle`; auxiliary construction for
`VectorPrebundle.toVectorBundle`.
-/
def toFiberBundle : @FiberBundle B F _ _ _ a.totalSpaceTopology _ :=
  a.toFiberPrebundle.toFiberBundle

set_option backward.isDefEq.respectTransparency false in
/-- Make a `VectorBundle` from a `VectorPrebundle`.  Concretely this means
that, given a `VectorPrebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`VectorPrebundle.totalSpaceTopology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
/-
**VectorPrebundle.toVectorBundle** 是 Mathlib 中的一个定理，位于命名空间 `VectorPrebundle`。
形式化陈述：∀ {R : Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : 
NontriviallyNormedField R]   [inst_1 : (x : B) → AddCommMonoid (E x)] [inst_2 : 
(x : B) → _root_.Module R (E x)] [inst_3 : NormedAddCommGroup F]   [inst_4 : Nor
medSpace R F] [inst_5 : TopologicalSpace B] [inst_6 : (x : B) → TopologicalSpace
 (E x)]   (a : VectorPrebundle R F E), VectorBundle R F E
参数：x : B；E x；x : B；E x；x : B；E x；a : VectorPrebundle R F E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorPrebundle.linear_trivializationOfMemPretrivializationAtlas`：∀ {R :
 Type u_1} {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : Nontrivially
NormedField R]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `VectorPrebundle.continuousOn_coordChange`：∀ {R : Type u_1} {B : Type u_2
} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1
 : (x : B) → AddCommMonoid (E …
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VectorPrebundle.coordChange_apply`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x :
 B) → AddCommMonoid (E …
· 使用定理 `ContinuousLinearEquiv.coe_coe`：coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ⇑(e : M₁ -
>SL[σ₁₂] M₂) = e
· 使用定理 `Bundle.Trivialization.coordChangeL_apply`：∀ {R : Type u_1} {B : Type u_2
} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpa
ce F]   [inst_2 : TopologicalS…

--- 原说明 ---
Make a `VectorBundle` from a `VectorPrebundle`.  Concretely this means
that, given a `VectorPrebundle` structure for a sigma-type `E` -- which consists
 of a
number of "pretrivializations" identifying parts of `E` with product spaces `U ×
 F` -- one
establishes that for the topology constructed on the sigma-type using
`VectorPrebundle.totalSpaceTopology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology
).
-/
theorem toVectorBundle : @VectorBundle R _ F E _ _ _ _ _ _ a.totalSpaceTopology _ a.toFiberBundle :=
  letI := a.totalSpaceTopology; letI := a.toFiberBundle
  { trivialization_linear' := by
      rintro _ ⟨e, he, rfl⟩
      apply linear_trivializationOfMemPretrivializationAtlas
    continuousOn_coordChange' := by
      rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
      refine (a.continuousOn_coordChange he he').congr fun b hb ↦ ?_
      ext v
      have h₁ := a.linear_trivializationOfMemPretrivializationAtlas he
      have h₂ := a.linear_trivializationOfMemPretrivializationAtlas he'
      rw [trivializationOfMemPretrivializationAtlas] at h₁ h₂
      rw [a.coordChange_apply he he' hb v, ContinuousLinearEquiv.coe_coe,
        Trivialization.coordChangeL_apply]
      exacts [rfl, hb] }

end VectorPrebundle

namespace ContinuousLinearMap

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
variable {σ : 𝕜₁ →+* 𝕜₂}
variable {B' : Type*} [TopologicalSpace B']
variable [NormedSpace 𝕜₁ F] [∀ x, Module 𝕜₁ (E x)] [TopologicalSpace (TotalSpace F E)]
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜₂ F'] {E' : B' → Type*}
  [∀ x, AddCommMonoid (E' x)] [∀ x, Module 𝕜₂ (E' x)] [TopologicalSpace (TotalSpace F' E')]

variable [FiberBundle F E] [VectorBundle 𝕜₁ F E]
variable [∀ x, TopologicalSpace (E' x)] [FiberBundle F' E'] [VectorBundle 𝕜₂ F' E']
variable (F' E')

/-- When `ϕ` is a continuous (semi)linear map between the fibers `E x` and `E' y` of two vector
bundles `E` and `E'`, `ContinuousLinearMap.inCoordinates F E F' E' x₀ x y₀ y ϕ` is a coordinate
change of this continuous linear map w.r.t. the chart around `x₀` and the chart around `y₀`.

It is defined by composing `ϕ` with appropriate coordinate changes given by the vector bundles
`E` and `E'`.
We use the operations `Bundle.Trivialization.continuousLinearMapAt` and
`Bundle.Trivialization.symmL` in the definition, instead of
`Bundle.Trivialization.continuousLinearEquivAt`, so that
`ContinuousLinearMap.inCoordinates` is defined everywhere (but see
`ContinuousLinearMap.inCoordinates_eq`).

This is the (second component of the) underlying function of a trivialization of the hom-bundle
(see `hom_trivializationAt_apply`). However, note that `ContinuousLinearMap.inCoordinates` is
defined even when `x` and `y` live in different base sets.
Therefore, it is also convenient when working with the hom-bundle between pulled back bundles.
-/
/-
**ContinuousLinearMap.inCoordinates** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：{B : Type u_2} →   (F : Type u_3) →     (E : B → Type u_4) →       [inst :
 (x : B) → AddCommMonoid (E x)] →         [inst_1 : NormedAddCommGroup F] →     
      [inst_2 : TopologicalSpace B] →             [inst_3 : (x : B) → Topologica
lSpace (E x)] →               {𝕜₁ : Type u_5} →                 {𝕜₂ : Type u_6} 
→                   [inst_4 : NontriviallyNormedField 𝕜₁] →                     
[inst_5 : NontriviallyNormedField 𝕜₂] →                       {σ : 𝕜₁ →+* 𝕜₂} → 
                        {B' : Type u_7} →                           [inst_6 : To
pologicalSpace B'] →                             [inst_7 : NormedSpace 𝕜₁ F] →  
                             [inst_8 : (x : B) → _root_.Module 𝕜₁ (E x)] →      
                           [inst_9 : TopologicalSpace (Bundle.TotalSpace F E)] →
                                   (F' : Type u_8) →                            
         [inst_10 : NormedAddCommGroup F'] →                                    
   [inst_11 : NormedSpace 𝕜₂ F'] →                                         (E' :
 B' → Type u_9) →                                           [inst_12 : (x : B') 
→ AddCommMonoid (E' x)] →                                             [inst_13 :
 (x : B') → _root_.Module 𝕜₂ (E' x)] →                                          
     [inst_14 : TopologicalSpace (Bundle.TotalSpace F' E')] →                   
                              [inst_15 : FiberBundle F E] →                     
                              [VectorBundle 𝕜₁ F E] →                           
                          [inst_17 : (x : B') → TopologicalSpace (E' x)] →      
                                                 [inst_18 : FiberBundle F' E'] →
                                                         [VectorBundle 𝕜₂ F' E']
 →                                                           B → (x : B) → B' → 
(y : B') → (E x →SL[σ] E' y) → F →SL[σ] F'
参数：F : Type u_3；E : B → Type u_4；x : B；E x；x : B；E x；x : B；E x；Bundle.TotalSpace
 F E；F' : Type u_8；E' : B' → Type u_9；x : B'；E' x；x : B'；E' x；Bundle.TotalSpace 
F' E'；x : B'；E' x；x : B；y : B'；E x →SL[σ] E' y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `ϕ` is a continuous (semi)linear map between the fibers `E x` and `E' y` of
 two vector
bundles `E` and `E'`, `ContinuousLinearMap.inCoordinates F E F' E' x₀ x y₀ y ϕ` 
is a coordinate
change of this continuous linear map w.r.t. the chart around `x₀` and the chart 
around `y₀`.

It is defined by composing `ϕ` with appropriate coordinate changes given by the 
vector bundles
`E` and `E'`.
We use the operations `Bundle.Trivialization.continuousLinearMapAt` and
`Bundle.Trivialization.symmL` in the definition, instead of
`Bundle.Trivialization.continuousLinearEquivAt`, so that
`ContinuousLinearMap.inCoordinates` is defined everywhere (but see
`ContinuousLinearMap.inCoordinates_eq`).

This is the (second component of the) underlying function of a trivialization of
 the hom-bundle
(see `hom_trivializationAt_apply`). However, note that `ContinuousLinearMap.inCo
ordinates` is
defined even when `x` and `y` live in different base sets.
Therefore, it is also convenient when working with the hom-bundle between pulled
 back bundles.
-/
def inCoordinates (x₀ x : B) (y₀ y : B') (ϕ : E x →SL[σ] E' y) : F →SL[σ] F' :=
  ((trivializationAt F' E' y₀).continuousLinearMapAt 𝕜₂ y).comp <|
    ϕ.comp <| (trivializationAt F E x₀).symmL 𝕜₁ x

variable {E E' F F'}

/-- Rewrite `ContinuousLinearMap.inCoordinates` using continuous linear equivalences. -/
/-
**ContinuousLinearMap.inCoordinates_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：∀ {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : (x : B) → AddCo
mmMonoid (E x)]   [inst_1 : NormedAddCommGroup F] [inst_2 : TopologicalSpace B] 
[inst_3 : (x : B) → TopologicalSpace (E x)]   {𝕜₁ : Type u_5} {𝕜₂ : Type u_6} [i
nst_4 : NontriviallyNormedField 𝕜₁] [inst_5 : NontriviallyNormedField 𝕜₂]   {σ :
 𝕜₁ →+* 𝕜₂} {B' : Type u_7} [inst_6 : TopologicalSpace B'] [inst_7 : NormedSpace
 𝕜₁ F]   [inst_8 : (x : B) → _root_.Module 𝕜₁ (E x)] [inst_9 : TopologicalSpace 
(Bundle.TotalSpace F E)] {F' : Type u_8}   [inst_10 : NormedAddCommGroup F'] [in
st_11 : NormedSpace 𝕜₂ F'] {E' : B' → Type u_9}   [inst_12 : (x : B') → AddCommM
onoid (E' x)] [inst_13 : (x : B') → _root_.Module 𝕜₂ (E' x)]   [inst_14 : Topolo
gicalSpace (Bundle.TotalSpace F' E')] [inst_15 : FiberBundle F E] [inst_16 : Vec
torBundle 𝕜₁ F E]   [inst_17 : (x : B') → TopologicalSpace (E' x)] [inst_18 : Fi
berBundle F' E'] [inst_19 : VectorBundle 𝕜₂ F' E']   {x₀ x : B} {y₀ y : B'} {ϕ :
 E x →SL[σ] E' y} (hx : x ∈ (trivializationAt F E x₀).baseSet)   (hy : y ∈ (triv
ializationAt F' E' y₀).baseSet),   ContinuousLinearMap.inCoordinates F E F' E' x
₀ x y₀ y ϕ =     ↑(Bundle.Trivialization.continuousLinearEquivAt 𝕜₂ (trivializat
ionAt F' E' y₀) y hy) ∘SL       ϕ ∘SL ↑(Bundle.Trivialization.continuousLinearEq
uivAt 𝕜₁ (trivializationAt F E x₀) x hx).symm
参数：x : B；E x；x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B'；E' x；x : B'；E' x；B
undle.TotalSpace F' E'；x : B'；E' x；hx : x ∈ (trivializationAt F E x₀).baseSet；hy
 : y ∈ (trivializationAt F' E' y₀).baseSet；Bundle.Trivialization.continuousLinea
rEquivAt 𝕜₂ (trivializationAt F' E' y₀) y hy；Bundle.Trivialization.continuousLin
earEquivAt 𝕜₁ (trivializationAt F E x₀) x hx。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Bundle.Trivialization.coe_continuousLinearEquivAt_eq`：∀ {R : Type u_1} {
B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField 
R]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bundle.Trivialization.symm_continuousLinearEquivAt_eq`：∀ {R : Type u_1} 
{B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField
 R]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Rewrite `ContinuousLinearMap.inCoordinates` using continuous linear equivalences
.
-/
theorem inCoordinates_eq {x₀ x : B} {y₀ y : B'} {ϕ : E x →SL[σ] E' y}
    (hx : x ∈ (trivializationAt F E x₀).baseSet) (hy : y ∈ (trivializationAt F' E' y₀).baseSet) :
    inCoordinates F E F' E' x₀ x y₀ y ϕ =
      ((trivializationAt F' E' y₀).continuousLinearEquivAt 𝕜₂ y hy : E' y →L[𝕜₂] F').comp
        (ϕ.comp <|
          (((trivializationAt F E x₀).continuousLinearEquivAt 𝕜₁ x hx).symm : F →L[𝕜₁] E x)) := by
  ext
  simp_rw [inCoordinates, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    Trivialization.coe_continuousLinearEquivAt_eq, Trivialization.symm_continuousLinearEquivAt_eq]

set_option backward.isDefEq.respectTransparency false in
/-- Rewrite `ContinuousLinearMap.inCoordinates` in a `VectorBundleCore`. -/
/-
**ContinuousLinearMap._root_.VectorBundleCore.inCoordinates_eq** 是 Mathlib 中的一个定
理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rewrite `ContinuousLinearMap.inCoordinates` in a `VectorBundleCore`.
-/
protected theorem _root_.VectorBundleCore.inCoordinates_eq {ι ι'} (Z : VectorBundleCore 𝕜₁ B F ι)
    (Z' : VectorBundleCore 𝕜₂ B' F' ι') {x₀ x : B} {y₀ y : B'} (ϕ : F →SL[σ] F')
    (hx : x ∈ Z.baseSet (Z.indexAt x₀)) (hy : y ∈ Z'.baseSet (Z'.indexAt y₀)) :
    inCoordinates F Z.Fiber F' Z'.Fiber x₀ x y₀ y ϕ =
      (Z'.coordChange (Z'.indexAt y) (Z'.indexAt y₀) y).comp
        (ϕ.comp <| Z.coordChange (Z.indexAt x₀) (Z.indexAt x) x) := by
  simp_rw [inCoordinates, Z'.trivializationAt_continuousLinearMapAt hy,
    Z.trivializationAt_symmL hx]

end ContinuousLinearMap

end

