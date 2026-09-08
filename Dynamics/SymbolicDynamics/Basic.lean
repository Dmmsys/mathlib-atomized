/-
Copyright (c) 2025 Silvère Gangloff. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Silvère Gangloff
-/
module

public import Mathlib.Topology.Separation.Basic

/-!
# Symbolic dynamics on cancellative monoids

This file develops a minimal API for symbolic dynamics over a
**left-cancellative monoid** `G`—formally, a structure carrying `[Monoid G]`
and `[IsLeftCancelMul G]` (which becomes `[AddMonoid G]` and
`[IsLeftCancelAdd G]` in the additive form). Throughout the documentation we use the
**additive** notations, which are the most common in symbolic dynamics, although
all the notions introduced are defined in the multiplicative notations and adapted
to the additive notation.

Given a finite alphabet `A`, the ambient configuration space is the set of
functions `G → A`, endowed with the product topology. We define the
left-translation action, cylinders, finite patterns, their occurrences,
forbidden sets, and subshifts (closed, shift-invariant subsets). Basic
topological facts (e.g. cylinders are clopen, occurrence sets are clopen,
forbidden sets are closed) are proved under discreteness assumptions on
the alphabet.

The development is generic for left-cancellative monoids. This covers both
groups (the standard setting of symbolic dynamics) and more general monoids
where cancellation holds but inverses may not exist. Geometry specific to
`ℤ^d` (boxes/cubes and the box-based entropy) is deferred to a separate
specialization.

## Why cancellativity?

Some constructions, such as translating a finite pattern to occur at a point `v`,
require solving equations of the form `w + v = h`. For this to have a unique
solution `w` given `h` and `v`, we assume **left-cancellation**:
if `v + a = v + b` then `a = b`. This allows us to define
`Pattern.shift` (which shifts a pattern) without using inverses,
so that the theory works not only for groups but also for cancellative monoids.

## Main definitions

* `shift g x` — left translation: in additive notation `(shift v x) u = x (v + u)` (using the
**left** action of `G` on configurations).
* `cylinder U x` — configurations agreeing with `x` on a finite set `U ⊆ G`.
* `Pattern A G` — a configuration which takes
default value outside of a finite support, together with this support.
* `Pattern.occursInAt p x g` — occurrence of `p` in `x` at translate `g`.
* `forbidden F` — configurations avoiding every pattern in `F`.
* `Subshift A G` — closed, shift-invariant subsets of the full shift.
* `MulSubshift.ofForbidden F` — the subshift defined by forbidding a family of patterns.
* `subshift_of_finite_type F` — a subshift of finite type defined by a finite set of
forbidden patterns.
* `languageOn X U` — the set of patterns of shape `U` obtained by restricting some `x ∈ X`.

## Design choice: ambient vs. inner (subshift-relative) viewpoint

All core notions (shift, cylinder, occurrence, language, …) are defined **in the
ambient full shift** `G → A`. A subshift is then a closed, invariant subset,
bundled as `Subshift A G`. Working inside a subshift is done by restriction.

**Motivation.**

If cylinders and shifts were defined only *inside* a subshift, local ergonomics
would improve but global operations would become awkward. For instance, to prove
that for finite shape `U`:

`languageOn (X ∪ Y) U = languageOn X U ∪ languageOn Y U,`

one must eventually move both sides to the ambient pattern type. Similar issues
arise for intersections, factors, and products. By contrast, with ambient
definitions these set-theoretic identities are tautological.
Thus the file develops the theory ambiently, and subshifts reuse it by restriction.

**Working inside a subshift.**

For `Y : Subshift A G`, cylinders and occurrence sets *inside `Y`* are simply
preimages of the ambient ones under the inclusion `Y → (G → A)`. For example:

`{ y : Y | ∀ i ∈ U, (y : G → A) i = (x : G → A) i } = (Subtype.val) ⁻¹' (cylinder U (x : G → A)).`

Shift invariance guarantees that the ambient shift restricts to `Y`.

**Ergonomics.**

Thin wrappers (e.g. `Subshift.shift`, `Subshift.cylinder`, `Subshift.languageOn`)
may be added for convenience. They introduce no new theory and unfold to the
ambient definitions.

## Namespacing policy

All ambient definitions live under the namespace `SymbolicDynamics.FullShift`.
If inner, subshift-relative wrappers are provided, they will be placed in the
subnamespace `SymbolicDynamics.Subshift`. This separation avoids name clashes
between the two viewpoints, since both may naturally want to reuse names like
`cylinder`, `shift`, `occursAt`, or `languageOn`.

## Implementation notes

* Openness results for cylinders and occurrence sets use
  `[DiscreteTopology A]`. Closeness results use `[T1Space A]`.
-/

@[expose] public section

noncomputable section
open Set Topology

namespace SymbolicDynamics

namespace FullShift

/-! ## Full shift and shift action -/

section ShiftDefinition

variable {A G : Type*} [Monoid G]

/-- The **left-translation shift** on configurations.

We call *configuration* an element of `G → A`.

Given a configuration `x : G → A` and an element `g : G` of the monoid, the shifted configuration
`mulShift g x` is defined by `(mulShift g x) h = x (g * h)`.

Intuitively, this moves the whole configuration "in the direction of `g`": the value
at position `h` in the shifted configuration is the value that was at position
`g * h` in the original one.

For example, if `G = ℤ` (with addition) and `A = {0, 1}`, then
`mulShift 1 x` is the sequence obtained from `x` by shifting every symbol one
step to the left. -/
@[to_additive /-- The **left-translation shift** on configurations, in additive notation.

We call *configuration* an element of `G → A`.

Given a configuration `x : G → A` and an element `g : G` of the additive monoid,
the shifted configuration `shift g x` is defined by `(shift g x) h = x (g + h)`.

Intuitively, this moves the whole configuration "in the direction of `g`": the value
at position `h` in the shifted configuration is the value that was at position
`g + h` in the original one.

For example, if `G = ℤ` and `A = {0, 1}`, then
`shift 1 x` is the sequence obtained from `x` by shifting every symbol one
step to the left. -/]
/-
**SymbolicDynamics.FullShift.mulShift** 是 Mathlib 中的一个定义，位于命名空间 `SymbolicDynamic
s.FullShift`。
形式化陈述：mulShift (g : G) (x : G -> A) : G -> A
参数：g : G；x : G -> A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulShift (g : G) (x : G → A) : G → A :=
  fun h => x (g * h)
/-
**SymbolicDynamics.FullShift.mulShift_apply** 是 Mathlib 中的一个定理，位于命名空间 `SymbolicD
ynamics.FullShift`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} [inst : Monoid G] (g : G) (x : G → A) (h :
 G),   SymbolicDynamics.FullShift.mulShift g x h = x (g * h)
参数：g : G；x : G → A；h : G；g * h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma mulShift_apply (g : G) (x : G → A) (h : G) :
    mulShift g x h = x (g * h) := rfl
/-
**SymbolicDynamics.FullShift.mulShift_one** 是 Mathlib 中的一个定理，位于命名空间 `SymbolicDyn
amics.FullShift`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} [inst : Monoid G] (x : G → A), SymbolicDyn
amics.FullShift.mulShift 1 x = x
参数：x : G → A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive (attr := simp)] lemma mulShift_one (x : G → A) : mulShift (1 : G) x = x := by
  ext h; simp [mulShift]

/-- Composition of left-translation shifts corresponds to multiplication in the monoid `G`. -/
@[to_additive
/-- Composition of left-translation shifts corresponds to addition in the additive monoid `G`. -/]
/-
**SymbolicDynamics.FullShift.mulShift_mul** 是 Mathlib 中的一个引理，位于命名空间 `SymbolicDyn
amics.FullShift`。
形式化陈述：mulShift_mul (g₁ g₂ : G) (x : G -> A) : mulShift (g₁ * g₂) x = mulShift g₂
 (mulShift g₁ x)
参数：g₁ g₂ : G；x : G -> A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulShift_mul (g₁ g₂ : G) (x : G → A) :
    mulShift (g₁ * g₂) x = mulShift g₂ (mulShift g₁ x) := by
  ext h; simp [mulShift, mul_assoc]

variable [TopologicalSpace A]

/-- The left-translation shift is continuous. -/
@[to_additive (attr := fun_prop)
/-- The left-translation shift is continuous. -/]
/-
**SymbolicDynamics.FullShift.continuous_mulShift** 是 Mathlib 中的一个引理，位于命名空间 `Symb
olicDynamics.FullShift`。
形式化陈述：continuous_mulShift (g : G) : Continuous (mulShift (A
参数：g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
lemma continuous_mulShift (g : G) :
    Continuous (mulShift (A := A) g) := by
  -- coordinate projections are continuous; composition preserves continuity
  unfold mulShift
  fun_prop

end ShiftDefinition

/-! ## Cylinders -/

section Cylinders

variable {A G : Type*}

/-- A *cylinder set* is the set of all configurations that agree with a given
reference configuration `x` on a fixed finite subset `U` of the index set `G`.

The set `U` is called the *support* of the cylinder.

Intuitively, cylinders specify the "letters" on finitely many coordinates, while
leaving all other coordinates free. For example, in the full shift `{0, 1}^ℤ`,
the cylinder determined by `U = {0, 1}` and `x 0 = 1, x 1 = 0` consists of all
bi-infinite sequences of `0`s and `1`s whose entries on positions `0` and `1`
respectively are `1` and `0`.

When `A` has the discrete topology, cylinder sets form a basis of clopen sets
for the product topology on `G → A`. -/
/-
**SymbolicDynamics.FullShift.cylinder** 是 Mathlib 中的一个定义，位于命名空间 `SymbolicDynamic
s.FullShift`。
形式化陈述：cylinder (U : Finset G) (x : G -> A) : Set (G -> A)
参数：U : Finset G；x : G -> A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *cylinder set* is the set of all configurations that agree with a given
reference configuration `x` on a fixed finite subset `U` of the index set `G`.

The set `U` is called the *support* of the cylinder.

Intuitively, cylinders specify the "letters" on finitely many coordinates, while
leaving all other coordinates free. For example, in the full shift `{0, 1}^ℤ`,
the cylinder determined by `U = {0, 1}` and `x 0 = 1, x 1 = 0` consists of all
bi-infinite sequences of `0`s and `1`s whose entries on positions `0` and `1`
respectively are `1` and `0`.

When `A` has the discrete topology, cylinder sets form a basis of clopen sets
for the product topology on `G → A`.
-/
def cylinder (U : Finset G) (x : G → A) : Set (G → A) :=
  { y | ∀ i ∈ U, y i = x i }

/-- A cylinder set on `U` is the `Set.pi` over `U` of the singletons `{x i}`,
viewed as a subset of `G → A`. Equivalently, it is the preimage of that product
of singletons in `U → A` under the restriction map `(G → A) → (U → A)`. -/
/-
**SymbolicDynamics.FullShift.cylinder_eq_set_pi** 是 Mathlib 中的一个引理，位于命名空间 `Symbo
licDynamics.FullShift`。
形式化陈述：cylinder_eq_set_pi (U : Finset G) (x : G -> A) : cylinder U x = Set.pi (↑U
 : Set G) (fun i => ({x i} : Set A))
参数：U : Finset G；x : G -> A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A cylinder set on `U` is the `Set.pi` over `U` of the singletons `{x i}`,
viewed as a subset of `G → A`. Equivalently, it is the preimage of that product
of singletons in `U → A` under the restriction map `(G → A) → (U → A)`.
-/
lemma cylinder_eq_set_pi (U : Finset G) (x : G → A) :
    cylinder U x = Set.pi (↑U : Set G) (fun i => ({x i} : Set A)) := by
  ext y; simp [cylinder, Set.pi]
/-
**SymbolicDynamics.FullShift.mem_cylinder** 是 Mathlib 中的一个引理，位于命名空间 `SymbolicDyn
amics.FullShift`。
形式化陈述：mem_cylinder {U : Finset G} {x y : G -> A} : y in cylinder U x ↔ forall i 
in U, y i = x i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_cylinder {U : Finset G} {x y : G → A} :
    y ∈ cylinder U x ↔ ∀ i ∈ U, y i = x i := Iff.rfl

variable [TopologicalSpace A]

/-- Cylinders are open when `A` is discrete. -/
/-
**SymbolicDynamics.FullShift.isOpen_cylinder** 是 Mathlib 中的一个引理，位于命名空间 `Symbolic
Dynamics.FullShift`。
形式化陈述：isOpen_cylinder [DiscreteTopology A] (U : Finset G) (x : G -> A) : IsOpen 
(cylinder U x)
参数：U : Finset G；x : G -> A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SymbolicDynamics.FullShift.cylinder_eq_set_pi`：cylinder_eq_set_pi (U : F
inset G) (x : G -> A) : cylinder U x = Set.pi (↑U : Set G) (fun i => ({x i} : Se
t A))
· 使用定理 `isOpen_set_pi`：isOpen_set_pi {i : Set ι} {s : forall a, Set (A a)} (hi :
 i.Finite) (hs : forall a in i, IsOpen (s a)) : IsOpen (pi i s)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Cylinders are open when `A` is discrete.
-/
lemma isOpen_cylinder [DiscreteTopology A] (U : Finset G) (x : G → A) :
    IsOpen (cylinder U x) := by
  simpa [cylinder_eq_set_pi U x] using isOpen_set_pi (U.finite_toSet) (by simp)

/-- Cylinders are closed when `A` is a T1 Space. -/
/-
**SymbolicDynamics.FullShift.isClosed_cylinder** 是 Mathlib 中的一个引理，位于命名空间 `Symbol
icDynamics.FullShift`。
形式化陈述：isClosed_cylinder [T1Space A] (U : Finset G) (x : G -> A) : IsClosed (cyli
nder U x)
参数：U : Finset G；x : G -> A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SymbolicDynamics.FullShift.cylinder_eq_set_pi`：cylinder_eq_set_pi (U : F
inset G) (x : G -> A) : cylinder U x = Set.pi (↑U : Set G) (fun i => ({x i} : Se
t A))
· 使用定理 `isClosed_set_pi`：isClosed_set_pi {i : Set ι} {s : forall a, Set (A a)} (
hs : forall a in i, IsClosed (s a)) : IsClosed (pi i s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Cylinders are closed when `A` is a T1 Space.
-/
lemma isClosed_cylinder [T1Space A] (U : Finset G) (x : G → A) :
    IsClosed (cylinder U x) := by
  simpa [cylinder_eq_set_pi U x] using isClosed_set_pi (by simp)

end Cylinders

/-! ## Patterns and occurrences -/

/-- A *subshift* on an alphabet `A` is a closed, shift-invariant subset of `G → A`. Formally, it is
composed of:
* `carrier`: the underlying set of allowed configurations.
* `isClosed`: the set is topologically closed in `A^G`.
* `mapsTo`: the set is invariant under all left-translation shifts
  `(shift g)`. -/
/-
**SymbolicDynamics.FullShift.Subshift** 是 Mathlib 中的一个归纳类型，位于命名空间 `SymbolicDynam
ics.FullShift`。
形式化陈述：(A : Type u_1) → [TopologicalSpace A] → (G : Type u_2) → [AddMonoid G] → T
ype (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *subshift* on an alphabet `A` is a closed, shift-invariant subset of `G → A`. 
Formally, it is
composed of:
* `carrier`: the underlying set of allowed configurations.
* `isClosed`: the set is topologically closed in `A^G`.
* `mapsTo`: the set is invariant under all left-translation shifts
  `(shift g)`.
-/
structure Subshift (A : Type*) [TopologicalSpace A] (G : Type*) [AddMonoid G] where
  /-- The underlying set of configurations (additive monoid version). -/
  carrier : Set (G → A)
  /-- Closedness of `carrier`. -/
  isClosed : IsClosed carrier
  /-- Shift invariance of `carrier` for the additive shift `shift`. -/
  mapsTo : ∀ g : G, MapsTo (shift g) carrier carrier

section MulSubshiftDef
variable (A : Type*) [TopologicalSpace A]
variable (G : Type*) [Monoid G]

/-- A *subshift* on an alphabet `A` over a multiplicative monoid `G` is a closed,
shift-invariant subset of `G → A`, where the shift is given by left-multiplication.
Formally, it is composed of:
* `carrier`: the underlying set of allowed configurations.
* `isClosed`: the set is topologically closed in `A^G`.
* `mapsTo`: the set is invariant under all left-translation shifts
  `(mulShift g)`. -/
@[to_additive existing]
/-
**SymbolicDynamics.FullShift.MulSubshift** 是 Mathlib 中的一个归纳类型，位于命名空间 `SymbolicDy
namics.FullShift`。
形式化陈述：(A : Type u_1) → [TopologicalSpace A] → (G : Type u_2) → [Monoid G] → Type
 (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *subshift* on an alphabet `A` over a multiplicative monoid `G` is a closed,
shift-invariant subset of `G → A`, where the shift is given by left-multiplicati
on.
Formally, it is composed of:
* `carrier`: the underlying set of allowed configurations.
* `isClosed`: the set is topologically closed in `A^G`.
* `mapsTo`: the set is invariant under all left-translation shifts
  `(mulShift g)`.
-/
structure MulSubshift where
  /-- The underlying set of configurations. -/
  carrier : Set (G → A)
  /-- Closedness of `carrier`. -/
  isClosed : IsClosed carrier
  /-- Shift invariance of `carrier`. -/
  mapsTo : ∀ g : G, MapsTo (mulShift g) carrier carrier

end MulSubshiftDef

/-- Example: the **full shift** on alphabet `A` over the multiplicative monoid `G`.
It is the subshift whose underlying set is the set of all configurations
`G → A`. -/
@[to_additive fullShift
/-- Example: the **full shift** on alphabet `A` over the additive monoid `G`.

It is the subshift whose underlying set is the set of all configurations
`G → A`.
-/]
/-
**SymbolicDynamics.FullShift.mulFullShift** 是 Mathlib 中的一个定义，位于命名空间 `SymbolicDyn
amics.FullShift`。
形式化陈述：mulFullShift (A G) [TopologicalSpace A] [Monoid G] : MulSubshift A G where
 carrier
参数：A G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
def mulFullShift (A G) [TopologicalSpace A] [Monoid G] : MulSubshift A G where
  carrier := Set.univ
  isClosed := isClosed_univ
  mapsTo := fun _ _ _ => trivial

/-- A *pattern* is a finite configuration in the full shift `A^G`.

It consists of:
* a full configuration `config : G → A` in the full shift;
* a finite subset `support : Finset G` of coordinates, called the support of `p`;
* a proof `condition` that outside `support`, `config` takes the default value of `A`.

Intuitively, a pattern is a "partial configuration" specifying finitely many values of
a configuration in `G → A` (the rest being `default`).
Patterns are the basic building blocks used to define subshifts via forbidden configurations.
Note that each pattern corresponds to a cylinder, which is the set of configurations
which agree with this pattern on its support. -/
/-
**SymbolicDynamics.FullShift.Pattern** 是 Mathlib 中的一个归纳类型，位于命名空间 `SymbolicDynami
cs.FullShift`。
形式化陈述：(A : Type u_1) → Type u_2 → [Inhabited A] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *pattern* is a finite configuration in the full shift `A^G`.

It consists of:
* a full configuration `config : G → A` in the full shift;
* a finite subset `support : Finset G` of coordinates, called the support of `p`
;
* a proof `condition` that outside `support`, `config` takes the default value o
f `A`.

Intuitively, a pattern is a "partial configuration" specifying finitely many val
ues of
a configuration in `G → A` (the rest being `default`).
Patterns are the basic building blocks used to define subshifts via forbidden co
nfigurations.
Note that each pattern corresponds to a cylinder, which is the set of configurat
ions
which agree with this pattern on its support.
-/
structure Pattern (A : Type*) (G : Type*) [Inhabited A] where
  /-- The full configuration in the full shift `A^G`. -/
  config : G → A
  /-- Finite support of the pattern. -/
  support : Finset G
  /-- Outside the support, `config` takes the default value of `A`. -/
  condition : ∀ g ∉ support, config g = default

section Forbidden

variable {A G : Type*} [Inhabited A] [Monoid G]

/-- `p.mulOccursInAt x g` means that the finite pattern
`p` appears in the configuration `x`
at position `g`.

Formally: for every position `h` in the support of `p`, the value of the configuration
at `g * h` coincides with the value of `p.config` at `h`.

Intuitively, if you shift the configuration `x` by `g` (using `mulShift g`),
then on the support of `p` you exactly recover the pattern `p`. This is the basic
notion of "pattern occurrence" used to define subshifts via forbidden patterns. -/
@[to_additive Pattern.occursInAt
/-- `p.occursInAt x g` means that the finite pattern `p` appears in the configuration `x`
at position `g`.

Formally: for every position `h` in the support of `p`, the value of the configuration
at `g + h` coincides with the value of `p.config` at `h`.

Intuitively, if you shift the configuration `x` by `g` (using `shift g`),
then on the support of `p` you exactly recover the pattern `p`. This is the basic
notion of "pattern occurrence" used to define subshifts via forbidden patterns. -/]
/-
**SymbolicDynamics.FullShift.Pattern.mulOccursInAt** 是 Mathlib 中的一个定义，位于命名空间 `Sy
mbolicDynamics.FullShift.Pattern`。
形式化陈述：{A : Type u_1} →   {G : Type u_2} → [inst : Inhabited A] → [Monoid G] → Sy
mbolicDynamics.FullShift.Pattern A G → (G → A) → G → Prop
参数：G → A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Pattern.mulOccursInAt (p : Pattern A G) (x : G → A) (g : G) : Prop :=
  ∀ (h) (_ : h ∈ p.support), x (g * h) = p.config h

/-- `mulForbidden F` is the set of configurations that avoid every pattern in `F`.

Formally: `x ∈ mulForbidden F` if and only if for every pattern `p ∈ F` and every
monoid element `g : G`, the pattern `p` does not occur in `x` at position `g`.

Intuitively, `mulForbidden F` is the shift space defined by declaring the finite set
(or family) of patterns `F` to be *forbidden*. A configuration belongs to the subshift if and only
it avoids all the forbidden patterns. -/
@[to_additive forbidden
/-- `forbidden F` is the set of configurations that avoid every pattern in `F`.

Formally: `x ∈ forbidden F` if and only if for every pattern `p ∈ F` and every
monoid element `g : G`, the pattern `p` does not occur in `x` at position `g`.

Intuitively, `forbidden F` is the shift space defined by declaring the finite set
(or family) of patterns `F` to be *forbidden*. A configuration belongs to the subshift if and only
it avoids all the forbidden patterns. -/]
/-
**SymbolicDynamics.FullShift.mulForbidden** 是 Mathlib 中的一个定义，位于命名空间 `SymbolicDyn
amics.FullShift`。
形式化陈述：mulForbidden (F : Set (Pattern A G)) : Set (G -> A)
参数：F : Set (Pattern A G)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulForbidden (F : Set (Pattern A G)) : Set (G → A) :=
  { x | ∀ p ∈ F, ∀ g : G, ¬ p.mulOccursInAt x g }

end Forbidden

section OccursInAt

variable {A : Type*} [Inhabited A]
variable {G : Type*} [Monoid G] [IsLeftCancelMul G]

/-- Translate a finite pattern `p` so that it occurs at the translate `v`, before completing into
a configuration.

On input `h : G`, we proceed as follows:
* if `h` lies in the left-translate of the support, i.e. `h ∈ p.support.image (v * ·)`,
  choose (noncomputably) `w ∈ p.support` with `v * w = h` and return `p.config w`;
* otherwise return `default`.

This definition does not assume left-cancellation; it only *chooses* a preimage.
Uniqueness (and the usual equations such as `Pattern.mulShift p v (v * w) = p.config w`)
require a left-cancellation hypothesis and are proved in separate lemmas.
-/
@[to_additive
/-- Translate a finite pattern `p` so that it occurs at the translate `v`, before completing into
a configuration.

On input `h : G`, we proceed as follows:
* if `h` lies in the left-translate of the support, i.e. `h ∈ p.support.image (v + ·)`,
  choose (noncomputably) `w ∈ p.support` with `v + w = h` and return `p.config w`;
* otherwise return `default`.

This definition does not assume left-cancellation; it only *chooses* a preimage.
Uniqueness (and the usual equations such as `Pattern.shift p v (v + w) = p.config w`)
require a left-cancellation hypothesis and are proved in separate lemmas.
-/]
/-
**SymbolicDynamics.FullShift.Pattern.mulShift** 是 Mathlib 中的一个定义，位于命名空间 `Symboli
cDynamics.FullShift.Pattern`。
形式化陈述：{A : Type u_1} → [inst : Inhabited A] → {G : Type u_2} → [Monoid G] → Symb
olicDynamics.FullShift.Pattern A G → G → G → A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected noncomputable def Pattern.mulShift (p : Pattern A G) (v : G) : G → A := by
  intro h
  if hmem : h ∈ p.support.image (v * ·) then
    -- package existence of a preimage under (v * ·)
    let ex : ∃ w, w ∈ p.support ∧ v * w = h := by
      simpa [Finset.mem_image] using hmem
    exact p.config (Classical.choose ex)
  else
    exact default

namespace Pattern
/-- Extract the finite pattern given by restricting a configuration `x : G → A`
to a finite subset `U : Finset G`.

The pattern has `config g = x g` for `g ∈ U` and `config g = default` outside `U`,
with support `U`. In other words, `Pattern.fromConfig x U` is the partial configuration of
`x` visible on the coordinates in `U`, padded with `default` elsewhere. -/
/-
**SymbolicDynamics.FullShift.Pattern.fromConfig** 是 Mathlib 中的一个定义，位于命名空间 `Symbo
licDynamics.FullShift.Pattern`。
形式化陈述：fromConfig (x : G -> A) (U : Finset G) : Pattern A G
参数：x : G -> A；U : Finset G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the finite pattern given by restricting a configuration `x : G → A`
to a finite subset `U : Finset G`.

The pattern has `config g = x g` for `g ∈ U` and `config g = default` outside `U
`,
with support `U`. In other words, `Pattern.fromConfig x U` is the partial config
uration of
`x` visible on the coordinates in `U`, padded with `default` elsewhere.
-/
noncomputable def fromConfig (x : G → A) (U : Finset G) : Pattern A G := by
  classical
  exact { config := fun g => if g ∈ U then x g else default,
          support := U,
          condition := fun g hg => if_neg hg }

/-- On the translated support, `p.mulShift v` agrees with `p.config` at the preimage.

More precisely, if `w ∈ p.support`, then at the translated site `v * w`,
the configuration `p.mulShift v` takes the value `p.config w`.

This uses `[IsLeftCancelMul G]` to identify the unique preimage of `v * w`
under left-multiplication by `v`. -/
@[to_additive
  /-- On the translated support, `p.shift v` agrees with `p.config` at the preimage.

  More precisely, if `w ∈ p.support`, then at the translated site `v + w`,
  the configuration `p.shift v` takes the value `p.config w`.

  This uses `[IsLeftCancelAdd G]` to identify the unique preimage of `v + w`
  under left-translation by `v`. -/]
/-
**SymbolicDynamics.FullShift.Pattern.mulShift_apply_mul_left_of_mem** 是 Mathlib 
中的一个引理，位于命名空间 `SymbolicDynamics.FullShift.Pattern`。
形式化陈述：mulShift_apply_mul_left_of_mem (p : Pattern A G) (v w : G) (hw : w in p.su
pport) : p.mulShift v (v * w) = p.config w
参数：p : Pattern A G；v w : G；hw : w in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Classical.choose.congr_simp`：∀ {α : Sort u} {p p_1 : α → Prop} (e_p : p 
= p_1) (h : ∃ x, p x), Classical.choose h = Classical.choose ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
-/
lemma mulShift_apply_mul_left_of_mem
    (p : Pattern A G) (v w : G) (hw : w ∈ p.support) :
    p.mulShift v (v * w) = p.config w := by
  classical
  -- (v * w) is in the translated support
  have hmem : (v * w) ∈ p.support.image (v * ·) :=
    Finset.mem_image.mpr ⟨w, hw, rfl⟩
  -- existential used in the branch
  have ex : ∃ w', w' ∈ p.support ∧ v * w' = v * w := by
    simpa [Finset.mem_image] using hmem
  -- open the `if` branch as returned by the definition
  have h1 : p.mulShift v (v * w) = p.config (Classical.choose ex) := by
    simp [Pattern.mulShift, hmem]
  -- the chosen witness equals w by left-cancellation
  have hwv' : v * Classical.choose ex = v * w := (Classical.choose_spec ex).2
  have h_eq : Classical.choose ex = w := mul_left_cancel hwv'
  rw [h1, h_eq]

/-- Shifting a configuration commutes with occurrences of a pattern.

Formally: a pattern `p` occurs in the shifted configuration `mulShift h x` at
position `g` if and only if it occurs in the original configuration `x` at
position `g * h`. -/
@[to_additive occursInAt_shift
/-- Shifting a configuration commutes with occurrences of a pattern.

Formally: a pattern `p` occurs in the shifted configuration `shift h x` at
position `g` if and only if it occurs in the original configuration `x` at
position `g + h`. -/]
/-
**SymbolicDynamics.FullShift.Pattern.mulOccursInAt_mulShift** 是 Mathlib 中的一个引理，位
于命名空间 `SymbolicDynamics.FullShift.Pattern`。
形式化陈述：mulOccursInAt_mulShift {A G : Type*} [Inhabited A] [Monoid G] (p : Pattern
 A G) (x : G -> A) (g h : G) : p.mulOccursInAt (mulShift g x) h ↔ p.mulOccursInA
t x (g * h)
参数：p : Pattern A G；x : G -> A；g h : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulOccursInAt_mulShift {A G : Type*} [Inhabited A] [Monoid G]
    (p : Pattern A G) (x : G → A) (g h : G) :
    p.mulOccursInAt (mulShift g x) h ↔ p.mulOccursInAt x (g * h) := by
  simp only [Pattern.mulOccursInAt, mulShift_apply, mul_assoc]

/-- Configurations that avoid a family `F` of patterns are stable under the shift.

Formally: if `x` avoids every `p ∈ F` at every position, then for any `h : G`,
the shifted configuration `mulShift h x` also avoids every `p ∈ F` at every position. -/
@[to_additive mapsTo_shift_forbidden
  /-- Configurations that avoid a family `F` of patterns are stable under the shift.

Formally: if `x` avoids every `p ∈ F` at every position, then for any `h : G`,
the shifted configuration `shift h x` also avoids every `p ∈ F` at every position. -/]
/-
**SymbolicDynamics.FullShift.Pattern.mapsTo_mulShift_mulForbidden** 是 Mathlib 中的
一个引理，位于命名空间 `SymbolicDynamics.FullShift.Pattern`。
形式化陈述：mapsTo_mulShift_mulForbidden {A G : Type*} [Inhabited A] [Monoid G] (F : S
et (Pattern A G)) (h : G) : Set.MapsTo (mulShift h) (mulForbidden (A
参数：F : Set (Pattern A G)；h : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
-/
lemma mapsTo_mulShift_mulForbidden {A G : Type*} [Inhabited A] [Monoid G]
    (F : Set (Pattern A G)) (h : G) :
    Set.MapsTo (mulShift h) (mulForbidden (A := A) (G := G) F) (mulForbidden F) := by
  -- unfold `MapsTo`
  intro x hx p hp g
  specialize hx p hp (h * g)
  contrapose! hx
  simpa [mulOccursInAt_mulShift] using hx

end Pattern

open scoped Classical in
/-- We call *occurrence set* for pattern `p` and position `g` the set of configurations
in which a pattern `p` occurs at position `g`.

This proves that it is exactly the cylinder corresponding to the
pattern obtained by translating `p` by `g`.

Equivalently, `p.mulOccursInAt x g` iff on every translated site
`g * w` (with `w ∈ p.support`)
the configuration `x` agrees with the translated pattern `Pattern.mulShift p g`.

(This uses `[IsLeftCancelMul G]` to identify the preimage along left-multiplication by `g`.) -/
@[to_additive occursInAt_eq_cylinder
  /-- We call *occurrence set* for pattern `p` and position `g` the set of configurations
in which a pattern `p` occurs at position `g`.

This proves that it is exactly the cylinder corresponding to the
pattern obtained by translating `p` by `g`.

Equivalently, `p.occursInAt x g` iff on every translated site `g + w` (with `w ∈ p.support`)
the configuration `x` agrees with the translated pattern `Pattern.shift p g`.

(This uses `[IsLeftCancelMul G]` to identify the preimage along left-multiplication by `g`.) -/]
/-
**SymbolicDynamics.FullShift.mulOccursInAt_eq_cylinder** 是 Mathlib 中的一个引理，位于命名空间
 `SymbolicDynamics.FullShift`。
形式化陈述：mulOccursInAt_eq_cylinder (p : Pattern A G) (g : G) : { x | p.mulOccursInA
t x g } = cylinder (p.support.image (g * ·)) (p.mulShift g)
参数：p : Pattern A G；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SymbolicDynamics.FullShift.Pattern.mulShift_apply_mul_left_of_mem`：mulSh
ift_apply_mul_left_of_mem (p : Pattern A G) (v w : G) (hw : w in p.support) : p.
mulShift v (v * w) = p.config w
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
lemma mulOccursInAt_eq_cylinder
    (p : Pattern A G) (g : G) :
    { x | p.mulOccursInAt x g } = cylinder (p.support.image (g * ·)) (p.mulShift g) := by
  ext x; constructor
  · -- ⇒: from an occurrence, get membership in the cylinder
    intro H u hu
    rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
    -- want: x ( w * g) = Pattern.mulShift p g ( w * g)
    have hx : x (g * w) = p.config w := H w hw
    simpa [Pattern.mulShift_apply_mul_left_of_mem (p := p) (v := g) (w := w) hw] using hx
  · -- ⇐: from the cylinder, recover an occurrence
    intro H u hu
    -- H gives equality with the translated pattern on the image
    have hx : x (g * u) = p.mulShift g (g * u) :=
      H (g * u) (Finset.mem_image_of_mem (g * ·) hu)
    -- rewrite the RHS by the “apply_of_mem” lemma
    simpa [Pattern.mulShift_apply_mul_left_of_mem (p := p) (v := g) (w := u) hu] using hx
end OccursInAt

/-! ## Forbidden sets and subshifts -/

section DefSubshiftByForbidden

variable {A : Type*} [TopologicalSpace A] [Inhabited A]
variable {G : Type*} [Monoid G] [IsLeftCancelMul G]

/-- Occurrence sets are open. -/
@[to_additive isOpen_occursInAt /-- Occurrence sets are open. -/]
/-
**SymbolicDynamics.FullShift.isOpen_mulOccursInAt** 是 Mathlib 中的一个引理，位于命名空间 `Sym
bolicDynamics.FullShift`。
形式化陈述：isOpen_mulOccursInAt [DiscreteTopology A] (p : Pattern A G) (g : G) : IsOp
en { x | p.mulOccursInAt x g }
参数：p : Pattern A G；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SymbolicDynamics.FullShift.mulOccursInAt_eq_cylinder`：mulOccursInAt_eq_c
ylinder (p : Pattern A G) (g : G) : { x | p.mulOccursInAt x g } = cylinder (p.su
pport.image (g * ·)) (p.mulShift g)
· 使用引理 `SymbolicDynamics.FullShift.isOpen_cylinder`：isOpen_cylinder [DiscreteTop
ology A] (U : Finset G) (x : G -> A) : IsOpen (cylinder U x)

--- 原说明 ---
Occurrence sets are open.
-/
lemma isOpen_mulOccursInAt [DiscreteTopology A] (p : Pattern A G) (g : G) :
    IsOpen { x | p.mulOccursInAt x g } := by
  simpa [mulOccursInAt_eq_cylinder] using isOpen_cylinder _ _

/-- Avoiding a fixed family of patterns is a closed condition (in the product topology on `G → A`).

Since each occurrence set `{ x | p.mulOccursInAt x v }` is open (when `A` is discrete),
its complement `{ x | ¬ p.mulOccursInAt x v }` is closed; `forbidden F` is the intersection
of these closed sets over `p ∈ F` and `v ∈ G`. -/
@[to_additive isClosed_forbidden /-- Avoiding a fixed family of patterns is a closed
condition (in the product topology on `G → A`).

Since each occurrence set `{ x | p.occursInAt x v }` is open (when `A` is discrete),
its complement `{ x | ¬ p.occursInAt x v }` is closed; `forbidden F` is the intersection
of these closed sets over `p ∈ F` and `v ∈ G`. -/]
/-
**SymbolicDynamics.FullShift.isClosed_mulForbidden** 是 Mathlib 中的一个引理，位于命名空间 `Sy
mbolicDynamics.FullShift`。
形式化陈述：isClosed_mulForbidden [DiscreteTopology A] (F : Set (Pattern A G)) : IsClo
sed (mulForbidden F)
参数：F : Set (Pattern A G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SymbolicDynamics.FullShift.mulForbidden.eq_1`：∀ {A : Type u_1} {G : Type
 u_2} [inst : Inhabited A] [inst_1 : Monoid G]   (F : Set (SymbolicDynamics.Full
Shift.Pattern A G)),   SymbolicDyn…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用引理 `SymbolicDynamics.FullShift.isOpen_mulOccursInAt`：isOpen_mulOccursInAt [D
iscreteTopology A] (p : Pattern A G) (g : G) : IsOpen { x | p.mulOccursInAt x g 
}
-/
lemma isClosed_mulForbidden [DiscreteTopology A] (F : Set (Pattern A G)) :
    IsClosed (mulForbidden F) := by
  rw [mulForbidden]
  -- Rewrite as an intersection indexed by `p ∈ F` and `v : G`.
  have h_eq : {x | ∀ p ∈ F, ∀ v : G, ¬ p.mulOccursInAt x v}
    = ⋂ (p : Pattern A G) (hp : p ∈ F) (v : G), {x | ¬ p.mulOccursInAt x v} := by ext; simp
  rw [h_eq]
  -- Now prove that this big intersection is closed.
  refine isClosed_iInter (fun p => ?_)
  refine isClosed_iInter (fun hp => ?_)
  refine isClosed_iInter (fun v => ?_)
  -- For each `p, hp, v`, the section is the complement of an open occurrence set.
  have : {x | ¬ p.mulOccursInAt x v} = {x | p.mulOccursInAt x v}ᶜ := by ext; simp
  simpa [this, isClosed_compl_iff] using isOpen_mulOccursInAt (A := A) (G := G) p v

/-- Occurrence sets are closed. -/
@[to_additive isClosed_occursInAt /-- Occurrence sets are closed. -/]
/-
**SymbolicDynamics.FullShift.isClosed_mulOccursInAt** 是 Mathlib 中的一个引理，位于命名空间 `S
ymbolicDynamics.FullShift`。
形式化陈述：isClosed_mulOccursInAt [T1Space A] (p : Pattern A G) (g : G) : IsClosed { 
x | p.mulOccursInAt x g }
参数：p : Pattern A G；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SymbolicDynamics.FullShift.mulOccursInAt_eq_cylinder`：mulOccursInAt_eq_c
ylinder (p : Pattern A G) (g : G) : { x | p.mulOccursInAt x g } = cylinder (p.su
pport.image (g * ·)) (p.mulShift g)
· 使用引理 `SymbolicDynamics.FullShift.isClosed_cylinder`：isClosed_cylinder [T1Space
 A] (U : Finset G) (x : G -> A) : IsClosed (cylinder U x)

--- 原说明 ---
Occurrence sets are closed.
-/
lemma isClosed_mulOccursInAt [T1Space A] (p : Pattern A G) (g : G) :
    IsClosed { x | p.mulOccursInAt x g } := by
  simpa [mulOccursInAt_eq_cylinder] using isClosed_cylinder _ _

/-- The subshift defined by a family of forbidden patterns `F`.

This is a standard way to construct subshifts:
`MulSubshift.ofForbidden F` consists of all configurations `x : G → A` in which no pattern
`p ∈ F` occurs at any position.

Formally:
* the carrier is `forbidden F` (configurations avoiding `F`),
* it is closed because each occurrence set is open, and
* it is shift-invariant since avoidance is preserved by shifts. -/
@[to_additive /-- The subshift defined by a family of forbidden patterns `F`.

This is a standard way to construct subshifts:
`Subshift.ofForbidden F` consists of all configurations `x : G → A` in which no pattern
`p ∈ F` occurs at any position.

Formally:
* the carrier is `forbidden F` (configurations avoiding `F`),
* it is closed because each occurrence set is open, and
* it is shift-invariant since avoidance is preserved by shifts. -/]
/-
**SymbolicDynamics.FullShift.MulSubshift.ofForbidden** 是 Mathlib 中的一个定义，位于命名空间 `
SymbolicDynamics.FullShift.MulSubshift`。
形式化陈述：{A : Type u_1} →   [inst : TopologicalSpace A] →     [inst_1 : Inhabited A
] →       {G : Type u_2} →         [inst_2 : Monoid G] →           [IsLeftCancel
Mul G] →             [DiscreteTopology A] →               Set (SymbolicDynamics.
FullShift.Pattern A G) → SymbolicDynamics.FullShift.MulSubshift A G
参数：SymbolicDynamics.FullShift.Pattern A G。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SymbolicDynamics.FullShift.isClosed_mulForbidden`：isClosed_mulForbidden 
[DiscreteTopology A] (F : Set (Pattern A G)) : IsClosed (mulForbidden F)
· 使用引理 `SymbolicDynamics.FullShift.Pattern.mapsTo_mulShift_mulForbidden`：mapsTo_
mulShift_mulForbidden {A G : Type*} [Inhabited A] [Monoid G] (F : Set (Pattern A
 G)) (h : G) : Set.MapsTo (mulShift h) (mulForbidden …
-/
def MulSubshift.ofForbidden [DiscreteTopology A] (F : Set (Pattern A G)) : MulSubshift A G where
  carrier := mulForbidden F
  isClosed := isClosed_mulForbidden F
  mapsTo := Pattern.mapsTo_mulShift_mulForbidden F

end DefSubshiftByForbidden

section Language

variable {A : Type*} [Fintype A] [Inhabited A]
variable {G : Type*}

/-- Patterns with support exactly `U` form a finite set. -/
/-
**SymbolicDynamics.FullShift.finite_setOfPred_pattern_support_eq** 是 Mathlib 中的一
个引理，位于命名空间 `SymbolicDynamics.FullShift`。
形式化陈述：finite_setOfPred_pattern_support_eq {A G : Type*} [Finite A] [Inhabited A]
 (U : Finset G) : ({p : Pattern A G | p.support = U}).Finite
参数：U : Finset G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `SymbolicDynamics.FullShift.Pattern.mk.congr_simp`：∀ {A : Type u_1} {G : 
Type u_2} [inst : Inhabited A] (config config_1 : G → A) (e_config : config = co
nfig_1)   (support support_1 : Finset …
· 使用定理 `SymbolicDynamics.FullShift.Pattern.mk.injEq`：∀ {A : Type u_1} {G : Type 
u_2} [inst : Inhabited A] (config : G → A) (support : Finset G)   (condition : ∀
 g ∉ support, config g = default)…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Patterns with support exactly `U` form a finite set.
-/
lemma finite_setOfPred_pattern_support_eq
    {A G : Type*} [Finite A] [Inhabited A]
    (U : Finset G) :
    ({p : Pattern A G | p.support = U}).Finite := by
  -- 1. Upgrade Finite A to Fintype A locally
  cases nonempty_fintype A
  classical
  -- Patterns with support U biject with (U → A) via restriction/extension
  let e : { p : Pattern A G // p.support = U } ≃ (U → A) :=
  { toFun := fun p i => p.1.config i.1
    invFun := fun f => ⟨{ config := fun g => if h : g ∈ U then f ⟨g, h⟩ else default,
                           support := U,
                           condition := fun g hg => by simp [hg] }, rfl⟩
    left_inv := by
      rintro ⟨⟨cfg, dom, cond⟩, hU⟩
      simp only at hU; subst hU
      apply Subtype.ext
      simp only [Pattern.mk.injEq, and_true]
      funext g
      by_cases hg : g ∈ dom
      · simp [hg]
      · simp [hg, cond g hg]
    right_inv := fun f => by ext i; simp [i.2] }
  let : Fintype { p : Pattern A G | p.support = U } := Fintype.ofEquiv (U → A) e.symm
  apply toFinite

@[deprecated (since := "2026-07-09")]
alias finite_setOf_pattern_support_eq := finite_setOfPred_pattern_support_eq

/-- The language of a set of configurations `X` on a finite shape `U`.

This is the set of all finite patterns obtained by restricting some configuration
`x ∈ X` to `U`. -/
/-
**SymbolicDynamics.FullShift.LanguageOn** 是 Mathlib 中的一个定义，位于命名空间 `SymbolicDynam
ics.FullShift`。
形式化陈述：LanguageOn (X : Set (G -> A)) (U : Finset G) : Set (Pattern A G)
参数：X : Set (G -> A)；U : Finset G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The language of a set of configurations `X` on a finite shape `U`.

This is the set of all finite patterns obtained by restricting some configuratio
n
`x ∈ X` to `U`.
-/
def LanguageOn (X : Set (G → A)) (U : Finset G) : Set (Pattern A G) :=
  { p | ∃ x ∈ X, Pattern.fromConfig x U = p }

/-- The language of a subshift `Y` on a finite shape `U`. -/
/-
**SymbolicDynamics.FullShift.MulSubshift.languageOn** 是 Mathlib 中的一个定义，位于命名空间 `S
ymbolicDynamics.FullShift.MulSubshift`。
形式化陈述：{A : Type u_3} →   {G : Type u_4} →     [inst : TopologicalSpace A] →     
  [inst_1 : Inhabited A] →         [inst_2 : Monoid G] →           SymbolicDynam
ics.FullShift.MulSubshift A G → Finset G → Set (SymbolicDynamics.FullShift.Patte
rn A G)
参数：SymbolicDynamics.FullShift.Pattern A G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The language of a subshift `Y` on a finite shape `U`.
-/
def MulSubshift.languageOn {A G} [TopologicalSpace A] [Inhabited A] [Monoid G]
    (Y : MulSubshift A G) (U : Finset G) : Set (Pattern A G) :=
  SymbolicDynamics.FullShift.LanguageOn (A := A) (G := G) Y.carrier U

end Language

end FullShift

end SymbolicDynamics

