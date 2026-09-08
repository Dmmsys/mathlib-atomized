/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Andrew Yang,
  Johannes Hölzl, Kevin Buzzard, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Order.Hom.CompleteLattice

/-!

# Restriction of scalars for submodules

If semiring `S` acts on a semiring `R` and `M` is a module over both (compatibly with this action)
then we can turn an `R`-submodule into an `S`-submodule by forgetting the action of `R`. We call
this restriction of scalars for submodules.

## Main definitions:
* `Submodule.restrictScalars`: regard an `R`-submodule as an `S`-submodule if `S` acts on `R`

-/

@[expose] public section

namespace Submodule

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

/-- `V.restrictScalars S` is the `S`-submodule of the `S`-module given by restriction of scalars,
corresponding to `V`, an `R`-submodule of the original `R`-module.
-/
/-
**Submodule.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：restrictScalars (V : Submodule R M) : Submodule S M where carrier
参数：V : Submodule R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p

--- 原说明 ---
`V.restrictScalars S` is the `S`-submodule of the `S`-module given by restrictio
n of scalars,
corresponding to `V`, an `R`-submodule of the original `R`-module.
-/
def restrictScalars (V : Submodule R M) : Submodule S M where
  carrier := V
  zero_mem' := V.zero_mem
  smul_mem' c _ h := V.smul_of_tower_mem c h
  add_mem' hx hy := V.add_mem hx hy

@[simp]
/-
**Submodule.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_restrictScalars (V : Submodule R M) : (V.restrictScalars S : Set M) = 
V
参数：V : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars (V : Submodule R M) : (V.restrictScalars S : Set M) = V :=
  rfl

@[simp]
/-
**Submodule.toAddSubmonoid_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：toAddSubmonoid_restrictScalars (V : Submodule R M) : (V.restrictScalars S)
.toAddSubmonoid = V.toAddSubmonoid
参数：V : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddSubmonoid_restrictScalars (V : Submodule R M) :
    (V.restrictScalars S).toAddSubmonoid = V.toAddSubmonoid :=
  rfl

@[simp]
/-
**Submodule.restrictScalars_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_mem (V : Submodule R M) (m : M) : m in V.restrictScalars S
 ↔ m in V
参数：V : Submodule R M；m : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.refl`：∀ (a : Prop), a ↔ a
-/
theorem restrictScalars_mem (V : Submodule R M) (m : M) : m ∈ V.restrictScalars S ↔ m ∈ V :=
  Iff.refl _

@[simp]
/-
**Submodule.restrictScalars_self** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_self (V : Submodule R M) : V.restrictScalars R = V
参数：V : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem restrictScalars_self (V : Submodule R M) : V.restrictScalars R = V :=
  SetLike.coe_injective rfl
/-
**Submodule.restrictScalars_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
`。
形式化陈述：∀ (S : Type u_1) {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1
 : AddCommMonoid M] [inst_2 : Semiring S]   [inst_3 : _root_.Module S M] [inst_4
 : _root_.Module R M] [inst_5 : SMul S R] [inst_6 : IsScalarTower S R M]   (T : 
Type u_4) [inst_7 : Semiring T] [inst_8 : SMul T R] [inst_9 : SMul S T] [inst_10
 : _root_.Module T M]   [inst_11 : IsScalarTower S T M] [inst_12 : IsScalarTower
 T R M] (V : Submodule R M),   Submodule.restrictScalars S (Submodule.restrictSc
alars T V) = Submodule.restrictScalars S V
参数：S : Type u_1；T : Type u_4；V : Submodule R M；Submodule.restrictScalars T V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem restrictScalars_restrictScalars
    (T : Type*) [Semiring T] [SMul T R] [SMul S T]
    [Module T M] [IsScalarTower S T M] [IsScalarTower T R M]
    (V : Submodule R M) :
    (V.restrictScalars T).restrictScalars S = V.restrictScalars S :=
  rfl

variable (R M)
/-
**Submodule.restrictScalars_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_injective : Function.Injective (restrictScalars S : Submod
ule R M -> Submodule S M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars S : Submodule R M → Submodule S M) := fun _ _ h =>
  ext <| Set.ext_iff.1 (SetLike.ext'_iff.1 h :)

@[simp]
/-
**Submodule.restrictScalars_inj** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_inj {V₁ V₂ : Submodule R M} : restrictScalars S V₁ = restr
ictScalars S V₂ ↔ V₁ = V₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars S : Submodule R M -> Submodule S M)
-/
theorem restrictScalars_inj {V₁ V₂ : Submodule R M} :
    restrictScalars S V₁ = restrictScalars S V₂ ↔ V₁ = V₂ :=
  (restrictScalars_injective S _ _).eq_iff

/-- Even though `p.restrictScalars S` has type `Submodule S M`, it is still an `R`-module. -/
/-
**Submodule.restrictScalars.origModule** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.rest
rictScalars`。
形式化陈述：(S : Type u_1) →   (R : Type u_2) →     (M : Type u_3) →       [inst : Sem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : Semiring S] 
→             [inst_3 : _root_.Module S M] →               [inst_4 : _root_.Modu
le R M] →                 [inst_5 : SMul S R] →                   [inst_6 : IsSc
alarTower S R M] →                     (p : Submodule R M) → _root_.Module R ↥(S
ubmodule.restrictScalars S p)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Even though `p.restrictScalars S` has type `Submodule S M`, it is still an `R`-m
odule.
-/
instance restrictScalars.origModule (p : Submodule R M) : Module R (p.restrictScalars S) :=
  inferInstanceAs <| Module R p
/-
**Submodule.restrictScalars.isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.r
estrictScalars`。
形式化陈述：∀ (S : Type u_1) (R : Type u_2) (M : Type u_3) [inst : Semiring R] [inst_1
 : AddCommMonoid M] [inst_2 : Semiring S]   [inst_3 : _root_.Module S M] [inst_4
 : _root_.Module R M] [inst_5 : SMul S R] [inst_6 : IsScalarTower S R M]   (p : 
Submodule R M), IsScalarTower S R ↥(Submodule.restrictScalars S p)
参数：S : Type u_1；R : Type u_2；M : Type u_3；p : Submodule R M；Submodule.restrictSc
alars S p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance restrictScalars.isScalarTower (p : Submodule R M) :
    IsScalarTower S R (p.restrictScalars S) where
  smul_assoc r s x := Subtype.ext <| smul_assoc r s (x : M)

variable {R M} in
/-
**Submodule.restrictScalars_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ (S : Type u_1) {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1
 : AddCommMonoid M] [inst_2 : Semiring S]   [inst_3 : _root_.Module S M] [inst_4
 : _root_.Module R M] [inst_5 : SMul S R] [inst_6 : IsScalarTower S R M]   {s t 
: Submodule R M}, Submodule.restrictScalars S s ≤ Submodule.restrictScalars S t 
↔ s ≤ t
参数：S : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[gcongr, simp] lemma restrictScalars_le {s t : Submodule R M} :
    s.restrictScalars S ≤ t.restrictScalars S ↔ s ≤ t :=
  Iff.rfl

variable {R M} in
/-
**Submodule.restrictScalars_lt** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ (S : Type u_1) {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1
 : AddCommMonoid M] [inst_2 : Semiring S]   [inst_3 : _root_.Module S M] [inst_4
 : _root_.Module R M] [inst_5 : SMul S R] [inst_6 : IsScalarTower S R M]   {s t 
: Submodule R M}, Submodule.restrictScalars S s < Submodule.restrictScalars S t 
↔ s < t
参数：S : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[gcongr, simp] lemma restrictScalars_lt {s t : Submodule R M} :
    s.restrictScalars S < t.restrictScalars S ↔ s < t :=
  Iff.rfl

/-- `restrictScalars S` is an embedding of the lattice of `R`-submodules into
the lattice of `S`-submodules. -/
@[simps]
/-
**Submodule.restrictScalarsEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：restrictScalarsEmbedding : Submodule R M ↪o Submodule S M where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars S : Submodule R M -> Submodule S M)
· 使用定理 `Submodule.restrictScalars_le`：∀ (S : Type u_1) {R : Type u_2} {M : Type 
u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S]   [ins
t_3 : _root_.Modul…

--- 原说明 ---
`restrictScalars S` is an embedding of the lattice of `R`-submodules into
the lattice of `S`-submodules.
-/
def restrictScalarsEmbedding : Submodule R M ↪o Submodule S M where
  toFun := restrictScalars S
  inj' := restrictScalars_injective S R M
  map_rel_iff' := restrictScalars_le S

@[mono]
/-
**Submodule.restrictScalars_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_monotone : Monotone (restrictScalars S : Submodule R M -> 
Submodule S M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
-/
lemma restrictScalars_monotone : Monotone (restrictScalars S : Submodule R M → Submodule S M) :=
  (restrictScalarsEmbedding S R M).monotone

variable {R M} in
/-
**Submodule.restrictScalars_mono** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_mono {s t : Submodule R M} (hst : s <= t) : s.restrictScal
ars S <= t.restrictScalars S
参数：hst : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.restrictScalars_monotone`：restrictScalars_monotone : Monotone 
(restrictScalars S : Submodule R M -> Submodule S M)
-/
lemma restrictScalars_mono {s t : Submodule R M} (hst : s ≤ t) :
    s.restrictScalars S ≤ t.restrictScalars S := restrictScalars_monotone S R M hst

/-- Turning `p : Submodule R M` into an `S`-submodule gives the same module structure
as turning it into a type and adding a module structure. -/
@[simps +simpRhs]
/-
**Submodule.restrictScalarsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：restrictScalarsEquiv (p : Submodule R M) : p.restrictScalars S ≃ₗ[R] p
参数：p : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turning `p : Submodule R M` into an `S`-submodule gives the same module structur
e
as turning it into a type and adding a module structure.
-/
def restrictScalarsEquiv (p : Submodule R M) : p.restrictScalars S ≃ₗ[R] p :=
  { AddEquiv.refl p with
    map_smul' := fun _ _ => rfl }

@[simp]
/-
**Submodule.restrictScalars_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_bot : restrictScalars S (⊥ : Submodule R M) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars_bot : restrictScalars S (⊥ : Submodule R M) = ⊥ :=
  rfl

@[simp]
/-
**Submodule.restrictScalars_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_eq_bot_iff {p : Submodule R M} : restrictScalars S p = ⊥ ↔
 p = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem restrictScalars_eq_bot_iff {p : Submodule R M} : restrictScalars S p = ⊥ ↔ p = ⊥ := by
  simp [SetLike.ext_iff]

@[simp]
/-
**Submodule.restrictScalars_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_top : restrictScalars S (⊤ : Submodule R M) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars_top : restrictScalars S (⊤ : Submodule R M) = ⊤ :=
  rfl

@[simp]
/-
**Submodule.restrictScalars_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_eq_top_iff {p : Submodule R M} : restrictScalars S p = ⊤ ↔
 p = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem restrictScalars_eq_top_iff {p : Submodule R M} : restrictScalars S p = ⊤ ↔ p = ⊤ := by
  simp [SetLike.ext_iff]

variable {R M}

@[simp]
/-
**Submodule.restrictScalars_sInf** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_sInf (s : Set (Submodule R M)) : (sInf s).restrictScalars 
S = sInf (restrictScalars S '' s)
参数：s : Set (Submodule R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrictScalars_sInf (s : Set (Submodule R M)) :
    (sInf s).restrictScalars S = sInf (restrictScalars S '' s) := by
  ext; simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Submodule.restrictScalars_sSup** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_sSup (s : Set (Submodule R M)) : (sSup s).restrictScalars 
S = sSup (restrictScalars S '' s)
参数：s : Set (Submodule R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.toAddSubmonoid_sSup`：toAddSubmonoid_sSup (s : Set (Submodule R
 M)) : (sSup s).toAddSubmonoid = sSup (toAddSubmonoid '' s)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrictScalars_sSup (s : Set (Submodule R M)) :
    (sSup s).restrictScalars S = sSup (restrictScalars S '' s) := by
  simp [← toAddSubmonoid_inj, toAddSubmonoid_sSup, ← Set.image_comp]

variable (R M) in
/-- If ring `S` acts on a ring `R` and `M` is a module over both (compatibly with this action) then
we can turn an `R`-submodule into an `S`-submodule by forgetting the action of `R`. -/
/-
**Submodule.restrictScalarsLatticeHom** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：restrictScalarsLatticeHom : CompleteLatticeHom (Submodule R M) (Submodule 
S M) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.restrictScalars_sInf`：restrictScalars_sInf (s : Set (Submodule
 R M)) : (sInf s).restrictScalars S = sInf (restrictScalars S '' s)
· 使用引理 `Submodule.restrictScalars_sSup`：restrictScalars_sSup (s : Set (Submodule
 R M)) : (sSup s).restrictScalars S = sSup (restrictScalars S '' s)

--- 原说明 ---
If ring `S` acts on a ring `R` and `M` is a module over both (compatibly with th
is action) then
we can turn an `R`-submodule into an `S`-submodule by forgetting the action of `
R`.
-/
def restrictScalarsLatticeHom : CompleteLatticeHom (Submodule R M) (Submodule S M) where
  toFun := restrictScalars S
  map_sInf' := restrictScalars_sInf S
  map_sSup' := restrictScalars_sSup S

@[simp]
/-
**Submodule.restrictScalars_iInf** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_iInf {ι : Sort*} (s : ι -> Submodule R M) : (iInf s).restr
ictScalars S = ⨅ i, restrictScalars S (s i)
参数：s : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrictScalars_iInf {ι : Sort*} (s : ι → Submodule R M) :
    (iInf s).restrictScalars S = ⨅ i, restrictScalars S (s i) := by
  ext; simp

@[simp]
/-
**Submodule.restrictScalars_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_iSup {ι : Sort*} (s : ι -> Submodule R M) : (iSup s).restr
ictScalars S = ⨆ i, restrictScalars S (s i)
参数：s : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_iSup`：map_iSup [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g
 : ι -> α) : f (⨆ i, g i) = ⨆ i, f (g i)
· 使用定理 `CompleteLatticeHomClass.tosSupHomClass`：∀ {F : Type u_8} {α : Type u_9} 
{β : Type u_10} {inst : CompleteLattice α} {inst_1 : CompleteLattice β}   {inst_
2 : FunLike F α β} [self : C…
· 使用定理 `CompleteLatticeHom.instCompleteLatticeHomClass`：∀ {α : Type u_2} {β : Ty
pe u_3} [inst : CompleteLattice α] [inst_1 : CompleteLattice β],   CompleteLatti
ceHomClass (CompleteLatticeHom α β) …
-/
lemma restrictScalars_iSup {ι : Sort*} (s : ι → Submodule R M) :
    (iSup s).restrictScalars S = ⨆ i, restrictScalars S (s i) :=
  map_iSup (restrictScalarsLatticeHom S R M) s

@[simp]
/-
**Submodule.restrictScalars_inf** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_inf (s t : Submodule R M) : (s ⊓ t).restrictScalars S = s.
restrictScalars S ⊓ t.restrictScalars S
参数：s t : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrictScalars_inf (s t : Submodule R M) :
    (s ⊓ t).restrictScalars S = s.restrictScalars S ⊓ t.restrictScalars S := by
  ext x; simp

@[simp]
/-
**Submodule.restrictScalars_sup** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_sup (s t : Submodule R M) : (s ⊔ t).restrictScalars S = s.
restrictScalars S ⊔ t.restrictScalars S
参数：s t : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.restrictScalars.congr_simp`：∀ (S : Type u_1) {R : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S
]   [inst_3 : _root_.Modul…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sSup_insert`：sSup_insert {a : α} {s : Set α} : sSup (insert a s) = a ⊔ s
Sup s
· 使用定理 `sSup_singleton`：sSup_singleton {a : α} : sSup {a} = a
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用引理 `Submodule.restrictScalars_sSup`：restrictScalars_sSup (s : Set (Submodule
 R M)) : (sSup s).restrictScalars S = sSup (restrictScalars S '' s)
-/
lemma restrictScalars_sup (s t : Submodule R M) :
    (s ⊔ t).restrictScalars S = s.restrictScalars S ⊔ t.restrictScalars S := by
  simpa [Set.image_insert_eq] using restrictScalars_sSup S (s := {s, t})

@[simp]
/-
**Submodule.toIntSubmodule_toAddSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：toIntSubmodule_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [Modu
le R M] (N : Submodule R M) : N.toAddSubgroup.toIntSubmodule = N.restrictScalars
 Int
参数：N : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toIntSubmodule_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    N.toAddSubgroup.toIntSubmodule = N.restrictScalars ℤ := rfl

@[simp]
/-
**Submodule.codisjoint_restrictScalars_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：codisjoint_restrictScalars_iff {s t : Submodule R M} : Codisjoint (s.restr
ictScalars S) (t.restrictScalars S) ↔ Codisjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem codisjoint_restrictScalars_iff {s t : Submodule R M} :
    Codisjoint (s.restrictScalars S) (t.restrictScalars S) ↔ Codisjoint s t := by
  simp [codisjoint_iff, ← restrictScalars_sup]

@[simp]
/-
**Submodule.disjoint_restrictScalars_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：disjoint_restrictScalars_iff {s t : Submodule R M} : Disjoint (s.restrictS
calars S) (t.restrictScalars S) ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_restrictScalars_iff {s t : Submodule R M} :
    Disjoint (s.restrictScalars S) (t.restrictScalars S) ↔ Disjoint s t := by
  simp [disjoint_def]

@[simp]
/-
**Submodule.isCompl_restrictScalars_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isCompl_restrictScalars_iff {s t : Submodule R M} : IsCompl (s.restrictSca
lars S) (t.restrictScalars S) ↔ IsCompl s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCompl_restrictScalars_iff {s t : Submodule R M} :
    IsCompl (s.restrictScalars S) (t.restrictScalars S) ↔ IsCompl s t := by
  simp [isCompl_iff]

end Submodule

