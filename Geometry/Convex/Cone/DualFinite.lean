/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Duals of finitely generated cones

This file defines the notion of dually finitely generated cones. A cone is dually finitely
generated (or `DualFG` for short) if it is the dual of a finite set, or equivalently, of a
finitely generated cone. In geometric terms, a cone is dually finitely generated if it can
be written as the intersection of finitely many halfspaces. This is also known as an H-cone.
This is the counterpart to `FG` (finitely generated) which states that the cone is the conic hull
of a finite set, or a V-cone.

In finite dimensional vector spaces, `FG` is equivalent to `DualFG` by the Minkowski-Weyl theorem.
In this case, V- and H-cones are known as polyhedral cones.

## Main declarations

- `PointedCone.DualFG` expresses that a cone is the dual of a finite set.

-/

@[expose] public section

namespace PointedCone

variable {R M N : Type*}
variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
/-- A cone is dually finitely generated (`DualFG`) if it is the dual of a finite set. Equivalently,
the cone can be written as the intersection of finitely many halfspace. It is also known as an
H-cone. This is the counterpart to `FG` (finitely generated) which states that the cone is the span
of a finite set, or a V-cone. -/
/-
**PointedCone.DualFG** 是 Mathlib 中的一个定义，位于命名空间 `PointedCone`。
形式化陈述：DualFG (C : PointedCone R N) : Prop
参数：C : PointedCone R N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone is dually finitely generated (`DualFG`) if it is the dual of a finite set
. Equivalently,
the cone can be written as the intersection of finitely many halfspace. It is al
so known as an
H-cone. This is the counterpart to `FG` (finitely generated) which states that t
he cone is the span
of a finite set, or a V-cone.
-/
def DualFG (C : PointedCone R N) : Prop := ∃ s : Finset M, dual p s = C

/-- The top cone is dually finitely generated. -/
/-
**PointedCone.DualFG.top** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.DualFG`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_
4 : _root_.Module R M] [inst_5 : AddCommGroup N] [inst_6 : _root_.Module R N]   
{p : M →ₗ[R] N →ₗ[R] R}, PointedCone.DualFG p ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `PointedCone.dual_empty`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddComm
Monoid M] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The top cone is dually finitely generated.
-/
@[simp] protected lemma DualFG.top : DualFG p ⊤ := ⟨∅, by simp⟩

/-- A dually finitely generated cone is the dual of a finitely generated cone. -/
/-
**PointedCone.DualFG.exists_fg_dual** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.DualF
G`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_
4 : _root_.Module R M] [inst_5 : AddCommGroup N] [inst_6 : _root_.Module R N]   
{p : M →ₗ[R] N →ₗ[R] R} {C : PointedCone R N},   PointedCone.DualFG p C → ∃ D, S
ubmodule.FG D ∧ PointedCone.dual p ↑D = C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Submodule.fg_span`：fg_span {s : Set M} (hs : s.Finite) : FG (span R s)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PointedCone.dual_hull`：dual_hull (s : Set M) : dual p (hull R s) = dual 
p s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A dually finitely generated cone is the dual of a finitely generated cone.
-/
lemma DualFG.exists_fg_dual {C : PointedCone R N} (hC : C.DualFG p) :
    ∃ D : PointedCone R M, D.FG ∧ dual p D = C := by
  obtain ⟨s, hs⟩ := hC; exact ⟨_, Submodule.fg_span s.finite_toSet, by simp [hs]⟩

/-- A cone is dually finitely generated if and only if it is the dual of a finitely generated
cone. -/
/-
**PointedCone.DualFG.iff_exists_fg_dual** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.D
ualFG`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_
4 : _root_.Module R M] [inst_5 : AddCommGroup N] [inst_6 : _root_.Module R N]   
{p : M →ₗ[R] N →ₗ[R] R} {C : PointedCone R N},   PointedCone.DualFG p C ↔ ∃ D, S
ubmodule.FG D ∧ PointedCone.dual p ↑D = C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.DualFG.exists_fg_dual`：∀ {R : Type u_1} {M : Type u_2} {N : 
Type u_3} [inst : CommRing R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing 
R]   [inst_3 : AddCommG…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PointedCone.dual_hull`：dual_hull (s : Set M) : dual p (hull R s) = dual 
p s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A cone is dually finitely generated if and only if it is the dual of a finitely 
generated
cone.
-/
lemma DualFG.iff_exists_fg_dual {C : PointedCone R N} :
    C.DualFG p ↔ ∃ D : PointedCone R M, D.FG ∧ dual p D = C where
  mp h := h.exists_fg_dual
  mpr := by
    rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    use s; simp

/-- A dually finitely generated cone is dually finitely generated w.r.t. the identity pairing. -/
/-
**PointedCone.DualFG.id** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.DualFG`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_
4 : _root_.Module R M] [inst_5 : AddCommGroup N] [inst_6 : _root_.Module R N]   
{p : M →ₗ[R] N →ₗ[R] R} {C : PointedCone R N}, PointedCone.DualFG p C → PointedC
one.DualFG LinearMap.id C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `PointedCone.dual_image`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddComm
Monoid M] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A dually finitely generated cone is dually finitely generated w.r.t. the identit
y pairing.
-/
lemma DualFG.id {C : PointedCone R N} (hC : C.DualFG p) : C.DualFG .id := by classical
  obtain ⟨s, rfl⟩ := hC
  use Finset.image p s
  simp

variable (p) in
/-- The dual of a finite set is dually finitely generated. -/
/-
**PointedCone.DualFG.dual_of_finset** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.DualF
G`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_
4 : _root_.Module R M] [inst_5 : AddCommGroup N] [inst_6 : _root_.Module R N]   
(p : M →ₗ[R] N →ₗ[R] R) (s : Finset M), PointedCone.DualFG p (PointedCone.dual p
 ↑s)
参数：p : M →ₗ[R] N →ₗ[R] R；s : Finset M；PointedCone.dual p ↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
The dual of a finite set is dually finitely generated.
-/
lemma DualFG.dual_of_finset (s : Finset M) : (dual p s).DualFG p := by use s

variable (p) in
/-- The dual of a finite set is dually finitely generated. -/
/-
**PointedCone.DualFG.dual_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.DualF
G`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_
4 : _root_.Module R M] [inst_5 : AddCommGroup N] [inst_6 : _root_.Module R N]   
(p : M →ₗ[R] N →ₗ[R] R) {s : Set M}, s.Finite → PointedCone.DualFG p (PointedCon
e.dual p s)
参数：p : M →ₗ[R] N →ₗ[R] R；PointedCone.dual p s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s

--- 原说明 ---
The dual of a finite set is dually finitely generated.
-/
lemma DualFG.dual_of_finite {s : Set M} (hs : s.Finite) : (dual p s).DualFG p := by
  use hs.toFinset
  rw [Set.Finite.coe_toFinset]

variable (p) in
/-- The dual of a finitely generated cone is dually finitely generated. -/
/-
**PointedCone.DualFG.dual_of_fg** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.DualFG`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_
4 : _root_.Module R M] [inst_5 : AddCommGroup N] [inst_6 : _root_.Module R N]   
(p : M →ₗ[R] N →ₗ[R] R) {C : PointedCone R M}, Submodule.FG C → PointedCone.Dual
FG p (PointedCone.dual p ↑C)
参数：p : M →ₗ[R] N →ₗ[R] R；PointedCone.dual p ↑C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PointedCone.dual_hull`：dual_hull (s : Set M) : dual p (hull R s) = dual 
p s

--- 原说明 ---
The dual of a finitely generated cone is dually finitely generated.
-/
lemma DualFG.dual_of_fg {C : PointedCone R M} (hC : C.FG) : (dual p C).DualFG p := by
  obtain ⟨s, rfl⟩ := hC
  use s; rw [← dual_hull]

alias FG.dual_dualfg := DualFG.dual_of_fg

/-- The intersection of two dually finitely generated cones is again dually finitely generated. -/
/-
**PointedCone.DualFG.inf** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.DualFG`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_
4 : _root_.Module R M] [inst_5 : AddCommGroup N] [inst_6 : _root_.Module R N]   
{p : M →ₗ[R] N →ₗ[R] R} {C D : PointedCone R N},   PointedCone.DualFG p C → Poin
tedCone.DualFG p D → PointedCone.DualFG p (C ⊓ D)
参数：C ⊓ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用引理 `PointedCone.dual_union`：dual_union (s t : Set M) : dual p (s union t) = 
dual p s ⊓ dual p t

--- 原说明 ---
The intersection of two dually finitely generated cones is again dually finitely
 generated.
-/
lemma DualFG.inf {C D : PointedCone R N} (hC : C.DualFG p) (hD : D.DualFG p) :
    (C ⊓ D).DualFG p := by classical
  obtain ⟨S, rfl⟩ := hC; obtain ⟨T, rfl⟩ := hD
  use S ∪ T; rw [Finset.coe_union, dual_union]

/-- The double dual of a dually finitely generated cone is the cone itself. -/
@[simp]
/-
**PointedCone.DualFG.dual_dual_flip** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.DualF
G`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_
4 : _root_.Module R M] [inst_5 : AddCommGroup N] [inst_6 : _root_.Module R N]   
{p : M →ₗ[R] N →ₗ[R] R} {C : PointedCone R N},   PointedCone.DualFG p C → Pointe
dCone.dual p ↑(PointedCone.dual p.flip ↑C) = C
参数：PointedCone.dual p.flip ↑C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.DualFG.exists_fg_dual`：∀ {R : Type u_1} {M : Type u_2} {N : 
Type u_3} [inst : CommRing R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing 
R]   [inst_3 : AddCommG…
· 使用定理 `PointedCone.dual_dual_flip_dual`：∀ {R : Type u_1} [inst : CommSemiring R
] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R] {M : Type u_2}   [inst_3 
: AddCommMonoid M] [i…

--- 原说明 ---
The double dual of a dually finitely generated cone is the cone itself.
-/
lemma DualFG.dual_dual_flip {C : PointedCone R N} (hC : C.DualFG p) :
    dual p (dual p.flip C) = C := by
  obtain ⟨D, hDualFG, rfl⟩ := exists_fg_dual hC
  exact dual_dual_flip_dual (p := p) D

/-- The double dual of a dually finitely generated cone is the cone itself. -/
@[simp]
/-
**PointedCone.DualFG.dual_flip_dual** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.DualF
G`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_
4 : _root_.Module R M] [inst_5 : AddCommGroup N] [inst_6 : _root_.Module R N]   
{p : M →ₗ[R] N →ₗ[R] R} {C : PointedCone R M},   PointedCone.DualFG p.flip C → P
ointedCone.dual p.flip ↑(PointedCone.dual p ↑C) = C
参数：PointedCone.dual p ↑C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.DualFG.dual_dual_flip`：∀ {R : Type u_1} {M : Type u_2} {N : 
Type u_3} [inst : CommRing R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing 
R]   [inst_3 : AddCommG…

--- 原说明 ---
The double dual of a dually finitely generated cone is the cone itself.
-/
lemma DualFG.dual_flip_dual {C : PointedCone R M} (hC : C.DualFG p.flip) :
    dual p.flip (dual p C) = C := hC.dual_dual_flip

end PointedCone

