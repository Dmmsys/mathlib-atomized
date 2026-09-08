/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
module

public import Mathlib.Algebra.Group.Submonoid.Support
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Nonneg.Module
public import Mathlib.Geometry.Convex.Cone.Basic


/-!
# Pointed cones

A *pointed cone* is defined to be a submodule of a module where the scalars are restricted to be
nonnegative. This is equivalent to saying that, as a set, a pointed cone is a convex cone which
contains `0`. This is a bundled version of `ConvexCone.Pointed`. We choose the submodule definition
as it allows us to use the `Module` API to work with convex cones.

-/

@[expose] public section

assert_not_exists TopologicalSpace Real Cardinal

variable {R E F G : Type*}

local notation3 "R≥0" => {c : R // 0 ≤ c}

/-- A pointed cone is a submodule of a module with scalars restricted to being nonnegative. -/
/-
**PointedCone** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PointedCone (R E) [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddComm
Monoid E] [Module R E]
参数：R E。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
A pointed cone is a submodule of a module with scalars restricted to being nonne
gative.
-/
abbrev PointedCone (R E)
    [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E] :=
  Submodule {c : R // 0 ≤ c} E

namespace PointedCone

open Function Submodule Pointwise

open scoped Pointwise

section Submodule

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E]
variable {C : PointedCone R E}

/-- A submodule is a pointed cone. -/
/-
**PointedCone.ofSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `PointedCone`。
形式化陈述：{R : Type u_1} →   {E : Type u_2} →     [inst : Semiring R] →       [inst_
1 : PartialOrder R] →         [inst_2 : IsOrderedRing R] →           [inst_3 : A
ddCommMonoid E] → [inst_4 : _root_.Module R E] → Submodule R E → PointedCone R E
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
A submodule is a pointed cone.
-/
@[coe] abbrev ofSubmodule (S : Submodule R E) : PointedCone R E := S.restrictScalars _
/-
**PointedCone.** 是 Mathlib 中的一个实例，位于命名空间 `PointedCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule is a pointed cone.
-/
instance : Coe (Submodule R E) (PointedCone R E) := ⟨ofSubmodule⟩
/-
**PointedCone.coe_ofSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [inst_4 : _root_.Mod
ule R E] (S : Submodule R E), ↑↑S = ↑S
参数：S : Submodule R E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
@[simp] lemma coe_ofSubmodule (S : Submodule R E) : (ofSubmodule S : Set E) = S := rfl
/-
**PointedCone.mem_ofSubmodule_iff** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：mem_ofSubmodule_iff {S : Submodule R E} {x : E} : x in (S : PointedCone R 
E) ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma mem_ofSubmodule_iff {S : Submodule R E} {x : E} : x ∈ (S : PointedCone R E) ↔ x ∈ S := .rfl
/-
**PointedCone.ofSubmodule_inj** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：ofSubmodule_inj {S T : Submodule R E} : ofSubmodule S = ofSubmodule T ↔ S 
= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.restrictScalars_inj`：restrictScalars_inj {V₁ V₂ : Submodule R 
M} : restrictScalars S V₁ = restrictScalars S V₂ ↔ V₁ = V₂
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma ofSubmodule_inj {S T : Submodule R E} : ofSubmodule S = ofSubmodule T ↔ S = T :=
  restrictScalars_inj ..
/-
**PointedCone.ofSubmodule_le_ofSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`
。
形式化陈述：ofSubmodule_le_ofSubmodule {S T : Submodule R E} : ofSubmodule S <= ofSubm
odule T ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma ofSubmodule_le_ofSubmodule {S T : Submodule R E} : ofSubmodule S ≤ ofSubmodule T ↔ S ≤ T :=
  .rfl
/-
**PointedCone.ofSubmodule_lt_ofSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`
。
形式化陈述：ofSubmodule_lt_ofSubmodule {S T : Submodule R E} : ofSubmodule S < ofSubmo
dule T ↔ S < T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma ofSubmodule_lt_ofSubmodule {S T : Submodule R E} : ofSubmodule S < ofSubmodule T ↔ S < T :=
  .rfl

/-- Coercion from submodules to pointed cones as an order embedding. -/
/-
**PointedCone.ofSubmoduleEmbedding** 是 Mathlib 中的一个缩写定义，位于命名空间 `PointedCone`。
形式化陈述：ofSubmoduleEmbedding : Submodule R E ↪o PointedCone R E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
Coercion from submodules to pointed cones as an order embedding.
-/
abbrev ofSubmoduleEmbedding : Submodule R E ↪o PointedCone R E :=
  restrictScalarsEmbedding ..

/-- Coercion from submodules to pointed cones as a lattice homomorphism. -/
/-
**PointedCone.ofSubmoduleLatticeHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `PointedCone`。
形式化陈述：ofSubmoduleLatticeHom : CompleteLatticeHom (Submodule R E) (PointedCone R 
E)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
Coercion from submodules to pointed cones as a lattice homomorphism.
-/
abbrev ofSubmoduleLatticeHom : CompleteLatticeHom (Submodule R E) (PointedCone R E) :=
  restrictScalarsLatticeHom ..
/-
**PointedCone.ofSubmodule_inf** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：ofSubmodule_inf (S T : Submodule R E) : S ⊓ T = (S ⊓ T : PointedCone R E)
参数：S T : Submodule R E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.restrictScalars_inf`：restrictScalars_inf (s t : Submodule R M)
 : (s ⊓ t).restrictScalars S = s.restrictScalars S ⊓ t.restrictScalars S
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma ofSubmodule_inf (S T : Submodule R E) : S ⊓ T = (S ⊓ T : PointedCone R E) :=
  restrictScalars_inf _ _ _
/-
**PointedCone.ofSubmodule_sup** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：ofSubmodule_sup (S T : Submodule R E) : S ⊔ T = (S ⊔ T : PointedCone R E)
参数：S T : Submodule R E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.restrictScalars_sup`：restrictScalars_sup (s t : Submodule R M)
 : (s ⊔ t).restrictScalars S = s.restrictScalars S ⊔ t.restrictScalars S
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma ofSubmodule_sup (S T : Submodule R E) : S ⊔ T = (S ⊔ T : PointedCone R E) :=
  restrictScalars_sup _ _ _
/-
**PointedCone.ofSubmodule_sInf** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：ofSubmodule_sInf (s : Set (Submodule R E)) : sInf s = sInf (ofSubmodule ''
 s)
参数：s : Set (Submodule R E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInfHom.map_sInf'`：∀ {α : Type u_8} {β : Type u_9} [inst : InfSet α] [in
st_1 : InfSet β] (self : sInfHom α β) (s : Set α),   self.toFun (sInf s) = sInf 
(self.t…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma ofSubmodule_sInf (s : Set (Submodule R E)) : sInf s = sInf (ofSubmodule '' s) :=
  ofSubmoduleLatticeHom.map_sInf' s
/-
**PointedCone.ofSubmodule_iInf** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：ofSubmodule_iInf (s : Set (Submodule R E)) : ⨅ S in s, S = ⨅ S in s, (S : 
PointedCone R E)
参数：s : Set (Submodule R E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
· 使用引理 `PointedCone.ofSubmodule_sInf`：ofSubmodule_sInf (s : Set (Submodule R E))
 : sInf s = sInf (ofSubmodule '' s)
· 使用定理 `iInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
γ : Type u_8} {f : β → γ} {g : γ → α} {t : Set β},   ⨅ c ∈ f '' t, g c = ⨅ b ∈ t
…
-/
lemma ofSubmodule_iInf (s : Set (Submodule R E)) : ⨅ S ∈ s, S = ⨅ S ∈ s, (S : PointedCone R E) := by
  rw [← sInf_eq_iInf, ofSubmodule_sInf, sInf_eq_iInf, iInf_image]
/-
**PointedCone.ofSubmodule_sSup** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：ofSubmodule_sSup (s : Set (Submodule R E)) : sSup s = sSup (ofSubmodule ''
 s)
参数：s : Set (Submodule R E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteLatticeHom.map_sSup'`：∀ {α : Type u_8} {β : Type u_9} [inst : Co
mpleteLattice α] [inst_1 : CompleteLattice β] (self : CompleteLatticeHom α β)   
(s : Set α), self.…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma ofSubmodule_sSup (s : Set (Submodule R E)) : sSup s = sSup (ofSubmodule '' s) :=
  ofSubmoduleLatticeHom.map_sSup' s
/-
**PointedCone.ofSubmodule_iSup** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：ofSubmodule_iSup (s : Set (Submodule R E)) : ⨆ S in s, S = ⨆ S in s, (S : 
PointedCone R E)
参数：s : Set (Submodule R E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用引理 `PointedCone.ofSubmodule_sSup`：ofSubmodule_sSup (s : Set (Submodule R E))
 : sSup s = sSup (ofSubmodule '' s)
· 使用定理 `iSup_image`：iSup_image {γ} {f : β -> γ} {g : γ -> α} {t : Set β} : ⨆ c i
n f '' t, g c = ⨆ b in t, g (f b)
-/
lemma ofSubmodule_iSup (s : Set (Submodule R E)) : ⨆ S ∈ s, S = ⨆ S ∈ s, (S : PointedCone R E) := by
  rw [← sSup_eq_iSup, ofSubmodule_sSup, sSup_eq_iSup, iSup_image]

variable {R E : Type*}
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E] [Module R E]
/-
**PointedCone.neg_ofSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：neg_ofSubmodule (S : Submodule R E) : -(ofSubmodule S) = ofSubmodule (-S)
参数：S : Submodule R E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.neg_restrictScalars`：∀ {R : Type u_2} {M : Type u_3} [inst : S
emiring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {S : Type u_
4} [inst_3 : Semiri…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma neg_ofSubmodule (S : Submodule R E) : -(ofSubmodule S) = ofSubmodule (-S) :=
  neg_restrictScalars S

end Submodule

section ConvexCone

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E]
variable {C C₁ C₂ : PointedCone R E} {x : E} {r : R}

/-- Every pointed cone is a convex cone. -/
@[coe]
/-
**PointedCone.toConvexCone** 是 Mathlib 中的一个定义，位于命名空间 `PointedCone`。
形式化陈述：toConvexCone (C : PointedCone R E) : ConvexCone R E where carrier
参数：C : PointedCone R E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
Every pointed cone is a convex cone.
-/
def toConvexCone (C : PointedCone R E) : ConvexCone R E where
  carrier := C
  smul_mem' c hc _ hx := C.smul_mem ⟨c, le_of_lt hc⟩ hx
  add_mem' _ hx _ hy := C.add_mem hx hy
/-
**PointedCone.** 是 Mathlib 中的一个实例，位于命名空间 `PointedCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (PointedCone R E) (ConvexCone R E) where
  coe := toConvexCone

set_option backward.isDefEq.respectTransparency false in
/-
**PointedCone.toConvexCone_injective** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：toConvexCone_injective : Injective ((↑) : PointedCone R E -> ConvexCone R 
E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ConvexCone.mk.injEq`：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] (car
rier : Se…
-/
theorem toConvexCone_injective : Injective ((↑) : PointedCone R E → ConvexCone R E) :=
  fun _ _ => by simp [toConvexCone]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PointedCone.pointed_toConvexCone** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：pointed_toConvexCone (C : PointedCone R E) : (C : ConvexCone R E).Pointed
参数：C : PointedCone R E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
theorem pointed_toConvexCone (C : PointedCone R E) : (C : ConvexCone R E).Pointed := by
  simp [toConvexCone, ConvexCone.Pointed]
/-
**PointedCone.mem_toConvexCone** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [inst_4 : _root_.Mod
ule R E] {C : PointedCone R E} {x : E}, x ∈ ↑C ↔ x ∈ C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_toConvexCone : x ∈ C.toConvexCone ↔ x ∈ C := .rfl
/-
**PointedCone.ext** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [inst_4 : _root_.Mod
ule R E] {C₁ C₂ : PointedCone R E},   (∀ (x : E), x ∈ C₁ ↔ x ∈ C₂) → C₁ = C₂
参数：∀ (x : E), x ∈ C₁ ↔ x ∈ C₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
@[ext] lemma ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h
/-
**PointedCone.convex** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：convex (C : PointedCone R E) : Convex R (C : Set E)
参数：C : PointedCone R E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexCone.convex`：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [
inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R 
M] (C :…
-/
lemma convex (C : PointedCone R E) : Convex R (C : Set E) := C.toConvexCone.convex

@[aesop 90% (rule_sets := [SetLike])]
nonrec lemma smul_mem (C : PointedCone R E) (hr : 0 ≤ r) (hx : x ∈ C) : r • x ∈ C :=
  C.smul_mem ⟨r, hr⟩ hx
/-
**PointedCone.smul_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：smul_mem_iff {𝕜 M : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 
𝕜] [AddCommMonoid M] [Module 𝕜 M] (C : PointedCone 𝕜 M) {c : 𝕜} (hc : 0 < c) {x 
: M} : c • x in C ↔ x in C
参数：C : PointedCone 𝕜 M；hc : 0 < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.smul_mem`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R
] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid
 E] [inst_…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma smul_mem_iff {𝕜 M : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommMonoid M] [Module 𝕜 M] (C : PointedCone 𝕜 M)
    {c : 𝕜} (hc : 0 < c) {x : M} : c • x ∈ C ↔ x ∈ C :=
  ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ C.smul_mem (inv_pos.2 hc).le h, C.smul_mem hc.le⟩

/-- The `PointedCone` constructed from a pointed `ConvexCone`. -/
/-
**PointedCone._root_.ConvexCone.toPointedCone** 是 Mathlib 中的一个定义，位于命名空间 `Pointed
Cone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `PointedCone` constructed from a pointed `ConvexCone`.
-/
def _root_.ConvexCone.toPointedCone (C : ConvexCone R E) (hC : C.Pointed) : PointedCone R E where
  carrier := C
  add_mem' hx hy := C.add_mem hx hy
  zero_mem' := hC
  smul_mem' := fun ⟨c, hc⟩ x hx => by
    simp_rw [SetLike.mem_coe]
    rcases eq_or_lt_of_le hc with hzero | hpos
    · unfold ConvexCone.Pointed at hC
      convert! hC
      simp [← hzero]
    · apply ConvexCone.smul_mem
      · convert! hpos
      · exact hx

@[simp]
/-
**PointedCone._root_.ConvexCone.mem_toPointedCone** 是 Mathlib 中的一个引理，位于命名空间 `Poi
ntedCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ConvexCone.mem_toPointedCone {C : ConvexCone R E} (hC : C.Pointed) (x : E) :
    x ∈ C.toPointedCone hC ↔ x ∈ C :=
  Iff.rfl

@[simp, norm_cast]
/-
**PointedCone._root_.ConvexCone.coe_toPointedCone** 是 Mathlib 中的一个引理，位于命名空间 `Poi
ntedCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ConvexCone.coe_toPointedCone (C : ConvexCone R E) (hC : C.Pointed) :
    C.toPointedCone hC = C :=
  rfl

@[simp]
/-
**PointedCone._root_.ConvexCone.toPointedCone_top** 是 Mathlib 中的一个引理，位于命名空间 `Poi
ntedCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ConvexCone.toPointedCone_top : (⊤ : ConvexCone R E).toPointedCone trivial = ⊤ := rfl
/-
**PointedCone.** 是 Mathlib 中的一个实例，位于命名空间 `PointedCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift (ConvexCone R E) (PointedCone R E) (↑) ConvexCone.Pointed where
  prf C hC := ⟨C.toPointedCone hC, rfl⟩

end ConvexCone

section Definitions

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E]
variable {C : PointedCone R E} {x : E}

/-- Construct a pointed cone from closure under two-element conical combinations.
I.e., a nonempty set closed under two-element conical combinations is a pointed cone. -/
@[simps!]
/-
**PointedCone.ofConeComb** 是 Mathlib 中的一个定义，位于命名空间 `PointedCone`。
形式化陈述：ofConeComb (C : Set E) (nonempty : C.Nonempty) (coneComb : forall x in C, 
forall y in C, forall a : R, 0 <= a -> forall b : R, 0 <= b -> a • x + b • y in 
C) : PointedCone R E
参数：C : Set E；nonempty : C.Nonempty；coneComb : forall x in C, forall y in C, fora
ll a : R, 0 <= a -> forall b : R, 0 <= b -> a • x + b • y in C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
Construct a pointed cone from closure under two-element conical combinations.
I.e., a nonempty set closed under two-element conical combinations is a pointed 
cone.
-/
def ofConeComb (C : Set E) (nonempty : C.Nonempty)
    (coneComb : ∀ x ∈ C, ∀ y ∈ C, ∀ a : R, 0 ≤ a → ∀ b : R, 0 ≤ b → a • x + b • y ∈ C) :
    PointedCone R E :=
  .ofLinearComb C nonempty fun x hx y hy ⟨a, ha⟩ ⟨b, hb⟩ => coneComb x hx y hy a ha b hb

variable (R) in
/-- The cone hull of a set `s` is the smallest pointed cone that contains `s`.

Pointed cones being defined as submodules over nonnegative scalars, this is implemented as
the submodule span of `s` w.r.t. nonnegative scalars. -/
/-
**PointedCone.hull** 是 Mathlib 中的一个缩写定义，位于命名空间 `PointedCone`。
形式化陈述：hull (s : Set E) : PointedCone R E
参数：s : Set E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
The cone hull of a set `s` is the smallest pointed cone that contains `s`.

Pointed cones being defined as submodules over nonnegative scalars, this is impl
emented as
the submodule span of `s` w.r.t. nonnegative scalars.
-/
abbrev hull (s : Set E) : PointedCone R E := span R≥0 s
/-
**PointedCone.subset_hull** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：subset_hull {s : Set E} : s subseteq PointedCone.hull R s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma subset_hull {s : Set E} : s ⊆ PointedCone.hull R s := subset_span

@[deprecated "`PointedCone.span` was renamed to `PointedCone.hull`" (since := "2026-03-22")]
alias subset_span := subset_hull

variable (R) in
/-
**PointedCone.hull_le_span** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：hull_le_span (s : Set E) : hull R s <= span R s
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_le_restrictScalars`：span_le_restrictScalars : span R s <=
 (span S s).restrictScalars R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma hull_le_span (s : Set E) : hull R s ≤ span R s := span_le_restrictScalars R≥0 R s

/-- Elements of the cone hull are expressible as conical combination of elements from s. -/
/-
**PointedCone.mem_hull_set** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：mem_hull_set {s : Set E} : x in hull R s ↔ exists c : E ->₀ R, ↑c.support 
subseteq s ∧ (forall y, 0 <= c y) ∧ c.sum (fun m r => r • m) = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_span_set`：Submodule.mem_span_set {m : M} {s : Set M} : m i
n Submodule.span R s ↔ exists c : M ->₀ R, (c.support : Set M) subseteq s ∧ (c.s
um fun mi r …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
Elements of the cone hull are expressible as conical combination of elements fro
m s.
-/
lemma mem_hull_set {s : Set E} : x ∈ hull R s ↔
      ∃ c : E →₀ R, ↑c.support ⊆ s ∧ (∀ y, 0 ≤ c y) ∧ c.sum (fun m r => r • m) = x := by
  rw [mem_span_set]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c.support, Subtype.val ∘ c, by simp [← Subtype.val_inj]⟩, hc, fun y ↦ (c y).2, rfl⟩
  · rintro ⟨c, hc, hc₀, rfl⟩
    exact ⟨⟨c.support, fun y ↦ ⟨c y, hc₀ _⟩, by simp⟩, hc, rfl⟩

@[deprecated "`PointedCone.span` was renamed to `PointedCone.hull`" (since := "2026-03-22")]
alias mem_span_set := mem_hull_set

end Definitions

section Maps

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [Module R E]
variable [AddCommMonoid F] [Module R F]
variable [AddCommMonoid G] [Module R G]

/-!

## Maps between pointed cones

There is already a definition of maps between submodules, `Submodule.map`. In our case, these maps
are induced from linear maps between the ambient modules that are linear over nonnegative scalars.
Such maps are unlikely to be of any use in practice. So, we construct some API to define maps
between pointed cones induced from linear maps between the ambient modules that are linear over
*all* scalars.

-/

/-- The image of a pointed cone under an `R`-linear map is a pointed cone. -/
/-
**PointedCone.map** 是 Mathlib 中的一个定义，位于命名空间 `PointedCone`。
形式化陈述：map (f : E ->ₗ[R] F) (C : PointedCone R E) : PointedCone R F
参数：f : E ->ₗ[R] F；C : PointedCone R E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
The image of a pointed cone under an `R`-linear map is a pointed cone.
-/
def map (f : E →ₗ[R] F) (C : PointedCone R E) : PointedCone R F :=
  Submodule.map (f : E →ₗ[R≥0] F) C

@[simp, norm_cast]
/-
**PointedCone.toConvexCone_map** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：toConvexCone_map (C : PointedCone R E) (f : E ->ₗ[R] F) : (C.map f : Conve
xCone R F) = (C : ConvexCone R E).map f
参数：C : PointedCone R E；f : E ->ₗ[R] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toConvexCone_map (C : PointedCone R E) (f : E →ₗ[R] F) :
    (C.map f : ConvexCone R F) = (C : ConvexCone R E).map f :=
  rfl

@[simp, norm_cast]
/-
**PointedCone.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：coe_map (C : PointedCone R E) (f : E ->ₗ[R] F) : (C.map f : Set F) = f '' 
C
参数：C : PointedCone R E；f : E ->ₗ[R] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem coe_map (C : PointedCone R E) (f : E →ₗ[R] F) : (C.map f : Set F) = f '' C :=
  rfl

@[simp]
/-
**PointedCone.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：mem_map {f : E ->ₗ[R] F} {C : PointedCone R E} {y : F} : y in C.map f ↔ ex
ists x in C, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem mem_map {f : E →ₗ[R] F} {C : PointedCone R E} {y : F} : y ∈ C.map f ↔ ∃ x ∈ C, f x = y :=
  Iff.rfl
/-
**PointedCone.map_map** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：map_map (g : F ->ₗ[R] G) (f : E ->ₗ[R] F) (C : PointedCone R E) : (C.map f
).map g = C.map (g.comp f)
参数：g : F ->ₗ[R] G；f : E ->ₗ[R] F；C : PointedCone R E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map (g : F →ₗ[R] G) (f : E →ₗ[R] F) (C : PointedCone R E) :
    (C.map f).map g = C.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image g f C

@[simp]
/-
**PointedCone.map_id** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：map_id (C : PointedCone R E) : C.map LinearMap.id = C
参数：C : PointedCone R E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem map_id (C : PointedCone R E) : C.map LinearMap.id = C :=
  SetLike.coe_injective <| Set.image_id _

/-- The preimage of a pointed cone under an `R`-linear map is a pointed cone. -/
/-
**PointedCone.comap** 是 Mathlib 中的一个定义，位于命名空间 `PointedCone`。
形式化陈述：comap (f : E ->ₗ[R] F) (C : PointedCone R F) : PointedCone R E
参数：f : E ->ₗ[R] F；C : PointedCone R F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
The preimage of a pointed cone under an `R`-linear map is a pointed cone.
-/
def comap (f : E →ₗ[R] F) (C : PointedCone R F) : PointedCone R E :=
  Submodule.comap (f : E →ₗ[R≥0] F) C

@[simp, norm_cast]
/-
**PointedCone.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：coe_comap (f : E ->ₗ[R] F) (C : PointedCone R F) : (C.comap f : Set E) = f
 ⁻¹' C
参数：f : E ->ₗ[R] F；C : PointedCone R F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem coe_comap (f : E →ₗ[R] F) (C : PointedCone R F) : (C.comap f : Set E) = f ⁻¹' C :=
  rfl

@[simp]
/-
**PointedCone.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：comap_id (C : PointedCone R E) : C.comap LinearMap.id = C
参数：C : PointedCone R E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_id (C : PointedCone R E) : C.comap LinearMap.id = C :=
  rfl
/-
**PointedCone.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：comap_comap (g : F ->ₗ[R] G) (f : E ->ₗ[R] F) (C : PointedCone R G) : (C.c
omap g).comap f = C.comap (g.comp f)
参数：g : F ->ₗ[R] G；f : E ->ₗ[R] F；C : PointedCone R G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap (g : F →ₗ[R] G) (f : E →ₗ[R] F) (C : PointedCone R G) :
    (C.comap g).comap f = C.comap (g.comp f) :=
  rfl

@[simp]
/-
**PointedCone.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：mem_comap {f : E ->ₗ[R] F} {C : PointedCone R F} {x : E} : x in C.comap f 
↔ f x in C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem mem_comap {f : E →ₗ[R] F} {C : PointedCone R F} {x : E} : x ∈ C.comap f ↔ f x ∈ C :=
  Iff.rfl

end Maps

section PositiveCone

variable (R E)
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E] [Module R E] [PosSMulMono R E]

/-- The positive cone is the pointed cone formed by the set of nonnegative elements in an ordered
module. -/
@[simps!]
/-
**PointedCone.positive** 是 Mathlib 中的一个定义，位于命名空间 `PointedCone`。
形式化陈述：positive : PointedCone R E where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
The positive cone is the pointed cone formed by the set of nonnegative elements 
in an ordered
module.
-/
def positive : PointedCone R E where
  __ := AddSubmonoid.nonneg E
  smul_mem' c _ hx := by simpa using smul_nonneg c.property hx

@[simp]
/-
**PointedCone.mem_positive** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：mem_positive {x : E} : x in positive R E ↔ 0 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem mem_positive {x : E} : x ∈ positive R E ↔ 0 ≤ x :=
  Iff.rfl

@[simp, norm_cast]
/-
**PointedCone.toConvexCone_positive** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：toConvexCone_positive : ↑(positive R E) = ConvexCone.positive R E
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toConvexCone_positive : ↑(positive R E) = ConvexCone.positive R E :=
  rfl

end PositiveCone

section AddCommGroup

variable {R M : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E] [Module R E]

/-
**PointedCone.sup_inf_assoc_of_le_submodule** 是 Mathlib 中的一个引理，位于命名空间 `PointedCo
ne`。
形式化陈述：sup_inf_assoc_of_le_submodule {C : PointedCone R E} (D : PointedCone R E) 
{S : Submodule R E} (hCS : C <= S) : (C ⊔ D) ⊓ S = C ⊔ (D ⊓ S)
参数：D : PointedCone R E；hCS : C <= S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Submodule.sup_inf_assoc_of_le_of_neg_le`：sup_inf_assoc_of_le_of_neg_le {
s : Submodule R M} (t : Submodule R M) {p : Submodule R M} (hsp : s <= p) (hnsp 
: -s <= p) : (s ⊔ t) ⊓ p = s …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.neg_restrictScalars`：∀ {R : Type u_2} {M : Type u_3} [inst : S
emiring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {S : Type u_
4} [inst_3 : Semiri…
· 使用定理 `Submodule.restrictScalars.congr_simp`：∀ (S : Type u_1) {R : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S
]   [inst_3 : _root_.Modul…
· 使用定理 `Submodule.neg_eq_self`：neg_eq_self [Ring R] [AddCommGroup M] [Module R M
] (p : Submodule R M) : -p = p
-/
lemma sup_inf_assoc_of_le_submodule {C : PointedCone R E} (D : PointedCone R E)
    {S : Submodule R E} (hCS : C ≤ S) : (C ⊔ D) ⊓ S = C ⊔ (D ⊓ S) :=
  sup_inf_assoc_of_le_of_neg_le _ hCS (by simpa [Submodule.neg_le])
/-
**PointedCone.inf_sup_assoc_of_le_of_submodule_le** 是 Mathlib 中的一个引理，位于命名空间 `Poi
ntedCone`。
形式化陈述：inf_sup_assoc_of_le_of_submodule_le {C : PointedCone R E} (D : PointedCone
 R E) {S : Submodule R E} (hSC : S <= C) : (C ⊓ D) ⊔ S = C ⊓ (D ⊔ S)
参数：D : PointedCone R E；hSC : S <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Submodule.inf_sup_assoc_of_le_of_neg_le`：inf_sup_assoc_of_le_of_neg_le {
s : Submodule R M} (t : Submodule R M) {p : Submodule R M} (hps : p <= s) (hnps 
: -p <= s) : (s ⊓ t) ⊔ p = s …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.neg_restrictScalars`：∀ {R : Type u_2} {M : Type u_3} [inst : S
emiring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {S : Type u_
4} [inst_3 : Semiri…
· 使用定理 `Submodule.restrictScalars.congr_simp`：∀ (S : Type u_1) {R : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S
]   [inst_3 : _root_.Modul…
· 使用定理 `Submodule.neg_eq_self`：neg_eq_self [Ring R] [AddCommGroup M] [Module R M
] (p : Submodule R M) : -p = p
-/
lemma inf_sup_assoc_of_le_of_submodule_le {C : PointedCone R E} (D : PointedCone R E)
    {S : Submodule R E} (hSC : S ≤ C) : (C ⊓ D) ⊔ S = C ⊓ (D ⊔ S) :=
  inf_sup_assoc_of_le_of_neg_le _ hSC (by simpa [Submodule.neg_le])

end AddCommGroup

section OrderedAddCommGroup

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E] [PartialOrder E]
  [IsOrderedAddMonoid E] [Module R E]

/-- Constructs an ordered module given an ordered group, a cone, and a proof that
the order relation is the one defined by the cone. -/
/-
**PointedCone.to_isOrderedModule** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：to_isOrderedModule (C : PointedCone R E) (h : forall x y : E, x <= y ↔ y -
 x in C) : IsOrderedModule R E
参数：C : PointedCone R E；h : forall x y : E, x <= y ↔ y - x in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `IsOrderedModule.of_smul_nonneg`：IsOrderedModule.of_smul_nonneg [IsOrdere
dAddMonoid α] [IsOrderedAddMonoid β] (h : forall a : α, 0 <= a -> forall b : β, 
0 <= b -> 0 <= a • b…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `PointedCone.smul_mem`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R
] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid
 E] [inst_…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Constructs an ordered module given an ordered group, a cone, and a proof that
the order relation is the one defined by the cone.
-/
lemma to_isOrderedModule (C : PointedCone R E) (h : ∀ x y : E, x ≤ y ↔ y - x ∈ C) :
    IsOrderedModule R E := .of_smul_nonneg <| by simp +contextual [h, C.smul_mem]

end OrderedAddCommGroup

section Lineal

variable [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup E] [Module R E]

/-- The lineality space of a cone `C` is the submodule given by `C ⊓ -C`. -/
@[simps!]
/-
**PointedCone.lineal** 是 Mathlib 中的一个定义，位于命名空间 `PointedCone`。
形式化陈述：lineal (C : PointedCone R E) : Submodule R E where __
参数：C : PointedCone R E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lineality space of a cone `C` is the submodule given by `C ⊓ -C`.
-/
def lineal (C : PointedCone R E) : Submodule R E where
  __ := C.support
  smul_mem' r _ hx := by
    by_cases hr : 0 ≤ r
    · simpa using And.intro (C.smul_mem hr hx.1) (C.smul_mem hr hx.2)
    · have hr := le_of_lt <| neg_pos_of_neg <| lt_of_not_ge hr
      simpa using And.intro (C.smul_mem hr hx.2) (C.smul_mem hr hx.1)
/-
**PointedCone.ofSubmodule_lineal** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} [inst : Ring R] [inst_1 : LinearOrder R] [
inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup E] [inst_4 : _root_.Module R 
E] (C : PointedCone R E), ↑C.lineal = C ⊓ -C
参数：C : PointedCone R E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofSubmodule_lineal (C : PointedCone R E) : C.lineal = C ⊓ -C := rfl
/-
**PointedCone.mem_lineal** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} [inst : Ring R] [inst_1 : LinearOrder R] [
inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup E] [inst_4 : _root_.Module R 
E] {C : PointedCone R E} {x : E}, x ∈ C.lineal ↔ x ∈ C ∧ -x ∈ C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_lineal {C : PointedCone R E} {x : E} : x ∈ C.lineal ↔ x ∈ C ∧ -x ∈ C := .rfl
/-
**PointedCone.support_eq** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} [inst : Ring R] [inst_1 : LinearOrder R] [
inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup E] [inst_4 : _root_.Module R 
E] (C : PointedCone R E), C.support = C.lineal.toAddSubgroup
参数：C : PointedCone R E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
@[simp] theorem support_eq (C : PointedCone R E) : C.support = C.lineal.toAddSubgroup := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The lineality space of a cone is the largest submodule contained in the cone. -/
/-
**PointedCone.gc_ofSubmodule_lineal** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：gc_ofSubmodule_lineal : GaloisConnection (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
The lineality space of a cone is the largest submodule contained in the cone.
-/
theorem gc_ofSubmodule_lineal :
    GaloisConnection (α := Submodule R E) ofSubmodule lineal :=
  fun _ _ ↦ ⟨fun _ _ ↦ by aesop, fun h _ hx ↦ (h hx).1⟩
/-
**PointedCone.lineal_le** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：lineal_le (C : PointedCone R E) : C.lineal <= C
参数：C : PointedCone R E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.gc_ofSubmodule_lineal`：gc_ofSubmodule_lineal : GaloisConnect
ion (α
-/
lemma lineal_le (C : PointedCone R E) : C.lineal ≤ C := gc_ofSubmodule_lineal.l_u_le C
/-
**PointedCone.lineal_eq_sSup** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：lineal_eq_sSup (C : PointedCone R E) : C.lineal = sSup {S : Submodule R E 
| S <= C}
参数：C : PointedCone R E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `GaloisConnection.le_iff_le`：le_iff_le {a : α} {b : β} : l a <= b ↔ a <= 
u b
· 使用定理 `PointedCone.gc_ofSubmodule_lineal`：gc_ofSubmodule_lineal : GaloisConnect
ion (α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `csSup_Iic`：csSup_Iic : sSup (Iic a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lineal_eq_sSup (C : PointedCone R E) : C.lineal = sSup {S : Submodule R E | S ≤ C} := by
  simp_rw [gc_ofSubmodule_lineal.le_iff_le, Set.Iic_def, csSup_Iic]

end Lineal

section Salient

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E] [Module R E]

/-- A pointed cone is salient iff the intersection of the cone with its negative
is the set `{0}`. -/
/-
**PointedCone.salient_iff_inter_neg_eq_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Poin
tedCone`。
形式化陈述：salient_iff_inter_neg_eq_singleton (C : PointedCone R E) : (C : ConvexCone
 R E).Salient ↔ (C inter -C : Set E) = {0}
参数：C : PointedCone R E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A pointed cone is salient iff the intersection of the cone with its negative
is the set `{0}`.
-/
lemma salient_iff_inter_neg_eq_singleton (C : PointedCone R E) :
    (C : ConvexCone R E).Salient ↔ (C ∩ -C : Set E) = {0} := by
  simp [ConvexCone.Salient, Set.eq_singleton_iff_unique_mem, not_imp_not]

end Salient

end PointedCone

