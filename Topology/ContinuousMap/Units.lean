/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Units of continuous functions

This file concerns itself with `C(X, M)ˣ` and `C(X, Mˣ)` when `X` is a topological space
and `M` has some monoid structure compatible with its topology.
-/

@[expose] public section


variable {X M R 𝕜 : Type*} [TopologicalSpace X]

namespace ContinuousMap

section Monoid

variable [Monoid M] [TopologicalSpace M] [ContinuousMul M]

/-- Equivalence between continuous maps into the units of a monoid with continuous multiplication
and the units of the monoid of continuous maps. -/
-- `simps` generates some lemmas here with LHS not in simp normal form,
-- so we write them out manually below.
@[to_additive (attr := simps apply_val_apply symm_apply_apply_val)
/-- Equivalence between continuous maps into the additive units of an additive monoid with
continuous addition and the additive units of the additive monoid of continuous maps. -/]
/-
**ContinuousMap.unitsLift** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：unitsLift : C(X, Mˣ) ≃ C(X, M)ˣ where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def unitsLift : C(X, Mˣ) ≃ C(X, M)ˣ where
  toFun f :=
    { val := ⟨fun x => f x, Units.continuous_val.comp f.continuous⟩
      inv := ⟨fun x => ↑(f x)⁻¹, Units.continuous_val.comp (continuous_inv.comp f.continuous)⟩
      val_inv := ext fun _ => Units.mul_inv _
      inv_val := ext fun _ => Units.inv_mul _ }
  invFun f :=
    { toFun := fun x =>
        ⟨(f : C(X, M)) x, (↑f⁻¹ : C(X, M)) x,
          ContinuousMap.congr_fun f.mul_inv x, ContinuousMap.congr_fun f.inv_mul x⟩
      continuous_toFun := continuous_induced_rng.2 <|
        (f : C(X, M)).continuous.prodMk <|
        MulOpposite.continuous_op.comp (↑f⁻¹ : C(X, M)).continuous }

@[to_additive (attr := simp)]
/-
**ContinuousMap.unitsLift_apply_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousM
ap`。
形式化陈述：unitsLift_apply_inv_apply (f : C(X, Mˣ)) (x : X) : (↑(ContinuousMap.unitsL
ift f)⁻¹ : C(X, M)) x = (f x)⁻¹
参数：f : C(X, Mˣ)；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unitsLift_apply_inv_apply (f : C(X, Mˣ)) (x : X) :
    (↑(ContinuousMap.unitsLift f)⁻¹ : C(X, M)) x = (f x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.unitsLift_symm_apply_apply_inv'** 是 Mathlib 中的一个引理，位于命名空间 `Conti
nuousMap`。
形式化陈述：unitsLift_symm_apply_apply_inv' (f : C(X, M)ˣ) (x : X) : (ContinuousMap.un
itsLift.symm f x)⁻¹ = (↑f⁻¹ : C(X, M)) x
参数：f : C(X, M)ˣ；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma unitsLift_symm_apply_apply_inv' (f : C(X, M)ˣ) (x : X) :
    (ContinuousMap.unitsLift.symm f x)⁻¹ = (↑f⁻¹ : C(X, M)) x := by
  rfl

end Monoid

section NormedRing

variable [NormedRing R] [CompleteSpace R]

/-
**ContinuousMap.continuous_isUnit_unit** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`
。
形式化陈述：continuous_isUnit_unit {f : C(X, R)} (h : forall x, IsUnit (f x)) : Contin
uous fun x => (h x).unit
参数：X, R；h : forall x, IsUnit (f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `MulOpposite.continuous_op`：continuous_op : Continuous (op : M -> Mᵐᵒᵖ)
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `NormedRing.inverse_continuousAt`：inverse_continuousAt (x : Rˣ) : Continu
ousAt inverse (x : R)
· 使用定理 `instHasSummableGeomSeriesOfCompleteSpace`：∀ {R : Type u_4} [inst : Norme
dRing R] [CompleteSpace R], HasSummableGeomSeries R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `ContinuousMap.continuousAt`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] (f : C(α, β)) (x : α),   Continuou
sAt (⇑f) x
-/
theorem continuous_isUnit_unit {f : C(X, R)} (h : ∀ x, IsUnit (f x)) :
    Continuous fun x => (h x).unit := by
  refine
    continuous_induced_rng.2
      (Continuous.prodMk f.continuous
        (MulOpposite.continuous_op.comp (continuous_iff_continuousAt.mpr fun x => ?_)))
  have := NormedRing.inverse_continuousAt (h x).unit
  simp only
  simp only [← Ring.inverse_unit, IsUnit.unit_spec] at this ⊢
  exact this.comp (f.continuousAt x)

/-- Construct a continuous map into the group of units of a normed ring from a function into the
normed ring and a proof that every element of the range is a unit. -/
@[simps]
/-
**ContinuousMap.unitsOfForallIsUnit** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：unitsOfForallIsUnit {f : C(X, R)} (h : forall x, IsUnit (f x)) : C(X, Rˣ) 
where toFun x
参数：X, R；h : forall x, IsUnit (f x)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_isUnit_unit`：continuous_isUnit_unit {f : C(X, R
)} (h : forall x, IsUnit (f x)) : Continuous fun x => (h x).unit

--- 原说明 ---
Construct a continuous map into the group of units of a normed ring from a funct
ion into the
normed ring and a proof that every element of the range is a unit.
-/
noncomputable def unitsOfForallIsUnit {f : C(X, R)} (h : ∀ x, IsUnit (f x)) : C(X, Rˣ) where
  toFun x := (h x).unit
  continuous_toFun := continuous_isUnit_unit h
/-
**ContinuousMap.canLift** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：canLift : CanLift C(X, R) C(X, Rˣ) (fun f => ⟨fun x => f x, Units.continuo
us_val.comp f.continuous⟩) fun f => forall x, IsUnit (f x) where prf f h
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Units.continuous_val`：continuous_val : Continuous ((↑) : Mˣ -> M)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
-/
instance canLift :
    CanLift C(X, R) C(X, Rˣ) (fun f => ⟨fun x => f x, Units.continuous_val.comp f.continuous⟩)
      fun f => ∀ x, IsUnit (f x) where
  prf f h := ⟨unitsOfForallIsUnit h, by ext; rfl⟩
/-
**ContinuousMap.isUnit_iff_forall_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMa
p`。
形式化陈述：isUnit_iff_forall_isUnit (f : C(X, R)) : IsUnit f ↔ forall x, IsUnit (f x)
参数：f : C(X, R)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
-/
theorem isUnit_iff_forall_isUnit (f : C(X, R)) : IsUnit f ↔ ∀ x, IsUnit (f x) :=
  Iff.intro (fun h => fun x => ⟨unitsLift.symm h.unit x, rfl⟩) fun h =>
    ⟨ContinuousMap.unitsLift (unitsOfForallIsUnit h), by ext; rfl⟩

end NormedRing

section NormedField

variable [NormedField 𝕜] [NormedDivisionRing R] [Algebra 𝕜 R] [CompleteSpace R]

/-
**ContinuousMap.isUnit_iff_forall_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ap`。
形式化陈述：isUnit_iff_forall_ne_zero (f : C(X, R)) : IsUnit f ↔ forall x, f x != 0
参数：f : C(X, R)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousMap.isUnit_iff_forall_isUnit`：isUnit_iff_forall_isUnit (f : C(
X, R)) : IsUnit f ↔ forall x, IsUnit (f x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUnit_iff_forall_ne_zero (f : C(X, R)) : IsUnit f ↔ ∀ x, f x ≠ 0 := by
  simp_rw [f.isUnit_iff_forall_isUnit, isUnit_iff_ne_zero]
/-
**ContinuousMap.spectrum_eq_preimage_range** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
Map`。
形式化陈述：spectrum_eq_preimage_range (f : C(X, R)) : spectrum 𝕜 f = algebraMap _ _ ⁻
¹' Set.range f
参数：f : C(X, R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem spectrum_eq_preimage_range (f : C(X, R)) :
    spectrum 𝕜 f = algebraMap _ _ ⁻¹' Set.range f := by
  ext x
  simp only [spectrum.mem_iff, isUnit_iff_forall_ne_zero, not_forall, sub_apply,
    Classical.not_not, Set.mem_range,
    sub_eq_zero, @eq_comm _ (x • 1 : R) _, Set.mem_preimage, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply]
/-
**ContinuousMap.spectrum_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：spectrum_eq_range [CompleteSpace 𝕜] (f : C(X, 𝕜)) : spectrum 𝕜 f = Set.ran
ge f
参数：f : C(X, 𝕜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.spectrum_eq_preimage_range`：spectrum_eq_preimage_range (f 
: C(X, R)) : spectrum 𝕜 f = algebraMap _ _ ⁻¹' Set.range f
· 使用定理 `Algebra.algebraMap_self`：∀ {R : Type u} [inst : CommSemiring R], algebra
Map R R = RingHom.id R
· 使用定理 `Set.preimage_id`：preimage_id {s : Set α} : id ⁻¹' s = s
-/
theorem spectrum_eq_range [CompleteSpace 𝕜] (f : C(X, 𝕜)) : spectrum 𝕜 f = Set.range f := by
  rw [spectrum_eq_preimage_range, Algebra.algebraMap_self]
  exact Set.preimage_id

end NormedField

end ContinuousMap

