/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Order.Module.HahnEmbedding
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Real.Embedding
public import Mathlib.GroupTheory.DivisibleHull

/-!

# Hahn embedding theorem

In this file, we prove the Hahn embedding theorem: every linearly ordered abelian group
can be embedded as an ordered subgroup of `Lex ℝ⟦Ω⟧`, where `Ω` is the type of finite
Archimedean classes of the group. The theorem is stated as `hahnEmbedding_isOrderedAddMonoid`.

## References

* [A. H. Clifford, *Note on Hahn’s theorem on ordered Abelian groups.*][clifford1954]

-/

public section

open ArchimedeanClass HahnSeries

variable (M : Type*) [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

section Module
variable [Module ℚ M] [IsOrderedModule ℚ M]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (HahnEmbedding.Seed ℚ M ℝ) := by
  obtain ⟨strata⟩ : Nonempty (HahnEmbedding.ArchimedeanStrata ℚ M) := inferInstance
  choose f hf using fun c ↦ Archimedean.exists_orderAddMonoidHom_real_injective (strata.stratum c)
  refine ⟨strata, fun c ↦ (f c).toRatLinearMap, fun c ↦ ?_⟩
  apply Monotone.strictMono_of_injective
  · simpa using OrderHomClass.monotone (f c)
  · simpa using hf c
/-
**hahnEmbedding_isOrderedModule_rat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hahnEmbedding_isOrderedModule_rat : exists f : M ->ₗ[Rat] Lex Real⟦FiniteA
rchimedeanClass M⟧, StrictMono f ∧ forall a, .mk a = FiniteArchimedeanClass.with
TopOrderIso M (ofLex (f a)).orderTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hahnEmbedding_isOrderedModule`：hahnEmbedding_isOrderedModule [IsOrderedA
ddMonoid R] [Archimedean R] [h : Nonempty (HahnEmbedding.Seed K M R)] : exists f
 : M ->ₗ[K] Lex R⟦F…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanRat`：Archimedean ℚ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `instNonemptySeedRatReal`：∀ (M : Type u_1) [inst : AddCommGroup M] [inst_
1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M]   [inst_3 : _root_.Module ℚ M
] [inst_4 : I…
-/
theorem hahnEmbedding_isOrderedModule_rat :
    ∃ f : M →ₗ[ℚ] Lex ℝ⟦FiniteArchimedeanClass M⟧, StrictMono f ∧
      ∀ a, .mk a = FiniteArchimedeanClass.withTopOrderIso M (ofLex (f a)).orderTop := by
  apply hahnEmbedding_isOrderedModule

end Module

/--
**Hahn embedding theorem**

For a linearly ordered additive group `M`, there exists an injective `OrderAddMonoidHom` from `M` to
`Lex ℝ⟦FiniteArchimedeanClass M⟧` that sends each `a : M` to an element of the `a`-Archimedean class
of the Hahn series.
-/
/-
**hahnEmbedding_isOrderedAddMonoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hahnEmbedding_isOrderedAddMonoid : exists f : M ->+o Lex Real⟦FiniteArchim
edeanClass M⟧, Function.Injective f ∧ forall a, .mk a = FiniteArchimedeanClass.w
ithTopOrderIso M (ofLex (f a)).orderTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `DivisibleHull.coe_injective`：coe_injective : Function.Injective ((↑) : M
 -> DivisibleHull M)
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `DivisibleHull.instIsOrderedCancelAddMonoid`：∀ {M : Type u_2} [inst : Add
CommMonoid M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedCancelAddMonoid M],   
IsOrderedCancelAddMonoid (Divisi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DivisibleHull.coeOrderAddMonoidHom_apply`：∀ (M : Type u_2) [inst : AddCo
mmGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] (m : M),   (
DivisibleHull.coeOrderAddMonoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `hahnEmbedding_isOrderedModule_rat`：hahnEmbedding_isOrderedModule_rat : e
xists f : M ->ₗ[Rat] Lex Real⟦FiniteArchimedeanClass M⟧, StrictMono f ∧ forall a
, .mk a = FiniteArchime…
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `DivisibleHull.instIsStrictOrderedModuleRat`：∀ {M : Type u_2} [inst : Add
CommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M],   IsStric
tOrderedModule ℚ (DivisibleHull …
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `HahnSeries.embDomainOrderAddMonoidHom_injective`：embDomainOrderAddMonoid
Hom_injective [AddMonoid R] : Function.Injective (embDomainOrderAddMonoidHom f (
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.symm_apply_eq`：symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.s
ymm y = x ↔ y = e x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
**Hahn embedding theorem**

For a linearly ordered additive group `M`, there exists an injective `OrderAddMo
noidHom` from `M` to
`Lex ℝ⟦FiniteArchimedeanClass M⟧` that sends each `a : M` to an element of the `
a`-Archimedean class
of the Hahn series.
-/
theorem hahnEmbedding_isOrderedAddMonoid :
    ∃ f : M →+o Lex ℝ⟦FiniteArchimedeanClass M⟧, Function.Injective f ∧
      ∀ a, .mk a = FiniteArchimedeanClass.withTopOrderIso M (ofLex (f a)).orderTop := by
  /-
  The desired embedding is the composition of three functions:

      Group type                                    `ArchimedeanClass` / `HahnSeries.orderTop` type

      `M`                                           `ArchimedeanClass M`
  `f₁` ↓+o                                           ↓o~
      `D-Hull M`                                    `ArchimedeanClass (D-Hull M)`
  `f₂` ↓+o                                           ↓o~
      `Lex ℝ⟦F-A-Class (D-Hull M)⟧`                 `WithTop (F-A-Class (D-Hull M))`
  `f₃` ↓+o(~)                                        ↓o~
      `Lex ℝ⟦F-A-Class M⟧`                          `WithTop (F-A-Class M)`
  -/
  let f₁ := DivisibleHull.coeOrderAddMonoidHom M
  have hf₁ : Function.Injective f₁ := DivisibleHull.coe_injective
  have hf₁class (a : M) : mk a = (DivisibleHull.archimedeanClassOrderIso M).symm (mk (f₁ a)) := by
    simp [f₁]
  obtain ⟨f₂', hf₂', hf₂class'⟩ := hahnEmbedding_isOrderedModule_rat (DivisibleHull M)
  let f₂ := OrderAddMonoidHom.mk f₂'.toAddMonoidHom hf₂'.monotone
  have hf₂ : Function.Injective f₂ := hf₂'.injective
  have hf₂class (a : DivisibleHull M) :
      mk a = (FiniteArchimedeanClass.withTopOrderIso (DivisibleHull M)) (ofLex (f₂ a)).orderTop :=
    hf₂class' a
  let f₃ : Lex ℝ⟦FiniteArchimedeanClass (DivisibleHull M)⟧ →+o Lex ℝ⟦FiniteArchimedeanClass M⟧ :=
    HahnSeries.embDomainOrderAddMonoidHom
    (FiniteArchimedeanClass.congrOrderIso (DivisibleHull.archimedeanClassOrderIso M).symm)
  have hf₃ : Function.Injective f₃ := HahnSeries.embDomainOrderAddMonoidHom_injective _
  have hf₃class (a : Lex ℝ⟦FiniteArchimedeanClass (DivisibleHull M)⟧) :
      (ofLex a).orderTop = OrderIso.withTopCongr
      ((FiniteArchimedeanClass.congrOrderIso (DivisibleHull.archimedeanClassOrderIso M)))
      (ofLex (f₃ a)).orderTop := by
    rw [← OrderIso.symm_apply_eq]
    simp [f₃, ← OrderIso.withTopCongr_symm]
  refine ⟨f₃.comp (f₂.comp f₁), hf₃.comp (hf₂.comp hf₁), ?_⟩
  intro a
  simp_rw [hf₁class, hf₂class, hf₃class, OrderAddMonoidHom.comp_apply]
  cases (ofLex (f₃ (f₂ (f₁ a)))).orderTop with
  | top => simp
  | coe x => simp [-DivisibleHull.archimedeanClassOrderIso_apply]
