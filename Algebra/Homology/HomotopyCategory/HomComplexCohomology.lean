/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Cohomology of the hom complex

Given `ℤ`-indexed cochain complexes `K` and `L`, and `n : ℤ`, we introduce
a type `HomComplex.CohomologyClass K L n` which is the quotient
of `HomComplex.Cocycle K L n` which identifies cohomologous cocycles.
We construct this type of cohomology classes instead of using
the homology API because `Cochain K L` can be considered both
as a complex of abelian groups or as a complex of `R`-modules
when the category is `R`-linear. This also complements the API
around `HomComplex` which is centered on terms in types
`Cochain` or `Cocycle` which are suitable for computations.

We also show that `HomComplex.CohomologyClass K L n` identifies to
the type of morphisms between `K` and `L⟦n⟧` in the homotopy category.
-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

namespace CochainComplex

variable (K L : CochainComplex C ℤ) (n m p : ℤ)

namespace HomComplex

/-- The subgroup of `Cocycle K L n` consisting of coboundaries. -/
/-
**CochainComplex.HomComplex.coboundaries** 是 Mathlib 中的一个定义，位于命名空间 `CochainCompl
ex.HomComplex`。
形式化陈述：coboundaries : AddSubgroup (Cocycle K L n) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup of `Cocycle K L n` consisting of coboundaries.
-/
def coboundaries : AddSubgroup (Cocycle K L n) where
  carrier := Set.ofPred (fun α ↦ ∃ (m : ℤ) (hm : m + 1 = n) (β : Cochain K L m), δ m n β = α)
  zero_mem' := ⟨n - 1, by simp, 0, by simp⟩
  add_mem' := by
    rintro α₁ α₂ ⟨m, hm, β₁, hβ₁⟩ ⟨m', hm', β₂, hβ₂⟩
    obtain rfl : m = m' := by lia
    exact ⟨m, hm, β₁ + β₂, by aesop⟩
  neg_mem' := by
    rintro α ⟨m, hm, β, hβ⟩
    exact ⟨m, hm, -β, by aesop⟩

set_option backward.isDefEq.respectTransparency.types false in
variable {K L n} in
/-
**CochainComplex.HomComplex.mem_coboundaries_iff** 是 Mathlib 中的一个引理，位于命名空间 `Coch
ainComplex.HomComplex`。
形式化陈述：mem_coboundaries_iff (α : Cocycle K L n) (m : Int) (hm : m + 1 = n) : α in
 coboundaries K L n ↔ exists (β : Cochain K L m), δ m n β = α
参数：α : Cocycle K L n；m : Int；hm : m + 1 = n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma mem_coboundaries_iff (α : Cocycle K L n) (m : ℤ) (hm : m + 1 = n) :
    α ∈ coboundaries K L n ↔ ∃ (β : Cochain K L m), δ m n β = α := by
  simp only [coboundaries, AddSubgroup.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk]
  grind

/-- The type of cohomology classes of degree `n` in the complex of morphisms
from `K` to `L`. -/
/-
**CochainComplex.HomComplex.CohomologyClass** 是 Mathlib 中的一个定义，位于命名空间 `CochainCo
mplex.HomComplex`。
形式化陈述：CohomologyClass : Type v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of cohomology classes of degree `n` in the complex of morphisms
from `K` to `L`.
-/
def CohomologyClass : Type v := Cocycle K L n ⧸ coboundaries K L n
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (CohomologyClass K L n) :=
  inferInstanceAs (AddCommGroup (Cocycle K L n ⧸ coboundaries K L n))

namespace CohomologyClass

variable {K L n}

/-- The cohomology class of a cocycle. -/
/-
**CochainComplex.HomComplex.CohomologyClass.mk** 是 Mathlib 中的一个定义，位于命名空间 `Cochai
nComplex.HomComplex.CohomologyClass`。
形式化陈述：mk (x : Cocycle K L n) : CohomologyClass K L n
参数：x : Cocycle K L n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cohomology class of a cocycle.
-/
def mk (x : Cocycle K L n) : CohomologyClass K L n :=
  Quotient.mk _ x
/-
**CochainComplex.HomComplex.CohomologyClass.mk_surjective** 是 Mathlib 中的一个引理，位于命
名空间 `CochainComplex.HomComplex.CohomologyClass`。
形式化陈述：mk_surjective : Function.Surjective (mk : Cocycle K L n -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)
-/
lemma mk_surjective : Function.Surjective (mk : Cocycle K L n → _) :=
  Quotient.mk_surjective

variable (K L n) in
@[simp]
/-
**CochainComplex.HomComplex.CohomologyClass.mk_zero** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.HomComplex.CohomologyClass`。
形式化陈述：mk_zero : mk (0 : Cocycle K L n) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_zero :
    mk (0 : Cocycle K L n) = 0 := rfl

@[simp]
/-
**CochainComplex.HomComplex.CohomologyClass.mk_add** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.CohomologyClass`。
形式化陈述：mk_add (x y : Cocycle K L n) : mk (x + y) = mk x + mk y
参数：x y : Cocycle K L n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_add (x y : Cocycle K L n) :
    mk (x + y) = mk x + mk y := rfl

@[simp]
/-
**CochainComplex.HomComplex.CohomologyClass.mk_sub** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.CohomologyClass`。
形式化陈述：mk_sub (x y : Cocycle K L n) : mk (x - y) = mk x - mk y
参数：x y : Cocycle K L n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_sub (x y : Cocycle K L n) :
    mk (x - y) = mk x - mk y := rfl

@[simp]
/-
**CochainComplex.HomComplex.CohomologyClass.mk_neg** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.CohomologyClass`。
形式化陈述：mk_neg (x : Cocycle K L n) : mk (-x) = -mk x
参数：x : Cocycle K L n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_neg (x : Cocycle K L n) :
    mk (-x) = -mk x := rfl
/-
**CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff** 是 Mathlib 中的一个引理，位于
命名空间 `CochainComplex.HomComplex.CohomologyClass`。
形式化陈述：mk_eq_zero_iff (x : Cocycle K L n) : mk x = 0 ↔ x in coboundaries K L n
参数：x : Cocycle K L n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.eq_zero_iff`：∀ {G : Type u_1} [inst : AddGroup G] {N : 
AddSubgroup G} [inst_1 : N.Normal] (x : G), ↑x = 0 ↔ x ∈ N
-/
lemma mk_eq_zero_iff (x : Cocycle K L n) :
    mk x = 0 ↔ x ∈ coboundaries K L n :=
  QuotientAddGroup.eq_zero_iff x

variable (K L n) in
/-- The projection map `Cocycle K L n →+ CohomologyClass K L n`. -/
@[simps]
/-
**CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom** 是 Mathlib 中的一个定义，位于
命名空间 `CochainComplex.HomComplex.CohomologyClass`。
形式化陈述：mkAddMonoidHom : Cocycle K L n ->+ CohomologyClass K L n where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection map `Cocycle K L n →+ CohomologyClass K L n`.
-/
def mkAddMonoidHom : Cocycle K L n →+ CohomologyClass K L n where
  toFun := mk
  map_zero' := by simp
  map_add' := by simp

section

variable {G : Type*} [AddCommGroup G]
  (f : Cocycle K L n →+ G) (hf : coboundaries K L n ≤ f.ker)

/-- Constructor for additive morphisms from `CohomologyClass K L n`. -/
/-
**CochainComplex.HomComplex.CohomologyClass.descAddMonoidHom** 是 Mathlib 中的一个定义，
位于命名空间 `CochainComplex.HomComplex.CohomologyClass`。
形式化陈述：descAddMonoidHom : CohomologyClass K L n ->+ G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for additive morphisms from `CohomologyClass K L n`.
-/
def descAddMonoidHom :
    CohomologyClass K L n →+ G :=
  QuotientAddGroup.lift _ f hf

@[simp]
/-
**CochainComplex.HomComplex.CohomologyClass.descAddMonoidHom_cohomologyClass** 是
 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComplex.CohomologyClass`。
形式化陈述：descAddMonoidHom_cohomologyClass (x : Cocycle K L n) : descAddMonoidHom f 
hf (mk x) = f x
参数：x : Cocycle K L n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma descAddMonoidHom_cohomologyClass (x : Cocycle K L n) :
    descAddMonoidHom f hf (mk x) = f x := rfl

end

set_option backward.isDefEq.respectTransparency false in
/-- The additive map which sends a cohomology class to the corresponding morphism
in the homotopy category. -/
/-
**CochainComplex.HomComplex.CohomologyClass.toHom** 是 Mathlib 中的一个定义，位于命名空间 `Coc
hainComplex.HomComplex.CohomologyClass`。
形式化陈述：toHom : CohomologyClass K L n ->+ ((HomotopyCategory.quotient C _).obj K ⟶
 (HomotopyCategory.quotient C _).obj (L⟦n⟧))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive map which sends a cohomology class to the corresponding morphism
in the homotopy category.
-/
def toHom :
    CohomologyClass K L n →+
      ((HomotopyCategory.quotient C _).obj K ⟶ (HomotopyCategory.quotient C _).obj (L⟦n⟧)) :=
  descAddMonoidHom ((Functor.mapAddHom _).comp Cocycle.equivHomShift.symm.toAddMonoidHom) (by
    rintro ⟨x, _⟩ ⟨m, hm, β, rfl⟩
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
      AddEquiv.toAddMonoidHom_eq_coe, Function.comp_apply, Cocycle.equivHomShift_symm_apply,
      Functor.mapAddHom_apply, HomotopyCategory.quotient_map_eq_zero_iff]
    exact ⟨(Cochain.equivHomotopy _ _).symm ⟨n.negOnePow • β.rightShift _ _ (by lia),
      by simp [Cochain.δ_rightShift _ _ _ _ _ _ (zero_add n), smul_smul]⟩⟩)
/-
**CochainComplex.HomComplex.CohomologyClass.toHom_mk** 是 Mathlib 中的一个引理，位于命名空间 `
CochainComplex.HomComplex.CohomologyClass`。
形式化陈述：toHom_mk (x : Cocycle K L n) : toHom (mk x) = (HomotopyCategory.quotient C
 _).map (Cocycle.equivHomShift.symm x)
参数：x : Cocycle K L n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma toHom_mk (x : Cocycle K L n) :
    toHom (mk x) = (HomotopyCategory.quotient C _).map (Cocycle.equivHomShift.symm x) := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.CohomologyClass.toHom_mk_eq_zero_iff** 是 Mathlib 中的一
个引理，位于命名空间 `CochainComplex.HomComplex.CohomologyClass`。
形式化陈述：toHom_mk_eq_zero_iff (x : Cocycle K L n) : toHom (mk x) = 0 ↔ x in cobound
aries K L n
参数：x : Cocycle K L n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddSubsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Add M] (carrier 
carrier_1 : Set M) (e_carrier : carrier = carrier_1)   (add_mem' : ∀ {a b : M}, 
a ∈ carrier → b ∈ c…
· 使用定理 `AddSubmonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : AddZeroClass M] (to
AddSubsemigroup toAddSubsemigroup_1 : AddSubsemigroup M)   (e_toAddSubsemigroup 
: toAddSubsemigr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddSubgroup.mk.congr_simp`：∀ {G : Type u_3} [inst : AddGroup G] (toAddSu
bmonoid toAddSubmonoid_1 : AddSubmonoid G)   (e_toAddSubmonoid : toAddSubmonoid 
= toAddSubmonoi…
· 使用引理 `HomotopyCategory.quotient_map_eq_zero_iff`：quotient_map_eq_zero_iff {C D
 : HomologicalComplex V c} (f : C ⟶ D) : (quotient V c).map f = 0 ↔ Nonempty (Ho
motopy f 0)
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.toHom_mk`：toHom_mk (x : Cocycl
e K L n) : toHom (mk x) = (HomotopyCategory.quotient C _).map (Cocycle.equivHomS
hift.symm x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CochainComplex.HomComplex.δ_units_smul`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {R : Type u_1} 
  [inst_2 : Ring R] [inst_3 …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `CochainComplex.HomComplex.Cochain.δ_rightUnshift`：δ_rightUnshift {a n' :
 Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n) (m m' : Int) (hm' : 
m' + a = m) : δ n m (γ.rightUnshift n …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditiv
e C]   {K L : CochainComplex C ℤ} {n : ℤ} (a : C…
· 使用引理 `CochainComplex.HomComplex.Cocycle.cochain_ofHom_homOf_eq_coe`：cochain_of
Hom_homOf_eq_coe (z : Cocycle F G 0) : Cochain.ofHom (homOf z) = (z : Cochain F 
G 0)
· 使用定理 `CochainComplex.HomComplex.Cocycle.rightShift_coe`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {K 
L : CochainComplex C ℤ} {n : ℤ} (γ : C…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_zero`：ofHom_zero : ofHom (0 : F 
⟶ G) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.rightUnshift_rightShift`：rightUnshift_
rightShift (a n' : Int) (hn' : n' + a = n) : (γ.rightShift a n' hn').rightUnshif
t n hn' = γ
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff`：mk_eq_zero_iff
 (x : Cocycle K L n) : mk x = 0 ↔ x in coboundaries K L n
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
（共 32 条，此处仅展示前 30 条）
-/
lemma toHom_mk_eq_zero_iff (x : Cocycle K L n) :
    toHom (mk x) = 0 ↔ x ∈ coboundaries K L n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [coboundaries, exists_prop, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
    rw [toHom_mk, HomotopyCategory.quotient_map_eq_zero_iff] at h
    obtain ⟨γ, h⟩ := Cochain.equivHomotopy _ _ h.some
    simp only [Cochain.ofHom_zero, add_zero, Cocycle.equivHomShift_symm_apply,
      Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.rightShift_coe] at h
    exact ⟨n - 1, by simp, n.negOnePow • γ.rightUnshift _ (by lia),
      by simp [Cochain.δ_rightUnshift _ _ _ _ _ (zero_add n), smul_smul, ← h]⟩
  · rw [← mk_eq_zero_iff] at h
    rw [h, map_zero]

variable (K L n) in
/-
**CochainComplex.HomComplex.CohomologyClass.toHom_bijective** 是 Mathlib 中的一个引理，位
于命名空间 `CochainComplex.HomComplex.CohomologyClass`。
形式化陈述：toHom_bijective : Function.Bijective (toHom : CohomologyClass K L n -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.mk_surjective`：mk_surjective :
 Function.Surjective (mk : Cocycle K L n -> _)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.mk_sub`：mk_sub (x y : Cocycle 
K L n) : mk (x - y) = mk x - mk y
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff`：mk_eq_zero_iff
 (x : Cocycle K L n) : mk x = 0 ↔ x in coboundaries K L n
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.toHom_mk_eq_zero_iff`：toHom_mk
_eq_zero_iff (x : Cocycle K L n) : toHom (mk x) = 0 ↔ x in coboundaries K L n
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `HomotopyCategory.instFullHomologicalComplexQuotient`：∀ {ι : Type u_2} (V
 : Type u) [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Pr
eadditive V]   (c : ComplexShape ι), (Hom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddEquiv.symm_apply_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (x : M), e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toHom_bijective : Function.Bijective (toHom : CohomologyClass K L n → _) := by
  refine ⟨fun x y h ↦ ?_, fun f ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [← sub_eq_zero, ← mk_sub, mk_eq_zero_iff, ← toHom_mk_eq_zero_iff,
      mk_sub, map_sub, h, sub_self]
  · obtain ⟨f, rfl⟩ := Functor.map_surjective _ f
    exact ⟨mk (Cocycle.equivHomShift f), by simp [toHom_mk]⟩

/-- Cohomology classes identify to morphisms in the homotopy category. -/
@[simps! apply]
/-
**CochainComplex.HomComplex.CohomologyClass.homAddEquiv** 是 Mathlib 中的一个定义，位于命名空
间 `CochainComplex.HomComplex.CohomologyClass`。
形式化陈述：homAddEquiv : CohomologyClass K L n ≃+ ((HomotopyCategory.quotient C _).ob
j K ⟶ (HomotopyCategory.quotient C _).obj (L⟦n⟧))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.toHom_bijective`：toHom_bijecti
ve : Function.Bijective (toHom : CohomologyClass K L n -> _)

--- 原说明 ---
Cohomology classes identify to morphisms in the homotopy category.
-/
noncomputable def homAddEquiv :
    CohomologyClass K L n ≃+
      ((HomotopyCategory.quotient C _).obj K ⟶ (HomotopyCategory.quotient C _).obj (L⟦n⟧)) :=
  AddEquiv.ofBijective toHom (toHom_bijective _ _ _)

end CohomologyClass

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `CohomologyClass K L m` identifies to the cohomology of the complex `HomComplex K L`
in degree `m`. -/
@[simps]
/-
**CochainComplex.HomComplex.leftHomologyData'** 是 Mathlib 中的一个定义，位于命名空间 `Cochain
Complex.HomComplex`。
形式化陈述：leftHomologyData' (hm : n + 1 = m) (hp : m + 1 = p) : ((HomComplex K L).sc
' n m p).LeftHomologyData where K
参数：hm : n + 1 = m；hp : m + 1 = p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CohomologyClass K L m` identifies to the cohomology of the complex `HomComplex 
K L`
in degree `m`.
-/
def leftHomologyData' (hm : n + 1 = m) (hp : m + 1 = p) :
    ((HomComplex K L).sc' n m p).LeftHomologyData where
  K := .of (Cocycle K L m)
  H := .of (CohomologyClass K L m)
  i := AddCommGrpCat.ofHom (Cocycle.toCochainAddMonoidHom K L m)
  π := AddCommGrpCat.ofHom (CohomologyClass.mkAddMonoidHom K L m)
  wi := by cat_disch
  hi := Cocycle.isKernel K L _ _ hp
  wπ := by
    ext x
    dsimp
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n, hm, x, rfl⟩
  hπ :=
    Cofork.IsColimit.mk _
      (fun s ↦ AddCommGrpCat.ofHom (CohomologyClass.descAddMonoidHom s.π.hom
        (by
          rintro ⟨_, _⟩ ⟨q, hq, y, rfl⟩
          obtain rfl : n = q := by lia
          simpa only [zero_comp] using! ConcreteCategory.congr_hom s.condition y)))
      (fun s ↦ rfl)
      (fun s l hl ↦ by
        ext x
        obtain ⟨y, rfl⟩ := x.mk_surjective
        simpa using! ConcreteCategory.congr_hom hl y)

/-- `CohomologyClass K L m` identifies to the cohomology of the complex `HomComplex K L`
in degree `m`. -/
@[simps!]
/-
**CochainComplex.HomComplex.leftHomologyData** 是 Mathlib 中的一个定义，位于命名空间 `CochainC
omplex.HomComplex`。
形式化陈述：leftHomologyData : ((HomComplex K L).sc n).LeftHomologyData
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CohomologyClass K L m` identifies to the cohomology of the complex `HomComplex 
K L`
in degree `m`.
-/
noncomputable def leftHomologyData :
    ((HomComplex K L).sc n).LeftHomologyData :=
  leftHomologyData' K L _ n _ (by simp) (by simp)

/-- The homology of `HomComplex K L` in degree `n` identifies to `CohomologyClass K L n`. -/
/-
**CochainComplex.HomComplex.homologyAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CochainC
omplex.HomComplex`。
形式化陈述：homologyAddEquiv : (HomComplex K L).homology n ≃+ CohomologyClass K L n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology of `HomComplex K L` in degree `n` identifies to `CohomologyClass K 
L n`.
-/
noncomputable def homologyAddEquiv :
    (HomComplex K L).homology n ≃+ CohomologyClass K L n :=
  (leftHomologyData K L n).homologyIso.addCommGroupIsoToAddEquiv

end HomComplex

end CochainComplex

