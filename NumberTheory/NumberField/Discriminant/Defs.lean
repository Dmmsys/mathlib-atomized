/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Localization.NormTrace

/-!
# Number field discriminant

This file defines the discriminant of a number field.

## Main definitions

* `NumberField.discr`: the absolute discriminant of a number field.

## Tags
number field, discriminant
-/

public section

open Module

-- TODO: Rewrite some of the FLT results on the discriminant using the definitions and results of
-- this file

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The absolute discriminant of a number field. -/
/-
**NumberField.discr** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberField`。
形式化陈述：discr : Int
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)

--- 原说明 ---
The absolute discriminant of a number field.
-/
noncomputable abbrev discr : ℤ := Algebra.discr ℤ (RingOfIntegers.basis K)
/-
**NumberField.coe_discr** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：coe_discr : (discr K : Rat) = Algebra.discr Rat (integralBasis K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
· 使用定理 `Algebra.discr_localizationLocalization`：Algebra.discr_localizationLocali
zation (b : Basis ι R S) : Algebra.discr Rₘ (b.localizationLocalization Rₘ M Sₘ)
 = algebraMap R Rₘ (Algebra.…
-/
theorem coe_discr : (discr K : ℚ) = Algebra.discr ℚ (integralBasis K) :=
  (Algebra.discr_localizationLocalization ℤ _ K (RingOfIntegers.basis K)).symm
/-
**NumberField.discr_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：discr_ne_zero : discr K != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.coe_discr`：coe_discr : (discr K : Rat) = Algebra.discr Rat (
integralBasis K)
· 使用定理 `Algebra.discr_not_zero_of_basis`：discr_not_zero_of_basis [Algebra.IsSepa
rable K L] (b : Basis ι K L) : discr K b != 0
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
-/
theorem discr_ne_zero : discr K ≠ 0 := by
  rw [← (Int.cast_injective (α := ℚ)).ne_iff, coe_discr]
  exact Algebra.discr_not_zero_of_basis ℚ (integralBasis K)
/-
**NumberField.discr_eq_discr** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：discr_eq_discr {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι Int (𝓞
 K)) : Algebra.discr Int b = discr K
参数：b : Basis ι Int (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `invariantBasisNumber_of_nontrivial_of_commRing`：∀ {R : Type u} [inst : C
ommRing R] [Nontrivial R], InvariantBasisNumber R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.discr_eq_discr`：discr_eq_discr (b : Basis ι Int A) (b' : Basis ι
 Int A) : Algebra.discr Int b = Algebra.discr Int b'
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `Algebra.discr_reindex`：discr_reindex (b : Basis ι A B) (f : ι ≃ ι') : di
scr A (b ∘ ⇑f.symm) = discr A b
-/
theorem discr_eq_discr {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (𝓞 K)) :
    Algebra.discr ℤ b = discr K := by
  let b₀ := Basis.reindex (RingOfIntegers.basis K) (Basis.indexEquiv (RingOfIntegers.basis K) b)
  rw [Algebra.discr_eq_discr (𝓞 K) b b₀, Basis.coe_reindex, Algebra.discr_reindex]
/-
**NumberField.discr_eq_discr_of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`
。
形式化陈述：discr_eq_discr_of_algEquiv {L : Type*} [Field L] [NumberField L] (f : K ≃ₐ
[Rat] L) : discr K = discr L
参数：f : K ≃ₐ[Rat] L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.intCast_inj`：∀ {a b : ℤ}, ↑a = ↑b ↔ a = b
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.coe_discr`：coe_discr : (discr K : Rat) = Algebra.discr Rat (
integralBasis K)
· 使用定理 `Algebra.discr_eq_discr_of_algEquiv`：discr_eq_discr_of_algEquiv [Fintype 
ι] (b : ι -> B) (f : B ≃ₐ[A] C) : Algebra.discr A b = Algebra.discr A (f ∘ b)
· 使用定理 `NumberField.discr_eq_discr`：discr_eq_discr {ι : Type*} [Fintype ι] [Deci
dableEq ι] (b : Basis ι Int (𝓞 K)) : Algebra.discr Int b = discr K
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
· 使用定理 `Algebra.discr_localizationLocalization`：Algebra.discr_localizationLocali
zation (b : Basis ι R S) : Algebra.discr Rₘ (b.localizationLocalization Rₘ M Sₘ)
 = algebraMap R Rₘ (Algebra.…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NumberField.integralBasis_apply`：integralBasis_apply (i : Free.ChooseBas
isIndex Int (𝓞 K)) : integralBasis K i = algebraMap (𝓞 K) K (RingOfIntegers.basi
s K i)
· 使用定理 `Module.Basis.localizationLocalization_apply`：localizationLocalization_ap
ply {ι : Type*} (b : Basis ι R A) (i) : b.localizationLocalization Rₛ S Aₛ i = a
lgebraMap A Aₛ (b i)
-/
theorem discr_eq_discr_of_algEquiv {L : Type*} [Field L] [NumberField L] (f : K ≃ₐ[ℚ] L) :
    discr K = discr L := by
  let f₀ : 𝓞 K ≃ₗ[ℤ] 𝓞 L := (f.restrictScalars ℤ).mapIntegralClosure.toLinearEquiv
  rw [← Rat.intCast_inj, coe_discr, Algebra.discr_eq_discr_of_algEquiv (integralBasis K) f,
    ← discr_eq_discr L ((RingOfIntegers.basis K).map f₀)]
  change _ = algebraMap ℤ ℚ _
  rw [← Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) L]
  congr 1
  ext
  simp only [Function.comp_apply, integralBasis_apply, Basis.localizationLocalization_apply,
    Basis.map_apply]
  rfl
/-
**NumberField.discr_eq_discr_of_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
`。
形式化陈述：discr_eq_discr_of_ringEquiv {L : Type*} [Field L] [NumberField L] (f : K ≃
+* L) : discr K = discr L
参数：f : K ≃+* L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.discr_eq_discr_of_algEquiv`：discr_eq_discr_of_algEquiv {L : 
Type*} [Field L] [NumberField L] (f : K ≃ₐ[Rat] L) : discr K = discr L
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
· 使用定理 `map_ratCast`：map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass
 F α β] (f : F) (q : Rat) : f q = q
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem discr_eq_discr_of_ringEquiv {L : Type*} [Field L] [NumberField L] (f : K ≃+* L) :
    discr K = discr L :=
  discr_eq_discr_of_algEquiv _ <| AlgEquiv.ofRingEquiv (f := f) fun _ ↦ by simp

end NumberField

namespace Rat

open NumberField

/-- The absolute discriminant of the number field `ℚ` is 1. -/
@[simp]
/-
**Rat.numberField_discr** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：numberField_discr : discr Rat = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.discr_eq_discr`：discr_eq_discr {ι : Type*} [Fintype ι] [Deci
dableEq ι] (b : Basis ι Int (𝓞 K)) : Algebra.discr Int b = discr K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.discr_def`：discr_def [Fintype ι] (b : ι -> B) : discr A b = (tra
ceMatrix A b).det
· 使用定理 `Matrix.det_unique`：det_unique {n : Type*} [Unique n] [DecidableEq n] [Fi
ntype n] (A : Matrix n n R) : det A = A default default
· 使用定理 `Algebra.traceMatrix_apply`：traceMatrix_apply (b : κ -> B) (i j) : traceM
atrix A b i j = traceForm A B (b i) (b j)
· 使用定理 `Algebra.traceForm_apply`：traceForm_apply (x y : S) : traceForm R S x y =
 trace R S (x * y)
· 使用定理 `Module.Basis.map_apply`：map_apply (i) : b.map f i = f (b i)
· 使用定理 `RingEquivClass.toAddEquivClass`：∀ {F : Type u_1} {R : Type u_4} {S : Typ
e u_5} [inst : EquivLike F R S] [inst_1 : Mul R] [inst_2 : Add R]   [inst_3 : Mu
l S] [inst_4 : Add S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.toAddEquiv_eq_coe`：toAddEquiv_eq_coe (f : R ≃+* S) : f.toAddEq
uiv = ↑f
· 使用定理 `AddEquiv.toIntLinearEquiv_symm`：toIntLinearEquiv_symm : e.symm.toIntLine
arEquiv (modM
· 使用定理 `AddEquiv.coe_toIntLinearEquiv`：coe_toIntLinearEquiv : ⇑(e.toIntLinearEqu
iv (modM
· 使用定理 `Module.Basis.singleton_apply`：singleton_apply (ι R : Type*) [Unique ι] [
Semiring R] (i) : Basis.singleton ι R i = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Algebra.trace_eq_matrix_trace`：trace_eq_matrix_trace [DecidableEq ι] (b 
: Basis ι R S) (s : S) : trace R S s = Matrix.trace (Algebra.leftMulMatrix b s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Matrix.trace_one`：trace_one : trace (1 : Matrix n n R) = Fintype.card n
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The absolute discriminant of the number field `ℚ` is 1.
-/
theorem numberField_discr : discr ℚ = 1 := by
  let b : Basis (Fin 1) ℤ (𝓞 ℚ) :=
    Basis.map (Basis.singleton (Fin 1) ℤ) ringOfIntegersEquiv.toAddEquiv.toIntLinearEquiv.symm
  calc NumberField.discr ℚ
    _ = Algebra.discr ℤ b := by convert! (discr_eq_discr ℚ b).symm
    _ = Algebra.trace ℤ (𝓞 ℚ) (b default * b default) := by
      rw [Algebra.discr_def, Matrix.det_unique, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    _ = Algebra.trace ℤ (𝓞 ℚ) 1 := by
      rw [Basis.map_apply, RingEquiv.toAddEquiv_eq_coe, ← AddEquiv.toIntLinearEquiv_symm,
        AddEquiv.coe_toIntLinearEquiv, Basis.singleton_apply,
        show (AddEquiv.symm ↑ringOfIntegersEquiv) (1 : ℤ) = ringOfIntegersEquiv.symm 1 by rfl,
        map_one, mul_one]
    _ = 1 := by rw [Algebra.trace_eq_matrix_trace b]; simp

alias _root_.NumberField.discr_rat := numberField_discr

end Rat

variable {ι ι'} (K) [Field K] [DecidableEq ι] [DecidableEq ι'] [Fintype ι] [Fintype ι']

/-- If `b` and `b'` are `ℚ`-bases of a number field `K` such that
`∀ i j, IsIntegral ℤ (b.toMatrix b' i j)` and `∀ i j, IsIntegral ℤ (b'.toMatrix b i j)` then
`discr ℚ b = discr ℚ b'`. -/
/-
**Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral [NumberField K] {b : B
asis ι Rat K} {b' : Basis ι' Rat K} (h : forall i j, IsIntegral Int (b.toMatrix 
b' i j)) (h' : forall i j, IsIntegral Int (b'.toMatrix b i j)) : discr Rat b = d
iscr Rat b'
参数：h : forall i j, IsIntegral Int (b.toMatrix b' i j)；h' : forall i j, IsIntegra
l Int (b'.toMatrix b i j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `invariantBasisNumber_of_nontrivial_of_commRing`：∀ {R : Type u} [inst : C
ommRing R] [Nontrivial R], InvariantBasisNumber R
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Basis.toMatrix_map_vecMul`：toMatrix_map_vecMul {S : Type*} [Semir
ing S] [Algebra R S] [Fintype ι] (b : Basis ι R S) (v : ι' -> S) : b ᵥ* ((b.toMa
trix v).map <| algebra…
· 使用定理 `Algebra.discr_of_matrix_vecMul`：discr_of_matrix_vecMul (b : ι -> B) (P :
 Matrix ι ι A) : discr A (b ᵥ* P.map (algebraMap A B)) = P.det ^ 2 * discr A b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Algebra.discr_reindex`：discr_reindex (b : Basis ι A B) (f : ι ≃ ι') : di
scr A (b ∘ ⇑f.symm) = discr A b
· 使用定理 `IsIntegral.det`：IsIntegral.det {n : Type*} [Fintype n] [DecidableEq n] {
M : Matrix n n A} (h : forall i j, IsIntegral R (M i j)) : IsIntegral R M.det
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegrallyClosed.isIntegral_iff`：isIntegral_iff [IsIntegrallyClosed R]
 {x : K} : IsIntegral R x ↔ exists y : R, algebraMap R K y = x
· 使用定理 `IsDedekindRing.toIsIntegralClosure`：∀ {A : Type u_2} {inst : CommRing A}
 [self : IsDedekindRing A], IsIntegralClosure A A (FractionRing A)
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
If `b` and `b'` are `ℚ`-bases of a number field `K` such that
`∀ i j, IsIntegral ℤ (b.toMatrix b' i j)` and `∀ i j, IsIntegral ℤ (b'.toMatrix 
b i j)` then
`discr ℚ b = discr ℚ b'`.
-/
theorem Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral [NumberField K]
    {b : Basis ι ℚ K} {b' : Basis ι' ℚ K} (h : ∀ i j, IsIntegral ℤ (b.toMatrix b' i j))
    (h' : ∀ i j, IsIntegral ℤ (b'.toMatrix b i j)) : discr ℚ b = discr ℚ b' := by
  replace h' : ∀ i j, IsIntegral ℤ (b'.toMatrix (b.reindex (b.indexEquiv b')) i j) := by
    intro i j
    convert! h' i ((b.indexEquiv b').symm j)
    simp [Basis.toMatrix_apply]
  rw [← (b.reindex (b.indexEquiv b')).toMatrix_map_vecMul b', discr_of_matrix_vecMul,
    ← one_mul (discr ℚ b), Basis.coe_reindex, discr_reindex]
  congr
  have hint : IsIntegral ℤ ((b.reindex (b.indexEquiv b')).toMatrix b').det :=
    IsIntegral.det fun i j => h _ _
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hunit : IsUnit r := by
    have : IsIntegral ℤ (b'.toMatrix (b.reindex (b.indexEquiv b'))).det :=
      IsIntegral.det fun i j => h' _ _
    obtain ⟨r', hr'⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    refine isUnit_iff_exists_inv.2 ⟨r', ?_⟩
    suffices algebraMap ℤ ℚ (r * r') = 1 by
      rw [← map_one (algebraMap ℤ ℚ)] at this
      exact (IsFractionRing.injective ℤ ℚ) this
    rw [map_mul, hr, hr', ← Matrix.det_mul, Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  rw [← map_one (algebraMap ℤ ℚ), ← hr]
  rcases Int.isUnit_iff.1 hunit with hp | hm
  · simp [hp]
  · simp [hm]
