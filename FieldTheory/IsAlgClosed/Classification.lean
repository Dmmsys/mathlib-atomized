/-
Copyright (c) 2022 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Classification of Algebraically closed fields

This file contains results related to classifying algebraically closed fields.

## Main statements

* `IsAlgClosed.equivOfTranscendenceBasis` Two algebraically closed fields with the same
  characteristic and the same cardinality of transcendence basis are isomorphic.
* `IsAlgClosed.ringEquivOfCardinalEqOfCharEq` Two uncountable algebraically closed fields
  are isomorphic if they have the same characteristic and the same cardinality.
-/

@[expose] public section


universe u v w

open scoped Cardinal Polynomial

open Cardinal

namespace IsAlgClosed

section Classification

noncomputable section

variable {R L K : Type*} [CommRing R]
variable [Field K] [Algebra R K]
variable [Field L] [Algebra R L]
variable {ι : Type*} (v : ι → K)
variable {κ : Type*} (w : κ → L)
variable (hv : AlgebraicIndependent R v)

/-
**IsAlgClosed.isAlgClosure_of_transcendence_basis** 是 Mathlib 中的一个定理，位于命名空间 `IsA
lgClosed`。
形式化陈述：isAlgClosure_of_transcendence_basis [IsAlgClosed K] (hv : IsTranscendenceB
asis R v) : IsAlgClosure (Algebra.adjoin R (Set.range v)) K
参数：hv : IsTranscendenceBasis R v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsTranscendenceBasis.isAlgebraic`：IsTranscendenceBasis.isAlgebraic [Nont
rivial R] (hx : IsTranscendenceBasis R x) : Algebra.IsAlgebraic (adjoin R (range
 x)) A
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem isAlgClosure_of_transcendence_basis [IsAlgClosed K] (hv : IsTranscendenceBasis R v) :
    IsAlgClosure (Algebra.adjoin R (Set.range v)) K :=
  letI := RingHom.domain_nontrivial (algebraMap R K)
  { isAlgClosed := by infer_instance
    isAlgebraic := hv.isAlgebraic }

variable (hw : AlgebraicIndependent R w)

/-- setting `R` to be `ZMod (ringChar R)` this result shows that if two algebraically
closed fields have equipotent transcendence bases and the same characteristic then they are
isomorphic. -/
/-
**IsAlgClosed.equivOfTranscendenceBasis** 是 Mathlib 中的一个定义，位于命名空间 `IsAlgClosed`。
形式化陈述：equivOfTranscendenceBasis [IsAlgClosed K] [IsAlgClosed L] (e : ι ≃ κ) (hv 
: IsTranscendenceBasis R v) (hw : IsTranscendenceBasis R w) : K ≃+* L
参数：e : ι ≃ κ；hv : IsTranscendenceBasis R v；hw : IsTranscendenceBasis R w。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `IsAlgClosed.isAlgClosure_of_transcendence_basis`：isAlgClosure_of_transce
ndence_basis [IsAlgClosed K] (hv : IsTranscendenceBasis R v) : IsAlgClosure (Alg
ebra.adjoin R (Set.range v)) K

--- 原说明 ---
setting `R` to be `ZMod (ringChar R)` this result shows that if two algebraicall
y
closed fields have equipotent transcendence bases and the same characteristic th
en they are
isomorphic.
-/
def equivOfTranscendenceBasis [IsAlgClosed K] [IsAlgClosed L] (e : ι ≃ κ)
    (hv : IsTranscendenceBasis R v) (hw : IsTranscendenceBasis R w) : K ≃+* L := by
  letI := isAlgClosure_of_transcendence_basis v hv
  letI := isAlgClosure_of_transcendence_basis w hw
  have e : Algebra.adjoin R (Set.range v) ≃+* Algebra.adjoin R (Set.range w) := by
    refine hv.1.aevalEquiv.symm.toRingEquiv.trans ?_
    refine (AlgEquiv.ofAlgHom (MvPolynomial.rename e)
      (MvPolynomial.rename e.symm) ?_ ?_).toRingEquiv.trans ?_
    · ext; simp
    · ext; simp
    exact hw.1.aevalEquiv.toRingEquiv
  exact IsAlgClosure.equivOfEquiv K L e

end

end Classification

section Cardinal

variable {R : Type u} {K : Type v} [CommRing R] [Field K] [Algebra R K] [IsAlgClosed K]
variable {ι : Type w} (v : ι → K)

variable {K' : Type u} [Field K'] [Algebra R K'] [IsAlgClosed K']
variable {ι' : Type u} (v' : ι' → K')

/-- The cardinality of an algebraically closed `R`-algebra is less than or equal to
the maximum of the cardinality of `R`, the cardinality of a transcendence basis and
`ℵ₀`

For a simpler, but less universe-polymorphic statement, see
`IsAlgClosed.cardinal_le_max_transcendence_basis'` -/
/-
**IsAlgClosed.cardinal_le_max_transcendence_basis** 是 Mathlib 中的一个定理，位于命名空间 `IsA
lgClosed`。
形式化陈述：cardinal_le_max_transcendence_basis (hv : IsTranscendenceBasis R v) : Card
inal.lift.{max u w} #K <= max (max (Cardinal.lift.{max v w} #R) (Cardinal.lift.{
max u v} #ι)) ℵ₀
参数：hv : IsTranscendenceBasis R v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsAlgClosed.isAlgClosure_of_transcendence_basis`：isAlgClosure_of_transce
ndence_basis [IsAlgClosed K] (hv : IsTranscendenceBasis R v) : IsAlgClosure (Alg
ebra.adjoin R (Set.range v)) K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_max`：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = m
ax (lift.{u, v} a) (lift.{u, v} b)
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.IsAlgebraic.cardinalMk_le_max`：cardinalMk_le_max : #L <= max #R 
ℵ₀
· 使用定理 `IsAlgClosure.isAlgebraic`：∀ {R : Type u} {K : Type v} {inst : CommRing R
} {inst_1 : Field K} {inst_2 : Algebra R K}   {inst_3 : Module.IsTorsionFree R K
} [self : IsAl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq`：lift_mk_eq {α : Type u} {β : Type v} : lift.{max v 
w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用定理 `MvPolynomial.cardinalMk_le_max_lift`：cardinalMk_le_max_lift {σ : Type u}
 {R : Type v} [CommSemiring R] : #(MvPolynomial σ R) <= lift.{u} #R ⊔ lift.{v} #
σ ⊔ ℵ₀
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The cardinality of an algebraically closed `R`-algebra is less than or equal to
the maximum of the cardinality of `R`, the cardinality of a transcendence basis 
and
`ℵ₀`

For a simpler, but less universe-polymorphic statement, see
`IsAlgClosed.cardinal_le_max_transcendence_basis'`
-/
theorem cardinal_le_max_transcendence_basis (hv : IsTranscendenceBasis R v) :
    Cardinal.lift.{max u w} #K ≤ max (max (Cardinal.lift.{max v w} #R)
      (Cardinal.lift.{max u v} #ι)) ℵ₀ :=
  calc
    Cardinal.lift.{max u w} #K ≤ Cardinal.lift.{max u w}
        (max #(Algebra.adjoin R (Set.range v)) ℵ₀) := by
      let := isAlgClosure_of_transcendence_basis v hv
      simpa using Algebra.IsAlgebraic.cardinalMk_le_max (Algebra.adjoin R (Set.range v)) K
    _ = Cardinal.lift.{v} (max #(MvPolynomial ι R) ℵ₀) := by
      rw [lift_max, ← Cardinal.lift_mk_eq.2 ⟨hv.1.aevalEquiv.toEquiv⟩, lift_aleph0,
        ← lift_aleph0.{max u v w, max u w}, ← lift_max, lift_umax.{max u w, v}]
    _ ≤ Cardinal.lift.{v} (max (max (max (Cardinal.lift #R) (Cardinal.lift #ι)) ℵ₀) ℵ₀) :=
        lift_le.2 (max_le_max MvPolynomial.cardinalMk_le_max_lift le_rfl)
    _ = _ := by simp

/-- The cardinality of an algebraically closed `R`-algebra is less than or equal to
the maximum of the cardinality of `R`, the cardinality of a transcendence basis and
`ℵ₀`

A less-universe polymorphic, but simpler statement of
`IsAlgClosed.cardinal_le_max_transcendence_basis` -/
/-
**IsAlgClosed.cardinal_le_max_transcendence_basis'** 是 Mathlib 中的一个定理，位于命名空间 `Is
AlgClosed`。
形式化陈述：cardinal_le_max_transcendence_basis' (hv : IsTranscendenceBasis R v') : #K
' <= max (max #R #ι') ℵ₀
参数：hv : IsTranscendenceBasis R v'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IsAlgClosed.cardinal_le_max_transcendence_basis`：cardinal_le_max_transce
ndence_basis (hv : IsTranscendenceBasis R v) : Cardinal.lift.{max u w} #K <= max
 (max (Cardinal.lift.{max v w} #R) (C…

--- 原说明 ---
The cardinality of an algebraically closed `R`-algebra is less than or equal to
the maximum of the cardinality of `R`, the cardinality of a transcendence basis 
and
`ℵ₀`

A less-universe polymorphic, but simpler statement of
`IsAlgClosed.cardinal_le_max_transcendence_basis`
-/
theorem cardinal_le_max_transcendence_basis' (hv : IsTranscendenceBasis R v') :
    #K' ≤ max (max #R #ι') ℵ₀ := by
  simpa using cardinal_le_max_transcendence_basis v' hv

/-- If `K` is an uncountable algebraically closed field, then its
cardinality is the same as that of a transcendence basis.

For a simpler, but less universe-polymorphic statement, see
`IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'` -/
/-
**IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt** 是 Mathlib 
中的一个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt [Nontrivial R] (hv :
 IsTranscendenceBasis R v) (hR : #R <= ℵ₀) (hK : ℵ₀ < #K) : Cardinal.lift.{w} #K
 = Cardinal.lift.{v} #ι
参数：hv : IsTranscendenceBasis R v；hR : #R <= ℵ₀；hK : ℵ₀ < #K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `IsAlgClosed.cardinal_le_max_transcendence_basis`：cardinal_le_max_transce
ndence_basis (hv : IsTranscendenceBasis R v) : Cardinal.lift.{max u w} #K <= max
 (max (Cardinal.lift.{max v w} #R) (C…
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_le`：lift_mk_le {α : Type v} {β : Type w} : lift.{max u 
w} #α <= lift.{max u v} #β ↔ Nonempty (α ↪ β)
· 使用定理 `AlgebraicIndependent.injective`：∀ {ι : Type u} {R : Type u_2} {A : Type 
v} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],
   AlgebraicIndepend…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Cardinal.lift_injective`：lift_injective : Injective lift.{u, v}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a

--- 原说明 ---
If `K` is an uncountable algebraically closed field, then its
cardinality is the same as that of a transcendence basis.

For a simpler, but less universe-polymorphic statement, see
`IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'`
-/
theorem cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt [Nontrivial R]
    (hv : IsTranscendenceBasis R v) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) :
    Cardinal.lift.{w} #K = Cardinal.lift.{v} #ι :=
  have : ℵ₀ ≤ Cardinal.lift.{max u v} #ι := le_of_not_gt fun h => not_le_of_gt
    (show ℵ₀ < Cardinal.lift.{max u w} #K by simpa) <|
    calc
      Cardinal.lift.{max u w, v} #K ≤ max (max (Cardinal.lift.{max v w, u} #R)
        (Cardinal.lift.{max u v, w} #ι)) ℵ₀ := cardinal_le_max_transcendence_basis v hv
      _ ≤ _ := max_le (max_le (by simpa) (by simpa using le_of_lt h)) le_rfl
  suffices Cardinal.lift.{max u w} #K = Cardinal.lift.{max u v} #ι
    from Cardinal.lift_injective.{u, max v w} (by simpa)
  le_antisymm
    (calc
      Cardinal.lift.{max u w} #K ≤ max (max
        (Cardinal.lift.{max v w} #R) (Cardinal.lift.{max u v} #ι)) ℵ₀ :=
        cardinal_le_max_transcendence_basis v hv
      _ = Cardinal.lift #ι := by
        rw [max_eq_left, max_eq_right]
        · exact le_trans (by simpa using hR) this
        · exact le_max_of_le_right this)
    (lift_mk_le.2 ⟨⟨v, hv.1.injective⟩⟩)

/-- If `K` is an uncountable algebraically closed field, then its
cardinality is the same as that of a transcendence basis.

This is a simpler, but less general statement of
`cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt`. -/
/-
**IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'** 是 Mathlib
 中的一个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' [Nontrivial R] (hv 
: IsTranscendenceBasis R v') (hR : #R <= ℵ₀) (hK : ℵ₀ < #K') : #K' = #ι'
参数：hv : IsTranscendenceBasis R v'；hR : #R <= ℵ₀；hK : ℵ₀ < #K'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt`：cardi
nal_eq_cardinal_transcendence_basis_of_aleph0_lt [Nontrivial R] (hv : IsTranscen
denceBasis R v) (hR : #R <= ℵ₀) (hK : ℵ₀ < #K) : Cardin…

--- 原说明 ---
If `K` is an uncountable algebraically closed field, then its
cardinality is the same as that of a transcendence basis.

This is a simpler, but less general statement of
`cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt`.
-/
theorem cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' [Nontrivial R]
    (hv : IsTranscendenceBasis R v') (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K') : #K' = #ι' := by
  simpa using cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt v' hv hR hK

end Cardinal

variable {K : Type u} {L : Type v} [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L]

/-- Two uncountable algebraically closed fields of characteristic zero are isomorphic
if they have the same cardinality. -/
/-
**IsAlgClosed.ringEquiv_of_equiv_of_charZero** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClo
sed`。
形式化陈述：ringEquiv_of_equiv_of_charZero [CharZero K] [CharZero L] (hK : ℵ₀ < #K) (h
KL : Nonempty (K ≃ L)) : Nonempty (K ≃+* L)
参数：hK : ℵ₀ < #K；hKL : Nonempty (K ≃ L)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isTranscendenceBasis`：exists_isTranscendenceBasis [FaithfulSMul R
 A] : exists s : Set A, IsTranscendenceBasis R ((↑) : s -> A)
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.aleph0_lt_lift`：aleph0_lt_lift {c : Cardinal.{u}} : ℵ₀ < lift.{
v} c ↔ ℵ₀ < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Cardinal.lift_injective`：lift_injective : Injective lift.{u, v}
· 使用定理 `IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt`：cardi
nal_eq_cardinal_transcendence_basis_of_aleph0_lt [Nontrivial R] (hv : IsTranscen
denceBasis R v) (hR : #R <= ℵ₀) (hK : ℵ₀ < #K) : Cardin…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Cardinal.mk_int`：mk_int : #Int = ℵ₀
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
Two uncountable algebraically closed fields of characteristic zero are isomorphi
c
if they have the same cardinality.
-/
theorem ringEquiv_of_equiv_of_charZero [CharZero K] [CharZero L] (hK : ℵ₀ < #K)
    (hKL : Nonempty (K ≃ L)) : Nonempty (K ≃+* L) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℤ K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℤ L
  have hL : ℵ₀ < #L := by
    rwa [← aleph0_lt_lift.{v, u}, ← lift_mk_eq'.2 hKL, aleph0_lt_lift]
  have : Cardinal.lift.{v} #s = Cardinal.lift.{u} #t := by
    rw [← lift_injective (cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _
        hs (le_of_eq mk_int) hK),
      ← lift_injective (cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _
        ht (le_of_eq mk_int) hL)]
    exact Cardinal.lift_mk_eq'.2 hKL
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.1 this
  exact ⟨equivOfTranscendenceBasis _ _ e hs ht⟩
/-
**IsAlgClosed.ringEquiv_of_Cardinal_eq_of_charP** 是 Mathlib 中的一个定理，位于命名空间 `IsAlg
Closed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ringEquiv_of_Cardinal_eq_of_charP (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]
    (hK : ℵ₀ < #K) (hKL : Nonempty (K ≃ L)) : Nonempty (K ≃+* L) := by
  let : Algebra (ZMod p) K := ZMod.algebra _ _
  let : Algebra (ZMod p) L := ZMod.algebra _ _
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (ZMod p) K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis (ZMod p) L
  have hL : ℵ₀ < #L := by
    rwa [← aleph0_lt_lift.{v, u}, ← lift_mk_eq'.2 hKL, aleph0_lt_lift]
  have : Cardinal.lift.{v} #s = Cardinal.lift.{u} #t := by
    rw [← lift_injective (cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _
        hs (le_of_lt (lt_aleph0_of_finite _)) hK),
      ← lift_injective (cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _
        ht (le_of_lt (lt_aleph0_of_finite _)) hL)]
    exact Cardinal.lift_mk_eq'.2 hKL
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.1 this
  exact ⟨equivOfTranscendenceBasis _ _ e hs ht⟩

/-- Two uncountable algebraically closed fields are isomorphic
if they have the same cardinality and the same characteristic. -/
/-
**IsAlgClosed.ringEquiv_of_equiv_of_char_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClos
ed`。
形式化陈述：ringEquiv_of_equiv_of_char_eq (p : Nat) [CharP K p] [CharP L p] (hK : ℵ₀ <
 #K) (hKL : Nonempty (K ≃ L)) : Nonempty (K ≃+* L)
参数：p : Nat；hK : ℵ₀ < #K；hKL : Nonempty (K ≃ L)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `_private.Mathlib.FieldTheory.IsAlgClosed.Classification.0.IsAlgClosed.ri
ngEquiv_of_Cardinal_eq_of_charP`：∀ {K : Type u} {L : Type v} [inst : Field K] [i
nst_1 : Field L] [IsAlgClosed K] [IsAlgClosed L] (p : ℕ)   [Fact (Nat.Prime p)] 
[CharP K p] […
· 使用引理 `CharP.charP_to_charZero`：charP_to_charZero [CharP R 0] : CharZero R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAlgClosed.ringEquiv_of_equiv_of_charZero`：ringEquiv_of_equiv_of_charZe
ro [CharZero K] [CharZero L] (hK : ℵ₀ < #K) (hKL : Nonempty (K ≃ L)) : Nonempty 
(K ≃+* L)

--- 原说明 ---
Two uncountable algebraically closed fields are isomorphic
if they have the same cardinality and the same characteristic.
-/
theorem ringEquiv_of_equiv_of_char_eq (p : ℕ) [CharP K p] [CharP L p] (hK : ℵ₀ < #K)
    (hKL : Nonempty (K ≃ L)) : Nonempty (K ≃+* L) := by
  rcases CharP.char_is_prime_or_zero K p with (hp | hp)
  · have : Fact p.Prime := ⟨hp⟩
    exact ringEquiv_of_Cardinal_eq_of_charP p hK hKL
  · simp only [hp] at *
    let : CharZero K := CharP.charP_to_charZero K
    let : CharZero L := CharP.charP_to_charZero L
    exact ringEquiv_of_equiv_of_charZero hK hKL

end IsAlgClosed

