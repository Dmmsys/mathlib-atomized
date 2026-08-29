/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Evaluation of polynomials

This file contains results on the interaction of `Polynomial.eval` and `Polynomial.coeff`
-/

@[expose] public section

noncomputable section

open Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : Nat}

section Semiring

variable [Semiring R] {p q r : R[X]}

section

variable [Semiring S]
variable (f : R ->+* S) (x : S)

@[simp]
/--
theorem `eval₂_at_zero` / 定理 `eval₂_at_zero`

English:
theorem eval₂_at_zero
  statement: p.eval₂ f 0 = f (coeff p 0)
  proof: by
  simp +contextual only [eval₂_eq_sum, zero_pow_eq, mul_ite, mul_zero,
    mul_one, sum, Classical.not_not, mem_support_iff, sum_ite_eq', ite_eq_left_iff, map_zero,
    imp_true_iff]

@[simp]

中文:
定理 eval₂_at_zero
  结论: p.eval₂ f 0 = f (coeff p 0)
  证明: by
  simp +contextual only [eval₂_eq_sum, zero_pow_eq, mul_ite, mul_zero,
    mul_one, sum, Classical.not_not, mem_support_iff, sum_ite_eq', ite_eq_left_iff, map_zero,
    imp_true_iff]

@[simp]

Depends on / 依赖: Classical, Classical.not_not, contextual, imp_true_iff, ite_eq_left_iff, map_zero, mem_support_iff, mul_ite, mul_one, mul_zero, not_not, sum_ite_eq, zero_pow_eq
-/
theorem eval₂_at_zero : p.eval₂ f 0 = f (coeff p 0) := by
  simp +contextual only [eval₂_eq_sum, zero_pow_eq, mul_ite, mul_zero,
    mul_one, sum, Classical.not_not, mem_support_iff, sum_ite_eq', ite_eq_left_iff, map_zero,
    imp_true_iff]

@[simp]
/--
theorem `eval₂_C_X` / 定理 `eval₂_C_X`

English:
theorem eval₂_C_X
  statement: eval₂ C X p = p
  proof: Polynomial.induction_on' p (fun p q hp hq => by simp [hp, hq]) fun n x => by
    rw [eval₂_monomial]; rw [← smul_X_eq_monomial]; rw [C_mul']

中文:
定理 eval₂_C_X
  结论: eval₂ C X p = p
  证明: Polynomial.induction_on' p (fun p q hp hq => by simp [hp, hq]) fun n x => by
    rw [eval₂_monomial]; rw [← smul_X_eq_monomial]; rw [C_mul']

Depends on / 依赖: C_mul, Polynomial, Polynomial.induction_on, induction_on, smul_X_eq_monomial
-/
theorem eval₂_C_X : eval₂ C X p = p :=
  Polynomial.induction_on' p (fun p q hp hq => by simp [hp, hq]) fun n x => by
    rw [eval₂_monomial]; rw [← smul_X_eq_monomial]; rw [C_mul']

end

section Eval

variable {x : R}

/--
theorem `coeff_zero_eq_eval_zero` / 定理 `coeff_zero_eq_eval_zero`

English:
theorem coeff_zero_eq_eval_zero
  given: (p : R[X])
  statement: coeff p 0 = p.eval 0
  proof: calc
    coeff p 0 = coeff p 0 * 0 ^ 0 := by simp
    _ = p.eval 0 := by
      symm
      rw [eval_eq_sum]
      exact Finset.sum_eq_single _ (fun b _ hb => by simp [zero_pow hb]) (by simp)

中文:
定理 coeff_zero_eq_eval_zero
  条件: (p : R[X])
  结论: coeff p 0 = p.eval 0
  证明: calc
    coeff p 0 = coeff p 0 * 0 ^ 0 := by simp
    _ = p.eval 0 := by
      symm
      rw [eval_eq_sum]
      exact Finset.sum_eq_single _ (fun b _ hb => by simp [zero_pow hb]) (by simp)

Depends on / 依赖: Finset, Finset.sum_eq_single, eval_eq_sum, p.eval, sum_eq_single, zero_pow
-/
theorem coeff_zero_eq_eval_zero (p : R[X]) : coeff p 0 = p.eval 0 :=
  calc
    coeff p 0 = coeff p 0 * 0 ^ 0 := by simp
    _ = p.eval 0 := by
      symm
      rw [eval_eq_sum]
      exact Finset.sum_eq_single _ (fun b _ hb => by simp [zero_pow hb]) (by simp)

/--
theorem `zero_isRoot_iff_coeff_zero_eq_zero` / 定理 `zero_isRoot_iff_coeff_zero_eq_zero`

English:
theorem zero_isRoot_iff_coeff_zero_eq_zero
  given: {p : R[X]}
  statement: IsRoot p 0 ↔ p.coeff 0 = 0
  proof: by
  rw [coeff_zero_eq_eval_zero]; rw [IsRoot]

alias ⟨coeff_zero_eq_zero_of_zero_isRoot, zero_isRoot_of_coeff_zero_eq_zero⟩ :=
  zero_isRoot_iff_coeff_zero_eq_zero

中文:
定理 zero_isRoot_iff_coeff_zero_eq_zero
  条件: {p : R[X]}
  结论: IsRoot p 0 ↔ p.coeff 0 = 0
  证明: by
  rw [coeff_zero_eq_eval_zero]; rw [IsRoot]

alias ⟨coeff_zero_eq_zero_of_zero_isRoot, zero_isRoot_of_coeff_zero_eq_zero⟩ :=
  zero_isRoot_iff_coeff_zero_eq_zero

Depends on / 依赖: IsRoot, center, coeff_zero_eq_eval_zero, toRing
-/
theorem zero_isRoot_iff_coeff_zero_eq_zero {p : R[X]} : IsRoot p 0 ↔ p.coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]; rw [IsRoot]

alias ⟨coeff_zero_eq_zero_of_zero_isRoot, zero_isRoot_of_coeff_zero_eq_zero⟩ :=
  zero_isRoot_iff_coeff_zero_eq_zero

end Eval

section Map

variable [Semiring S]
variable (f : R ->+* S)

@[simp]
/--
theorem `coeff_map` / 定理 `coeff_map`

English:
theorem coeff_map
  given: (n : Nat)
  statement: coeff (p.map f) n = f (coeff p n)
  proof: by
  rw [map]; rw [eval₂_def]; rw [coeff_sum]; rw [sum]
  simp_all

中文:
定理 coeff_map
  条件: (n : 自然数)
  结论: coeff (p.map f) n = f (coeff p n)
  证明: by
  rw [map]; rw [eval₂_def]; rw [coeff_sum]; rw [sum]
  simp_all

Depends on / 依赖: coeff_sum
-/
theorem coeff_map (n : Nat) : coeff (p.map f) n = f (coeff p n) := by
  rw [map]; rw [eval₂_def]; rw [coeff_sum]; rw [sum]
  simp_all

/--
lemma `coeff_map_eq_comp` / 引理 `coeff_map_eq_comp`

English:
lemma coeff_map_eq_comp
  given: (p : R[X]) (f : R ->+* S)
  statement: (p.map f).coeff = f ∘ p.coeff
  proof: by
  ext n; exact coeff_map ..

中文:
引理 coeff_map_eq_comp
  条件: (p : R[X]) (f : R ->+* S)
  结论: (p.map f).coeff = f ∘ p.coeff
  证明: by
  ext n; exact coeff_map ..

Depends on / 依赖: coeff_map
-/
lemma coeff_map_eq_comp (p : R[X]) (f : R ->+* S) : (p.map f).coeff = f ∘ p.coeff := by
  ext n; exact coeff_map ..

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: [Semiring T] (g : S ->+* T) (p : R[X])
  statement: (p.map f).map g = p.map (g.comp f)
  proof: ext (by simp [coeff_map])

@[simp]

中文:
定理 map_map
  条件: [Semiring T] (g : S ->+* T) (p : R[X])
  结论: (p.map f).map g = p.map (g.comp f)
  证明: ext (by simp [coeff_map])

@[simp]

Depends on / 依赖: coeff_map
-/
theorem map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.map f).map g = p.map (g.comp f) :=
  ext (by simp [coeff_map])

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: p.map (RingHom.id _) = p
  proof: by simp [Polynomial.ext_iff, coeff_map]

中文:
定理 map_id
  结论: p.map (RingHom.id _) = p
  证明: by simp [Polynomial.ext_iff, coeff_map]

Depends on / 依赖: Polynomial, Polynomial.ext_iff, coeff_map, ext_iff
-/
theorem map_id : p.map (RingHom.id _) = p := by simp [Polynomial.ext_iff, coeff_map]

/--
Definition of `piEquiv` / `piEquiv` 的定义

English:
definition piEquiv
  signature: {ι} [Finite ι] (R : ι -> Type*) [forall i, Semiring (R i)]
  body: .ofBijective (RingHom.pi fun i => mapRingHom (Pi.evalRingHom R i))
    ⟨fun p q h => by ext n i; simpa using congr_arg (fun p => coeff (p i) n) h,
fun p => ⟨.ofFinsupp .ofCoeff .ofSupportFinite (fun n i => coeff (p i) n)
        (Set.finite_iUnion fun i => (p i).support.finite_toSet).subset fun n hn

中文:
定义 piEquiv
  签名: {ι} [Finite ι] (R : ι -> 类型) [对任意 i, Semiring (R i)]
  定义体: .ofBijective (RingHom.pi fun i => mapRingHom (Pi.evalRingHom R i))
    ⟨fun p q h => by ext n i; simpa using congr_arg (fun p => coeff (p i) n) h,
fun p => ⟨.ofFinsupp .ofCoeff .ofSupportFinite (fun n i => coeff (p i) n)
        (Set.finite_iUnion fun i => (p i).support.finite_toSet).subset fun n hn

Depends on / 依赖: Finset, Finset.mem_coe, Function, Function.mem_support, Pi.evalRingHom, RingHom, RingHom.pi, Set.finite_iUnion, Set.mem_iUnion, coeff_map, congr_arg, contrapose, evalRingHom, finite_iUnion, finite_toSet, mapRingHom, mem_coe, mem_iUnion, mem_support, mem_support_iff
-/
def piEquiv {ι} [Finite ι] (R : ι -> Type*) [forall i, Semiring (R i)] :
    (forall i, R i)[X] ≃+* forall i, (R i)[X] :=
  .ofBijective (RingHom.pi fun i => mapRingHom (Pi.evalRingHom R i))
    ⟨fun p q h => by ext n i; simpa using congr_arg (fun p => coeff (p i) n) h,
fun p => ⟨.ofFinsupp .ofCoeff .ofSupportFinite (fun n i => coeff (p i) n)
        (Set.finite_iUnion fun i => (p i).support.finite_toSet).subset fun n hn => by
          simp only [Set.mem_iUnion, Finset.mem_coe, mem_support_iff, Function.mem_support] at hn ⊢
          contrapose! hn; exact funext hn, by ext i n; exact coeff_map _ _⟩⟩

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: (hf : Function.Injective f)
  statement: Function.Injective (map f)
  proof: fun p q h =>
ext fun m => hf by rw [← coeff_map f, ← coeff_map f, h]

中文:
定理 map_injective
  条件: (hf : Function.Injective f)
  结论: Function.Injective (map f)
  证明: fun p q h =>
ext fun m => hf by rw [← coeff_map f, ← coeff_map f, h]
-/
theorem map_injective (hf : Function.Injective f) : Function.Injective (map f) := fun p q h =>
ext fun m => hf by rw [← coeff_map f, ← coeff_map f, h]

/--
theorem `map_injective_iff` / 定理 `map_injective_iff`

English:
theorem map_injective_iff
  statement: Function.Injective (map f) ↔ Function.Injective f
  proof: ⟨fun h r r' eq => by simpa using h (a₁ := C r) (a₂ := C r') (by simpa), map_injective f⟩

中文:
定理 map_injective_iff
  结论: Function.Injective (map f) ↔ Function.Injective f
  证明: ⟨fun h r r' eq => by simpa using h (a₁ := C r) (a₂ := C r') (by simpa), map_injective f⟩

Depends on / 依赖: map_injective
-/
theorem map_injective_iff : Function.Injective (map f) ↔ Function.Injective f :=
  ⟨fun h r r' eq => by simpa using h (a₁ := C r) (a₂ := C r') (by simpa), map_injective f⟩

/--
theorem `map_surjective` / 定理 `map_surjective`

English:
theorem map_surjective
  given: (hf : Function.Surjective f)
  statement: Function.Surjective (map f)
  proof: fun p =>
  p.induction_on'
    (by rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩; exact ⟨p + q, Polynomial.map_add f⟩)
    fun n s =>
    let ⟨r, hr⟩ := hf s
    ⟨monomial n r, by rw [map_monomial f, hr]⟩

中文:
定理 map_surjective
  条件: (hf : Function.Surjective f)
  结论: Function.Surjective (map f)
  证明: fun p =>
  p.induction_on'
    (by rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩; exact ⟨p + q, Polynomial.map_add f⟩)
    fun n s =>
    let ⟨r, hr⟩ := hf s
    ⟨monomial n r, by rw [map_monomial f, hr]⟩
-/
theorem map_surjective (hf : Function.Surjective f) : Function.Surjective (map f) := fun p =>
  p.induction_on'
    (by rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩; exact ⟨p + q, Polynomial.map_add f⟩)
    fun n s =>
    let ⟨r, hr⟩ := hf s
    ⟨monomial n r, by rw [map_monomial f, hr]⟩

/--
theorem `map_surjective_iff` / 定理 `map_surjective_iff`

English:
theorem map_surjective_iff
  statement: Function.Surjective (map f) ↔ Function.Surjective f
  proof: ⟨fun h s => let ⟨p, h⟩ := h (C s); ⟨p.coeff 0, by simpa using congr(coeff $h 0)⟩, map_surjective f⟩

中文:
定理 map_surjective_iff
  结论: Function.Surjective (map f) ↔ Function.Surjective f
  证明: ⟨fun h s => let ⟨p, h⟩ := h (C s); ⟨p.coeff 0, by simpa using congr(coeff $h 0)⟩, map_surjective f⟩

Depends on / 依赖: map_surjective, p.coeff
-/
theorem map_surjective_iff : Function.Surjective (map f) ↔ Function.Surjective f :=
  ⟨fun h s => let ⟨p, h⟩ := h (C s); ⟨p.coeff 0, by simpa using congr(coeff $h 0)⟩, map_surjective f⟩

variable {f}

/--
theorem `map_eq_zero_iff` / 定理 `map_eq_zero_iff`

English:
theorem map_eq_zero_iff
  given: (hf : Function.Injective f)
  statement: p.map f = 0 ↔ p = 0
  proof: map_eq_zero_iff (mapRingHom f) (map_injective f hf)

中文:
定理 map_eq_zero_iff
  条件: (hf : Function.Injective f)
  结论: p.map f = 0 ↔ p = 0
  证明: map_eq_zero_iff (mapRingHom f) (map_injective f hf)
-/
protected theorem map_eq_zero_iff (hf : Function.Injective f) : p.map f = 0 ↔ p = 0 :=
  map_eq_zero_iff (mapRingHom f) (map_injective f hf)

/--
theorem `map_ne_zero_iff` / 定理 `map_ne_zero_iff`

English:
theorem map_ne_zero_iff
  given: (hf : Function.Injective f)
  statement: p.map f != 0 ↔ p != 0
  proof: (Polynomial.map_eq_zero_iff hf).not

中文:
定理 map_ne_zero_iff
  条件: (hf : Function.Injective f)
  结论: p.map f != 0 ↔ p != 0
  证明: (Polynomial.map_eq_zero_iff hf).not
-/
protected theorem map_ne_zero_iff (hf : Function.Injective f) : p.map f != 0 ↔ p != 0 :=
  (Polynomial.map_eq_zero_iff hf).not

variable (f)

@[simp]
/--
theorem `mapRingHom_id` / 定理 `mapRingHom_id`

English:
theorem mapRingHom_id
  statement: mapRingHom (RingHom.id R) = RingHom.id R[X]
  proof: RingHom.ext fun _x => map_id

@[simp]

中文:
定理 mapRingHom_id
  结论: mapRingHom (RingHom.id R) = RingHom.id R[X]
  证明: RingHom.ext fun _x => map_id

@[simp]

Depends on / 依赖: RingHom, RingHom.ext, map_id
-/
theorem mapRingHom_id : mapRingHom (RingHom.id R) = RingHom.id R[X] :=
  RingHom.ext fun _x => map_id

@[simp]
/--
theorem `mapRingHom_comp` / 定理 `mapRingHom_comp`

English:
theorem mapRingHom_comp
  given: [Semiring T] (f : S ->+* T) (g : R ->+* S)
  proof: RingHom.ext Polynomial.map_map g f

中文:
定理 mapRingHom_comp
  条件: [Semiring T] (f : S ->+* T) (g : R ->+* S)
  证明: RingHom.ext Polynomial.map_map g f

Depends on / 依赖: Polynomial, Polynomial.map_map, RingHom, RingHom.ext, map_map
-/
theorem mapRingHom_comp [Semiring T] (f : S ->+* T) (g : R ->+* S) :
    (mapRingHom f).comp (mapRingHom g) = mapRingHom (f.comp g) :=
RingHom.ext Polynomial.map_map g f

/--
theorem `eval₂_map` / 定理 `eval₂_map`

English:
theorem eval₂_map
  given: [Semiring T] (g : S ->+* T) (x : T)
  proof: by
  rw [eval₂_eq_eval_map]; rw [eval₂_eq_eval_map]; rw [map_map]

@[simp]

中文:
定理 eval₂_map
  条件: [Semiring T] (g : S ->+* T) (x : T)
  证明: by
  rw [eval₂_eq_eval_map]; rw [eval₂_eq_eval_map]; rw [map_map]

@[simp]

Depends on / 依赖: map_map
-/
theorem eval₂_map [Semiring T] (g : S ->+* T) (x : T) :
    (p.map f).eval₂ g x = p.eval₂ (g.comp f) x := by
  rw [eval₂_eq_eval_map]; rw [eval₂_eq_eval_map]; rw [map_map]

@[simp]
/--
theorem `eval_zero_map` / 定理 `eval_zero_map`

English:
theorem eval_zero_map
  given: (f : R ->+* S) (p : R[X])
  statement: (p.map f).eval 0 = f (p.eval 0)
  proof: by
  simp [← coeff_zero_eq_eval_zero]

@[simp]

中文:
定理 eval_zero_map
  条件: (f : R ->+* S) (p : R[X])
  结论: (p.map f).eval 0 = f (p.eval 0)
  证明: by
  simp [← coeff_zero_eq_eval_zero]

@[simp]

Depends on / 依赖: coeff_zero_eq_eval_zero
-/
theorem eval_zero_map (f : R ->+* S) (p : R[X]) : (p.map f).eval 0 = f (p.eval 0) := by
  simp [← coeff_zero_eq_eval_zero]

@[simp]
/--
theorem `eval_one_map` / 定理 `eval_one_map`

English:
theorem eval_one_map
  given: (f : R ->+* S) (p : R[X])
  statement: (p.map f).eval 1 = f (p.eval 1)
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [one_pow, mul_one, eval_monomial, map_monomial]

@[simp]

中文:
定理 eval_one_map
  条件: (f : R ->+* S) (p : R[X])
  结论: (p.map f).eval 1 = f (p.eval 1)
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [one_pow, mul_one, eval_monomial, map_monomial]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.induction_on, Polynomial.map_add, eval_add, eval_monomial, induction_on, map_add, map_monomial, monomial, mul_one, one_pow
-/
theorem eval_one_map (f : R ->+* S) (p : R[X]) : (p.map f).eval 1 = f (p.eval 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [one_pow, mul_one, eval_monomial, map_monomial]

@[simp]
/--
theorem `eval_natCast_map` / 定理 `eval_natCast_map`

English:
theorem eval_natCast_map
  given: (f : R ->+* S) (p : R[X]) (n : Nat)
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [map_natCast f, eval_monomial, map_monomial, f.map_pow, f.map_mul]

@[simp]

中文:
定理 eval_natCast_map
  条件: (f : R ->+* S) (p : R[X]) (n : 自然数)
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [map_natCast f, eval_monomial, map_monomial, f.map_pow, f.map_mul]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.induction_on, Polynomial.map_add, eval_add, eval_monomial, f.map_mul, f.map_pow, induction_on, map_add, map_monomial, map_mul, map_natCast, map_pow, monomial
-/
theorem eval_natCast_map (f : R ->+* S) (p : R[X]) (n : Nat) :
    (p.map f).eval (n : S) = f (p.eval n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [map_natCast f, eval_monomial, map_monomial, f.map_pow, f.map_mul]

@[simp]
/--
theorem `eval_intCast_map` / 定理 `eval_intCast_map`

English:
theorem eval_intCast_map
  given: {R S : Type*} [Ring R] [Ring S] (f : R ->+* S) (p : R[X]) (i : Int)
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [map_intCast, eval_monomial, map_monomial, map_pow, map_mul]

中文:
定理 eval_intCast_map
  条件: {R S : 类型} [Ring R] [Ring S] (f : R ->+* S) (p : R[X]) (i : 整数)
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [map_intCast, eval_monomial, map_monomial, map_pow, map_mul]

Depends on / 依赖: Polynomial, Polynomial.induction_on, Polynomial.map_add, eval_add, eval_monomial, induction_on, map_add, map_intCast, map_monomial, map_mul, map_pow, monomial
-/
theorem eval_intCast_map {R S : Type*} [Ring R] [Ring S] (f : R ->+* S) (p : R[X]) (i : Int) :
    (p.map f).eval (i : S) = f (p.eval i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [map_intCast, eval_monomial, map_monomial, map_pow, map_mul]

end Map

section HomEval₂

variable [Semiring S] [Semiring T] (f : R ->+* S) (g : S ->+* T) (p)

/--
theorem `hom_eval₂` / 定理 `hom_eval₂`

English:
theorem hom_eval₂
  given: (x : S)
  statement: g (p.eval₂ f x) = p.eval₂ (g.comp f) (g x)
  proof: by
  rw [← eval₂_map]; rw [eval₂_at_apply]; rw [eval_map]

中文:
定理 hom_eval₂
  条件: (x : S)
  结论: g (p.eval₂ f x) = p.eval₂ (g.comp f) (g x)
  证明: by
  rw [← eval₂_map]; rw [eval₂_at_apply]; rw [eval_map]

Depends on / 依赖: eval_map
-/
theorem hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.comp f) (g x) := by
  rw [← eval₂_map]; rw [eval₂_at_apply]; rw [eval_map]

end HomEval₂

end Semiring

section CommSemiring

section Eval

section

variable [Semiring R] {p q : R[X]} {x : R} [Semiring S] (f : R ->+* S)

/--
theorem `eval₂_hom` / 定理 `eval₂_hom`

English:
theorem eval₂_hom
  given: (x : R)
  statement: p.eval₂ f (f x) = f (p.eval x)
  proof: RingHom.comp_id f ▸ (hom_eval₂ p (RingHom.id R) f x).symm

中文:
定理 eval₂_hom
  条件: (x : R)
  结论: p.eval₂ f (f x) = f (p.eval x)
  证明: RingHom.comp_id f ▸ (hom_eval₂ p (RingHom.id R) f x).symm

Depends on / 依赖: RingHom, RingHom.comp_id, RingHom.id, comp_id
-/
theorem eval₂_hom (x : R) : p.eval₂ f (f x) = f (p.eval x) :=
  RingHom.comp_id f ▸ (hom_eval₂ p (RingHom.id R) f x).symm

end

section

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R ->+* S)

/--
theorem `evalRingHom_zero` / 定理 `evalRingHom_zero`

English:
theorem evalRingHom_zero
  statement: evalRingHom 0 = constantCoeff
  proof: DFunLike.ext _ _ fun p => p.coeff_zero_eq_eval_zero.symm

中文:
定理 evalRingHom_zero
  结论: evalRingHom 0 = constantCoeff
  证明: DFunLike.ext _ _ fun p => p.coeff_zero_eq_eval_zero.symm

Depends on / 依赖: DFunLike, DFunLike.ext, coeff_zero_eq_eval_zero, p.coeff_zero_eq_eval_zero.symm
-/
theorem evalRingHom_zero : evalRingHom 0 = constantCoeff :=
  DFunLike.ext _ _ fun p => p.coeff_zero_eq_eval_zero.symm

end

end Eval

section Map

/--
theorem `support_map_subset` / 定理 `support_map_subset`

English:
theorem support_map_subset
  given: [Semiring R] [Semiring S] (f : R ->+* S) (p : R[X])
  proof: by
  intro x
  contrapose
  simp +contextual

中文:
定理 support_map_subset
  条件: [Semiring R] [Semiring S] (f : R ->+* S) (p : R[X])
  证明: by
  intro x
  contrapose
  simp +contextual

Depends on / 依赖: contextual, contrapose
-/
theorem support_map_subset [Semiring R] [Semiring S] (f : R ->+* S) (p : R[X]) :
    (map f p).support subseteq p.support := by
  intro x
  contrapose
  simp +contextual

/--
theorem `support_map_of_injective` / 定理 `support_map_of_injective`

English:
theorem support_map_of_injective
  statement: [Semiring R] [Semiring S] (p : R[X]) {f : R ->+* S}
  proof: by
  simp_rw [Finset.ext_iff, mem_support_iff, coeff_map, ← map_zero f, hf.ne_iff,
    forall_const]

中文:
定理 support_map_of_injective
  结论: [Semiring R] [Semiring S] (p : R[X]) {f : R ->+* S}
  证明: by
  simp_rw [Finset.ext_iff, mem_support_iff, coeff_map, ← map_zero f, hf.ne_iff,
    forall_const]

Depends on / 依赖: Finset, Finset.ext_iff, coeff_map, ext_iff, forall_const, hf.ne_iff, map_zero, mem_support_iff, ne_iff, simp_rw
-/
theorem support_map_of_injective [Semiring R] [Semiring S] (p : R[X]) {f : R ->+* S}
    (hf : Function.Injective f) : (map f p).support = p.support := by
  simp_rw [Finset.ext_iff, mem_support_iff, coeff_map, ← map_zero f, hf.ne_iff,
    forall_const]

variable [CommSemiring R] [CommSemiring S] (f : R ->+* S)

/--
theorem `IsRoot.map` / 定理 `IsRoot.map`

English:
theorem IsRoot.map
  given: {f : R ->+* S} {x : R} {p : R[X]} (h : IsRoot p x)
  statement: IsRoot (p.map f) (f x)
  proof: by
  rw [IsRoot]; rw [eval_map]; rw [eval₂_hom]; rw [h.eq_zero]; rw [f.map_zero]

中文:
定理 IsRoot.map
  条件: {f : R ->+* S} {x : R} {p : R[X]} (h : IsRoot p x)
  结论: IsRoot (p.map f) (f x)
  证明: by
  rw [IsRoot]; rw [eval_map]; rw [eval₂_hom]; rw [h.eq_zero]; rw [f.map_zero]

Depends on / 依赖: IsRoot, eq_zero, eval_map, f.map_zero, h.eq_zero, map_zero
-/
theorem IsRoot.map {f : R ->+* S} {x : R} {p : R[X]} (h : IsRoot p x) : IsRoot (p.map f) (f x) := by
  rw [IsRoot]; rw [eval_map]; rw [eval₂_hom]; rw [h.eq_zero]; rw [f.map_zero]

/--
theorem `IsRoot.of_map` / 定理 `IsRoot.of_map`

English:
theorem IsRoot.of_map
  statement: {R} [Ring R] {f : R ->+* S} {x : R} {p : R[X]} (h : IsRoot (p.map f) (f x))
  proof: by
  rwa [IsRoot, ← (injective_iff_map_eq_zero' f).mp hf, ← eval₂_hom, ← eval_map]

中文:
定理 IsRoot.of_map
  结论: {R} [Ring R] {f : R ->+* S} {x : R} {p : R[X]} (h : IsRoot (p.map f) (f x))
  证明: by
  rwa [IsRoot, ← (injective_iff_map_eq_zero' f).mp hf, ← eval₂_hom, ← eval_map]

Depends on / 依赖: IsRoot, eval_map, injective_iff_map_eq_zero
-/
theorem IsRoot.of_map {R} [Ring R] {f : R ->+* S} {x : R} {p : R[X]} (h : IsRoot (p.map f) (f x))
    (hf : Function.Injective f) : IsRoot p x := by
  rwa [IsRoot, ← (injective_iff_map_eq_zero' f).mp hf, ← eval₂_hom, ← eval_map]

/--
theorem `isRoot_map_iff` / 定理 `isRoot_map_iff`

English:
theorem isRoot_map_iff
  statement: {R : Type*} [CommRing R] {f : R ->+* S} {x : R} {p : R[X]}
  proof: ⟨fun h => h.of_map hf, fun h => h.map⟩

中文:
定理 isRoot_map_iff
  结论: {R : 类型} [CommRing R] {f : R ->+* S} {x : R} {p : R[X]}
  证明: ⟨fun h => h.of_map hf, fun h => h.map⟩

Depends on / 依赖: h.map, h.of_map, of_map
-/
theorem isRoot_map_iff {R : Type*} [CommRing R] {f : R ->+* S} {x : R} {p : R[X]}
    (hf : Function.Injective f) : IsRoot (p.map f) (f x) ↔ IsRoot p x :=
  ⟨fun h => h.of_map hf, fun h => h.map⟩

end Map

end CommSemiring

end Polynomial
