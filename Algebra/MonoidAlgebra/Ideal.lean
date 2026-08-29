/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Lemmas about ideals of `MonoidAlgebra` and `AddMonoidAlgebra`
-/

public section


variable {k A G : Type*}

/--
theorem `MonoidAlgebra.mem_ideal_span_of_image` / 定理 `MonoidAlgebra.mem_ideal_span_of_image`

English:
theorem MonoidAlgebra.mem_ideal_span_of_image
  statement: [Monoid G] [Semiring k] {s : Set G}
  proof: by
  classical
  let RHS : Ideal (MonoidAlgebra k G) :=
    { carrier := { p | forall m : G, m in p.coeff.support -> exists m' in s, exists d, m = d * m' }
      add_mem' {x y} hx hy m hm := (Finset.mem_union.1 <| Finsupp.support_add hm).elim (hx m) (hy m)
      zero_mem' := by simp
      smul_mem' x y hy m hm := by
        simp only [smul_eq_mul, mul_def, coeff_finsuppSum] at hm
        obtain ⟨xm, -, hm⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hm)
        obtain ⟨ym, hym, hm⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hm)
        obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hm)
        refine (hy _ hym).imp fun sm p => And.imp_right ?_ p
        rintro ⟨d, rfl⟩
        exact ⟨xm * d, (mul_assoc _ _ _).symm⟩ }
  change _ ↔ x in RHS
  constructor
  · suffices Ideal.span (⇑(of k G) '' s) <= RHS from @this x
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩ m hm
    refine ⟨_, hi, 1, ?_⟩
    simpa using Finsupp.support_single_subset hm
  · intro hx
    rw [← x.sum_coeff_single]
    apply Ideal.sum_mem _ fun i hi => ?_
    obtain ⟨d, hd, d2, rfl⟩ := hx _ hi
    simpa using Ideal.mul_mem_left _ (.single d2 <| x.coeff (d2 * d)) (b := of k G d)
      (Ideal.subset_span <| Set.mem_image_of_mem _ hd)

中文:
定理 幺半群代数.mem_ideal_span_of_image
  结论: [幺半群 G] [半环 k] {s : 集合 G}
  证明: by
  classical
  let RHS : Ideal (MonoidAlgebra k G) :=
    { carrier := { p | forall m : G, m in p.coeff.support -> exists m' in s, exists d, m = d * m' }
      add_mem' {x y} hx hy m hm := (Finset.mem_union.1 <| Finsupp.support_add hm).elim (hx m) (hy m)
      zero_mem' := by simp
      smul_mem' x y hy m hm := by
        simp only [smul_eq_mul, mul_def, coeff_finsuppSum] at hm
        obtain ⟨xm, -, hm⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hm)
        obtain ⟨ym, hym, hm⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hm)
        obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hm)
        refine (hy _ hym).imp fun sm p => And.imp_right ?_ p
        rintro ⟨d, rfl⟩
        exact ⟨xm * d, (mul_assoc _ _ _).symm⟩ }
  change _ ↔ x in RHS
  constructor
  · suffices Ideal.span (⇑(of k G) '' s) <= RHS from @this x
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩ m hm
    refine ⟨_, hi, 1, ?_⟩
    simpa using Finsupp.support_single_subset hm
  · intro hx
    rw [← x.sum_coeff_single]
    apply Ideal.sum_mem _ fun i hi => ?_
    obtain ⟨d, hd, d2, rfl⟩ := hx _ hi
    simpa using Ideal.mul_mem_left _ (.single d2 <| x.coeff (d2 * d)) (b := of k G d)
      (Ideal.subset_span <| Set.mem_image_of_mem _ hd)

Depends on / 依赖: Finset, Finset.mem_biUnion.mp, Finset.mem_union, Finsupp, Finsupp.support_add, Finsupp.support_sum, MonoidAlgebra, add_mem, carrier, classical, coeff_finsuppSum, mem_biUnion, mem_union, mul_def, p.coeff.support, smul_eq_mul, smul_mem, support, support_add, support_sum
-/
theorem MonoidAlgebra.mem_ideal_span_of_image [Monoid G] [Semiring k] {s : Set G}
    {x : MonoidAlgebra k G} :
    x in Ideal.span (MonoidAlgebra.of k G '' s) ↔
      forall m in x.coeff.support, exists m' in s, exists d, m = d * m' := by
  classical
  let RHS : Ideal (MonoidAlgebra k G) :=
    { carrier := { p | forall m : G, m in p.coeff.support -> exists m' in s, exists d, m = d * m' }
      add_mem' {x y} hx hy m hm := (Finset.mem_union.1 <| Finsupp.support_add hm).elim (hx m) (hy m)
      zero_mem' := by simp
      smul_mem' x y hy m hm := by
        simp only [smul_eq_mul, mul_def, coeff_finsuppSum] at hm
        obtain ⟨xm, -, hm⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hm)
        obtain ⟨ym, hym, hm⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hm)
        obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hm)
        refine (hy _ hym).imp fun sm p => And.imp_right ?_ p
        rintro ⟨d, rfl⟩
        exact ⟨xm * d, (mul_assoc _ _ _).symm⟩ }
  change _ ↔ x in RHS
  constructor
  · suffices Ideal.span (⇑(of k G) '' s) <= RHS from @this x
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩ m hm
    refine ⟨_, hi, 1, ?_⟩
    simpa using Finsupp.support_single_subset hm
  · intro hx
    rw [← x.sum_coeff_single]
    apply Ideal.sum_mem _ fun i hi => ?_
    obtain ⟨d, hd, d2, rfl⟩ := hx _ hi
    simpa using Ideal.mul_mem_left _ (.single d2 <| x.coeff (d2 * d)) (b := of k G d)
      (Ideal.subset_span <| Set.mem_image_of_mem _ hd)

/--
theorem `AddMonoidAlgebra.mem_ideal_span_of'_image` / 定理 `AddMonoidAlgebra.mem_ideal_span_of'_image`

English:
theorem AddMonoidAlgebra.mem_ideal_span_of'_image
  statement: [AddMonoid A] [Semiring k] {s : Set A}
  proof: by
  -- TODO: this proof is a direct copy of MonoidAlgebra.mem_ideal_span_of_image.
  -- Alternatively, we could prove it via the equiv between `MonoidAlgebra` and `AddMonoidAlgebra`,
  -- but that would require a lot more API.
  classical
  let RHS : Ideal (AddMonoidAlgebra k A) := {
    carrier := { p | forall m : A, m in p.coeff.support -> exists m' in s, exists d, m = d + m' }
    add_mem' {x y} hx hy m hm := (Finset.mem_union.1 <| Finsupp.support_add hm).elim (hx m) (hy m)
    zero_mem' := by simp
    smul_mem' x y hy m hm := by
      simp only [smul_eq_mul, mul_def, coeff_finsuppSum] at hm
obtain ⟨xm, -, hm⟩ := Finset.mem_biUnion.mp Finsupp.support_sum hm
obtain ⟨ym, hym, hm⟩ := Finset.mem_biUnion.mp Finsupp.support_sum hm
obtain rfl := Finset.mem_singleton.mp Finsupp.support_single_subset hm
      refine (hy _ hym).imp fun sm => .imp_right ?_
      rintro ⟨d, rfl⟩
      exact ⟨xm + d, (add_assoc ..).symm⟩
  }
  change _ ↔ x in RHS
  constructor
  · suffices Ideal.span (of' k A '' s) <= RHS from @this x
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩ m hm
    refine ⟨_, hi, 0, ?_⟩
    simpa using Finsupp.support_single_subset hm
  · intro hx
    rw [← x.sum_coeff_single]
    apply Ideal.sum_mem _ fun i hi => ?_
    obtain ⟨d, hd, d2, rfl⟩ := hx _ hi
    simpa using Ideal.mul_mem_left _ (.single d2 <| x.coeff (d2 + d))
      (b := of' k A d) (Ideal.subset_span <| Set.mem_image_of_mem _ hd)

中文:
定理 加法幺半群代数.mem_ideal_span_of'_image
  结论: [加法幺半群 A] [半环 k] {s : 集合 A}
  证明: by
  -- TODO: this proof is a direct copy of MonoidAlgebra.mem_ideal_span_of_image.
  -- Alternatively, we could prove it via the equiv between `MonoidAlgebra` and `AddMonoidAlgebra`,
  -- but that would require a lot more API.
  classical
  let RHS : Ideal (AddMonoidAlgebra k A) := {
    carrier := { p | forall m : A, m in p.coeff.support -> exists m' in s, exists d, m = d + m' }
    add_mem' {x y} hx hy m hm := (Finset.mem_union.1 <| Finsupp.support_add hm).elim (hx m) (hy m)
    zero_mem' := by simp
    smul_mem' x y hy m hm := by
      simp only [smul_eq_mul, mul_def, coeff_finsuppSum] at hm
obtain ⟨xm, -, hm⟩ := Finset.mem_biUnion.mp Finsupp.support_sum hm
obtain ⟨ym, hym, hm⟩ := Finset.mem_biUnion.mp Finsupp.support_sum hm
obtain rfl := Finset.mem_singleton.mp Finsupp.support_single_subset hm
      refine (hy _ hym).imp fun sm => .imp_right ?_
      rintro ⟨d, rfl⟩
      exact ⟨xm + d, (add_assoc ..).symm⟩
  }
  change _ ↔ x in RHS
  constructor
  · suffices Ideal.span (of' k A '' s) <= RHS from @this x
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩ m hm
    refine ⟨_, hi, 0, ?_⟩
    simpa using Finsupp.support_single_subset hm
  · intro hx
    rw [← x.sum_coeff_single]
    apply Ideal.sum_mem _ fun i hi => ?_
    obtain ⟨d, hd, d2, rfl⟩ := hx _ hi
    simpa using Ideal.mul_mem_left _ (.single d2 <| x.coeff (d2 + d))
      (b := of' k A d) (Ideal.subset_span <| Set.mem_image_of_mem _ hd)
-/
theorem AddMonoidAlgebra.mem_ideal_span_of'_image [AddMonoid A] [Semiring k] {s : Set A}
    {x : AddMonoidAlgebra k A} :
    x in Ideal.span (AddMonoidAlgebra.of' k A '' s) ↔
      forall m in x.coeff.support, exists m' in s, exists d, m = d + m' := by
  -- TODO: this proof is a direct copy of MonoidAlgebra.mem_ideal_span_of_image.
  -- Alternatively, we could prove it via the equiv between `MonoidAlgebra` and `AddMonoidAlgebra`,
  -- but that would require a lot more API.
  classical
  let RHS : Ideal (AddMonoidAlgebra k A) := {
    carrier := { p | forall m : A, m in p.coeff.support -> exists m' in s, exists d, m = d + m' }
    add_mem' {x y} hx hy m hm := (Finset.mem_union.1 <| Finsupp.support_add hm).elim (hx m) (hy m)
    zero_mem' := by simp
    smul_mem' x y hy m hm := by
      simp only [smul_eq_mul, mul_def, coeff_finsuppSum] at hm
obtain ⟨xm, -, hm⟩ := Finset.mem_biUnion.mp Finsupp.support_sum hm
obtain ⟨ym, hym, hm⟩ := Finset.mem_biUnion.mp Finsupp.support_sum hm
obtain rfl := Finset.mem_singleton.mp Finsupp.support_single_subset hm
      refine (hy _ hym).imp fun sm => .imp_right ?_
      rintro ⟨d, rfl⟩
      exact ⟨xm + d, (add_assoc ..).symm⟩
  }
  change _ ↔ x in RHS
  constructor
  · suffices Ideal.span (of' k A '' s) <= RHS from @this x
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩ m hm
    refine ⟨_, hi, 0, ?_⟩
    simpa using Finsupp.support_single_subset hm
  · intro hx
    rw [← x.sum_coeff_single]
    apply Ideal.sum_mem _ fun i hi => ?_
    obtain ⟨d, hd, d2, rfl⟩ := hx _ hi
    simpa using Ideal.mul_mem_left _ (.single d2 <| x.coeff (d2 + d))
      (b := of' k A d) (Ideal.subset_span <| Set.mem_image_of_mem _ hd)
